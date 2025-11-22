import { spawn, ChildProcess } from 'child_process';
import fs from 'fs';
import path from 'path';
import os from 'os';
import { StateManager, ThreadStatus } from './state';
import { EventEmitter } from 'events';

export class ProcessManager {
    private stateManager: StateManager;

    constructor(stateManager: StateManager) {
        this.stateManager = stateManager;
    }

    async startTurn(
        prompt: string,
        workdir: string,
        requestedThreadId?: string
    ): Promise<string> {
        const codexBin = process.env.AGENTCTL_CODEX_BIN || 'codex';
        const isMock = codexBin.endsWith('mock-codex.ts') || process.env.AGENTCTL_CODEX_BIN?.includes('mock');

        // Construct args
        const args = ['exec'];
        if (requestedThreadId) {
            args.push('resume', requestedThreadId);
        }
        args.push('--yolo', '--json');

        // We need to decide where to put the final message *before* we know the thread ID if it's new?
        // Actually, the spec says: "--output-final-message <FINAL_MSG_PATH>"
        // If we don't have a thread ID yet, we can't predict the path `.../threads/<id>/final_message.txt`.
        // BUT, the user said: "ofc only makes sense if you know where the file is by the time you start the codex process"
        // If we create a NEW thread, we don't know the ID.
        // So we might have to use a temporary path and move it?
        // OR, we assume the handshake gives us the ID fast enough? No, the arg is passed at start.
        // If requestedThreadId is null, we are in a bind.
        // Workaround: Use a temp file, then move it to the thread dir once we know the ID and the process finishes.
        // Or, if we are using the SDK, maybe we don't need this arg?
        // The spec says "Real Codex ... --output-final-message".
        // But the actual codex CLI uses --output-last-message
        // Let's use a temp file for now.
        const tempFinalMsg = path.join(os.tmpdir(), `agentctl-final-${Date.now()}-${Math.random()}.txt`);
        args.push('--output-last-message', tempFinalMsg);

        args.push('--cd', workdir);
        args.push(prompt);

        // If mock, we might need to run it with ts-node if it's a .ts file
        let cmd = codexBin;
        let finalArgs = args;

        if (codexBin.endsWith('.ts')) {
            cmd = 'npx';
            finalArgs = ['ts-node', codexBin, ...args];
        }

        console.log(`Spawning: ${cmd} ${finalArgs.join(' ')}`);

        const child = spawn(cmd, finalArgs, {
            cwd: workdir,
            env: { ...process.env },
            stdio: ['ignore', 'pipe', 'pipe'] // stdin ignore, stdout/err pipe
        });

        return new Promise((resolve, reject) => {
            let threadId = requestedThreadId;
            let initialized = false;
            let stdoutBuffer: Buffer[] = [];
            let stderrBuffer: Buffer[] = [];

            const init = (id: string) => {
                if (initialized) return;
                initialized = true;
                threadId = id;

                // Create state
                this.stateManager.ensureThreadDir(id);

                // Initial status
                const status: ThreadStatus = {
                    id,
                    pid: child.pid || null,
                    status: 'running',
                    exit_code: null,
                    workdir,
                    created_at: new Date().toISOString(),
                    updated_at: new Date().toISOString()
                };
                this.stateManager.saveStatus(status);

                // Open streams
                const logStream = fs.createWriteStream(this.stateManager.getLogPath(id), { flags: 'a' });
                const outStream = fs.createWriteStream(this.stateManager.getStdoutPath(id), { flags: 'a' });
                const errStream = fs.createWriteStream(this.stateManager.getStderrPath(id), { flags: 'a' });

                // Flush buffers
                if (stdoutBuffer.length > 0) {
                    const buf = Buffer.concat(stdoutBuffer);
                    logStream.write(buf); // Assuming stdout is JSONL
                    outStream.write(buf);
                }
                if (stderrBuffer.length > 0) {
                    const buf = Buffer.concat(stderrBuffer);
                    errStream.write(buf);
                }

                // Pipe remainder
                child.stdout?.pipe(logStream); // Also to log.jsonl? Yes, spec says stdout IS jsonl.
                child.stdout?.pipe(outStream);
                child.stderr?.pipe(errStream);

                // Handle exit
                child.on('exit', (code) => {
                    // Reload status to check if it was aborted
                    const currentStatus = this.stateManager.getStatus(id);
                    if (currentStatus && currentStatus.status === 'aborted') {
                        return;
                    }

                    status.status = code === 0 ? 'done' : 'failed';
                    status.exit_code = code;
                    status.updated_at = new Date().toISOString();
                    this.stateManager.saveStatus(status);

                    // Move final message if exists
                    if (fs.existsSync(tempFinalMsg)) {
                        const finalPath = path.join(this.stateManager.getThreadDir(id), 'final_message.txt');
                        fs.renameSync(tempFinalMsg, finalPath);
                    }
                });

                resolve(id);
            };

            // Handshake listener
            child.stdout?.on('data', (chunk: Buffer) => {
                if (initialized) return; // Already piped
                stdoutBuffer.push(chunk);

                // Try to parse lines
                const text = Buffer.concat(stdoutBuffer).toString('utf-8');
                const lines = text.split('\n');

                for (const line of lines) {
                    if (!line.trim()) continue;
                    try {
                        const event = JSON.parse(line);
                        // Look for thread_id in the event
                        // Spec says: "first JSON event contains the thread_id"
                        // We assume event.thread_id or event.id exists.
                        // Adjust based on real codex output if known. 
                        // For now assume `thread_id` or `id`.
                        const foundId = event.thread_id || event.id || event.threadId;
                        if (foundId) {
                            init(foundId);
                            break;
                        }
                    } catch (e) {
                        // Partial line or non-json
                    }
                }
            });

            child.stderr?.on('data', (chunk) => {
                if (initialized) return;
                stderrBuffer.push(chunk);
            });

            child.on('error', (err) => {
                if (!initialized) reject(err);
            });

            child.on('exit', (code) => {
                if (!initialized) {
                    // Exited before handshake!
                    const stderr = Buffer.concat(stderrBuffer).toString('utf-8');
                    reject(new Error(`Process exited early with code ${code}. Stderr: ${stderr}`));
                }
            });

            // Timeout for handshake
            setTimeout(() => {
                if (!initialized) {
                    child.kill();
                    reject(new Error('Timeout waiting for handshake (thread_id)'));
                }
            }, 10000); // 10s timeout
        });
    }

    stopTurn(threadId: string) {
        const status = this.stateManager.getStatus(threadId);
        if (!status || !status.pid) return;

        try {
            process.kill(status.pid, 'SIGTERM');
            // Update status to aborted? 
            // The exit handler will set it to 'failed' (non-zero) or 'done'.
            // We should explicitly mark it if we killed it.
            status.status = 'aborted';
            status.updated_at = new Date().toISOString();
            this.stateManager.saveStatus(status);
        } catch (e) {
            // Process might be gone
        }
    }
}


