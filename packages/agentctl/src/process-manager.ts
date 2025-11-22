import { spawn, ChildProcess } from 'child_process';
import fs from 'fs';
import path from 'path';
import os from 'os';
import { StateManager, ThreadStatus } from './state';
import { EventEmitter } from 'events';

export class ProcessManager {
    private stateManager: StateManager;
    private handshakeTimeoutMs: number;

    constructor(stateManager: StateManager) {
        this.stateManager = stateManager;
        const envTimeout = Number(process.env.AGENTCTL_HANDSHAKE_TIMEOUT_MS);
        this.handshakeTimeoutMs = Number.isFinite(envTimeout) && envTimeout > 0 ? envTimeout : 10_000;
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
        let spawnCwd = workdir;

        if (process.env.AGENTCTL_DEBUG_SPAWN === '1') {
            console.log('AGENTCTL spawn debug', { codexBin, isJs: codexBin.endsWith('.js'), isTs: codexBin.endsWith('.ts') });
        }

        if (codexBin.endsWith('.js')) {
            cmd = 'node';
            finalArgs = [codexBin, ...args];
            spawnCwd = path.dirname(codexBin);
        }

        if (codexBin.endsWith('.ts')) {
            // Use local ts-node to avoid npx overhead; run from repo root so resolution works.
            cmd = path.resolve(__dirname, '..', 'node_modules', '.bin', 'ts-node');
            finalArgs = [codexBin, ...args];
            spawnCwd = path.dirname(codexBin);
        }

        // Fallback: if the codex bin is a non-executable file, run it via node
        try {
            const stat = fs.statSync(codexBin);
            const isExecutable = !!(stat.mode & 0o111);
            if (!isExecutable && stat.isFile()) {
                cmd = 'node';
                finalArgs = [codexBin, ...args];
                spawnCwd = path.dirname(codexBin);
            }
        } catch {
            // ignore stat errors; let spawn surface issues
        }

        // Last-resort guard: if we're still about to exec a .js file directly, run it with node.
        if (cmd === codexBin && codexBin.endsWith('.js')) {
            cmd = 'node';
            finalArgs = [codexBin, ...args];
            spawnCwd = path.dirname(codexBin);
        }

        console.log(`Spawning: ${cmd} ${finalArgs.join(' ')}`);

        const child = spawn(cmd, finalArgs, {
            cwd: spawnCwd,
            env: { ...process.env },
            stdio: ['ignore', 'pipe', 'pipe'] // stdin ignore, stdout/err pipe
        });

        return new Promise((resolve, reject) => {
            let threadId = requestedThreadId;
            let initialized = false;
            let stdoutBuffer: Buffer[] = [];
            let stderrBuffer: Buffer[] = [];

            /**
             * Initialize state for this thread once we've discovered its ID.
             * This is called after the handshake completes (i.e., we've extracted thread_id from Codex output).
             * 
             * Flow:
             * 1. Create state directory for thread
             * 2. Write initial status.json
             * 3. Open file streams for logs
             * 4. Flush any buffered output collected during handshake
             * 5. Pipe remaining stdout/stderr to files
             * 6. Set up exit handler
             * 7. Resolve promise to return thread_id to caller
             */
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

            /**
             * Handshake protocol:
             * Codex prints JSONL events to stdout. The first JSON event contains the thread_id.
             * We buffer stdout until we find a valid JSON object with thread_id/id/threadId.
             * Once found, we call init() which sets up logging and resolves the promise.
             * 
             * Note: We parse line-by-line because Codex outputs newline-delimited JSON.
             * Partial lines are handled by buffering until we see a complete JSON object.
             */
            child.stdout?.on('data', (chunk: Buffer) => {
                if (initialized) return; // Already piped, no need to buffer
                stdoutBuffer.push(chunk);

                // Try to parse lines
                const text = Buffer.concat(stdoutBuffer).toString('utf-8');
                const lines = text.split('\n');

                for (const line of lines) {
                    if (!line.trim()) continue;
                    try {
                        const event = JSON.parse(line);
                        // Codex event format varies: might be event.thread_id, event.id, or event.threadId
                        // We check all three to be compatible with different Codex versions
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

            // Handle case where Codex exits before we complete the handshake
            // This indicates a failure (missing binary, invalid args, immediate crash, etc.)
            child.on('exit', (code) => {
                if (!initialized) {
                    // Process died before printing thread_id → reject the promise
                    const stderr = Buffer.concat(stderrBuffer).toString('utf-8');
                    reject(new Error(`Process exited early with code ${code}. Stderr: ${stderr}`));
                }
            });

            // Handshake timeout: Give Codex 10 seconds to print the first JSON event.
            // If it's silent or prints non-JSON output for 10s, assume something is wrong.
            // This prevents hanging forever if Codex is stuck or prints unexpected output.
            setTimeout(() => {
                if (!initialized) {
                    child.kill();
                    reject(new Error('Timeout waiting for handshake (thread_id)'));
                }
            }, this.handshakeTimeoutMs);
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
