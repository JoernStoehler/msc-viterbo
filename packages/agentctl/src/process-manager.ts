import { spawn } from 'child_process';
import fs from 'fs';
import path from 'path';
import os from 'os';
import { StateManager, ThreadStatus } from './state';
import { discoverSessionFile } from './session-files';

export class ProcessManager {
    private stateManager: StateManager;
    private discoveryTimeoutMs: number;

    constructor(stateManager: StateManager) {
        this.stateManager = stateManager;
        const envTimeout = Number(process.env.AGENTCTL_HANDSHAKE_TIMEOUT_MS || process.env.AGENTCTL_DISCOVERY_TIMEOUT_MS);
        this.discoveryTimeoutMs = Number.isFinite(envTimeout) && envTimeout > 0 ? envTimeout : 1_000;
    }

    async startTurn(
        prompt: string,
        workdir: string,
        requestedThreadId?: string
    ): Promise<string> {
        const codexBin = process.env.AGENTCTL_CODEX_BIN || 'codex';

        // Construct args for codex exec
        const args = ['exec'];
        if (requestedThreadId) {
            args.push('resume', requestedThreadId);
        }
        args.push('--yolo', '--json');

        // Capture last message to a temp file; rename after we know thread id
        const tempFinalMsg = path.join(os.tmpdir(), `agentctl-final-${Date.now()}-${Math.random()}.txt`);
        args.push('--output-last-message', tempFinalMsg);

        args.push('--cd', workdir);
        args.push(prompt);

        // Resolve how to spawn (ts/js binary support)
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
            cmd = path.resolve(__dirname, '..', 'node_modules', '.bin', 'ts-node');
            finalArgs = [codexBin, ...args];
            spawnCwd = path.dirname(codexBin);
        }

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

        if (cmd === codexBin && codexBin.endsWith('.js')) {
            cmd = 'node';
            finalArgs = [codexBin, ...args];
            spawnCwd = path.dirname(codexBin);
        }

        console.log(`Spawning: ${cmd} ${finalArgs.join(' ')}`);

        const startTime = Date.now();
        let exitCode: number | null = null;
        const child = spawn(cmd, finalArgs, {
            cwd: spawnCwd,
            env: { ...process.env },
            stdio: ['ignore', 'ignore', 'inherit']
        });

        child.on('exit', (code) => {
            exitCode = code === null ? null : code;
        });

        try {
            const { file, meta } = await discoverSessionFile({
                sinceMs: startTime,
                expectedUuid: requestedThreadId,
                expectedCwd: workdir,
                timeoutMs: this.discoveryTimeoutMs
            });

            const threadId = meta.id;
            this.stateManager.ensureThreadDir(threadId);
            const status: ThreadStatus = {
                id: threadId,
                pid: child.pid || null,
                status: 'running',
                exit_code: null,
                workdir: meta.cwd || workdir,
                managed: 'daemon',
                session_file: file.path,
                originator: meta.originator,
                source: meta.source,
                codex_cwd: meta.cwd,
                created_at: new Date().toISOString(),
                updated_at: new Date().toISOString()
            };
            this.stateManager.saveStatus(status);
            // TODO: optionally mirror/copy the session file into the thread dir for portability instead of only storing the pointer.

            const finalize = (code: number | null) => {
                const currentStatus = this.stateManager.getStatus(threadId);
                if (currentStatus && currentStatus.status === 'aborted') {
                    return;
                }
                status.status = code === 0 ? 'done' : 'failed';
                status.exit_code = code;
                status.updated_at = new Date().toISOString();
                this.stateManager.saveStatus(status);

                if (fs.existsSync(tempFinalMsg)) {
                    const finalPath = path.join(this.stateManager.getThreadDir(threadId), 'final_message.txt');
                    try {
                        fs.renameSync(tempFinalMsg, finalPath);
                    } catch {
                        // ignore
                    }
                }
            };

            const codeNow = exitCode ?? (typeof child.exitCode === 'number' ? child.exitCode : null);
            if (codeNow !== null) {
                finalize(codeNow);
            } else {
                child.on('exit', (code) => finalize(code === null ? null : code));
            }

            return threadId;
        } catch (e) {
            child.kill();
            throw e;
        }
    }

    stopTurn(threadId: string) {
        const status = this.stateManager.getStatus(threadId);
        if (!status || !status.pid) return;

        try {
            process.kill(status.pid, 'SIGTERM');
            status.status = 'aborted';
            status.updated_at = new Date().toISOString();
            this.stateManager.saveStatus(status);
        } catch {
            // Process might be gone
        }
    }
}
