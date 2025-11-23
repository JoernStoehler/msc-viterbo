#!/usr/bin/env node
import yargs from 'yargs';
import { hideBin } from 'yargs/helpers';
import axios from 'axios';
import { spawn } from 'child_process';
import path from 'path';
import fs from 'fs';
import os from 'os';
import { discoverSessionFile } from './session-files';

const PORT = Number(process.env.AGENTCTL_PORT) || 3000;
const BASE_URL = `http://localhost:${PORT}`;

type Identity = {
    identity: 'project_owner' | 'agent' | 'unknown';
    agent_uuid?: string;
    source?: 'pid';
    message?: string;
};

async function getExistingDaemon(): Promise<{ pid?: number; port?: number } | null> {
    try {
        const res = await axios.get(`${BASE_URL}/health`, { timeout: 500 });
        if (res.data?.status === 'ok') {
            return { pid: res.data.pid, port: res.data.port };
        }
    } catch {
        // Ignore connection errors; treated as daemon not running.
    }
    return null;
}

/**
 * Handles errors from daemon HTTP requests.
 * Provides helpful error messages when daemon is not running.
 */
function handleDaemonError(e: any, command: string): never {
    if (e.code === 'ECONNREFUSED' || e.message?.includes('ECONNREFUSED')) {
        console.error(`Error: agentctl daemon not running on port ${PORT}.`);
        console.error(`Start the daemon with: agentctl daemon`);
        process.exit(1);
    }
    console.error('Error:', e.response?.data || e.message);
    process.exit(1);
}


function detectIdentity(): Identity {
    // Not running under codex shell → assume project owner
    if (!process.env.CODEX_SHELL_ENV) {
        return { identity: 'project_owner' };
    }

    // PID-based detection
    try {
        const ancestors = getAncestors(process.pid);
        const threadId = findThreadByPid(ancestors);
        if (threadId) {
            return { identity: 'agent', agent_uuid: threadId, source: 'pid' };
        }
    } catch (e: any) {
        // Check if this is a state dir issue
        if (e.message && e.message.includes('state directory')) {
            return { identity: 'unknown', message: e.message };
        }
        // Ignore other errors during PID lookup
    }

    return {
        identity: 'unknown',
        message: 'Running inside Codex shell but not managed by agentctl daemon. Either the daemon is not running, or this Codex process was not started via agentctl.'
    };
}

function getAncestors(pid: number): number[] {
    const ancestors: number[] = [];
    let current = pid;
    // Limit depth to avoid infinite loops or excessive work
    for (let i = 0; i < 10; i++) {
        ancestors.push(current);
        try {
            const stat = fs.readFileSync(`/proc/${current}/stat`, 'utf-8');
            // Format: pid (comm) state ppid ...
            // comm can contain spaces and parens, so find the last ')'
            const lastParenIndex = stat.lastIndexOf(')');
            if (lastParenIndex === -1) break;
            const parts = stat.substring(lastParenIndex + 1).trim().split(/\s+/);
            const ppid = parseInt(parts[1], 10); // ppid is the 2nd field after comm (state is 1st)
            // Wait, parts[0] is state, parts[1] is ppid.
            if (isNaN(ppid) || ppid === 0) break;
            current = ppid;
        } catch (e) {
            break;
        }
    }
    return ancestors;
}

function findThreadByPid(pids: number[]): string | undefined {
    const stateDir = process.env.AGENTCTL_STATE_DIR || path.join(os.homedir(), '.agentctl', 'state');
    const threadsDir = path.join(stateDir, 'threads');

    if (!fs.existsSync(threadsDir)) {
        throw new Error(
            `agentctl state directory not found at ${stateDir}. ` +
            `The agentctl daemon may not be running. Start it with: agentctl daemon`
        );
    }

    const entries = fs.readdirSync(threadsDir);
    for (const id of entries) {
        try {
            const statusPath = path.join(threadsDir, id, 'status.json');
            if (!fs.existsSync(statusPath)) continue;

            const status = JSON.parse(fs.readFileSync(statusPath, 'utf-8'));
            if (status.pid && pids.includes(status.pid)) {
                return id;
            }
        } catch (e) {
            // ignore
        }
    }
    return undefined;
}

yargs(hideBin(process.argv))
    .parserConfiguration({ 'populate--': true })
    .version('1.1.2')
    .option('json', { type: 'boolean', description: 'Emit machine-readable JSON to stdout' })
    .command('daemon', 'Start the daemon', (yargs) => {
        return yargs.option('background', { type: 'boolean', default: false });
    }, async (argv) => {
        const existing = await getExistingDaemon();
        if (existing) {
            const pidMsg = existing.pid ? ` (pid ${existing.pid})` : '';
            console.error(`agentctl daemon already running on port ${existing.port ?? PORT}${pidMsg}.`);
            process.exit(1);
        }

        if (argv.background) {
            const subprocess = spawn(process.argv[0], [process.argv[1], 'daemon'], {
                detached: true,
                stdio: 'ignore'
            });
            subprocess.unref();
            console.log('Daemon started in background');
        } else {
            // Run the daemon code directly
            // We import it dynamically to avoid side effects if we are just running CLI commands
            require('./daemon');
        }
    })
    .command('self', 'Print whether we are inside an agent session', (yargs) => {
        return yargs;
    }, (argv) => {
        const result = detectIdentity();
        if (argv.json) {
            console.log(JSON.stringify(result));
        } else {
            if (result.identity === 'agent' && result.agent_uuid) {
                console.log(result.agent_uuid);
            } else {
                console.log(result.identity);
            }
        }

        if (result.identity === 'unknown') {
            process.exit(1);
        }
    })
    .command('start [prompt]', 'Start a turn', (yargs) => {
        return yargs
            .positional('prompt', { type: 'string' })
            .option('workdir', { type: 'string', demandOption: false, description: 'Working directory; if omitted with --thread, the stored workdir is used' })
            .option('thread', { type: 'string' })
            .option('detach', { type: 'boolean', default: true, description: 'Return immediately (default). Set to false to wait for completion.' })
            .option('await', { type: 'boolean', default: false, description: 'Block until the turn completes.' });
    }, async (argv) => {
        // Validate workdir is safe (within workspace) when provided
        const workdir = argv.workdir as string | undefined;
        if (workdir) {
            if (!workdir.startsWith('/workspaces/') && !workdir.startsWith('/tmp/')) {
                console.error('Error: --workdir must be inside /workspaces/ or /tmp/ for safety');
                console.error(`Got: ${workdir}`);
                process.exit(1);
            }
        }

        try {
            const res = await axios.post(`${BASE_URL}/turn/start`, {
                prompt: argv.prompt,
                workdir: argv.workdir,
                thread_id: argv.thread
            });
            const { thread_id, status } = res.data;
            const shouldAwait = argv.await || argv.detach === false;

            if (argv.json) {
                if (shouldAwait) {
                    const finalStatus = await poll(thread_id);
                    console.log(JSON.stringify({ thread_id, status: finalStatus?.status ?? status, final_status: finalStatus?.status, data: finalStatus ?? null }));
                } else {
                    console.log(JSON.stringify(res.data));
                }
            } else {
                console.log(thread_id);
                if (shouldAwait) {
                    await poll(thread_id);
                }
            }
        } catch (e: any) {
            handleDaemonError(e, 'start');
        }
    })
    .command('status <id>', 'Get status', (yargs) => {
        return yargs.positional('id', { type: 'string', demandOption: true });
    }, async (argv) => {
        try {
            const res = await axios.get(`${BASE_URL}/turn/${argv.id}`);
            if (argv.json) {
                console.log(JSON.stringify(res.data));
            } else {
                console.log(JSON.stringify(res.data, null, 2));
            }
        } catch (e: any) {
            handleDaemonError(e, 'status');
        }
    })
    .command('await <id>', 'Wait for completion', (yargs) => {
        return yargs
            .positional('id', { type: 'string', demandOption: true })
            .option('timeout', { type: 'number' });
    }, async (argv) => {
        try {
            const finalStatus = await poll(argv.id, argv.timeout);
            if (argv.json && finalStatus) {
                console.log(JSON.stringify(finalStatus));
            }
        } catch (e: any) {
            if (e.message === 'Timeout') {
                console.error('Timeout waiting for thread completion');
                process.exit(124);
            }
            console.error(e.message);
            process.exit(1);
        }
    })
    .command('list', 'List threads', (yargs) => {
        return yargs
            .option('status', { type: 'string' })
            .option('jsonl', { type: 'boolean', default: false, description: 'Emit newline-delimited JSON instead of a single array (requires --json).' })
            .option('header', { type: 'boolean', default: true, description: 'Include column header in plain output (use --no-header to suppress).' });
    }, async (argv) => {
        try {
            const res = await axios.get(`${BASE_URL}/list`, { params: { status: argv.status } });

            const sortByLastActive = (threads: any[]) => {
                return [...threads].sort((a, b) => {
                    const ta = new Date(a.updated_at || a.created_at || 0).getTime();
                    const tb = new Date(b.updated_at || b.created_at || 0).getTime();
                    return tb - ta; // desc
                });
            };

            const threads = sortByLastActive(res.data);

            if (argv.jsonl) {
                threads.forEach((t: any) => console.log(JSON.stringify(t)));
            } else if (argv.json) {
                console.log(JSON.stringify(threads, null, 2));
            } else {
                if (argv.header) {
                    console.log('workdir id status managed pid last_active_at');
                }
                threads.forEach((t: any) => {
                    const lastActive = t.updated_at || t.created_at || '';
                    // Plain, grep-friendly single-line format (workdir first for scanability)
                    console.log(`${t.workdir} ${t.id} ${t.status} ${t.managed ?? ''} ${t.pid ?? ''} ${lastActive}`);
                });
            }
        } catch (e: any) {
            handleDaemonError(e, 'list');
        }
    })
    .command('stop <id>', 'Stop thread', (yargs) => {
        return yargs.positional('id', { type: 'string', demandOption: true });
    }, async (argv) => {
        try {
            const res = await axios.post(`${BASE_URL}/turn/stop`, { thread_id: argv.id });
            if (argv.json) {
                console.log(JSON.stringify({ thread_id: argv.id, ...res.data }));
            } else {
                console.log('Stopped');
            }
        } catch (e: any) {
            handleDaemonError(e, 'stop');
        }
    })
    .command('codex-tui [thread_id]', 'Run codex (TUI) and register as externally managed', (yargs) => {
        return yargs
            .positional('thread_id', { type: 'string', description: 'Optional session id to resume (same as first positional to `codex resume`)' })
            .option('resume', { type: 'string', description: 'Deprecated: use positional thread_id instead' })
            .option('workdir', { type: 'string', description: 'Working directory to run codex in' })
            .option('timeout', { type: 'number', default: 1000, description: 'Timeout (ms) to discover new session file' })
            .option('codex-bin', { type: 'string', description: 'Override codex binary', default: process.env.AGENTCTL_CODEX_BIN || 'codex' });
    }, async (argv) => {
        let workdir = argv.workdir as string | undefined;
        const resume = (argv.thread_id as string | undefined) || (argv.resume as string | undefined);
        const extraArgs = (argv['--'] as string[] | undefined) ?? [];

        // If resuming a known thread, fetch its recorded workdir and enforce match.
        if (resume) {
            try {
                const resp = await axios.get(`${BASE_URL}/turn/${resume}`);
                const recorded = resp.data;
                if (recorded && recorded.workdir) {
                    if (workdir && path.resolve(workdir) !== path.resolve(recorded.workdir)) {
                        console.error('Workdir mismatch with existing thread');
                        process.exit(1);
                    }
                    workdir = recorded.workdir;
                }
            } catch (e: any) {
                console.error(`Failed to load thread ${resume}:`, e.response?.data || e.message);
                process.exit(1);
            }
        }

        if (!workdir) {
            workdir = process.cwd();
        }

        const codexArgs: string[] = [];
        if (resume) {
            codexArgs.push('resume', '--cd', workdir);
            codexArgs.push(resume);
            codexArgs.push(...extraArgs);
        } else {
            codexArgs.push('--cd', workdir);
            codexArgs.push(...extraArgs);
        }

        const codexBin = argv['codex-bin'] as string;
        let cmd = codexBin;
        let spawnArgs = codexArgs;
        let spawnCwd = workdir;

        if (codexBin.endsWith('.js')) {
            cmd = 'node';
            spawnArgs = [codexBin, ...codexArgs];
            spawnCwd = path.dirname(codexBin);
        } else if (codexBin.endsWith('.ts')) {
            cmd = path.resolve(__dirname, '..', 'node_modules', '.bin', 'ts-node');
            spawnArgs = [codexBin, ...codexArgs];
            spawnCwd = path.dirname(codexBin);
        }

        const startTime = Date.now();
        const child = spawn(cmd, spawnArgs, {
            cwd: spawnCwd,
            env: { ...process.env, CODEX_SHELL_ENV: '1' },
            stdio: 'inherit'
        });

        let sessionId: string | undefined;
        let sessionPath: string | undefined;
        try {
            const { file, meta } = await discoverSessionFile({
                sinceMs: startTime,
                expectedUuid: resume,
                expectedCwd: workdir,
                timeoutMs: argv.timeout as number
            });
            sessionId = meta.id;
            sessionPath = file.path;
            await axios.post(`${BASE_URL}/external/start`, {
                thread_id: sessionId,
                workdir: meta.cwd || workdir,
                pid: child.pid,
                session_file: file.path,
                originator: meta.originator,
                source: meta.source,
                codex_cwd: meta.cwd,
                managed: 'external'
            });
            console.log(`Registered external session ${sessionId}`);
        } catch (e: any) {
            console.error('Failed to register codex session:', e.message);
            try {
                process.kill(child.pid ?? 0, 'SIGTERM');
            } catch {
                // ignore
            }
            process.exit(1);
        }

        const exitCode: number | null = await new Promise(resolve => {
            child.on('exit', (code) => resolve(code));
        });

        if (sessionId) {
            try {
                await axios.post(`${BASE_URL}/external/finish`, {
                    thread_id: sessionId,
                    exit_code: exitCode
                });
            } catch (e: any) {
                console.error('Failed to finalize external session:', e.message);
            }
        }
        process.exit(exitCode === null ? 1 : exitCode);
    })
    .parse();

async function poll(id: string, timeoutSec?: number) {
    const start = Date.now();
    while (true) {
        if (timeoutSec && (Date.now() - start) > timeoutSec * 1000) {
            throw new Error('Timeout');
        }
        try {
            const res = await axios.get(`${BASE_URL}/turn/${id}`);
            const status = res.data.status;
            if (status === 'done' || status === 'failed' || status === 'aborted') {
                return res.data;
            }
        } catch (e) {
            // ignore transient errors
        }
        await new Promise(r => setTimeout(r, 1000));
    }
}
