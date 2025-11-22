#!/usr/bin/env node
import yargs from 'yargs';
import { hideBin } from 'yargs/helpers';
import axios from 'axios';
import { spawn } from 'child_process';
import path from 'path';
import fs from 'fs';
import os from 'os';

const PORT = process.env.AGENTCTL_PORT || 3000;
const BASE_URL = `http://localhost:${PORT}`;

type Identity = {
    identity: 'project_owner' | 'agent' | 'unknown';
    agent_uuid?: string;
    source?: 'pid';
    message?: string;
};

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
    .version('1.1.0')
    .option('json', { type: 'boolean', description: 'Emit machine-readable JSON to stdout' })
    .command('daemon', 'Start the daemon', (yargs) => {
        return yargs.option('background', { type: 'boolean', default: false });
    }, async (argv) => {
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
            .option('workdir', { type: 'string', demandOption: true })
            .option('thread', { type: 'string' })
            .option('detach', { type: 'boolean', default: true, description: 'Return immediately (default). Set to false to wait for completion.' })
            .option('await', { type: 'boolean', default: false, description: 'Block until the turn completes.' });
    }, async (argv) => {
        // Validate workdir is safe (within workspace)
        const workdir = argv.workdir as string;
        if (!workdir.startsWith('/workspaces/') && !workdir.startsWith('/tmp/')) {
            console.error('Error: --workdir must be inside /workspaces/ or /tmp/ for safety');
            console.error(`Got: ${workdir}`);
            process.exit(1);
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
            .option('jsonl', { type: 'boolean', default: false, description: 'Emit newline-delimited JSON instead of a single array (requires --json).' });
    }, async (argv) => {
        try {
            const res = await axios.get(`${BASE_URL}/list`, { params: { status: argv.status } });
            if (argv.jsonl) {
                res.data.forEach((t: any) => console.log(JSON.stringify(t)));
            } else if (argv.json) {
                console.log(JSON.stringify(res.data, null, 2));
            } else {
                res.data.forEach((t: any) => {
                    // Plain, grep-friendly single-line format
                    // id status pid exit_code workdir
                    console.log(`${t.id} ${t.status} ${t.pid ?? ''} ${t.exit_code ?? ''} ${t.workdir}`);
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
