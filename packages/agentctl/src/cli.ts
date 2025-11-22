#!/usr/bin/env node
import yargs from 'yargs';
import { hideBin } from 'yargs/helpers';
import axios from 'axios';
import { spawn } from 'child_process';
import path from 'path';

const PORT = process.env.AGENTCTL_PORT || 3000;
const BASE_URL = `http://localhost:${PORT}`;

yargs(hideBin(process.argv))
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
    .command('start [prompt]', 'Start a turn', (yargs) => {
        return yargs
            .positional('prompt', { type: 'string' })
            .option('workdir', { type: 'string', demandOption: true })
            .option('thread', { type: 'string' })
            .option('detach', { type: 'boolean', default: true })
            .option('await', { type: 'boolean', default: false });
    }, async (argv) => {
        try {
            const res = await axios.post(`${BASE_URL}/turn/start`, {
                prompt: argv.prompt,
                workdir: argv.workdir,
                thread_id: argv.thread
            });
            const { thread_id } = res.data;
            console.log(thread_id);

            if (argv.await) {
                await poll(thread_id);
            }
        } catch (e: any) {
            console.error('Error:', e.response?.data || e.message);
            process.exit(1);
        }
    })
    .command('status <id>', 'Get status', (yargs) => {
        return yargs.positional('id', { type: 'string', demandOption: true });
    }, async (argv) => {
        try {
            const res = await axios.get(`${BASE_URL}/turn/${argv.id}`);
            console.log(JSON.stringify(res.data, null, 2));
        } catch (e: any) {
            console.error('Error:', e.response?.data || e.message);
            process.exit(1);
        }
    })
    .command('await <id>', 'Wait for completion', (yargs) => {
        return yargs
            .positional('id', { type: 'string', demandOption: true })
            .option('timeout', { type: 'number' });
    }, async (argv) => {
        try {
            await poll(argv.id, argv.timeout);
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
        return yargs.option('status', { type: 'string' }).option('json', { type: 'boolean' });
    }, async (argv) => {
        try {
            const res = await axios.get(`${BASE_URL}/list`, { params: { status: argv.status } });
            if (argv.json) {
                res.data.forEach((t: any) => console.log(JSON.stringify(t)));
            } else {
                console.table(res.data);
            }
        } catch (e: any) {
            console.error('Error:', e.response?.data || e.message);
            process.exit(1);
        }
    })
    .command('stop <id>', 'Stop thread', (yargs) => {
        return yargs.positional('id', { type: 'string', demandOption: true });
    }, async (argv) => {
        try {
            await axios.post(`${BASE_URL}/turn/stop`, { thread_id: argv.id });
            console.log('Stopped');
        } catch (e: any) {
            console.error('Error:', e.response?.data || e.message);
            process.exit(1);
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
                return;
            }
        } catch (e) {
            // ignore transient errors
        }
        await new Promise(r => setTimeout(r, 1000));
    }
}
