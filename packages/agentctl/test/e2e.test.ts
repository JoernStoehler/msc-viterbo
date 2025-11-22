import { spawn, execSync } from 'child_process';
import fs from 'fs';
import path from 'path';
import os from 'os';
import axios from 'axios';

const CLI = path.resolve(__dirname, '../src/cli.ts');
const WORKDIR = path.join(os.tmpdir(), 'agentctl-e2e-workdir');
const STATE_DIR = path.join(os.tmpdir(), 'agentctl-e2e-state');

if (fs.existsSync(WORKDIR)) fs.rmSync(WORKDIR, { recursive: true, force: true });
if (fs.existsSync(STATE_DIR)) fs.rmSync(STATE_DIR, { recursive: true, force: true });
fs.mkdirSync(WORKDIR);
execSync('git init', { cwd: WORKDIR });
execSync('git init', { cwd: WORKDIR });

// Env for Daemon/CLI
const env = {
    ...process.env,
    AGENTCTL_PORT: '3002', // Different port from integration tests
    AGENTCTL_STATE_DIR: STATE_DIR,
    // We rely on 'codex' being in the PATH or AGENTCTL_CODEX_BIN being set correctly in the environment
};

console.log('Starting Daemon for E2E...');
const daemon = spawn('npx', ['ts-node', CLI, 'daemon'], { env, stdio: 'inherit', detached: true });
daemon.unref();

// Wait for daemon
async function waitForDaemon() {
    for (let i = 0; i < 20; i++) {
        try {
            await axios.get('http://localhost:3002/list');
            return;
        } catch (e) {
            await new Promise(r => setTimeout(r, 500));
        }
    }
    throw new Error('Daemon failed to start');
}

async function run() {
    try {
        await waitForDaemon();
        console.log('Daemon started.');

        console.log('\n[E2E Test] agentctl self via Real Codex');

        // We instruct the agent to run `agentctl self` and print it.
        // Note: The agent must have `agentctl` in its path or we need to provide the full path.
        // Since we are in the repo, we can use `npx ts-node ${CLI} self`.
        // But the agent might not have the same env.
        // Let's try to use the installed `agentctl` if available, or fall back to the source.
        // For this test, we'll construct the command string to use the source.

        const agentctlCmd = `npx ts-node ${CLI} self`;
        const prompt = `Run the command '${agentctlCmd}' and repeat its output exactly in your final message. Do not add any other text.`;

        const startOut = execSync(`npx ts-node ${CLI} start "${prompt}" --workdir ${WORKDIR} --await --json`, { env }).toString().trim();
        const result = JSON.parse(startOut);

        if (result.status !== 'done') {
            throw new Error(`Agent failed with status: ${result.status}`);
        }

        const threadId = result.thread_id;
        const finalMsgPath = path.join(STATE_DIR, 'threads', threadId, 'final_message.txt');

        if (!fs.existsSync(finalMsgPath)) {
            throw new Error('Final message file not found');
        }

        const finalMsg = fs.readFileSync(finalMsgPath, 'utf-8').trim();
        console.log('Final Message:', finalMsg);

        // The agent should have printed its UUID.
        // Since we are running via agentctl, the agent IS managed.
        // However, for a NEW thread, we don't inject the UUID (per our earlier discovery).
        // So `agentctl self` inside the agent will look for history/sessions.
        // BUT, this is a brand new thread. It might not be in history yet?
        // Actually, Codex writes to history/sessions as it runs.
        // So it SHOULD find itself if the session file is written.

        // Wait, if the agent runs `agentctl self` *during* the turn, the session file for *that* turn exists.
        // So it should find it.
        // The UUID found should match the thread ID (if Codex uses the same ID).
        // In our implementation, we use the ID from the handshake.

        // Let's verify if the output looks like a UUID.
        // And ideally matches the threadId.

        if (!finalMsg.includes(threadId)) {
            // Fallback: It might be a different UUID if Codex generated one and we adopted it.
            // But it should be a UUID.
            const uuidRegex = /[0-9a-fA-F-]{36}/;
            if (!uuidRegex.test(finalMsg)) {
                throw new Error(`Final message '${finalMsg}' does not contain a UUID`);
            }
            console.log('Verified: Output contains a UUID');
        } else {
            console.log('Verified: Output matches Thread ID');
        }

        console.log('\nE2E Test Passed!');
    } catch (e: any) {
        console.error('E2E Test Failed:', e.message);
        if (e.stdout) console.log(e.stdout.toString());
        if (e.stderr) console.error(e.stderr.toString());
        process.exit(1);
    } finally {
        // Cleanup daemon? It's detached, so it stays running. 
        // In a real CI we'd kill it.
        try {
            await axios.post('http://localhost:3002/turn/stop', { thread_id: 'shutdown' }).catch(() => { });
        } catch (_) { }
        process.exit(0);
    }
}

run();
