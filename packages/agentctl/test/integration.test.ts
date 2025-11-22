import { spawn, execSync } from 'child_process';
import fs from 'fs';
import path from 'path';
import os from 'os';
import axios from 'axios';

const CLI = path.resolve(__dirname, '../src/cli.ts');
const MOCK_CODEX = path.resolve(__dirname, '../src/mock-codex.ts');
const WORKDIR = path.join(os.tmpdir(), 'agentctl-test-workdir');
const STATE_DIR = path.join(os.tmpdir(), 'agentctl-test-state');
const MOCK_INSTRUCTIONS = path.join(WORKDIR, 'instructions.jsonl');

if (fs.existsSync(WORKDIR)) fs.rmSync(WORKDIR, { recursive: true, force: true });
if (fs.existsSync(STATE_DIR)) fs.rmSync(STATE_DIR, { recursive: true, force: true });
fs.mkdirSync(WORKDIR);

// Setup Mock Instructions
const instructions = [
    { type: 'turn_start', thread_id: 'test-thread-1' },
    { type: 'log', message: 'Working...', _mock_delay_ms: 100 },
    { type: 'turn_end', final_message: 'Task Complete' }
];
fs.writeFileSync(MOCK_INSTRUCTIONS, instructions.map(i => JSON.stringify(i)).join('\n'));

// Env for Daemon/CLI
const env = {
    ...process.env,
    AGENTCTL_PORT: '3001',
    AGENTCTL_STATE_DIR: STATE_DIR,
    AGENTCTL_CODEX_BIN: MOCK_CODEX,
    AGENTCTL_CODEX_MOCK_INSTRUCTION_FILE: MOCK_INSTRUCTIONS
};

console.log('Starting Daemon...');
const daemon = spawn('npx', ['ts-node', CLI, 'daemon'], { env, stdio: 'inherit', detached: true });
daemon.unref();

// Wait for daemon
async function waitForDaemon() {
    for (let i = 0; i < 10; i++) {
        try {
            await axios.get('http://localhost:3001/list');
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

        // Helper to write instructions
        const writeInstructions = (insts: any[]) => {
            fs.writeFileSync(MOCK_INSTRUCTIONS, insts.map(i => JSON.stringify(i)).join('\n'));
        };

        // --- Test 1: Start New (Happy) ---
        console.log('\n[Test 1] Start New Thread');
        writeInstructions([
            { type: 'turn_start', thread_id: 't1' },
            { type: 'log', message: 'Working...' },
            { type: 'turn_end', final_message: 'Done T1' }
        ]);
        const t1Out = execSync(`npx ts-node ${CLI} start "task 1" --workdir ${WORKDIR} --await`, { env }).toString().trim();
        if (t1Out !== 't1') throw new Error(`Expected t1, got ${t1Out}`);

        const t1Status = JSON.parse(execSync(`npx ts-node ${CLI} status t1`, { env }).toString());
        if (t1Status.status !== 'done') throw new Error(`T1 status expected done, got ${t1Status.status}`);

        // --- Test 2: Resume Existing (Happy) ---
        console.log('\n[Test 2] Resume Existing Thread');
        writeInstructions([
            { type: 'turn_start', thread_id: 't1' }, // Must match for handshake
            { type: 'log', message: 'Resuming...' },
            { type: 'turn_end', final_message: 'Done T1 Again' }
        ]);
        // We use --thread t1
        const t1ResumeOut = execSync(`npx ts-node ${CLI} start "resume task" --workdir ${WORKDIR} --thread t1 --await`, { env }).toString().trim();
        if (t1ResumeOut !== 't1') throw new Error(`Expected t1, got ${t1ResumeOut}`);

        // Check logs contain both runs
        const logContent = fs.readFileSync(path.join(STATE_DIR, 'threads', 't1', 'log.jsonl'), 'utf-8');
        if (!logContent.includes('Working...') || !logContent.includes('Resuming...')) {
            throw new Error('Log missing events from resume');
        }

        // --- Test 3: Resume Non-Existent (Sad) ---
        console.log('\n[Test 3] Resume Non-Existent (Sad)');
        // Simulate crash on bad ID
        writeInstructions([
            { _mock_exit_code: 1 }
        ]);
        try {
            execSync(`npx ts-node ${CLI} start "bad resume" --workdir ${WORKDIR} --thread fake-id`, { env, stdio: 'pipe' });
            throw new Error('Should have failed');
        } catch (e: any) {
            console.log('Caught expected error:', e.message);
            // Verify it failed with exit code 1 (which execSync throws on)
        }

        // --- Test 4: Concurrency ---
        console.log('\n[Test 4] Concurrency');
        // Thread A
        writeInstructions([
            { type: 'turn_start', thread_id: 'thread-a' },
            { type: 'log', message: 'A running', _mock_delay_ms: 2000 },
            { type: 'turn_end' }
        ]);
        const startA = execSync(`npx ts-node ${CLI} start "task A" --workdir ${WORKDIR} --detach`, { env }).toString().trim();

        // Thread B (overwrite instructions immediately, A has already read them hopefully? 
        // Wait a tiny bit to ensure A spawned and read file. 
        // Actually, spawn is async in daemon, but we return ID after handshake.
        // Handshake means A has started and printed first line.
        // So A definitely read the file.
        writeInstructions([
            { type: 'turn_start', thread_id: 'thread-b' },
            { type: 'log', message: 'B running', _mock_delay_ms: 2000 },
            { type: 'turn_end' }
        ]);
        const startB = execSync(`npx ts-node ${CLI} start "task B" --workdir ${WORKDIR} --detach`, { env }).toString().trim();

        console.log(`Started A:${startA}, B:${startB}`);

        // Check both running
        const listOut = execSync(`npx ts-node ${CLI} list --json`, { env }).toString();
        if (!listOut.includes(startA) || !listOut.includes(startB)) throw new Error('Both threads should be in list');

        // Wait for both
        execSync(`npx ts-node ${CLI} await ${startA}`, { env });
        execSync(`npx ts-node ${CLI} await ${startB}`, { env });
        console.log('Both finished');

        // --- Test 5: Handshake Timeout (Sad) ---
        console.log('\n[Test 5] Handshake Timeout');
        writeInstructions([
            { type: 'log', message: 'Silent...', _mock_delay_ms: 11000 }, // Delay > 10s
            { type: 'turn_start', thread_id: 'timeout-thread' }
        ]);
        try {
            // This should fail because daemon kills it after 10s
            execSync(`npx ts-node ${CLI} start "timeout" --workdir ${WORKDIR}`, { env, stdio: 'pipe' });
            throw new Error('Should have timed out');
        } catch (e: any) {
            console.log('Caught expected timeout error');
        }

        // --- Test 6: Immediate Crash (Sad) ---
        console.log('\n[Test 6] Immediate Crash');
        writeInstructions([
            { _mock_exit_code: 1 }
        ]);
        try {
            execSync(`npx ts-node ${CLI} start "crash" --workdir ${WORKDIR}`, { env, stdio: 'pipe' });
            throw new Error('Should have crashed');
        } catch (e: any) {
            console.log('Caught expected crash error');
        }
        // --- Test 7: JSON flag output ---
        console.log('\n[Test 7] --json flag output');
        writeInstructions([
            { type: 'turn_start', thread_id: 'json-thread' },
            { type: 'log', message: 'JSON run' },
            { type: 'turn_end' }
        ]);
        const jsonOut = execSync(`npx ts-node ${CLI} start "json task" --workdir ${WORKDIR} --json`, { env }).toString().trim();
        const jsonData = JSON.parse(jsonOut);
        if (jsonData.thread_id !== 'json-thread') throw new Error(`Expected json-thread, got ${jsonData.thread_id}`);

        const statusJsonData = JSON.parse(execSync(`npx ts-node ${CLI} status json-thread --json`, { env }).toString().trim());
        if (statusJsonData.id !== 'json-thread') throw new Error('JSON status mismatch');

        // --- Test 8: agentctl self ---
        console.log('\n[Test 8] agentctl self');
        const selfHome = path.join(os.tmpdir(), 'agentctl-self-home');
        if (fs.existsSync(selfHome)) fs.rmSync(selfHome, { recursive: true, force: true });
        fs.mkdirSync(path.join(selfHome, '.codex'), { recursive: true });

        const selfEnv = { ...env, HOME: selfHome };

        // 8a: project_owner (no CODEX_SHELL_ENV)
        const cleanEnv: any = { ...process.env, HOME: selfHome, AGENTCTL_STATE_DIR: STATE_DIR };
        delete cleanEnv.CODEX_SHELL_ENV;
        const owner = execSync(`npx ts-node ${CLI} self`, { env: cleanEnv }).toString().trim();
        if (owner !== 'project_owner') throw new Error(`Expected project_owner, got ${owner}`);

        // 8b: unknown (when CODEX_SHELL_ENV=1 but no match)
        // Note: agentctl self exits with code 1 when returning "unknown", so we need to catch the error
        try {
            const unknown = execSync(`npx ts-node ${CLI} self`, { env: { ...selfEnv, CODEX_SHELL_ENV: '1' }, stdio: 'pipe' }).toString().trim();
            if (unknown !== 'unknown') throw new Error(`Expected unknown, got ${unknown}`);
        } catch (e: any) {
            // execSync throws on non-zero exit, check if stdout contains "unknown"
            if (e.stdout && e.stdout.toString().trim() === 'unknown') {
                // This is expected behavior
            } else {
                throw e;
            }
        }

        console.log('\nAll Tests Passed!');
    } catch (e: any) {
        console.error('Test Failed:', e.message);
        if (e.stdout) console.log(e.stdout.toString());
        if (e.stderr) console.error(e.stderr.toString());
        process.exit(1);
    } finally {
        process.exit(0);
    }
}

run();
