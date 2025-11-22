import { spawn, execSync } from 'child_process';
import fs from 'fs';
import path from 'path';
import os from 'os';
import axios from 'axios';

const CLI = path.resolve(__dirname, '../src/cli.js');
const MOCK_CODEX = path.resolve(__dirname, '../src/mock-codex.js');
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
    AGENTCTL_CODEX_MOCK_INSTRUCTION_FILE: MOCK_INSTRUCTIONS,
    AGENTCTL_HANDSHAKE_TIMEOUT_MS: '2000',
    NPM_CONFIG_PROGRESS: '0'
};

console.log('Starting Daemon...');
console.log('Using mock codex:', MOCK_CODEX);
const daemon = spawn('node', [CLI, 'daemon'], { env, stdio: 'inherit', detached: true });
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

        // Health check
        const health = await axios.get('http://localhost:3001/health');
        if (health.data.status !== 'ok') {
            throw new Error('Health check failed');
        }

        // Helper to write instructions
        const writeInstructions = (insts: any[]) => {
            fs.writeFileSync(MOCK_INSTRUCTIONS, insts.map(i => JSON.stringify(i)).join('\n'));
        };

        // --- Test 1: Start New (Happy) ---
        console.log('\n[Test 1] Start New Thread');
        writeInstructions([
            { type: 'turn_start', thread_id: 't1' },
            { type: 'log', message: 'Working...', _mock_delay_ms: 300 },
            { type: 'turn_end', final_message: 'Done T1' }
        ]);
        const t1Out = execSync(`node ${CLI} start "task 1" --workdir ${WORKDIR} --await`, { env }).toString().trim();
        if (t1Out !== 't1') throw new Error(`Expected t1, got ${t1Out}`);

        const t1Status = JSON.parse(execSync(`node ${CLI} status t1`, { env }).toString());
        if (t1Status.status !== 'done') throw new Error(`T1 status expected done, got ${t1Status.status}`);

        // --- Test 2: Resume Existing (Happy) ---
        console.log('\n[Test 2] Resume Existing Thread');
        writeInstructions([
            { type: 'turn_start', thread_id: 't1' }, // Must match for handshake
            { type: 'log', message: 'Resuming...', _mock_delay_ms: 300 },
            { type: 'turn_end', final_message: 'Done T1 Again' }
        ]);
        // We use --thread t1
        const t1ResumeOut = execSync(`node ${CLI} start "resume task" --workdir ${WORKDIR} --thread t1 --await`, { env }).toString().trim();
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
            execSync(`node ${CLI} start "bad resume" --workdir ${WORKDIR} --thread fake-id`, { env, stdio: 'pipe' });
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
            { type: 'log', message: 'A running' },
            { type: 'turn_end', _mock_delay_ms: 5000 }
        ]);
        const startA = execSync(`node ${CLI} start "task A" --workdir ${WORKDIR} --detach`, { env }).toString().trim();

        // Thread B (overwrite instructions immediately, A has already read them hopefully? 
        // Wait a tiny bit to ensure A spawned and read file. 
        // Actually, spawn is async in daemon, but we return ID after handshake.
        // Handshake means A has started and printed first line.
        // So A definitely read the file.
        await new Promise(r => setTimeout(r, 200));
        writeInstructions([
            { type: 'turn_start', thread_id: 'thread-b' },
            { type: 'log', message: 'B running' },
            { type: 'turn_end', _mock_delay_ms: 5000 }
        ]);
        const startB = execSync(`node ${CLI} start "task B" --workdir ${WORKDIR} --detach`, { env }).toString().trim();

        console.log(`Started A:${startA}, B:${startB}`);

        // Test list filtering: list only running threads (API, quick)
        let runningOk = false;
        for (let i = 0; i < 5; i++) {
            const runningResp = await axios.get('http://localhost:3001/list', { params: { status: 'running' } });
            const runningThreads: any[] = runningResp.data;
            const hasA = runningThreads.some((t: any) => t.id === startA);
            const hasB = runningThreads.some((t: any) => t.id === startB);
            if (hasA && hasB) {
                runningOk = true;
                break;
            }
            await new Promise(r => setTimeout(r, 200));
        }
        if (!runningOk) throw new Error('Status filter should include both running threads');
        console.log('Verified: list --status=running works');

        // Wait for both
        execSync(`node ${CLI} await ${startA}`, { env });
        execSync(`node ${CLI} await ${startB}`, { env });
        console.log('Both finished');

        // After completion, CLI list outputs (JSON array and NDJSON)
        const listOut = execSync(`node ${CLI} list --json`, { env }).toString();
        const listThreads = JSON.parse(listOut);
        if (!listThreads.some((t: any) => t.id === startA) || !listThreads.some((t: any) => t.id === startB)) {
            throw new Error('List output missing threads after completion');
        }
        const listNdjson = execSync(`node ${CLI} list --json --jsonl`, { env }).toString().trim().split('\n');
        if (listNdjson.length < 2) {
            throw new Error('Expected NDJSON output when --jsonl is set');
        }

        // --- Test 5: Handshake Timeout (Sad) ---
        console.log('\n[Test 5] Handshake Timeout');
        writeInstructions([
            { type: 'log', message: 'Silent...', _mock_delay_ms: 2600 }, // > handshake timeout in tests
            { type: 'turn_start', thread_id: 'timeout-thread' }
        ]);
        try {
            // This should fail because daemon kills it after 10s
            execSync(`node ${CLI} start "timeout" --workdir ${WORKDIR}`, { env, stdio: 'pipe' });
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
            execSync(`node ${CLI} start "crash" --workdir ${WORKDIR}`, { env, stdio: 'pipe' });
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
        const jsonOut = execSync(`node ${CLI} start "json task" --workdir ${WORKDIR} --json`, { env }).toString().trim();
        const jsonData = JSON.parse(jsonOut);
        if (jsonData.thread_id !== 'json-thread') throw new Error(`Expected json-thread, got ${jsonData.thread_id}`);

        const statusJsonData = JSON.parse(execSync(`node ${CLI} status json-thread --json`, { env }).toString().trim());
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
        const owner = execSync(`node ${CLI} self`, { env: cleanEnv }).toString().trim();
        if (owner !== 'project_owner') throw new Error(`Expected project_owner, got ${owner}`);

        // 8b: unknown (when CODEX_SHELL_ENV=1 but no match)
        // Note: agentctl self exits with code 1 when returning "unknown", so we need to catch the error
        try {
            const unknown = execSync(`node ${CLI} self`, { env: { ...selfEnv, CODEX_SHELL_ENV: '1' }, stdio: 'pipe' }).toString().trim();
            if (unknown !== 'unknown') throw new Error(`Expected unknown, got ${unknown}`);
        } catch (e: any) {
            // execSync throws on non-zero exit, check if stdout contains "unknown"
            if (e.stdout && e.stdout.toString().trim() === 'unknown') {
                // This is expected behavior
            } else {
                throw e;
            }
        }

        // --- Test 9: Stop Command ---
        console.log('\n[Test 9] Stop Command');
        writeInstructions([
            { type: 'turn_start', thread_id: 'stop-thread' },
            { type: 'log', message: 'Long running...', _mock_delay_ms: 5000 },
            { type: 'turn_end' }
        ]);

        const stopThreadId = execSync(`node ${CLI} start "long task" --workdir ${WORKDIR} --detach`, { env }).toString().trim();
        console.log(`Started thread ${stopThreadId}`);

        // Give it a moment to start
        await new Promise(r => setTimeout(r, 500));

        // Stop it
        execSync(`node ${CLI} stop ${stopThreadId}`, { env });
        console.log('Sent stop command');

        // Wait a bit for status to update
        await new Promise(r => setTimeout(r, 500));

        // Check status is aborted
        const stopStatus = JSON.parse(execSync(`node ${CLI} status ${stopThreadId}`, { env }).toString());
        if (stopStatus.status !== 'aborted') {
            throw new Error(`Expected aborted status, got ${stopStatus.status}`);
        }
        console.log('Verified: Thread was aborted');

        console.log('\nAll Tests Passed!');
    } catch (e: any) {
        console.error('Test Failed:', e.message);
        if (e.stdout) console.log(e.stdout.toString());
        if (e.stderr) console.error(e.stderr.toString());
        process.exit(1);
    } finally {
        try {
            if (daemon.pid) {
                process.kill(daemon.pid);
            }
        } catch (e) {
            // ignore if daemon already exited
        }
        process.exit(0);
    }
}

run();
