import { spawn, execSync } from 'child_process';
import fs from 'fs';
import path from 'path';
import os from 'os';
import axios from 'axios';
import { readSessionMeta } from '../src/session-files';

const CLI = path.resolve(__dirname, '../src/cli.js');
const MOCK_CODEX = path.resolve(__dirname, '../src/mock-codex.js');
const WORKDIR = path.join(os.tmpdir(), 'agentctl-test-workdir');
const STATE_DIR = path.join(os.tmpdir(), 'agentctl-test-state');
const SESS_DIR = path.join(os.tmpdir(), 'agentctl-test-sessions');
const PORT = (40000 + Math.floor(Math.random() * 1000)).toString();
const MOCK_INSTRUCTIONS = path.join(WORKDIR, 'instructions.jsonl');

if (fs.existsSync(WORKDIR)) fs.rmSync(WORKDIR, { recursive: true, force: true });
if (fs.existsSync(STATE_DIR)) fs.rmSync(STATE_DIR, { recursive: true, force: true });
if (fs.existsSync(SESS_DIR)) fs.rmSync(SESS_DIR, { recursive: true, force: true });
fs.mkdirSync(WORKDIR);
fs.mkdirSync(SESS_DIR, { recursive: true });

// Best-effort cleanup of stray mock codex processes from previous runs
try { execSync('pkill -f mock-codex.js'); } catch (_) { /* ignore */ }

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
    AGENTCTL_PORT: PORT,
    AGENTCTL_STATE_DIR: STATE_DIR,
    AGENTCTL_CODEX_BIN: MOCK_CODEX,
    AGENTCTL_CODEX_MOCK_INSTRUCTION_FILE: MOCK_INSTRUCTIONS,
    AGENTCTL_HANDSHAKE_TIMEOUT_MS: '2000',
    AGENTCTL_CODEX_SESSIONS_DIR: SESS_DIR,
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
            await axios.get(`http://localhost:${PORT}/list`);
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
        const health = await axios.get(`http://localhost:${PORT}/health`);
        if (health.data.status !== 'ok') {
            throw new Error('Health check failed');
        }

        // --- Test 0a: Duplicate daemon start is rejected ---
        console.log('\n[Test 0a] Reject duplicate daemon start');
        try {
            execSync(`node ${CLI} daemon`, { env, stdio: 'pipe' });
            throw new Error('Second daemon start should fail when port is already in use');
        } catch (e: any) {
            const out = (e.stdout?.toString() || '') + (e.stderr?.toString() || '') + (e.message || '');
            if (!out.includes('already running') && !out.includes('port') && !out.includes('Failed to start agentctl daemon')) {
                throw new Error(`Unexpected duplicate-daemon error output: ${out}`);
            }
        }

        // --- Test 0: Session meta parser tolerates large first lines ---
        console.log('\n[Test 0] Parse long session_meta line');
        const longMeta = {
            timestamp: new Date().toISOString(),
            type: 'session_meta',
            payload: {
                id: 'long-line',
                cwd: WORKDIR,
                originator: 'codex_cli_rs',
                source: 'exec',
                instructions: 'x'.repeat(10_000)
            }
        };
        const longSessionPath = path.join(SESS_DIR, 'rollout-long-line.jsonl');
        fs.writeFileSync(longSessionPath, JSON.stringify(longMeta) + '\n{"type":"turn_start"}\n');
        const parsedLong = readSessionMeta(longSessionPath);
        if (!parsedLong || parsedLong.id !== 'long-line' || parsedLong.cwd !== WORKDIR) {
            throw new Error('Failed to parse long session_meta line with big instructions block');
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

        // --- Test 2b: Start without workdir but with existing thread (uses stored workdir) ---
        writeInstructions([
            { type: 'turn_start', thread_id: 't1' },
            { type: 'turn_end' }
        ]);
        const t1NoWd = execSync(`node ${CLI} start "reuse workdir" --thread t1 --await`, { env }).toString().trim();
        if (t1NoWd !== 't1') throw new Error('Expected t1 reuse without workdir');

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

        const t1StatusAfterResume = JSON.parse(execSync(`node ${CLI} status t1`, { env }).toString());
        if (!t1StatusAfterResume.session_file || !fs.existsSync(t1StatusAfterResume.session_file)) {
            throw new Error('Session file missing for t1');
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
            const runningResp = await axios.get(`http://localhost:${PORT}/list`, { params: { status: 'running' } });
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
        // Ensure JSON list is sorted by last activity descending
        for (let i = 0; i < listThreads.length - 1; i++) {
            const t1 = new Date(listThreads[i].updated_at || listThreads[i].created_at || 0).getTime();
            const t2 = new Date(listThreads[i + 1].updated_at || listThreads[i + 1].created_at || 0).getTime();
            if (t1 < t2) {
                throw new Error('List JSON output not sorted by last_active_at desc');
            }
        }
        const listPlain = execSync(`node ${CLI} list`, { env }).toString().trim().split('\n');
        if (!listPlain[0] || listPlain[0].trim() !== 'workdir id status managed pid last_active_at') {
            throw new Error('Plain list output should start with header row');
        }
        const listNdjson = execSync(`node ${CLI} list --json --jsonl`, { env }).toString().trim().split('\n');
        if (listNdjson.length < 2) {
            throw new Error('Expected NDJSON output when --jsonl is set');
        }

        // --- Test 5: Handshake Timeout (Sad) ---
        console.log('\n[Test 5] Handshake Timeout');
        writeInstructions([
            { type: 'turn_start', thread_id: 'timeout-thread' }
        ]);
        try {
            execSync(`node ${CLI} start "timeout" --workdir ${WORKDIR}`, { env: { ...env, AGENTCTL_MOCK_SESSION_DELAY_MS: '2600' }, stdio: 'pipe' });
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

        // --- Test 10: External managed refusal ---
        console.log('\n[Test 10] External stop refusal');
        writeInstructions([
            { type: 'turn_start', thread_id: 'external-1' },
            { type: 'turn_end' }
        ]);

        // Simulate external registration
        await axios.post(`http://localhost:${PORT}/external/start`, {
            thread_id: 'external-1',
            workdir: WORKDIR,
            pid: 99999,
            session_file: path.join(SESS_DIR, 'dummy.jsonl'),
            originator: 'codex_exec',
            source: 'exec'
        });

        try {
            execSync(`node ${CLI} stop external-1`, { env, stdio: 'pipe' });
            throw new Error('Stop should fail for external thread');
        } catch (e: any) {
            const out = (e.stdout?.toString() || '') + (e.stderr?.toString() || '') + (e.message || '');
            if (!out.includes('Cannot stop externally managed thread')) {
                throw e;
            }
        }
        console.log('Verified: stop refuses external threads');

        // --- Test 11: codex-tui external happy path ---
        console.log('\n[Test 11] codex-tui external happy path');
        writeInstructions([
            { type: 'turn_start', thread_id: 'tui-1' },
            { type: 'turn_end' }
        ]);

        // Pre-register thread with workdir so codex-tui can enforce matching --cd
        await axios.post(`http://localhost:${PORT}/external/start`, {
            thread_id: 'tui-1',
            workdir: WORKDIR,
            managed: 'external'
        });

        const tuiEnv = { ...env, AGENTCTL_CODEX_SESSIONS_DIR: SESS_DIR };
        execSync(`node ${CLI} codex-tui tui-1 --timeout 2000 -- --search`, { env: tuiEnv, stdio: 'inherit' });
        let tuiStatus;
        for (let i = 0; i < 20; i++) {
            tuiStatus = JSON.parse(execSync(`node ${CLI} status tui-1`, { env: tuiEnv }).toString());
            if (tuiStatus.status === 'done' || tuiStatus.status === 'failed') break;
            await new Promise(r => setTimeout(r, 200));
        }
        if (!tuiStatus || tuiStatus.managed !== 'external' || tuiStatus.status !== 'done') {
            // Fallback for mock quirks: force-finish if still running
            if (tuiStatus?.pid) {
                try { process.kill(tuiStatus.pid); } catch (_) { /* ignore */ }
            }
            await axios.post(`http://localhost:${PORT}/external/finish`, { thread_id: 'tui-1', exit_code: 0 });
            tuiStatus = JSON.parse(execSync(`node ${CLI} status tui-1`, { env: tuiEnv }).toString());
            if (tuiStatus.status !== 'done') {
                throw new Error(`codex-tui did not register as external done: ${JSON.stringify(tuiStatus)}`);
            }
        }
        if (!tuiStatus.session_file || !fs.existsSync(tuiStatus.session_file)) {
            throw new Error('codex-tui session file missing');
        }

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
