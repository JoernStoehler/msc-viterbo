import fs from 'fs';
import path from 'path';
import os from 'os';
import { setTimeout } from 'timers/promises';

function getArgValue(flag: string, args: string[]): string | undefined {
    const idx = args.indexOf(flag);
    if (idx !== -1 && idx + 1 < args.length) return args[idx + 1];
    return undefined;
}

function sessionRoot(): string {
    return process.env.AGENTCTL_CODEX_SESSIONS_DIR || path.join(os.homedir(), '.codex', 'sessions');
}

function ensureDir(p: string) {
    if (!fs.existsSync(p)) fs.mkdirSync(p, { recursive: true });
}

async function main() {
    const args = process.argv.slice(2);
    const outputLastMessage = getArgValue('--output-last-message', args);
    const cd = getArgValue('--cd', args) || process.cwd();

    const instructionFile = process.env.AGENTCTL_CODEX_MOCK_INSTRUCTION_FILE;
    if (!instructionFile) {
        console.error('Error: AGENTCTL_CODEX_MOCK_INSTRUCTION_FILE not set');
        process.exit(1);
    }
    if (!fs.existsSync(instructionFile)) {
        console.error(`Error: Instruction file not found: ${instructionFile}`);
        process.exit(1);
    }

    const content = fs.readFileSync(instructionFile, 'utf-8');
    const lines = content.split('\n').filter(line => line.trim() !== '');
    if (lines.length === 0) {
        console.error('Instruction file empty');
        process.exit(1);
    }

    const events = lines.map(line => JSON.parse(line));
    const first = events[0];
    const threadId = first.thread_id || first.id || 'mock-thread-id';

    const now = new Date();
    const dateDir = path.join(sessionRoot(), now.getUTCFullYear().toString(), String(now.getUTCMonth() + 1).padStart(2, '0'), String(now.getUTCDate()).padStart(2, '0'));
    ensureDir(dateDir);
    const iso = now.toISOString().replace(/:/g, '-');
    const sessionPath = path.join(dateDir, `rollout-${iso}-${threadId}.jsonl`);

    const meta = {
        timestamp: now.toISOString(),
        type: 'session_meta',
        payload: {
            id: threadId,
            timestamp: now.toISOString(),
            cwd: cd,
            originator: 'codex_exec',
            source: 'exec',
            model_provider: 'mock'
        }
    };

    const sessionDelayMs = Number(process.env.AGENTCTL_MOCK_SESSION_DELAY_MS || 0);
    if (sessionDelayMs > 0) {
        await setTimeout(sessionDelayMs);
    }

    fs.writeFileSync(sessionPath, JSON.stringify(meta) + '\n');

    for (const ev of events) {
        if (ev._mock_delay_ms) {
            await setTimeout(ev._mock_delay_ms);
            delete ev._mock_delay_ms;
        }
        if (ev._mock_exit_code !== undefined) {
            process.exit(ev._mock_exit_code);
        }
        fs.appendFileSync(sessionPath, JSON.stringify(ev) + '\n');

        if (outputLastMessage && ev.type === 'turn_end' && ev.final_message) {
            fs.writeFileSync(outputLastMessage, ev.final_message);
        }
    }
}

main().catch(err => {
    console.error(err);
    process.exit(1);
});
