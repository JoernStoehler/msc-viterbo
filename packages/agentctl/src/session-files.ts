import fs from 'fs';
import path from 'path';
import os from 'os';

export type SessionMeta = {
    id: string;
    cwd?: string;
    originator?: string;
    source?: string;
    model_provider?: string;
};

export type SessionFile = {
    path: string;
    mtimeMs: number;
    meta?: SessionMeta | null;
};

export const DEFAULT_SESSIONS_ROOT = path.join(os.homedir(), '.codex', 'sessions');

export function getSessionsRoot(): string {
    return process.env.AGENTCTL_CODEX_SESSIONS_DIR || DEFAULT_SESSIONS_ROOT;
}

function walkSessions(root: string): SessionFile[] {
    if (!fs.existsSync(root)) return [];
    const results: SessionFile[] = [];

    const stack: string[] = [root];
    while (stack.length) {
        const current = stack.pop() as string;
        const entries = fs.readdirSync(current, { withFileTypes: true });
        for (const entry of entries) {
            const full = path.join(current, entry.name);
            if (entry.isDirectory()) {
                if (entry.name === 'archived_sessions') continue;
                stack.push(full);
            } else if (entry.isFile() && entry.name.endsWith('.jsonl')) {
                try {
                    const stat = fs.statSync(full);
                    results.push({ path: full, mtimeMs: stat.mtimeMs });
                } catch {
                    // ignore
                }
            }
        }
    }
    return results;
}

export function extractSessionIdFromFilename(filePath: string): string | null {
    const base = path.basename(filePath);
    const match = base.match(/([0-9a-fA-F-]{36})\.jsonl$/);
    return match ? match[1] : null;
}

export function readSessionMeta(filePath: string): SessionMeta | null {
    const READ_CHUNK_BYTES = 4096;
    const MAX_FIRST_LINE_BYTES = 1024 * 1024; // defensive cap; session_meta lines can include full AGENTS.md

    try {
        const fd = fs.openSync(filePath, 'r');
        let firstLine = '';
        const buffer = Buffer.alloc(READ_CHUNK_BYTES);
        let position = 0;

        try {
            while (firstLine.length < MAX_FIRST_LINE_BYTES) {
                const bytes = fs.readSync(fd, buffer, 0, buffer.length, position);
                if (bytes <= 0) break;
                const chunk = buffer.toString('utf-8', 0, bytes);
                const newlineIdx = chunk.indexOf('\n');
                if (newlineIdx !== -1) {
                    firstLine += chunk.slice(0, newlineIdx);
                    break;
                }
                firstLine += chunk;
                position += bytes;
                if (bytes < READ_CHUNK_BYTES) break; // EOF without newline
            }
        } finally {
            try { fs.closeSync(fd); } catch { /* ignore */ }
        }

        if (!firstLine.trim()) return null;
        const parsed = JSON.parse(firstLine);
        if (parsed?.payload?.id) {
            return {
                id: parsed.payload.id,
                cwd: parsed.payload.cwd,
                originator: parsed.payload.originator,
                source: parsed.payload.source,
                model_provider: parsed.payload.model_provider
            };
        }
        return null;
    } catch {
        return null;
    }
}

export type DiscoverOptions = {
    expectedUuid?: string;
    expectedCwd?: string;
    sinceMs: number;
    timeoutMs?: number;
    pollIntervalMs?: number;
};

export async function discoverSessionFile(options: DiscoverOptions): Promise<{ file: SessionFile; meta: SessionMeta }> {
    const root = getSessionsRoot();
    const timeout = options.timeoutMs ?? 1000;
    const poll = options.pollIntervalMs ?? 100;
    const deadline = Date.now() + timeout;
    const expectedCwdNorm = options.expectedCwd ? path.resolve(options.expectedCwd) : undefined;

    const seen = new Set<string>();

    while (Date.now() < deadline) {
        const files = walkSessions(root)
            .filter(f => f.mtimeMs >= options.sinceMs)
            .sort((a, b) => {
                const diff = b.mtimeMs - a.mtimeMs;
                if (diff !== 0) return diff;
                return b.path.localeCompare(a.path); // deterministic tie-breaker
            });

        for (const f of files) {
            if (seen.has(f.path)) continue;
            seen.add(f.path);
            const meta = readSessionMeta(f.path);
            if (!meta) continue;
            const filenameId = extractSessionIdFromFilename(f.path);
            if (options.expectedUuid && meta.id !== options.expectedUuid && filenameId !== options.expectedUuid) {
                continue;
            }
            if (expectedCwdNorm && meta.cwd && path.resolve(meta.cwd) !== expectedCwdNorm) {
                continue;
            }
            return { file: { ...f, meta }, meta };
        }

        await new Promise(r => setTimeout(r, poll));
    }

    throw new Error('Session file not found within timeout window');
}
