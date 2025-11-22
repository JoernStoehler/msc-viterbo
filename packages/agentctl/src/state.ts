import fs from 'fs';
import path from 'path';
import os from 'os';

const DEFAULT_STATE_DIR = path.join(os.homedir(), '.agentctl', 'state');

export interface ThreadStatus {
    id: string;
    pid: number | null;
    status: 'running' | 'done' | 'failed' | 'aborted';
    exit_code: number | null;
    workdir: string;
    managed?: 'daemon' | 'external';
    session_file?: string;
    originator?: string;
    source?: string;
    codex_cwd?: string;
    notes?: string;
    created_at: string;
    updated_at: string;
}

export class StateManager {
    private baseDir: string;

    constructor(baseDir: string = process.env.AGENTCTL_STATE_DIR || DEFAULT_STATE_DIR) {
        this.baseDir = baseDir;
        if (!fs.existsSync(this.baseDir)) {
            fs.mkdirSync(this.baseDir, { recursive: true });
        }
        const threadsDir = path.join(this.baseDir, 'threads');
        if (!fs.existsSync(threadsDir)) {
            fs.mkdirSync(threadsDir);
        }
    }

    getThreadDir(threadId: string): string {
        return path.join(this.baseDir, 'threads', threadId);
    }

    ensureThreadDir(threadId: string) {
        const dir = this.getThreadDir(threadId);
        if (!fs.existsSync(dir)) {
            fs.mkdirSync(dir, { recursive: true });
        }
        return dir;
    }

    saveStatus(status: ThreadStatus) {
        const dir = this.ensureThreadDir(status.id);
        fs.writeFileSync(path.join(dir, 'status.json'), JSON.stringify(status, null, 2));
    }

    getStatus(threadId: string): ThreadStatus | null {
        const p = path.join(this.getThreadDir(threadId), 'status.json');
        if (!fs.existsSync(p)) return null;
        try {
            return JSON.parse(fs.readFileSync(p, 'utf-8'));
        } catch {
            return null;
        }
    }

    listThreads(): ThreadStatus[] {
        const threadsDir = path.join(this.baseDir, 'threads');
        if (!fs.existsSync(threadsDir)) return [];

        const ids = fs.readdirSync(threadsDir);
        const statuses: ThreadStatus[] = [];

        for (const id of ids) {
            const s = this.getStatus(id);
            if (s) statuses.push(s);
        }
        return statuses;
    }

    getLogPath(threadId: string): string {
        return path.join(this.getThreadDir(threadId), 'log.jsonl');
    }

    getStdoutPath(threadId: string): string {
        return path.join(this.getThreadDir(threadId), 'stdout.log');
    }

    getStderrPath(threadId: string): string {
        return path.join(this.getThreadDir(threadId), 'stderr.log');
    }

    writeDaemonPid(pid: number) {
        fs.writeFileSync(path.join(this.baseDir, 'daemon.pid'), pid.toString());
    }

    writeDaemonPort(port: number) {
        fs.writeFileSync(path.join(this.baseDir, 'daemon.port'), port.toString());
    }
}
