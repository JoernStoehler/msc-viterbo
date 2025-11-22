import express from 'express';
import path from 'path';
import { StateManager, ThreadStatus } from './state';
import { ProcessManager } from './process-manager';

const app = express();
app.use(express.json());

const stateManager = new StateManager();
const processManager = new ProcessManager(stateManager);

const PORT = process.env.AGENTCTL_PORT || 3000;

app.post('/turn/start', async (req, res) => {
    try {
        const { prompt, workdir, thread_id } = req.body;
        if (!prompt) {
            return res.status(400).json({ error: 'Missing prompt' });
        }

        let resolvedWorkdir = workdir as string | undefined;

        if (thread_id) {
            const existing = stateManager.getStatus(thread_id);
            if (existing && existing.workdir) {
                // If caller provided a workdir, ensure it matches; otherwise use existing.
                if (resolvedWorkdir && path.resolve(resolvedWorkdir) !== path.resolve(existing.workdir)) {
                    return res.status(400).json({ error: 'Workdir mismatch with existing thread' });
                }
                resolvedWorkdir = existing.workdir;
            } else if (!resolvedWorkdir) {
                return res.status(400).json({ error: 'Missing workdir; thread_id not known' });
            }
        }

        if (!resolvedWorkdir) {
            return res.status(400).json({ error: 'Missing workdir' });
        }

        const id = await processManager.startTurn(prompt, resolvedWorkdir, thread_id);
        res.json({ thread_id: id, status: 'running' });
    } catch (e: any) {
        console.error(e);
        res.status(500).json({ error: e.message });
    }
});

app.get('/turn/:id', (req, res) => {
    const status = stateManager.getStatus(req.params.id);
    if (!status) {
        return res.status(404).json({ error: 'Thread not found' });
    }
    res.json(status);
});

app.post('/turn/stop', (req, res) => {
    const { thread_id } = req.body;
    if (!thread_id) {
        return res.status(400).json({ error: 'Missing thread_id' });
    }
    const status = stateManager.getStatus(thread_id);
    if (status?.managed === 'external') {
        return res.status(400).json({ error: 'Cannot stop externally managed thread' });
    }
    processManager.stopTurn(thread_id);
    res.json({ status: 'aborted' });
});

app.post('/external/start', (req, res) => {
    const { thread_id, workdir, pid, session_file, originator, source, codex_cwd, notes } = req.body;
    if (!thread_id) {
        return res.status(400).json({ error: 'Missing thread_id' });
    }
    const now = new Date().toISOString();
    const status: ThreadStatus = {
        id: thread_id,
        pid: pid ?? null,
        status: 'running' as const,
        exit_code: null,
        workdir: workdir || '',
        managed: 'external' as const,
        session_file,
        originator,
        source,
        codex_cwd,
        notes,
        created_at: now,
        updated_at: now
    };
    stateManager.saveStatus(status);
    res.json({ thread_id, status: 'running' });
});

app.post('/external/finish', (req, res) => {
    const { thread_id, exit_code, status: endStatus } = req.body;
    if (!thread_id) {
        return res.status(400).json({ error: 'Missing thread_id' });
    }
    const current = stateManager.getStatus(thread_id);
    if (!current) {
        return res.status(404).json({ error: 'Thread not found' });
    }
    const finalStatus = endStatus || (exit_code === 0 ? 'done' : 'failed');
    const updated = {
        ...current,
        status: finalStatus,
        exit_code: exit_code ?? current.exit_code,
        updated_at: new Date().toISOString()
    };
    stateManager.saveStatus(updated);
    res.json({ status: updated.status });
});

app.get('/list', (req, res) => {
    let threads = stateManager.listThreads();
    const statusFilter = req.query.status as string;
    if (statusFilter) {
        threads = threads.filter(t => t.status === statusFilter);
    }
    res.json(threads);
});

app.get('/health', (_req, res) => {
    res.json({
        status: 'ok',
        pid: process.pid,
        port: Number(PORT),
        uptime_s: Math.round(process.uptime())
    });
});

app.listen(PORT, () => {
    console.log(`Daemon listening on port ${PORT}`);
    stateManager.writeDaemonPid(process.pid);
    stateManager.writeDaemonPort(Number(PORT));
});
