import express from 'express';
import { StateManager } from './state';
import { ProcessManager } from './process-manager';

const app = express();
app.use(express.json());

const stateManager = new StateManager();
const processManager = new ProcessManager(stateManager);

const PORT = process.env.AGENTCTL_PORT || 3000;

app.post('/turn/start', async (req, res) => {
    try {
        const { prompt, workdir, thread_id } = req.body;
        if (!prompt || !workdir) {
            return res.status(400).json({ error: 'Missing prompt or workdir' });
        }

        const id = await processManager.startTurn(prompt, workdir, thread_id);
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
    processManager.stopTurn(thread_id);
    res.json({ status: 'aborted' });
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
