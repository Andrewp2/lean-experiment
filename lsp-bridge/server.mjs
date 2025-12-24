import express from 'express'
import cors from 'cors'
import { spawn } from 'node:child_process'
import { randomUUID } from 'node:crypto'
import { StreamMessageReader, StreamMessageWriter, createMessageConnection } from 'vscode-jsonrpc/node'

const app = express()
const allowedOrigins = getEnv('ALLOWED_ORIGINS', '')
  .split(',')
  .map((value) => value.trim())
  .filter(Boolean)
app.use(
  cors({
    origin: (origin, callback) => {
      if (!origin || allowedOrigins.length === 0 || allowedOrigins.includes(origin)) {
        callback(null, true)
        return
      }
      callback(new Error('Origin not allowed'))
    },
  }),
)
app.use(express.json({ limit: '5mb' }))

const sessions = new Map()

const getEnv = (name, fallback) => process.env[name] ?? fallback

const createSession = async () => {
  const id = randomUUID()
  const cmd = getEnv('LEAN_SERVER_CMD', 'lean')
  const args = getEnv('LEAN_SERVER_ARGS', '--server').split(' ').filter(Boolean)
  const cwd = getEnv('LEAN_PROJECT_ROOT', process.cwd())
  const rootUri = getEnv('LEAN_PROJECT_URI', `file://${cwd}`)

  const child = spawn(cmd, args, { cwd, stdio: 'pipe' })
  const reader = new StreamMessageReader(child.stdout)
  const writer = new StreamMessageWriter(child.stdin)
  const connection = createMessageConnection(reader, writer)
  connection.listen()

  const session = {
    id,
    child,
    connection,
    rootUri,
    docs: new Map(),
  }

  sessions.set(id, session)

  await connection.sendRequest('initialize', {
    processId: process.pid,
    rootUri,
    capabilities: {},
  })
  connection.sendNotification('initialized', {})

  return session
}

const getSession = (id) => sessions.get(id)

const ensureSession = async (req, res) => {
  const { sessionId } = req.body ?? {}
  if (sessionId) {
    const existing = getSession(sessionId)
    if (existing) {
      return existing
    }
  }
  const created = await createSession()
  res.setHeader('X-Session-Id', created.id)
  return created
}

const requireAuth = (req, res, next) => {
  const required = getEnv('LEAN_BRIDGE_TOKEN', '')
  if (!required) {
    next()
    return
  }
  const token = req.get('x-lean-bridge-token')
  if (token !== required) {
    res.status(401).json({ error: 'Unauthorized' })
    return
  }
  next()
}

app.get('/health', (req, res) => {
  res.json({ ok: true })
})

app.post('/session', requireAuth, async (req, res) => {
  const session = await createSession()
  res.json({ sessionId: session.id })
})

app.post('/session/open', requireAuth, async (req, res) => {
  const session = await ensureSession(req, res)
  const { uri, text } = req.body ?? {}
  if (!uri || typeof text !== 'string') {
    res.status(400).json({ error: 'uri and text are required.' })
    return
  }

  session.docs.set(uri, { version: 1 })
  session.connection.sendNotification('textDocument/didOpen', {
    textDocument: {
      uri,
      languageId: 'lean',
      version: 1,
      text,
    },
  })
  res.json({ sessionId: session.id, ok: true })
})

app.post('/session/change', requireAuth, async (req, res) => {
  const session = await ensureSession(req, res)
  const { uri, text } = req.body ?? {}
  if (!uri || typeof text !== 'string') {
    res.status(400).json({ error: 'uri and text are required.' })
    return
  }

  const doc = session.docs.get(uri) ?? { version: 0 }
  const version = doc.version + 1
  session.docs.set(uri, { version })
  session.connection.sendNotification('textDocument/didChange', {
    textDocument: { uri, version },
    contentChanges: [{ text }],
  })
  res.json({ sessionId: session.id, ok: true })
})

app.post('/session/request', requireAuth, async (req, res) => {
  const session = await ensureSession(req, res)
  const { method, params } = req.body ?? {}
  if (!method) {
    res.status(400).json({ error: 'method is required.' })
    return
  }
  try {
    const result = await session.connection.sendRequest(method, params ?? {})
    res.json({ sessionId: session.id, result })
  } catch (error) {
    res.status(500).json({ error: error instanceof Error ? error.message : 'Request failed.' })
  }
})

app.post('/session/notify', requireAuth, async (req, res) => {
  const session = await ensureSession(req, res)
  const { method, params } = req.body ?? {}
  if (!method) {
    res.status(400).json({ error: 'method is required.' })
    return
  }
  session.connection.sendNotification(method, params ?? {})
  res.json({ sessionId: session.id, ok: true })
})

app.post('/session/goals', requireAuth, async (req, res) => {
  const session = await ensureSession(req, res)
  const { uri, position } = req.body ?? {}
  if (!uri || !position) {
    res.status(400).json({ error: 'uri and position are required.' })
    return
  }
  const method = getEnv('LEAN_GOALS_METHOD', '$/lean/plainGoal')
  try {
    const result = await session.connection.sendRequest(method, {
      textDocument: { uri },
      position,
    })
    res.json({ sessionId: session.id, result })
  } catch (error) {
    res.status(500).json({ error: error instanceof Error ? error.message : 'Request failed.' })
  }
})

app.post('/session/close', requireAuth, async (req, res) => {
  const { sessionId } = req.body ?? {}
  const session = sessionId ? getSession(sessionId) : null
  if (!session) {
    res.status(404).json({ error: 'Session not found.' })
    return
  }
  try {
    session.connection.sendNotification('exit')
    session.child.kill()
  } finally {
    sessions.delete(sessionId)
  }
  res.json({ ok: true })
})

const port = Number(getEnv('PORT', '8787'))
const host = getEnv('HOST', '0.0.0.0')
app.listen(port, host, () => {
  console.log(`Lean LSP bridge listening on ${host}:${port}`)
})
