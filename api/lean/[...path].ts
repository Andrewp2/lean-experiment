import type { VercelRequest, VercelResponse } from '@vercel/node'

const getEnv = (name: string) => process.env[name] ?? ''

export default async function handler(req: VercelRequest, res: VercelResponse) {
  const baseUrl = getEnv('LEAN_BRIDGE_URL')
  const token = getEnv('LEAN_BRIDGE_TOKEN')

  if (!baseUrl) {
    res.status(500).json({ error: 'LEAN_BRIDGE_URL is not set.' })
    return
  }
  if (!token) {
    res.status(500).json({ error: 'LEAN_BRIDGE_TOKEN is not set.' })
    return
  }

  const queryPath = Array.isArray(req.query.path) ? req.query.path.join('/') : req.query.path
  const urlPath =
    typeof queryPath === 'string' && queryPath.length > 0
      ? queryPath
      : req.url?.replace(/^\/api\/lean\/?/, '').split('?')[0] ?? ''
  const url = `${baseUrl.replace(/\/$/, '')}/${urlPath}`

  try {
    const upstream = await fetch(url, {
      method: req.method,
      headers: {
        'x-lean-bridge-token': token,
        'Content-Type': req.headers['content-type'] ?? 'application/json',
      },
      body: req.method === 'GET' || req.method === 'HEAD' ? undefined : JSON.stringify(req.body),
    })

    const contentType = upstream.headers.get('content-type') ?? 'application/json'
    res.status(upstream.status)
    res.setHeader('Content-Type', contentType)
    res.send(await upstream.text())
  } catch (error) {
    const message = error instanceof Error ? error.message : 'Proxy failed.'
    const cause =
      error instanceof Error && 'cause' in error
        ? (error as Error & { cause?: unknown }).cause
        : undefined
    console.error('Lean proxy fetch failed', { url, message, cause })
    res.status(500).json({ error: message })
  }
}
