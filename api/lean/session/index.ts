import type { VercelRequest, VercelResponse } from '@vercel/node'
import { proxyToLean } from '../_proxy'

export default async function handler(req: VercelRequest, res: VercelResponse) {
  await proxyToLean(req, res, 'session')
}
