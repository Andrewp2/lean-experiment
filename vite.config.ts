import { defineConfig } from 'vite'
import react from '@vitejs/plugin-react'
import type { IncomingMessage } from 'node:http'
import { resolve } from 'node:path'

type ExplainRequest = {
  proof?: string
  imports?: Array<{ name: string; content: string }>
}

const readJson = async (req: IncomingMessage) =>
  new Promise<ExplainRequest>((resolve, reject) => {
    let body = ''
    req.on('data', (chunk) => {
      body += chunk
    })
    req.on('end', () => {
      try {
        resolve(body ? JSON.parse(body) : {})
      } catch (error) {
        reject(error)
      }
    })
    req.on('error', (error) => reject(error))
  })

const extractText = (data: any) => {
  const responseText = Array.isArray(data?.output)
    ? data.output
        .flatMap((item: any) => item?.content ?? [])
        .filter((content: any) => content?.type === 'output_text')
        .map((content: any) => content?.text ?? '')
        .join('\n')
    : ''
  const chatText = data?.choices?.[0]?.message?.content
  return (responseText || chatText || '').trim()
}

// https://vitejs.dev/config/
export default defineConfig({
  base: './',
  plugins: [
    react(),
    {
      name: 'openai-proxy',
      configureServer(server) {
        server.middlewares.use('/api/explain', async (req, res) => {
          if (req.method !== 'POST') {
            res.statusCode = 405
            res.end('Method Not Allowed')
            return
          }

          try {
            const apiKey = process.env.OPENAI_API_KEY
            if (!apiKey) {
              res.statusCode = 500
              res.end('OPENAI_API_KEY is not set.')
              return
            }

            const body = await readJson(req)
            const proof = body.proof ?? ''
            const imports = body.imports ?? []
            const importsSection =
              imports.length > 0
                ? imports
                    .map((entry) => `# ${entry.name}\n${entry.content}`)
                    .join('\n\n')
                : 'None'

            const prompt = [
              'You are a Lean proof explainer.',
              'Explain the proof step by step in clear, plain language.',
              'If a tactic depends on an import, mention it briefly.',
              '',
              'Imports:',
              importsSection,
              '',
              'Proof:',
              proof,
            ].join('\n')

            const upstream = await fetch('https://api.openai.com/v1/responses', {
              method: 'POST',
              headers: {
                Authorization: `Bearer ${apiKey}`,
                'Content-Type': 'application/json',
              },
              body: JSON.stringify({
                model: 'gpt-5-nano',
                input: [
                  {
                    role: 'system',
                    content: 'You explain Lean proofs with a technical, concise tone.',
                  },
                  {
                    role: 'user',
                    content: prompt,
                  },
                ],
              }),
            })

            const data = await upstream.json()
            if (!upstream.ok) {
              res.statusCode = upstream.status
              res.setHeader('Content-Type', 'application/json')
              res.end(JSON.stringify({ error: data?.error?.message ?? 'OpenAI error.' }))
              return
            }

            const text = extractText(data)
            res.statusCode = 200
            res.setHeader('Content-Type', 'application/json')
            res.end(JSON.stringify({ text }))
          } catch (error) {
            res.statusCode = 500
            res.end(error instanceof Error ? error.message : 'Server error.')
          }
        })
      },
    },
  ],
  build: {
    rollupOptions: {
      input: {
        main: resolve(__dirname, 'index.html'),
        'pages/tactics': resolve(__dirname, 'pages/tactics.html'),
        'pages/visualizer': resolve(__dirname, 'pages/visualizer.html'),
        mathlib: resolve(__dirname, 'pages/mathlib.html'),
        'pages/mathlib-vscode': resolve(__dirname, 'pages/mathlib-vscode.html'),
      },
    },
  },
  server: {
    port: 1421,
    strictPort: true,
  },
})
