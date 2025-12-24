import type { VercelRequest, VercelResponse } from '@vercel/node'

type ExplainRequest = {
  proof?: string
  imports?: Array<{ name: string; content: string }>
}

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

export default async function handler(req: VercelRequest, res: VercelResponse) {
  if (req.method !== 'POST') {
    res.status(405).send('Method Not Allowed')
    return
  }

  const apiKey = process.env.OPENAI_API_KEY
  if (!apiKey) {
    res.status(500).send('OPENAI_API_KEY is not set.')
    return
  }

  try {
    const body = (req.body ?? {}) as ExplainRequest
    const proof = body.proof ?? ''
    const imports = body.imports ?? []
    const importsSection =
      imports.length > 0
        ? imports.map((entry) => `# ${entry.name}\n${entry.content}`).join('\n\n')
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
      res.status(upstream.status).json({ error: data?.error?.message ?? 'OpenAI error.' })
      return
    }

    const text = extractText(data)
    res.status(200).json({ text })
  } catch (error) {
    res.status(500).send(error instanceof Error ? error.message : 'Server error.')
  }
}
