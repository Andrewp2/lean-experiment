import { useState } from 'react'
import './App.css'
import { leanSamples } from './assets/samples'
import { importRegistry } from './assets/imports'

function App() {
  const [input, setInput] = useState(leanSamples[0]?.value ?? '')
  const [activeImports, setActiveImports] = useState<string[]>(leanSamples[0]?.imports ?? [])
  const [output, setOutput] = useState<string[]>([])
  const [theme, setTheme] = useState<'highk' | 'reticle'>('highk')
  const [status, setStatus] = useState<'idle' | 'pending' | 'ready' | 'error'>('idle')
  const [errorMessage, setErrorMessage] = useState<string | null>(null)

  const idleLines = ['LLM output will appear here.']
  const pendingLines = ['Request in progress.']
  const errorLines = [errorMessage ?? 'LLM request failed.']

  const displayedLines =
    output.length > 0
      ? output
      : status === 'pending'
        ? pendingLines
        : status === 'error'
          ? errorLines
          : idleLines
  const isPlaceholder = output.length === 0 && status === 'idle'

  const handleRequest = async () => {
    if (!input.trim()) {
      setErrorMessage('Add a Lean proof before requesting the LLM.')
      setStatus('error')
      return
    }

    const importPayload = activeImports
      .map((name) => {
        const content = importRegistry[name]
        return content ? { name, content } : null
      })
      .filter((entry): entry is { name: string; content: string } => entry !== null)

    setStatus('pending')
    setErrorMessage(null)
    setOutput([])

    try {
      const response = await fetch('/api/explain', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          proof: input,
          imports: importPayload,
        }),
      })

      if (!response.ok) {
        const errorText = await response.text()
        throw new Error(errorText || 'Request failed.')
      }

      const data = (await response.json()) as { text?: string }
      const text = data.text?.trim()
      if (!text) {
        setStatus('error')
        setErrorMessage('No response text returned from the server.')
        return
      }

      setOutput(text.split('\n').filter((line) => line.trim().length > 0))
      setStatus('ready')
    } catch (error) {
      const message = error instanceof Error ? error.message : 'Request failed.'
      setErrorMessage(message)
      setStatus('error')
    }
  }

  return (
    <div className={`page theme-${theme}`}>
      <header className="site-header">
        <div className="wordmark">
          <span className="wordmark-title">LEAN LAB</span>
          <span className="wordmark-sub">PROOF WALKTHROUGH SYSTEM</span>
        </div>
        <nav className="site-nav">
          <a href="#">Work</a>
          <a href="#">Spec</a>
          <a href="#">Tools</a>
          <a href="#">Contact</a>
        </nav>
        <button
          className="ghost-button theme-toggle"
          onClick={() => setTheme(theme === 'highk' ? 'reticle' : 'highk')}
        >
          {theme === 'highk' ? 'RETICLE MODE' : 'HIGHK MODE'}
        </button>
      </header>

      <section className="intro">
        <h1>TR-001 · Proof Walkthrough Generator</h1>
        <p>
          Paste a Lean proof or tactic script. The system sends the proof plus its imports to a server
          LLM and returns a walkthrough.
        </p>
      </section>

      <main className="workspace">
        <section className="panel">
          <div className="panel-header">
            <div>
              <h2>Section A · Lean input</h2>
              <p>Paste a theorem, lemma, or tactic block.</p>
            </div>
          </div>
          <textarea
            className="code-input"
            spellCheck={false}
            value={input}
            onChange={(event) => setInput(event.target.value)}
          />
          <div className="panel-actions">
            <button
              className="primary-button"
              onClick={handleRequest}
              disabled={status === 'pending'}
            >
              Request LLM Explanation
            </button>
          </div>
          {activeImports.length > 0 ? (
            <div className="callout note">
              <span className="callout-label">NOTE</span>
              <div>
                <p>Imports available to the LLM:</p>
                <ul>
                  {activeImports.map((entry) => (
                    <li key={entry}>{entry}</li>
                  ))}
                </ul>
              </div>
            </div>
          ) : null}
        </section>

        <section className="panel">
          <div className="panel-header">
            <div>
              <h2>Section B · LLM response</h2>
              <p>Receive an explanation from a LLM.</p>
            </div>
            <span className={`status-chip ${status}`}>
              {status === 'ready'
                ? 'READY'
                : status === 'pending'
                  ? 'PENDING'
                  : status === 'error'
                    ? 'ERROR'
                    : 'IDLE'}
            </span>
          </div>
          <div className="explain-output">
            {displayedLines.map((line, index) => (
              <p key={`${line}-${index}`} className={isPlaceholder ? 'placeholder' : undefined}>
                {line}
              </p>
            ))}
          </div>
          <div className="panel-footer">
            <div>
              <p className="meta-label">NEXT</p>
              <p className="meta-value">LLM walkthroughs return here after processing.</p>
            </div>
            <button
              className="ghost-button"
              onClick={() => {
                setOutput([])
                setStatus('idle')
                setErrorMessage(null)
              }}
            >
              Clear explanation
            </button>
          </div>
        </section>
      </main>

      <section className="samples">
        <div className="panel-header">
          <div>
            <h2>Section C · Sample proofs</h2>
            <p>Select a stored proof block from the registry.</p>
          </div>
        </div>
        <div className="table">
          <div className="table-row table-head">
            <span>LABEL</span>
            <span>IMPORTS</span>
            <span className="table-action">LOAD</span>
          </div>
          {leanSamples.map((sample) => (
            <div className="table-row" key={sample.label}>
              <span>{sample.label}</span>
              <span>{sample.imports?.join(', ') ?? 'NONE'}</span>
              <button
                className="ghost-button"
                onClick={() => {
                  setInput(sample.value)
                  setActiveImports(sample.imports ?? [])
                }}
              >
                Load
              </button>
            </div>
          ))}
        </div>
      </section>
    </div>
  )
}

export default App
