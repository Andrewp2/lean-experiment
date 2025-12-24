import { useState } from 'react'
import './App.css'
import { leanSamples } from './assets/samples'

function App() {
  const [input, setInput] = useState(leanSamples[0]?.value ?? '')
  const [activeImports, setActiveImports] = useState<string[]>(leanSamples[0]?.imports ?? [])
  const [output, setOutput] = useState<string[]>([])

  const idleLines = ['LLM output will appear here.']

  return (
    <div className="page theme-highk">
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
              onClick={() => setOutput(['LLM request queued. Connect API to return results.'])}
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
              <p>Server-generated commentary aligned with the proof context.</p>
            </div>
            <span className="status-chip">{output.length > 0 ? 'PENDING' : 'IDLE'}</span>
          </div>
          <div className="explain-output">
            {(output.length > 0 ? output : idleLines).map((line, index) => (
              <p key={`${line}-${index}`} className={output.length > 0 ? undefined : 'placeholder'}>
                {line}
              </p>
            ))}
          </div>
          <div className="panel-footer">
            <div>
              <p className="meta-label">NEXT</p>
              <p className="meta-value">LLM walkthroughs return here after processing.</p>
            </div>
            <button className="ghost-button" onClick={() => setOutput([])}>
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
