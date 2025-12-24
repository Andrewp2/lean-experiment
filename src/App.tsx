import { useMemo, useState } from 'react'
import './App.css'
import { leanSamples } from './assets/samples'

const tacticNotes = [
  { label: 'intro', pattern: /\bintro\b|\bintros\b/, text: 'Introduces variables or hypotheses into the goal.' },
  { label: 'induction', pattern: /\binduction\b/, text: 'Splits the proof into base and inductive cases.' },
  { label: 'cases', pattern: /\bcases\b/, text: 'Performs case analysis on a data type.' },
  { label: 'simp', pattern: /\bsimp\b/, text: 'Simplifies the goal using rewrite rules.' },
  { label: 'rw', pattern: /\brw\b/, text: 'Rewrites the goal with a known equality.' },
  { label: 'exact', pattern: /\bexact\b/, text: 'Closes the goal with an exact proof term.' },
  { label: 'decide', pattern: /\bdecide\b/, text: 'Discharges the goal via decision procedure.' },
]

function buildExplanation(input: string) {
  const trimmed = input.trim()
  if (!trimmed) {
    return ['Paste a Lean proof or tactic script to get a walkthrough.']
  }

  const lines = trimmed.split('\n').filter((line) => line.trim().length > 0)
  const tacticHits = tacticNotes.filter((note) => note.pattern.test(trimmed))
  const headerMatch = trimmed.match(/\b(lemma|theorem)\s+([^\s:]+)/)
  const header =
    headerMatch && headerMatch[2]
      ? `You are proving "${headerMatch[2]}" using ${lines.length} line(s).`
      : `You are proving a statement using ${lines.length} line(s).`

  const usesBy = /\bby\b/.test(trimmed)
  const usesTermMode = /:=\s*by/.test(trimmed)
  const mode = usesBy
    ? `Lean is in ${usesTermMode ? 'term' : 'tactic'} mode with a scripted proof block.`
    : ''
  const structure =
    lines.length > 1
      ? `The proof is structured into ${lines.length} step(s); each line refines the goal or splits cases.`
      : 'The proof is a single step that closes the goal directly.'

  const tacticSummary =
    tacticHits.length > 0
      ? `Key tactics spotted: ${tacticHits.map((note) => note.label).join(', ')}.`
      : 'No common tactics were detected; check the script for custom lemmas or terms.'

  const details =
    tacticHits.length > 0
      ? tacticHits.map((note) => `- ${note.text}`)
      : ['- Add a tactic like `simp` or `rw` to see a more detailed breakdown.']

  return [header, mode, structure, tacticSummary, ...details].filter((line) => line.length > 0)
}

function App() {
  const [input, setInput] = useState(leanSamples[0]?.value ?? '')
  const [output, setOutput] = useState<string[]>([])

  const preview = useMemo(() => buildExplanation(input), [input])

  return (
    <div className="page">
      <header className="hero">
        <div className="hero-text">
          <p className="eyebrow">Lean Proof Interpreter</p>
          <h1>Paste a Lean proof. Get a human walkthrough.</h1>
          <p className="lead">
            Drop in a tactic script, then let an AI explain the proof line by line in the context of your goal.
          </p>
        </div>
        <div className="hero-card">
          <p className="hero-card-title">What it does</p>
          <ul>
            <li>Highlights proof structure and key tactics.</li>
            <li>Connects each step to the evolving goal.</li>
            <li>Summarizes the core idea in plain language.</li>
          </ul>
        </div>
      </header>

      <main className="workspace">
        <section className="panel">
          <div className="panel-header">
            <div>
              <h2>Lean input</h2>
              <p>Paste a theorem, lemma, or tactic block.</p>
            </div>
            <div className="sample-buttons">
              {leanSamples.map((sample) => (
                <button
                  key={sample.label}
                  className="ghost-button"
                  onClick={() => setInput(sample.value)}
                >
                  {sample.label}
                </button>
              ))}
            </div>
          </div>
          <textarea
            className="code-input"
            spellCheck={false}
            value={input}
            onChange={(event) => setInput(event.target.value)}
          />
          <div className="panel-actions">
            <button className="primary-button" onClick={() => setOutput(preview)}>
              Explain proof
            </button>
            <button className="ghost-button" onClick={() => setOutput([])}>
              Clear explanation
            </button>
          </div>
        </section>

        <section className="panel panel-contrast">
          <div className="panel-header">
            <div>
              <h2>Explanation</h2>
              <p>Generated commentary stays aligned with the proof context.</p>
            </div>
            <span className="status-pill">{output.length > 0 ? 'Ready' : 'Awaiting input'}</span>
          </div>
          <div className="explain-output">
            {(output.length > 0 ? output : preview).map((line, index) => (
              <p key={`${line}-${index}`}>{line}</p>
            ))}
          </div>
          <div className="panel-footer">
            <div>
              <p className="footer-title">Next idea</p>
              <p>Wire this to a Lean-aware LLM for contextual goal tracking.</p>
            </div>
            <button className="link-button">Connect API</button>
          </div>
        </section>
      </main>

      <section className="steps">
        <div className="step">
          <span className="step-number">01</span>
          <h3>Paste your proof</h3>
          <p>Bring a Lean lemma, theorem, or tactic block straight from your editor.</p>
        </div>
        <div className="step">
          <span className="step-number">02</span>
          <h3>Generate the story</h3>
          <p>We translate tactics into plain language and keep the goal in view.</p>
        </div>
        <div className="step">
          <span className="step-number">03</span>
          <h3>Teach back</h3>
          <p>Use the explanation to annotate proofs or onboard teammates faster.</p>
        </div>
      </section>
    </div>
  )
}

export default App
