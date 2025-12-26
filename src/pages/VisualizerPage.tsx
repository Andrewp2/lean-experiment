import { useState } from 'react'
import { SiteHeader } from '../components/SiteHeader'
import { useThemeMode } from '../hooks/useThemeMode'
import '../App.css'

export const VisualizerPage = () => {
  const { mode, setMode, theme } = useThemeMode()
  const [proofInput, setProofInput] = useState(`import Mathlib

theorem add_zero (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [Nat.add_succ, ih]`)
  const [goalText, setGoalText] = useState<string>('No goals fetched yet.')
  const [goalSnapshots, setGoalSnapshots] = useState<
    Array<{ line: number; text: string; source: string }>
  >([])
  const [status, setStatus] = useState<'idle' | 'pending' | 'ready' | 'error'>('idle')
  const [errorMessage, setErrorMessage] = useState<string | null>(null)

  const parseJsonSafe = async (response: Response) => {
    const raw = await response.text()
    if (!raw) {
      return { data: null, raw }
    }
    try {
      return { data: JSON.parse(raw), raw }
    } catch {
      return { data: null, raw }
    }
  }

  const fetchGoals = async () => {
    setStatus('pending')
    setErrorMessage(null)
    setGoalSnapshots([])

    try {
      const sessionResponse = await fetch('/api/lean/session', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({}),
      })
      const sessionParsed = await parseJsonSafe(sessionResponse)
      const sessionData = sessionParsed.data as { sessionId?: string; error?: string } | null
      if (!sessionResponse.ok || !sessionData?.sessionId) {
        throw new Error(
          sessionData?.error ??
          (sessionParsed.raw ||
            `Failed to create session (status ${sessionResponse.status}).`),
        )
      }

      const sessionId = sessionData.sessionId
      const uri = 'file:///opt/lean-workspace/Visualizer.lean'

      const openResponse = await fetch('/api/lean/session/open', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ sessionId, uri, text: proofInput }),
      })
      if (!openResponse.ok) {
        const errorText = await openResponse.text()
        throw new Error(errorText || 'Failed to open document.')
      }

      const lines = proofInput.split('\n')

      const maxSnapshots = 12
      const snapshots: Array<{ line: number; text: string; source: string }> = []

      for (let index = 0; index < lines.length; index += 1) {
        const source = lines[index]?.trim() ?? ''
        if (!source) {
          continue
        }
        if (snapshots.length >= maxSnapshots) {
          break
        }

        const goalsResponse = await fetch('/api/lean/session/goals', {
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({
            sessionId,
            uri,
            position: { line: index, character: lines[index]?.length ?? 0 },
          }),
        })

        const goalsParsed = await parseJsonSafe(goalsResponse)
        const goalsData = goalsParsed.data as { result?: unknown; error?: string } | null
        if (!goalsResponse.ok) {
          throw new Error(
            goalsData?.error ??
              (goalsParsed.raw ||
                `Failed to fetch goals (status ${goalsResponse.status}).`),
          )
        }

        const result = goalsData?.result
        const text =
          typeof result === 'string' ? result : JSON.stringify(result ?? 'No goal state', null, 2)

        snapshots.push({ line: index + 1, text, source })
      }

      const latest = snapshots.at(-1)
      if (latest) {
        setGoalText(latest.text)
      } else {
        setGoalText('No goals fetched yet.')
      }
      setGoalSnapshots(snapshots)
      setStatus('ready')
    } catch (error) {
      setStatus('error')
      setErrorMessage(error instanceof Error ? error.message : 'Request failed.')
    }
  }

  return (
    <div className={`page theme-${theme}`}>
      <SiteHeader mode={mode} onModeChange={setMode} />

      <section className="intro">
        <h1>TR-003 · Proof Visualizer</h1>
        <p>Static scaffold for goal-state graphs, tactic timelines, and dependency views.</p>
      </section>

      <section className="samples">
        <div className="panel-header">
          <div>
            <h2>Section A · Visual output</h2>
            <p>Mock layout showing where tactics and goals will surface.</p>
          </div>
        </div>
        <div className="panel">
          <div className="panel-header">
            <div>
              <h2>Input · Lean source</h2>
              <p>Paste a Lean proof and request goal snapshots.</p>
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
          <textarea
            className="code-input"
            spellCheck={false}
            value={proofInput}
            onChange={(event) => setProofInput(event.target.value)}
          />
          <div className="panel-actions">
            <button
              type="button"
              className="primary-button"
              onClick={fetchGoals}
              disabled={status === 'pending'}
            >
              Fetch goal snapshot
            </button>
          </div>
          {status === 'error' && errorMessage ? (
            <p className="placeholder">Error: {errorMessage}</p>
          ) : null}
        </div>
        <div className="visualizer-grid">
          <div className="panel">
            <div className="panel-header">
              <div>
                <h2>Track · Tactic stream</h2>
                <p>Stepwise tactic sequence extracted from the proof.</p>
              </div>
            </div>
            <ol className="tactic-list">
              {(goalSnapshots.length > 0 ? goalSnapshots : [{ line: 1, source: 'Waiting...' }]).map(
                (snapshot, idx) => (
                  <li key={`${snapshot.line}-${idx}`}>
                    L{snapshot.line}: {snapshot.source ?? 'Waiting...'}
                  </li>
                ),
              )}
            </ol>
          </div>
          <div className="panel">
            <div className="panel-header">
              <div>
                <h2>Track · Goal states</h2>
                <p>Before/after snapshots of the active goal.</p>
              </div>
            </div>
            <div className="goal-flow">
              {goalSnapshots.length > 0 ? (
                goalSnapshots.map((snapshot, idx) => (
                  <div key={`${snapshot.line}-${idx}`}>
                    <div className="goal-card">
                      <p className="meta-label">GOAL {idx}</p>
                      <pre>{snapshot.text}</pre>
                    </div>
                    {idx < goalSnapshots.length - 1 ? <div className="goal-arrow">↓</div> : null}
                  </div>
                ))
              ) : (
                <div className="goal-card">
                  <p className="meta-label">GOAL</p>
                  <pre>{goalText}</pre>
                </div>
              )}
            </div>
          </div>
        </div>
        <div className="panel">
          <div className="panel-header">
            <div>
              <h2>Section B · Dependency map</h2>
              <p>Placeholder for lemma graph and rewrite edges.</p>
            </div>
          </div>
          <div className="dependency-grid">
            <div className="dependency-node">Nat.add_succ</div>
            <div className="dependency-node">ih</div>
            <div className="dependency-node">simp</div>
            <div className="dependency-node">rfl</div>
          </div>
        </div>
      </section>
    </div>
  )
}
