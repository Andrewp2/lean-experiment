import { SiteHeader } from '../components/SiteHeader'
import { useThemeMode } from '../hooks/useThemeMode'
import '../App.css'

export const VisualizerPage = () => {
  const { mode, setMode, theme } = useThemeMode()

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
        <div className="visualizer-grid">
          <div className="panel">
            <div className="panel-header">
              <div>
                <h2>Track · Tactic stream</h2>
                <p>Stepwise tactic sequence extracted from the proof.</p>
              </div>
            </div>
            <ol className="tactic-list">
              <li>intro n</li>
              <li>induction n</li>
              <li>case zero</li>
              <li>case succ n ih</li>
              <li>simp [Nat.add_succ, ih]</li>
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
              <div className="goal-card">
                <p className="meta-label">GOAL 0</p>
                <pre>⊢ n + 0 = n</pre>
              </div>
              <div className="goal-arrow">↓</div>
              <div className="goal-card">
                <p className="meta-label">GOAL 1</p>
                <pre>⊢ 0 + 0 = 0</pre>
              </div>
              <div className="goal-arrow">↓</div>
              <div className="goal-card">
                <p className="meta-label">GOAL 2</p>
                <pre>⊢ Nat.succ n + 0 = Nat.succ n</pre>
              </div>
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
