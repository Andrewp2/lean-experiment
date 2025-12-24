import { SiteHeader } from '../components/SiteHeader'
import { tactics } from '../assets/tactics'
import { useThemeMode } from '../hooks/useThemeMode'
import '../App.css'

export const TacticsPage = () => {
  const { mode, setMode, theme } = useThemeMode()

  return (
    <div className={`page theme-${theme}`}>
      <SiteHeader mode={mode} onModeChange={setMode} />

      <section className="intro">
        <h1>TR-002 · Tactic Reference</h1>
        <p>Common Lean tactics with short explanations and minimal examples.</p>
      </section>

      <section className="samples">
        <div className="panel-header">
          <div>
            <h2>Section A · Tactics</h2>
            <p>Scan by name, then copy a minimal example.</p>
          </div>
        </div>
        <div className="table table-tactics">
          <div className="table-row table-head">
            <span>TACTIC</span>
            <span>SUMMARY</span>
            <span>EXAMPLE</span>
          </div>
          {tactics.map((tactic) => (
            <div className="table-row" key={tactic.name}>
              <span>{tactic.name}</span>
              <span>{tactic.description}</span>
              <pre>{tactic.example}</pre>
            </div>
          ))}
        </div>
      </section>
    </div>
  )
}
