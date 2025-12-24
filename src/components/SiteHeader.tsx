type SiteHeaderProps = {
  mode: 'light' | 'dark' | 'system'
  onModeChange: (mode: 'light' | 'dark' | 'system') => void
}

const navItems = [
  { href: '/', label: 'Proof walkthroughs' },
  { href: '/tactics.html', label: 'Tactic reference' },
  { href: '/visualizer.html', label: 'Proof visualizer' },
]

export const SiteHeader = ({ mode, onModeChange }: SiteHeaderProps) => (
  <header className="site-header">
    <div className="wordmark">
      <span className="wordmark-title">LEAN LAB</span>
      <span className="wordmark-sub">PROOF WALKTHROUGH SYSTEM</span>
    </div>
    <nav className="site-nav">
      {navItems.map((item) => (
        <a key={item.href} href={item.href}>
          {item.label}
        </a>
      ))}
    </nav>
    <div className="theme-toggle">
      <button
        className={`ghost-button ${mode === 'light' ? 'active' : ''}`}
        onClick={() => onModeChange('light')}
      >
        LIGHT
      </button>
      <button
        className={`ghost-button ${mode === 'system' ? 'active' : ''}`}
        onClick={() => onModeChange('system')}
      >
        SYSTEM
      </button>
      <button
        className={`ghost-button ${mode === 'dark' ? 'active' : ''}`}
        onClick={() => onModeChange('dark')}
      >
        DARK
      </button>
    </div>
  </header>
)
