import { StrictMode } from 'react'
import { createRoot } from 'react-dom/client'
import './index.css'
import { TacticsPage } from './pages/TacticsPage'

createRoot(document.getElementById('root')!).render(
  <StrictMode>
    <TacticsPage />
  </StrictMode>,
)
