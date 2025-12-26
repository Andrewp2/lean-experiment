import { StrictMode } from 'react'
import { createRoot } from 'react-dom/client'
import './index.css'
import { MathlibPage } from './pages/MathlibPage'

createRoot(document.getElementById('root')!).render(
  <StrictMode>
    <MathlibPage />
  </StrictMode>,
)
