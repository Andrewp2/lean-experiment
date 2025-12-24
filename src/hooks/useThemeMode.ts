import { useEffect, useState } from 'react'

type ThemeMode = 'light' | 'dark' | 'system'
type ThemeName = 'highk' | 'reticle'

const getStoredMode = (): ThemeMode | null => {
  if (typeof window === 'undefined') {
    return null
  }
  const stored = window.localStorage.getItem('theme')
  if (stored === 'light' || stored === 'dark' || stored === 'system') {
    return stored
  }
  return null
}

const getPreferredTheme = (): ThemeName => {
  if (typeof window === 'undefined') {
    return 'highk'
  }
  return window.matchMedia('(prefers-color-scheme: dark)').matches ? 'reticle' : 'highk'
}

export const useThemeMode = () => {
  const [mode, setMode] = useState<ThemeMode>(() => getStoredMode() ?? 'system')
  const [theme, setTheme] = useState<ThemeName>(() => getPreferredTheme())

  useEffect(() => {
    if (typeof document === 'undefined') {
      return
    }
    document.documentElement.classList.toggle('theme-reticle', theme === 'reticle')
    document.documentElement.classList.toggle('theme-highk', theme === 'highk')
  }, [theme])

  useEffect(() => {
    if (typeof window === 'undefined') {
      return
    }
    const media = window.matchMedia('(prefers-color-scheme: dark)')
    const handleChange = (event: MediaQueryListEvent) => {
      if (mode === 'system') {
        setTheme(event.matches ? 'reticle' : 'highk')
      }
    }
    media.addEventListener('change', handleChange)
    return () => {
      media.removeEventListener('change', handleChange)
    }
  }, [mode])

  useEffect(() => {
    if (typeof window === 'undefined') {
      return
    }
    if (mode === 'system') {
      setTheme(getPreferredTheme())
    } else {
      setTheme(mode === 'dark' ? 'reticle' : 'highk')
    }
    window.localStorage.setItem('theme', mode)
  }, [mode])

  return { mode, setMode, theme }
}
