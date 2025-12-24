import harmonicAttrs from './harmonic/Attrs.lean?raw'
import harmonicImports from './harmonic/Imports.lean?raw'

export const importRegistry: Record<string, string> = {
  'HarmonicLean.Attrs': harmonicAttrs,
  'HarmonicLean.Imports': harmonicImports,
}
