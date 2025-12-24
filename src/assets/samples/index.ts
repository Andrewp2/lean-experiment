import addZero from './general/add_zero.lean?raw'
import mulComm from './general/mul_comm.lean?raw'
import boolOr from './general/bool_or.lean?raw'
import harmonicImo2025P1 from './harmonic/IMO_2025_P1.lean?raw'
import harmonicImo2025P3 from './harmonic/IMO_2025_P3.lean?raw'
import harmonicImo2025P4 from './harmonic/IMO_2025_P4.lean?raw'
import harmonicImo2025P5 from './harmonic/IMO_2025_P5.lean?raw'

export const leanSamples = [
  {
    label: 'General · simp + intro',
    value: addZero,
  },
  {
    label: 'General · rw + exact',
    value: mulComm,
  },
  {
    label: 'General · by cases',
    value: boolOr,
  },
  {
    label: 'Harmonic · IMO 2025 P1',
    value: harmonicImo2025P1,
    imports: ['HarmonicLean.Imports'],
  },
  {
    label: 'Harmonic · IMO 2025 P3',
    value: harmonicImo2025P3,
    imports: ['HarmonicLean.Imports'],
  },
  {
    label: 'Harmonic · IMO 2025 P4',
    value: harmonicImo2025P4,
    imports: ['HarmonicLean.Imports'],
  },
  {
    label: 'Harmonic · IMO 2025 P5',
    value: harmonicImo2025P5,
    imports: ['HarmonicLean.Imports'],
  },
]
