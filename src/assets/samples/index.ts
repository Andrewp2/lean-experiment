import addZero from './add_zero.lean?raw'
import mulComm from './mul_comm.lean?raw'
import boolOr from './bool_or.lean?raw'

export const leanSamples = [
  {
    label: 'simp + intro',
    value: addZero,
  },
  {
    label: 'rw + exact',
    value: mulComm,
  },
  {
    label: 'by cases',
    value: boolOr,
  },
]
