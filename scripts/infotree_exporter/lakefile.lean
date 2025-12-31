import Lake

open Lake DSL

package infotree_exporter

lean_exe infotree_export where
  root := `Main
  supportInterpreter := true
