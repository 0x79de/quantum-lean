import Lake
open Lake DSL

package "quantum-lean" where
  -- add package configuration options here

lean_lib «QuantumLean» where
  -- add library configuration options here

@[default_target]
lean_exe "quantum-lean" where
  root := `Main
