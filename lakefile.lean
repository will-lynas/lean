import Lake
open Lake DSL

package "lean-practice" where
  -- add package configuration options here

lean_lib «LeanPractice» where
  -- add library configuration options here

@[default_target]
lean_exe "lean-practice" where
  root := `Main
