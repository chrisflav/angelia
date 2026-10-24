import Lake

open Lake DSL

package angelia where
  version := v!"0.1.0"
  testDriver := "test"

require leansqlite from git "https://github.com/leanprover/leansqlite" @ "v4.35.0"

@[default_target]
lean_lib Angelia

@[default_target]
lean_exe angelia where
  root := `Main

lean_exe test where
  root := `Tests