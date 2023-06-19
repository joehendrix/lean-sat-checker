import Lake
open Lake DSL

package «sat-checker» {
  -- add configuration options here
}

lean_lib «SatChecker» {
  -- add library configuration options here
}

require std from git "https://github.com/leanprover/std4.git"

@[default_target]
lean_exe «sat-checker» {
  root := `Main
}