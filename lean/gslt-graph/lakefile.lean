import Lake
open Lake DSL

package «gslt-graph» where
  version := v!"0.1.0"

require "leanprover-community" / mathlib @ git "85e3a25e006c35636f0e53b0e9296caca2685bc0"

lean_lib Foundation where
  globs := #[.submodules `Foundation]

lean_lib Mettapedia where
  globs := #[.submodules `Mettapedia]

@[default_target] lean_lib GSLTGraphAudit
