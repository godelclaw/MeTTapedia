import Lean

/-! Compatibility names share the canonical declarations and data carriers. -/

open Lean Elab Command

elab "export_namespace " source:ident : command => do
  let env ← getEnv
  let target ← getCurrNamespace
  let origin := source.getId
  let mut names : Array (TSyntax `ident) := #[]
  for (name, _) in env.constants.toList do
    if origin.isPrefixOf name && !name.isInternal then
      let relative := name.replacePrefix origin Name.anonymous
      if !relative.isAnonymous && !env.contains (target ++ relative) then
        names := names.push (mkIdent relative)
  unless names.isEmpty do
    elabCommand (← `(export $source ($[$names]*)))
