import Mettapedia.Languages.MeTTa.PeTTa.BridgeKit

/-!
# Which heads of a library are proved

`@[metta_head "head"]` marks a theorem as the bridge theorem of a MeTTa head: it states what the
head returns in terms of its Lean model. `#metta_coverage library` lists every head of the
library's source with its marked theorems, and the heads that have none. It is the measure of a
library's verification, as `#print axioms` is of its theorems.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.BridgeKit

open Lean Elab Command

/-- Marked bridge theorems: each head with the theorems stating what it returns. -/
initialize mettaHeadExtension : SimplePersistentEnvExtension (String × Name) (Array (String × Name)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun imported => imported.foldl (· ++ ·) #[] }

syntax (name := mettaHead) "metta_head " str : attr

initialize registerBuiltinAttribute {
  name := `mettaHead
  descr := "the bridge theorem of a MeTTa head"
  add := fun declaration syntaxNode _ => do
    let some head := syntaxNode[1].isStrLit? | throwError "metta_head: expected the head as a string"
    modifyEnv fun environment => mettaHeadExtension.addEntry environment (head, declaration) }

/-- The heads a library's source defines, in order. -/
def sourceHeads (library : Library) : List String := library.source.equations.map (·.head)

/-- The theorems marked for each head. -/
def markedHeads (environment : Environment) : Array (String × Name) :=
  mettaHeadExtension.getState environment

/-- List the heads of a library's source with their bridge theorems, and the heads without one. -/
elab "#metta_coverage " library:term : command => liftTermElabM do
  let expression ← Term.elabTermEnsuringType library (mkConst ``Library)
  let expression ← instantiateMVars expression
  let heads ← unsafe Meta.evalExpr (List String) (mkApp (mkConst ``List [.zero]) (mkConst ``String))
    (mkApp (mkConst ``sourceHeads) expression)
  let marked := markedHeads (← getEnv)
  let mut proved : Array String := #[]
  let mut missing : Array String := #[]
  for head in heads do
    let theorems := marked.filterMap fun (other, name) => if other == head then some name else none
    if theorems.isEmpty then missing := missing.push head
    else proved := proved.push s!"{head}: {theorems.toList}"
  logInfo m!"{proved.size} of {heads.length} heads proved\n{String.intercalate "\n" proved.toList}\n\
    missing ({missing.size}): {missing.toList}"

end Mettapedia.Languages.MeTTa.PeTTa.BridgeKit
