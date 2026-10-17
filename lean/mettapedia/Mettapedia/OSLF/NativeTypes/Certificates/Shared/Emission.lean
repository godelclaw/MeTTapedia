import Mettapedia.OSLF.NativeTypes.Certificates.Shared.Cache

/-!
# Computable sharing of generated typed rule derivations

The emitter reuses previously checked judgments. New rows retain their
complete rule and ordered premise references. Every emitted graph rechecks
against the original independent rule presentation. Operational receipt
payloads are outside this proof-sharing table.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Certificates.Shared

open Mettapedia.TypeTheory
universe u
variable {P : Presentation.{u}} [DecidableEq P.Judgment]

def memo {judgment : P.Judgment} : (tree : P.Derivation judgment) →
    (cache : Cache P) → Result cache judgment
  | .node ⟨rule, rfl⟩ children, cache =>
      match find? cache (P.conclusion rule) with
      | some located => ⟨cache, ⟨[], List.append_nil _⟩, located⟩
      | none =>
          let forest := sequence (fun position : Fin (P.premises rule).length => (P.premises rule).get position)
            (fun position next => memo (children ⟨position⟩) next) cache
          let emitted := appendRow forest.next rule forest.located
          ⟨emitted.next, forest.prefixTable.trans emitted.prefixTable, emitted.located⟩

def emit {judgment : P.Judgment} (tree : P.Derivation judgment) : Certificate P :=
  let result := memo tree emptyCache
  ⟨result.next.rows, result.located.position⟩

theorem emit_checked {judgment : P.Judgment} (tree : P.Derivation judgment) :
    check (emit tree) judgment = true := by
  let result := memo tree emptyCache
  change (do
    let table ← decodeFrom? [] result.next.rows
    lookup? table result.located.position judgment).isSome = true
  rw [result.next.decoded]
  exact result.located.pointed

theorem emit_check_exact {judgment : P.Judgment} (tree : P.Derivation judgment) (wanted : P.Judgment) :
    check (emit tree) wanted = true ↔ judgment = wanted := by
  let result := memo tree emptyCache
  change (do
    let table ← decodeFrom? [] result.next.rows
    lookup? table result.located.position wanted).isSome = true ↔ _
  rw [result.next.decoded]
  change (lookup? result.next.table result.located.position wanted).isSome = true ↔ _
  rw [lookup?_exact]
  have pointed := (lookup?_exact _ _ _).mp result.located.pointed
  rw [pointed]
  exact Option.some_inj

end Mettapedia.OSLF.NativeTypes.Certificates.Shared
