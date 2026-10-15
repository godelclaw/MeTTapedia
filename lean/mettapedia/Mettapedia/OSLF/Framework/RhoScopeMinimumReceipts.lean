import Mettapedia.OSLF.Framework.RhoScopeBoundedReceipts
import Mettapedia.OSLF.Framework.RhoGeneratedScopeMinimum

/-!+# Constructed scope certificates attaining the actual minimum depth

The independent numeric search supplies a depth at which the complete
certificate search runs. Successful results retain the process premises and
recursive children of the derivation. Their depth is proved to equal the
independent minimum, and rejection agrees with the generated scope's
complement. Other supplied derivations and their origins remain distinct.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoScopeMinimumReceipts

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres
open RhoEquationGeneratedScope RhoGeneratedScopeStrata
open RhoScopePartReceipts RhoScopeBoundedReceipts RhoGeneratedScopeMinimum
open RhoGeneratedScopeDecision

def minimumReceipt? {context : Ctx sig} (left right : Process context → Prop)
    [DecidablePred left] [DecidablePred right] (name : Name context) :
    Option (Certificate left right name) :=
  match minimumDepth? left right name with
  | none => none
  | some depth => (boundedReceipt? left right depth name).map Subtype.val

theorem minimumReceipt?_depth_readout {context : Ctx sig}
    (left right : Process context → Prop) [DecidablePred left] [DecidablePred right]
    (name : Name context) :
    (minimumReceipt? left right name).map Certificate.depth = minimumDepth? left right name := by
  cases minimumReadout : minimumDepth? left right name with
  | none => simp only [minimumReceipt?, minimumReadout, Option.map_none]
  | some depth =>
    obtain ⟨_, attained, earlierExcluded⟩ := minimum_some_spec left right name minimumReadout
    have present := (boundedReceipt?_presence left right depth name).mpr attained
    cases receiptReadout : boundedReceipt? left right depth name with
    | none => rw [receiptReadout] at present; cases present
    | some receipt =>
      have exactDepth : receipt.val.depth = depth := by
        apply Nat.le_antisymm receipt.property
        by_contra notSmall
        exact earlierExcluded receipt.val.depth (Nat.lt_of_not_ge notSmall)
          ⟨receipt.val, Nat.le_refl _⟩
      simp only [minimumReceipt?, minimumReadout, receiptReadout, Option.map_some, exactDepth]

theorem minimumReceipt?_presence {context : Ctx sig} (left right : Process context → Prop)
    [DecidablePred left] [DecidablePred right] (name : Name context) :
    (minimumReceipt? left right name).isSome = true ↔ generated left right name := by
  rw [← Option.isSome_map (f := Certificate.depth), minimumReceipt?_depth_readout,
    minimum_isSome_iff]

theorem minimumReceipt?_none_iff {context : Ctx sig} (left right : Process context → Prop)
    [DecidablePred left] [DecidablePred right] (name : Name context) :
    minimumReceipt? left right name = none ↔ ¬ generated left right name := by
  rw [← minimumReceipt?_presence]
  cases minimumReceipt? left right name <;> simp

theorem minimumReceipt?_some_depth {context : Ctx sig} (left right : Process context → Prop)
    [DecidablePred left] [DecidablePred right] (name : Name context)
    {receipt : Certificate left right name}
    (readout : minimumReceipt? left right name = some receipt) :
    minimumDepth? left right name = some receipt.depth := by
  rw [← minimumReceipt?_depth_readout, readout]
  rfl

theorem minimumReceipt?_least {context : Ctx sig} (left right : Process context → Prop)
    [DecidablePred left] [DecidablePred right] (name : Name context)
    {receipt : Certificate left right name}
    (readout : minimumReceipt? left right name = some receipt)
    (other : Certificate left right name) : receipt.depth ≤ other.depth :=
  returned_minimum_le_every_receipt left right name
    (minimumReceipt?_some_depth left right name readout) other

theorem minimumReceipt?_presence_agrees_with_guard {context : Ctx sig}
    (left right : Process context → Prop) [DecidablePred left] [DecidablePred right]
    (name : Name context) : (minimumReceipt? left right name).isSome = guard left right name := by
  apply Bool.eq_iff_iff.mpr
  rw [minimumReceipt?_presence, guard_true_iff]

theorem no_left_atoms_excludes_scope {context : Ctx sig} {left right : Process context → Prop}
    (noAtoms : ∀ process, ¬ left process) (name : Name context) : ¬ generated left right name := by
  have empty : generated left right ≤ (⊥ : NamePredicate context) := by
    apply generated_induction
    intro result
    rintro ⟨first, _, _, admitted, _⟩
    rcases admitted with atomic | ⟨_, impossible, _⟩
    · exact noAtoms first atomic
    · exact impossible
  exact empty name

theorem no_right_atoms_excludes_scope {context : Ctx sig} {left right : Process context → Prop}
    (noAtoms : ∀ process, ¬ right process) (name : Name context) : ¬ generated left right name := by
  have empty : generated left right ≤ (⊥ : NamePredicate context) := by
    apply generated_induction
    intro result
    rintro ⟨_, second, _, _, admitted⟩
    rcases admitted with atomic | ⟨_, impossible, _⟩
    · exact noAtoms second atomic
    · exact impossible
  exact empty name

end Mettapedia.OSLF.Framework.RhoScopeMinimumReceipts
