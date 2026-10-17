import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Checking

/-! # Exact conclusions of erased native certificates -/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

universe u
variable {S : Symbols.{u}} {D : Signature S}

theorem erased_root : ∀ {judgment : Judgment S} (tree : Derivation D judgment),
    (Certificates.Refinement.erase tree).root.conclusion = judgment
  | _, .node rule _ => rule.property

variable [DecidableEq S.TypeSymbol] [DecidableEq S.TermSymbol] [DecidableEq S.PredicateSymbol]

theorem check_erased_against {judgment : Judgment S} (tree : Derivation D judgment)
    (requested : Judgment S) :
    Certificates.Refinement.check (Certificates.Refinement.erase tree) requested = true ↔
      judgment = requested := by
  constructor
  · intro accepted
    have rootEqual : (Certificates.Refinement.erase tree).root.conclusion = requested := by
      cases certificate : Certificates.Refinement.erase tree with
      | node rule children =>
          rw [certificate] at accepted
          simp only [Certificates.Refinement.check, Certificates.Tree.check,
            Bool.and_eq_true] at accepted
          exact of_decide_eq_true accepted.1
    exact (erased_root tree).symm.trans rootEqual
  · intro same
    subst requested
    exact Certificates.Refinement.check_erase tree

theorem full_check_erased_rejected {judgment : Judgment S} (tree : Derivation D judgment)
    (requested : Judgment S) (different : judgment ≠ requested) :
    NativeLogic.check NativeLogic.full (Certificates.Refinement.erase tree) requested = .certificateRejected := by
  have rejected : Certificates.Refinement.check (Certificates.Refinement.erase tree) requested = false := by
    cases checked : Certificates.Refinement.check (Certificates.Refinement.erase tree) requested with
    | false => rfl
    | true => exact False.elim (different ((check_erased_against tree requested).mp checked))
  unfold NativeLogic.check
  simp only [if_true, rejected, Bool.false_eq_true, if_false]

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal
