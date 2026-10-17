import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Joined
import Mettapedia.OSLF.NativeTypes.Certificates.Shared.Emission

/-!
# Shared formation evidence checked against the existing native rules

Full-vocabulary checking validates the finite reference table directly.
Other vocabulary policies retain the original certificate policy on the
reconstructed tree. Acceptance in either route produces an ordinary native
certificate accepted by the existing checker.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.SharedChecking

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.NativeTypes.Certificates

variable {S : Symbols} (signature : Signature S)
variable [DecidableEq S.TypeSymbol] [DecidableEq S.TermSymbol] [DecidableEq S.PredicateSymbol]

abbrev Certificate := Shared.Certificate (Certificates.Refinement.presentation signature)

def emit {judgment : Judgment S} (tree : Derivation signature judgment) : Certificate signature :=
  Shared.emit tree

def reconstruct (certificate : Certificate signature) (judgment : Judgment S) :
    Option (Derivation signature judgment) :=
  Shared.reconstruct? certificate judgment

def check (fragment : NativeLogic.Fragment) (certificate : Certificate signature) (judgment : Judgment S) :
    NativeLogic.CheckResult :=
  if fragment = NativeLogic.full then
    if Shared.check certificate judgment then .accepted else .certificateRejected
  else
    if !fragment.accepts judgment then .vocabularyRefused
    else match Shared.reconstruct? certificate judgment with
    | none => .certificateRejected
    | some tree => NativeLogic.check fragment (Certificates.Refinement.erase tree) judgment

theorem check_exact (fragment : NativeLogic.Fragment) (certificate : Certificate signature) (judgment : Judgment S) :
    check signature fragment certificate judgment = .accepted ↔
      ∃ derivation : Derivation signature judgment,
        reconstruct signature certificate judgment = some derivation ∧
        NativeLogic.check fragment (Certificates.Refinement.erase derivation) judgment = .accepted := by
  unfold reconstruct
  unfold check
  split
  · rename_i full
    subst fragment
    constructor
    · intro accepted
      split at accepted
      · rename_i shared
        obtain ⟨tree, found, _checked⟩ := Shared.accepted_original certificate judgment shared
        exact ⟨tree, found, by
          unfold NativeLogic.check
          rw [if_pos rfl, if_pos (Certificates.Refinement.check_erase tree)]⟩
      · cases accepted
    · rintro ⟨tree, found, _⟩
      have checked : Shared.check certificate judgment = true := by
        simp only [Shared.check, found]
        rfl
      rw [if_pos checked]
  · constructor
    · intro accepted
      split at accepted
      · cases accepted
      · split at accepted
        · cases accepted
        · rename_i tree found
          exact ⟨tree, found, accepted⟩
    · rintro ⟨tree, found, accepted⟩
      have vocabulary : fragment.accepts judgment = true := by
        have permitted := (NativeLogic.check_exact fragment _ _).mp accepted
        exact (NativeLogic.accepts_exact _ _).mpr permitted.1
      simp only [vocabulary, Bool.not_true, Bool.false_eq_true, ↓reduceIte, found]
      exact accepted

theorem emit_checked {judgment : Judgment S} (tree : Derivation signature judgment) :
    check signature NativeLogic.full (Shared.emit tree) judgment = .accepted := by
  unfold check
  rw [if_pos rfl, if_pos (Shared.emit_checked (P := Certificates.Refinement.presentation signature) tree)]

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.SharedChecking
