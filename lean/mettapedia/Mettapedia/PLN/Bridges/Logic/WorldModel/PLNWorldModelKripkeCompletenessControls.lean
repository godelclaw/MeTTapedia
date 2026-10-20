import Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelKripkeCompleteness

/-!
# Controls for the Kripke world-model strength transport

The transport theorems of `PLNWorldModelKripkeCompleteness` assume a state of pointed Kripke
models whose frames lie in a frame class, and a proof of an implication in the matching
modal logic. Both hold together at the one-world reflexive model: its frame is serial,
reflexive and transitive, so it lies in the classes of `K`, `KD`, `KT` and `K4`.

Positive: the strength of `p₀` is at most the strength of `p₀` in this state, for each of
the four logics (`point_strength_le_K`, `point_strength_le_KD`, `point_strength_le_KT`,
`point_strength_le_K4`).

Negative: the transport does not run backwards along an unprovable implication: in this
state `⊥` has strength `0` and `p₀` has strength `1` (`point_strength_bot_lt_atom`), so
`p₀ ➝ ⊥` is not a theorem of `K` (`atom_imp_bot_not_provable_K`).
-/

set_option autoImplicit false

namespace Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelKripkeCompletenessControls

open LO LO.Modal LO.Entailment
open Mettapedia.PLN.WorldModel
open Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelKripke
open Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelKripkeCompleteness

/-- The one-world reflexive Kripke model in which every atom is true. -/
def pointModel : Kripke.Model where
  toFrame := Kripke.whitepoint
  Val := fun _ _ => True

/-- The state containing the single pointed model. -/
def pointState : Multiset PointedKripke := {⟨pointModel, ()⟩}

theorem pointState_frame {C : Kripke.FrameClass} (h : Kripke.whitepoint ∈ C) :
    ∀ pk ∈ pointState, pk.model.toFrame ∈ C := by
  intro pk hpk
  rw [pointState, Multiset.mem_singleton] at hpk
  subst hpk
  exact h

/-- **Positive control** for `multiset_strength_le_of_provable_imp_K`. -/
theorem point_strength_le_K :
    type_of% (multiset_strength_le_of_provable_imp_K (W := pointState)
      (pointState_frame (Set.mem_univ _)) (C!_id : Modal.K ⊢ (.atom 0 ➝ .atom 0))) :=
  multiset_strength_le_of_provable_imp_K (W := pointState)
    (pointState_frame (Set.mem_univ _)) (C!_id : Modal.K ⊢ (.atom 0 ➝ .atom 0))

/-- **Positive control** for `multiset_strength_le_of_provable_imp_KD`. -/
theorem point_strength_le_KD :
    type_of% (multiset_strength_le_of_provable_imp_KD (W := pointState)
      (pointState_frame (Set.mem_ofPred_eq.mpr (by infer_instance)))
      (C!_id : Modal.KD ⊢ (.atom 0 ➝ .atom 0))) :=
  multiset_strength_le_of_provable_imp_KD (W := pointState)
    (pointState_frame (Set.mem_ofPred_eq.mpr (by infer_instance)))
    (C!_id : Modal.KD ⊢ (.atom 0 ➝ .atom 0))

/-- **Positive control** for `multiset_strength_le_of_provable_imp_KT`. -/
theorem point_strength_le_KT :
    type_of% (multiset_strength_le_of_provable_imp_KT (W := pointState)
      (pointState_frame (Set.mem_ofPred_eq.mpr (by infer_instance)))
      (C!_id : Modal.KT ⊢ (.atom 0 ➝ .atom 0))) :=
  multiset_strength_le_of_provable_imp_KT (W := pointState)
    (pointState_frame (Set.mem_ofPred_eq.mpr (by infer_instance)))
    (C!_id : Modal.KT ⊢ (.atom 0 ➝ .atom 0))

/-- **Positive control** for `multiset_strength_le_of_provable_imp_K4`. -/
theorem point_strength_le_K4 :
    type_of% (multiset_strength_le_of_provable_imp_K4 (W := pointState)
      (pointState_frame (Set.mem_ofPred_eq.mpr (by infer_instance)))
      (C!_id : Modal.K4 ⊢ (.atom 0 ➝ .atom 0))) :=
  multiset_strength_le_of_provable_imp_K4 (W := pointState)
    (pointState_frame (Set.mem_ofPred_eq.mpr (by infer_instance)))
    (C!_id : Modal.K4 ⊢ (.atom 0 ➝ .atom 0))

theorem pointState_strength_atom :
    BinaryWorldModel.queryStrength (State := Multiset PointedKripke)
      (Query := LO.Modal.Formula ℕ) pointState (.atom 0) = 1 :=
  PLNWorldModelCrispSpecialization.queryStrength_singleton_of_satisfies
    PointedKripke.satisfies _ _ trivial

theorem pointState_strength_bot :
    BinaryWorldModel.queryStrength (State := Multiset PointedKripke)
      (Query := LO.Modal.Formula ℕ) pointState ⊥ = 0 :=
  PLNWorldModelCrispSpecialization.queryStrength_singleton_of_not_satisfies
    PointedKripke.satisfies _ _ (fun h => h)

/-- **Negative control.** In this state `⊥` has strength `0` and `p₀` strength `1`, so the
transport cannot run from `p₀` to `⊥`. -/
theorem point_strength_bot_lt_atom :
    BinaryWorldModel.queryStrength (State := Multiset PointedKripke)
        (Query := LO.Modal.Formula ℕ) pointState ⊥ <
      BinaryWorldModel.queryStrength (State := Multiset PointedKripke)
        (Query := LO.Modal.Formula ℕ) pointState (.atom 0) := by
  rw [pointState_strength_bot, pointState_strength_atom]
  exact zero_lt_one

/-- **Negative control.** Hence `p₀ ➝ ⊥` is not a theorem of `K`. -/
theorem atom_imp_bot_not_provable_K : ¬ Modal.K ⊢ (.atom 0 ➝ ⊥) := fun h =>
  absurd (multiset_strength_le_of_provable_imp_K (W := pointState)
    (pointState_frame (Set.mem_univ _)) h) (not_le.mpr point_strength_bot_lt_atom)

#print axioms point_strength_le_K
#print axioms point_strength_le_KD
#print axioms point_strength_le_KT
#print axioms point_strength_le_K4
#print axioms point_strength_bot_lt_atom
#print axioms atom_imp_bot_not_provable_K

end Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelKripkeCompletenessControls
