import Mettapedia.Computability.PNP.WeightedFiberNeutralityObstruction
import Mettapedia.Computability.PNP.ResolutionDemandObstructionAdvantage
import Mettapedia.Computability.PNP.ResolutionDemandObstructionPairBounds
import Mettapedia.Computability.PNP.ResolutionDemandObstructionResolvedMass
import Mettapedia.Computability.PNP.ResolutionDemandObstructionPrediction
import Mettapedia.Computability.PNP.ResolutionDemandObstructionWitnesses
import Mathlib.Logic.Equiv.Basic

/-!
# Weighted feature-fiber margin: core masses

Subtype equivalences, filtered fiber-mass formulas, and the visible-fiber majority classifier.
-/

namespace Mettapedia.Computability.PNP

section

variable {α U : Type*} [Fintype α] [DecidableEq U]

/-- Flatten the nested `true` fiber subtype into a single conjunction subtype. -/
def featureFiberTrueEquivAnd
    (u : α → U) (y : α → Bool) (v : U) :
    FeatureFiberTrue u y v ≃ {x : α // u x = v ∧ y x = true} where
  toFun x := ⟨x.1.1, x.1.2, x.2⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

/-- Flatten the nested `false` fiber subtype into a single conjunction subtype. -/
def featureFiberFalseEquivAnd
    (u : α → U) (y : α → Bool) (v : U) :
    FeatureFiberFalse u y v ≃ {x : α // u x = v ∧ y x = false} where
  toFun x := ⟨x.1.1, x.1.2, x.2⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

/-- The weighted `true` mass on one visible fiber is the corresponding filtered
sum over the ambient finite domain. -/
theorem weightedFeatureFiberTrueMass_eq_sum_filter
    (u : α → U) (y : α → Bool) (w : α → ℕ) (v : U) :
    weightedFeatureFiberTrueMass u y w v =
      ∑ x ∈ (Finset.univ : Finset α) with u x = v ∧ y x = true, w x := by
  classical
  unfold weightedFeatureFiberTrueMass
  calc
    (∑ x : FeatureFiberTrue u y v, w x.1.1)
        = ∑ x : {x : α // u x = v ∧ y x = true}, w x.1 := by
            exact Fintype.sum_equiv
              (featureFiberTrueEquivAnd u y v)
              (fun x : FeatureFiberTrue u y v => w x.1.1)
              (fun x : {x : α // u x = v ∧ y x = true} => w x.1)
              (fun _ => rfl)
    _ = ∑ x ∈ (Finset.univ : Finset α) with u x = v ∧ y x = true, w x := by
      simpa using
    (Finset.sum_subtype_eq_sum_filter
      (s := (Finset.univ : Finset α))
      (p := fun x => u x = v ∧ y x = true)
      (f := w))

/-- The weighted `false` mass on one visible fiber is the corresponding filtered
sum over the ambient finite domain. -/
theorem weightedFeatureFiberFalseMass_eq_sum_filter
    (u : α → U) (y : α → Bool) (w : α → ℕ) (v : U) :
    weightedFeatureFiberFalseMass u y w v =
      ∑ x ∈ (Finset.univ : Finset α) with u x = v ∧ y x = false, w x := by
  classical
  unfold weightedFeatureFiberFalseMass
  calc
    (∑ x : FeatureFiberFalse u y v, w x.1.1)
        = ∑ x : {x : α // u x = v ∧ y x = false}, w x.1 := by
            exact Fintype.sum_equiv
              (featureFiberFalseEquivAnd u y v)
              (fun x : FeatureFiberFalse u y v => w x.1.1)
              (fun x : {x : α // u x = v ∧ y x = false} => w x.1)
              (fun _ => rfl)
    _ = ∑ x ∈ (Finset.univ : Finset α) with u x = v ∧ y x = false, w x := by
      simpa using
    (Finset.sum_subtype_eq_sum_filter
      (s := (Finset.univ : Finset α))
      (p := fun x => u x = v ∧ y x = false)
      (f := w))

section

variable [Fintype U]

/-- Predict `true` on a visible fiber exactly when the retained `true` mass on
that fiber strictly exceeds the retained `false` mass. -/
def weightedFeatureFiberMajorityClassifier
    (u : α → U) (y : α → Bool) (w : α → ℕ) : U → Bool := fun v =>
  if weightedFeatureFiberFalseMass u y w v < weightedFeatureFiberTrueMass u y w v
    then true
    else false

end

end

end Mettapedia.Computability.PNP
