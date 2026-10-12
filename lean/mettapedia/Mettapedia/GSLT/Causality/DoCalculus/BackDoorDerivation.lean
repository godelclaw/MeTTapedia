import Mettapedia.GSLT.Causality.DoCalculus.BackDoorCheck
import Mettapedia.GSLT.Causality.DoCalculus.Derivation

/-!
# Back door inside the derivation tree

On the door graph `Z → X`, `Z → Y`, `X → Y`, the set `{Z}` meets
`BackDoorCriterion`. The interventional query `P(y | do(x))` rewrites, by
the authored rules, to the do-free adjustment `Σ_z P(z) P(y | x, z)`.
Under the positivity that derivation collects, the two ends agree in
`gDenote`, so the query `Factors` through the observational joint.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.ProbabilityTheory.BayesianNetworks
open BayesianNetwork
open Mettapedia.GSLT.Core.NonFactorization
open scoped ENNReal

/-- Two conditional expressions with the same three coordinate sets. -/
lemma door_cond_eq {i n d i' n' d' : Finset Door}
    (hi : i = i') (hn : n = n') (hd : d = d') :
    (MassExpr.cond i n d : MassExpr Door) = .cond i' n' d' := by
  cases hi
  cases hn
  cases hd
  rfl

/-- `P(y | do(x))`. -/
def doorQuery : MassExpr Door :=
  .cond doorX (doorY ∪ doorX) doorX

def doorMarginalSource : MassExpr Door :=
  .cond doorX (doorX ∪ doorY ∪ (∅ : Finset Door)) (doorX ∪ ∅)

theorem doorQuery_eq_marginalSource : doorQuery = doorMarginalSource := by
  unfold doorQuery doorMarginalSource
  refine door_cond_eq rfl ?_ ?_
  · ext vertex; cases vertex <;> simp [doorX, doorY]
  · ext vertex; cases vertex <;> simp [doorX]

/-- Sum over the covariate of `P(y, z | do(x))`. -/
def doorOpened : MassExpr Door :=
  .sum doorZ
    (.cond doorX (doorX ∪ doorY ∪ doorZ ∪ (∅ : Finset Door)) (doorX ∪ ∅))

def openDoorMarginal : Deriv doorGraph doorMarginalSource doorOpened :=
  .marginalIntro doorX doorY doorZ ∅
    (by
      rw [Finset.disjoint_left]
      intro vertex hmember
      simp only [doorZ, doorX, Finset.mem_singleton] at hmember ⊢
      subst hmember
      decide)
    (by
      rw [Finset.disjoint_left]
      intro vertex hmember
      simp only [doorZ, doorY, Finset.mem_singleton] at hmember ⊢
      subst hmember
      decide)
    (Finset.disjoint_empty_right _)

def openDoor : Deriv doorGraph doorQuery doorOpened :=
  .rewriteEq doorQuery_eq_marginalSource.symm rfl openDoorMarginal

/-- Chain splits the summand into `P(y | do(x), z) P(z | do(x))`. -/
def doorChainedBody : MassExpr Door :=
  .mul
    (.cond doorX (doorX ∪ doorY ∪ doorZ ∪ (∅ : Finset Door)) (doorX ∪ doorZ ∪ ∅))
    (.cond doorX (doorX ∪ doorZ ∪ (∅ : Finset Door)) (doorX ∪ ∅))

def chainDoorBody :
    Deriv doorGraph
      (.cond doorX (doorX ∪ doorY ∪ doorZ ∪ (∅ : Finset Door)) (doorX ∪ ∅))
      doorChainedBody :=
  .chain doorX doorY doorZ ∅

def doorChained : MassExpr Door :=
  .sum doorZ doorChainedBody

def chainDoor : Deriv doorGraph doorOpened doorChained :=
  .sumBody chainDoorBody

def doorOutcomeSource : MassExpr Door :=
  .cond ((∅ : Finset Door) ∪ doorX)
    ((∅ : Finset Door) ∪ doorY ∪ doorX ∪ doorZ)
    ((∅ : Finset Door) ∪ doorX ∪ doorZ)

/-- `P(y | x, z)`, do-free. -/
def doorOutcomeObs : MassExpr Door :=
  .cond (∅ : Finset Door)
    ((∅ : Finset Door) ∪ doorY ∪ doorX ∪ doorZ)
    ((∅ : Finset Door) ∪ doorX ∪ doorZ)

theorem doorLeft_eq_rule2 :
    (.cond doorX (doorX ∪ doorY ∪ doorZ ∪ (∅ : Finset Door)) (doorX ∪ doorZ ∪ ∅)) =
      doorOutcomeSource := by
  unfold doorOutcomeSource
  refine door_cond_eq ?_ ?_ ?_
  · ext vertex; cases vertex <;> simp [doorX]
  · ext vertex; cases vertex <;> simp [doorX, doorY, doorZ]
  · ext vertex; cases vertex <;> simp [doorX, doorZ]

def exchangeOutcome : Deriv doorGraph doorOutcomeSource doorOutcomeObs :=
  .rule2 ∅ doorY doorX doorZ door_rule2_outcome_treatment_checked

def leftToOutcomeObs :
    Deriv doorGraph
      (.cond doorX (doorX ∪ doorY ∪ doorZ ∪ (∅ : Finset Door)) (doorX ∪ doorZ ∪ ∅))
      doorOutcomeObs :=
  .rewriteEq doorLeft_eq_rule2.symm rfl exchangeOutcome

def doorCovariateNow : MassExpr Door :=
  .cond doorX (doorX ∪ doorZ ∪ (∅ : Finset Door)) (doorX ∪ ∅)

def doorAbsorbSource : MassExpr Door :=
  .cond doorX (doorZ ∪ doorX) ((∅ : Finset Door) ∪ doorX)

def doorAbsorbTarget : MassExpr Door :=
  .cond doorX doorZ ∅

theorem doorRight_eq_absorb : doorCovariateNow = doorAbsorbSource := by
  unfold doorCovariateNow doorAbsorbSource
  refine door_cond_eq rfl ?_ ?_
  · ext vertex; cases vertex <;> simp [doorX, doorZ]
  · ext vertex; cases vertex <;> simp [doorX]

def absorbTreatment : Deriv doorGraph doorAbsorbSource doorAbsorbTarget :=
  .absorb doorX doorZ ∅ doorX (fun _ hmember => hmember)

def doorRule3Source : MassExpr Door :=
  .cond ((∅ : Finset Door) ∪ doorX)
    ((∅ : Finset Door) ∪ doorZ ∪ ∅)
    ((∅ : Finset Door) ∪ ∅)

/-- `P(z)`, do-free. -/
def doorCovariateObs : MassExpr Door :=
  .cond (∅ : Finset Door)
    ((∅ : Finset Door) ∪ doorZ ∪ ∅)
    ((∅ : Finset Door) ∪ ∅)

theorem doorAbsorb_eq_rule3 : doorAbsorbTarget = doorRule3Source := by
  unfold doorAbsorbTarget doorRule3Source
  refine door_cond_eq ?_ ?_ ?_
  · ext vertex; cases vertex <;> simp [doorX]
  · ext vertex; cases vertex <;> simp [doorZ]
  · ext vertex; cases vertex <;> simp

def deleteTreatment : Deriv doorGraph doorRule3Source doorCovariateObs :=
  .rule3 ∅ doorZ doorX ∅ door_rule3_covariate_checked

def rightToCovariateObs : Deriv doorGraph doorCovariateNow doorCovariateObs :=
  .trans
    (.rewriteEq doorRight_eq_absorb.symm rfl absorbTreatment)
    (.rewriteEq doorAbsorb_eq_rule3.symm rfl deleteTreatment)

def doorAdjustedBody : MassExpr Door :=
  .mul doorOutcomeObs doorCovariateObs

def adjustBody : Deriv doorGraph doorChainedBody doorAdjustedBody :=
  .trans (.mulLeft leftToOutcomeObs) (.mulRight rightToCovariateObs)

/-- `Σ_z P(z) P(y | x, z)`. -/
def doorExpr : MassExpr Door :=
  .sum doorZ doorAdjustedBody

def adjustDoor : Deriv doorGraph doorChained doorExpr :=
  .sumBody adjustBody

/-- Derivation from `P(y | do(x))` to the back-door adjustment. -/
def doorDeriv : Deriv doorGraph doorQuery doorExpr :=
  .trans openDoor (.trans chainDoor adjustDoor)

theorem doorExpr_doFree : doFree doorExpr = true := by
  decide

section Denote

variable {β : Type}
variable [Fintype β] [DecidableEq β] [Inhabited β] [MeasurableSpace β]
variable [MeasurableSingletonClass β] [StandardBorelSpace β]
variable [StandardBorelSpace (Door → β)]

/-- The derivation's ends agree in `gDenote`, and the end is do-free. -/
theorem door_backDoor_end
    (cpt : (network (β := β) doorGraph doorAcyclic).DiscreteCPT)
    (anchor : Door → β)
    (hpos : Positive doorGraph doorAcyclic doorDeriv cpt anchor) :
    doFree doorExpr = true ∧
      gDenote doorGraph doorAcyclic cpt anchor doorQuery =
        gDenote doorGraph doorAcyclic cpt anchor doorExpr :=
  ⟨doorExpr_doFree, deriv_gDenote doorGraph doorAcyclic doorDeriv cpt anchor hpos⟩

/-- Tables for which the door derivation's positivity holds at `anchor`. -/
def DoorRows (anchor : Door → β) :=
  {cpt : (network (β := β) doorGraph doorAcyclic).DiscreteCPT //
    Positive doorGraph doorAcyclic doorDeriv cpt anchor}

/-- `P(y | do(x))` `Factors` through the observational joint on those tables. -/
theorem door_query_factors_joint (anchor : Door → β) :
    Factors
      (fun cpt : DoorRows anchor => cpt.1.jointWeight)
      (fun cpt => gDenote doorGraph doorAcyclic cpt.1 anchor doorQuery) := by
  refine ⟨fun joint => denoteJoint anchor joint doorExpr, fun cpt => ?_⟩
  have hends := (door_backDoor_end cpt.1 anchor cpt.2).2
  change denoteJoint anchor cpt.1.jointWeight doorExpr =
    gDenote doorGraph doorAcyclic cpt.1 anchor doorQuery
  rw [hends]
  exact (denote_eq_joint doorGraph doorAcyclic doorExpr doorExpr_doFree cpt.1 anchor).symm

end Denote

end Mettapedia.GSLT.Causality.DoCalculus
