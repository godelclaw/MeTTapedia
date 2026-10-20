import Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization
import Mettapedia.PLN.RuleFamilies.HigherOrder.Reduction.PredCode.Basic

/-!
# Predicate codes as a crisp world model

States are multisets of pointed individuals, queries are finite Boolean
predicate codes, and the evidence for a code counts the individuals it holds of
and those it does not.  This is the world model of the crisp semantics
`PointedPredCode.satisfies` (`PLNWorldModelCrispSpecialization.crispWorldModel`).

This is a useful fragment, but it is not the general Church/Henkin HOL layer.
-/

namespace Mettapedia.PLN.Bridges.HOL.PLNWorldModelPredCode

open Mettapedia.PLN.WorldModel
open Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization

/-- Predicate-code query type. -/
abbrev PredCodeQuery (U : Type*) := Mettapedia.PLN.RuleFamilies.HigherOrder.Reduction.PredCode U

/-- A pointed predicate-code state with one individual witness. -/
structure PointedPredCode (U : Type*) where
  point : U

/-- Predicate-code satisfaction at a pointed individual. -/
def PointedPredCode.satisfies {U : Type*} (pw : PointedPredCode U) (q : PredCodeQuery U) : Prop :=
  Mettapedia.PLN.RuleFamilies.HigherOrder.Reduction.evalPred q pw.point

/-- Predicate-code world-model states are multisets of pointed witnesses. -/
abbrev PredCodeState (U : Type*) := Multiset (PointedPredCode U)

/-- The predicate-code world model: count the witnesses a code holds of. -/
noncomputable instance {U : Type*} : BinaryWorldModel (PredCodeState U) (PredCodeQuery U) :=
  crispWorldModel PointedPredCode.satisfies

/-- Negative example: on `Bool`, the trivial code does not entail its negation
at singleton-consequence level; the witness is the point `true`. -/
theorem bool_not_trivial_counterexample :
    ¬ singletonStrengthLE (PointedPredCode.satisfies (U := Bool)) .trivial (.comp_not .trivial) :=
  singletonStrengthLE_not_of_counterexample _ _ _ ⟨true⟩
    (by simp [PointedPredCode.satisfies, Mettapedia.PLN.RuleFamilies.HigherOrder.Reduction.evalPred])
    (by simp [PointedPredCode.satisfies, Mettapedia.PLN.RuleFamilies.HigherOrder.Reduction.evalPred])

end Mettapedia.PLN.Bridges.HOL.PLNWorldModelPredCode
