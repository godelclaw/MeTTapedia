import Mettapedia.PLN.Bridges.HOL.PLNWorldModelPredCode

/-!
# Countably infinitary predicate codes as a crisp world model

The countably infinitary closure (`PLNWorldModelCrispSpecialization.InfQuery`)
of the predicate-code semantics: base codes, countable conjunctions and
countable disjunctions, satisfied by `SatisfiesInf PointedPredCode.satisfies`.
Conjunction elimination and disjunction introduction on every state are the
generic `queryStrength_le_iAnd_component` and `queryStrength_le_iOr_of_component`.

It is intentionally separate from the Church-style HOL layer.
-/

namespace Mettapedia.PLN.Bridges.HOL.PLNWorldModelPredCodeInfinitary

open Mettapedia.PLN.WorldModel
open Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization
open Mettapedia.PLN.Bridges.HOL.PLNWorldModelPredCode

/-- Countably infinitary predicate-code queries. -/
abbrev PredCodeInfQuery (U : Type*) := InfQuery (PredCodeQuery U)

/-- Infinitary predicate-code states are multisets of pointed witnesses. -/
abbrev PredCodeInfState (U : Type*) := Multiset (PointedPredCode U)

/-- The infinitary predicate-code world model. -/
noncomputable instance {U : Type*} : BinaryWorldModel (PredCodeInfState U) (PredCodeInfQuery U) :=
  crispWorldModel (SatisfiesInf PointedPredCode.satisfies)

end Mettapedia.PLN.Bridges.HOL.PLNWorldModelPredCodeInfinitary
