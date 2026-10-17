import Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL

/-!
# Countably infinitary first-order sentences as a crisp world model

The countably infinitary closure (`PLNWorldModelCrispSpecialization.InfQuery`)
of first-order satisfaction: base sentences, countable conjunctions and
countable disjunctions, satisfied by `SatisfiesInf folSatisfies` over pointed
first-order structures.  Conjunction elimination and disjunction introduction
on every state are the generic `queryStrength_le_iAnd_component` and
`queryStrength_le_iOr_of_component`.
-/

namespace Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLInfinitary

open LO
open LO.FirstOrder
open Mettapedia.PLN.WorldModel.PLNWorldModel
open Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization
open Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL

universe u

/-- Countably infinitary first-order queries. -/
abbrev FOLInfQuery (L : Language.{u}) := InfQuery (Sentence L)

/-- Infinitary first-order states are multisets of pointed structures. -/
abbrev FOLInfState (L : Language.{u}) := Multiset (PointedFOL L)

/-- The infinitary first-order world model. -/
noncomputable instance {L : Language.{u}} : BinaryWorldModel (FOLInfState L) (FOLInfQuery L) :=
  crispWorldModel (SatisfiesInf folSatisfies)

end Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLInfinitary
