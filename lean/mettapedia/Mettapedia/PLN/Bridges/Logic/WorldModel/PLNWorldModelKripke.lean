import Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization
import Foundation.Modal.Kripke.Basic

/-!
# Kripke models as a crisp world model

States are multisets of pointed Kripke models (provenance with multiplicity),
queries are modal formulas (`Formula ℕ`), and the evidence for a formula counts
the pointed models that satisfy it and those that do not.  This is the world
model of the crisp semantics `PointedKripke.satisfies`
(`PLNWorldModelCrispSpecialization.crispWorldModel`); singleton adequacy,
consequence lifting and query equivalence are the generic theorems of that
module at this semantics.
-/

namespace Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelKripke

open LO.Modal
open Mettapedia.PLN.WorldModel
open Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization


/-- A pointed Kripke model (`M,w`). -/
structure PointedKripke where
  model : Kripke.Model
  world : model.World

/-- Pointed-model satisfaction predicate. -/
def PointedKripke.satisfies (pk : PointedKripke) (φ : (LO.Modal.Formula ℕ)) : Prop :=
  Formula.Kripke.Satisfies pk.model pk.world φ

/-- The Kripke world model: count the pointed models satisfying a formula. -/
noncomputable instance : BinaryWorldModel (Multiset PointedKripke) (LO.Modal.Formula ℕ) :=
  crispWorldModel PointedKripke.satisfies

end Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelKripke
