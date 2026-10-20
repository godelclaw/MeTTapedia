import Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization
import Foundation.Modal.Neighborhood.Basic

/-!
# Neighborhood models as a crisp world model

States are multisets of pointed neighborhood models, queries are modal formulas
(`Formula ℕ`), and the evidence for a formula counts the pointed models that
satisfy it under neighborhood semantics and those that do not.  This is the
world model of the crisp semantics `PointedNeighborhood.satisfies`
(`PLNWorldModelCrispSpecialization.crispWorldModel`), so it shares the whole
consequence theory of the Kripke world model.
-/

namespace Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelNeighborhood

open LO.Modal
open Mettapedia.PLN.WorldModel
open Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization


/-- A pointed neighborhood model (`M,w`). -/
structure PointedNeighborhood where
  model : Neighborhood.Model
  world : model.World

/-- Pointed-model neighborhood satisfaction predicate. -/
def PointedNeighborhood.satisfies (pn : PointedNeighborhood) (φ : (LO.Modal.Formula ℕ)) : Prop :=
  Formula.Neighborhood.Satisfies pn.model pn.world φ

/-- The neighborhood world model: count the pointed models satisfying a formula. -/
noncomputable instance : BinaryWorldModel (Multiset PointedNeighborhood) (LO.Modal.Formula ℕ) :=
  crispWorldModel PointedNeighborhood.satisfies

end Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelNeighborhood
