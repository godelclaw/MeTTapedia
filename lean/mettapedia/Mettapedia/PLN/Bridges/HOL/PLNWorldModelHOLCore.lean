import Mettapedia.Logic.HOL.Semantics.Satisfaction
import Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization

/-!
# Henkin HOL models as a crisp world model

States are multisets of pointed Henkin models, queries are closed HOL formulas,
and the evidence for a formula counts the models that satisfy it and those that
do not.  This is the world model of the crisp semantics `holSatisfies`
(`PLNWorldModelCrispSpecialization.crispWorldModel`); singleton adequacy,
consequence lifting and query equivalence are the generic theorems of that
module at this semantics.
-/

namespace Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLCore

open Mettapedia.Logic.HOL
open Mettapedia.PLN.WorldModel
open Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

/-- The Henkin world model: count the models satisfying a closed formula. -/
noncomputable instance :
    BinaryWorldModel (Multiset (HenkinModel.{u, v, w} Base Const)) (HOLQuery Const) :=
  crispWorldModel holSatisfies

end Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLCore
