import Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization
import Foundation.FirstOrder.Basic

/-!
# First-Order (Foundation Sentence) Instance for the WM Calculus

This module instantiates `BinaryWorldModel` on Foundation first-order semantics:

- state = multiset of first-order structures (`Struc L`),
- query = first-order sentence (`Sentence L`),
- evidence = positive/negative support counts from Tarskian satisfaction.

Singleton states recover crisp 0/1 query strength.
-/

namespace Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL

open LO
open LO.FirstOrder
open Mettapedia.PLN.WorldModel
open Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.Evidence
open scoped ENNReal

universe u

abbrev FOLQuery (L : Language.{u}) := Sentence L
abbrev PointedFOL (L : Language.{u}) := SmallStruc L

/-- Sentence satisfaction at a pointed first-order structure. -/
def folSatisfies {L : Language.{u}} (S : PointedFOL L) (φ : FOLQuery L) : Prop :=
  Semantics.Models S φ

/-! ## Consequence adequacy on singleton and multiset FOL states -/

/-- The world model of this crisp semantics. -/
noncomputable instance {L : Language.{u}} : BinaryWorldModel (Multiset (PointedFOL L)) (FOLQuery L) :=
  crispWorldModel folSatisfies

end Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL
