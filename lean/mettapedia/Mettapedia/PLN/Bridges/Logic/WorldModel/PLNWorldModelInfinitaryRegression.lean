import Mettapedia.PLN.Bridges.HOL.PLNWorldModelPredCodeInfinitary
import Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLInfinitary

/-!
# Infinitary WM Regression Fixtures (PredCode + FOL)

Concrete theorem-level fixtures exercising the new countable-connective wrappers:

- `iAnd → component` (elimination)
- `component → iOr` (introduction)

for both infinitary predicate-code and infinitary FOL WM layers.
-/

namespace Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelInfinitaryRegression

open LO
open LO.FirstOrder
open Mettapedia.PLN.WorldModel

/-! ## Predicate-code fixtures -/

abbrev predCodeInfFalse :
    Mettapedia.PLN.Bridges.HOL.PLNWorldModelPredCodeInfinitary.PredCodeInfQuery Bool :=
  .atom (.comp_not .trivial)

abbrev predCodeInfTrue :
    Mettapedia.PLN.Bridges.HOL.PLNWorldModelPredCodeInfinitary.PredCodeInfQuery Bool :=
  .atom .trivial

def predCodeInfSeq :
    Nat → Mettapedia.PLN.Bridges.HOL.PLNWorldModelPredCodeInfinitary.PredCodeInfQuery Bool
  | 0 => predCodeInfFalse
  | _ => predCodeInfTrue

def predCodeInfFixtureState :
    Mettapedia.PLN.Bridges.HOL.PLNWorldModelPredCodeInfinitary.PredCodeInfState Bool :=
  ({⟨true⟩} : Mettapedia.PLN.Bridges.HOL.PLNWorldModelPredCodeInfinitary.PredCodeInfState Bool) +
    ({⟨false⟩} : Mettapedia.PLN.Bridges.HOL.PLNWorldModelPredCodeInfinitary.PredCodeInfState Bool)

/-- Predicate-code infinitary fixture: conjunction-elimination transport via wrapper API. -/
theorem predCodeInf_iAnd_component_fixture :
    BinaryWorldModel.queryStrength
        (State := Mettapedia.PLN.Bridges.HOL.PLNWorldModelPredCodeInfinitary.PredCodeInfState Bool)
        (Query := Mettapedia.PLN.Bridges.HOL.PLNWorldModelPredCodeInfinitary.PredCodeInfQuery Bool)
        predCodeInfFixtureState (.iAnd predCodeInfSeq) ≤
      BinaryWorldModel.queryStrength
        (State := Mettapedia.PLN.Bridges.HOL.PLNWorldModelPredCodeInfinitary.PredCodeInfState Bool)
        (Query := Mettapedia.PLN.Bridges.HOL.PLNWorldModelPredCodeInfinitary.PredCodeInfQuery Bool)
        predCodeInfFixtureState (predCodeInfSeq 0) := by
  exact
    (Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization.wmConsequenceRule_of_pointwise
      (Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization.SatisfiesInf
        Mettapedia.PLN.Bridges.HOL.PLNWorldModelPredCode.PointedPredCode.satisfies) (q₁ := .iAnd predCodeInfSeq) (q₂ := predCodeInfSeq 0)).sound
      (Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization.pointwise_iAnd_to_component
        Mettapedia.PLN.Bridges.HOL.PLNWorldModelPredCode.PointedPredCode.satisfies predCodeInfSeq 0)
      predCodeInfFixtureState

/-- Predicate-code infinitary fixture: disjunction-introduction transport via wrapper API. -/
theorem predCodeInf_component_iOr_fixture :
    BinaryWorldModel.queryStrength
        (State := Mettapedia.PLN.Bridges.HOL.PLNWorldModelPredCodeInfinitary.PredCodeInfState Bool)
        (Query := Mettapedia.PLN.Bridges.HOL.PLNWorldModelPredCodeInfinitary.PredCodeInfQuery Bool)
        predCodeInfFixtureState (predCodeInfSeq 0) ≤
      BinaryWorldModel.queryStrength
        (State := Mettapedia.PLN.Bridges.HOL.PLNWorldModelPredCodeInfinitary.PredCodeInfState Bool)
        (Query := Mettapedia.PLN.Bridges.HOL.PLNWorldModelPredCodeInfinitary.PredCodeInfQuery Bool)
        predCodeInfFixtureState (.iOr predCodeInfSeq) := by
  exact
    (Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization.wmConsequenceRule_of_pointwise
      (Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization.SatisfiesInf
        Mettapedia.PLN.Bridges.HOL.PLNWorldModelPredCode.PointedPredCode.satisfies) (q₁ := predCodeInfSeq 0) (q₂ := .iOr predCodeInfSeq)).sound
      (Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization.pointwise_component_to_iOr
        Mettapedia.PLN.Bridges.HOL.PLNWorldModelPredCode.PointedPredCode.satisfies predCodeInfSeq 0)
      predCodeInfFixtureState

/-! ## FOL fixtures -/

abbrev folInfTop {L : Language} :
    Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLInfinitary.FOLInfQuery L :=
  .atom (⊤ : Sentence L)

abbrev folInfBottom {L : Language} :
    Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLInfinitary.FOLInfQuery L :=
  .atom (⊥ : Sentence L)

def folInfSeq {L : Language} :
    Nat → Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLInfinitary.FOLInfQuery L
  | 0 => folInfBottom
  | _ => folInfTop

/-- FOL infinitary singleton fixture: conjunction-elimination transport via wrapper API. -/
theorem folInf_iAnd_component_singleton_fixture
    {L : Language} (S : Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL.PointedFOL L) :
    BinaryWorldModel.queryStrength
        (State := Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLInfinitary.FOLInfState L)
        (Query := Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLInfinitary.FOLInfQuery L)
        ({S} : Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLInfinitary.FOLInfState L)
        (.iAnd (folInfSeq (L := L))) ≤
      BinaryWorldModel.queryStrength
        (State := Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLInfinitary.FOLInfState L)
        (Query := Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLInfinitary.FOLInfQuery L)
        ({S} : Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLInfinitary.FOLInfState L)
        (folInfSeq (L := L) 0) := by
  exact
    (Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization.wmConsequenceRule_of_pointwise
      (Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization.SatisfiesInf
        Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL.folSatisfies) (q₁ := .iAnd (folInfSeq (L := L))) (q₂ := folInfSeq (L := L) 0)).sound
      (Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization.pointwise_iAnd_to_component
        Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL.folSatisfies (folInfSeq (L := L)) 0)
      ({S} : Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLInfinitary.FOLInfState L)

/-- FOL infinitary singleton fixture: disjunction-introduction transport via wrapper API. -/
theorem folInf_component_iOr_singleton_fixture
    {L : Language} (S : Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL.PointedFOL L) :
    BinaryWorldModel.queryStrength
        (State := Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLInfinitary.FOLInfState L)
        (Query := Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLInfinitary.FOLInfQuery L)
        ({S} : Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLInfinitary.FOLInfState L)
        (folInfSeq (L := L) 0) ≤
      BinaryWorldModel.queryStrength
        (State := Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLInfinitary.FOLInfState L)
        (Query := Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLInfinitary.FOLInfQuery L)
        ({S} : Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLInfinitary.FOLInfState L)
        (.iOr (folInfSeq (L := L))) := by
  exact
    (Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization.wmConsequenceRule_of_pointwise
      (Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization.SatisfiesInf
        Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL.folSatisfies) (q₁ := folInfSeq (L := L) 0) (q₂ := .iOr (folInfSeq (L := L)))).sound
      (Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization.pointwise_component_to_iOr
        Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL.folSatisfies (folInfSeq (L := L)) 0)
      ({S} : Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLInfinitary.FOLInfState L)

end Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelInfinitaryRegression
