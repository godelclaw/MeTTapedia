import Mettapedia.PLN.Bridges.ProbabilityTheory.MassSemantics
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Multiset.Basic
import Mettapedia.PLN.WorldModel.BinaryWorldModel

/-!
# Abstract MLN Semantics

This module records the semantics-first core for the MLN→WM bridge.

- `AbstractMLNSemantics` keeps the world/query/feature layer abstract.
- The shared probability-theory `Mettapedia.ProbabilityTheory.MassSemantics` supplies query and total masses.
- `MassState` turns any such semantic source into an additive `BinaryWorldModel`.

The key theorem is the generic transfer:

`BinaryWorldModel.queryStrength = queryProb`

whenever the extracted evidence matches the semantic query mass and total mass.
-/

namespace Mettapedia.Logic.MarkovLogicAbstract

open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.Evidence
open Mettapedia.PLN.WorldModel
open scoped ENNReal

/-- Abstract MLN-style semantics: world weights, query truth, and feature potentials.

The abstract layer intentionally does **not** impose a specific factorization law.
Those details enter in the countable and finite-specialization modules. -/
structure AbstractMLNSemantics (World Query Feature : Type*) where
  worldWeight : World → ENNReal
  queryHolds : Query → World → Prop
  featurePotential : Feature → World → ENNReal

/-- Additive state of semantic sources. Revision is multiset addition. -/
abbrev MassState (Query : Type*) := Multiset (Mettapedia.ProbabilityTheory.MassSemantics Query)

namespace MassState

variable {Query : Type*}

instance : EvidenceType (MassState Query) where
  toAddCommMonoid := inferInstance

/-- Extract the evidence supplied by a multiset of semantic sources. -/
noncomputable def evidence (W : MassState Query) (q : Query) : BinaryEvidence :=
  (W.map fun src => src.binaryMass q).sum

noncomputable instance : BinaryWorldModel (MassState Query) Query where
  evidence W q := evidence W q
  evidence_add W₁ W₂ q := by
    let f : Mettapedia.ProbabilityTheory.MassSemantics Query → BinaryEvidence := fun src => src.binaryMass q
    have h :
        (Multiset.map f (W₁ + W₂)).sum =
          (Multiset.map f W₁).sum + (Multiset.map f W₂).sum := by
      rw [Multiset.map_add, Multiset.sum_add]
    change (Multiset.map f (W₁ + W₂)).sum =
      (Multiset.map f W₁).sum + (Multiset.map f W₂).sum
    exact h
  evidence_zero _ := by
    simp [evidence, Multiset.map_zero, Multiset.sum_zero]

theorem evidence_singleton (S : Mettapedia.ProbabilityTheory.MassSemantics Query) (q : Query) :
    evidence ({S} : MassState Query) q = S.binaryMass q := by
  unfold evidence
  simp [Multiset.map_singleton, Multiset.sum_singleton]

theorem queryStrength_singleton_eq_queryProb (S : Mettapedia.ProbabilityTheory.MassSemantics Query) (q : Query) :
    BinaryWorldModel.queryStrength ({S} : MassState Query) q = S.queryProb q := by
  unfold BinaryWorldModel.queryStrength
  rw [show BinaryWorldModel.evidence ({S} : MassState Query) q = S.binaryMass q by
      exact evidence_singleton S q]
  exact S.toStrength_binaryMass q

end MassState

theorem queryStrength_eq_queryProb_of_evidence_eq
    {State Query : Type*}
    [EvidenceType State] [BinaryWorldModel State Query]
    (W : State) (S : Mettapedia.ProbabilityTheory.MassSemantics Query)
    (hEvidence : ∀ q, BinaryWorldModel.evidence (State := State) (Query := Query) W q = S.binaryMass q)
    (q : Query) :
    BinaryWorldModel.queryStrength (State := State) (Query := Query) W q = S.queryProb q := by
  unfold BinaryWorldModel.queryStrength
  rw [hEvidence q]
  exact S.toStrength_binaryMass q

end Mettapedia.Logic.MarkovLogicAbstract
