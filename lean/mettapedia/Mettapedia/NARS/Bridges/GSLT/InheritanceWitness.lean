import Mettapedia.GSLT.Core.ProofRelevantJudgment
import Mettapedia.KR.ConceptGeometry.AbstractInheritanceStampedWitness

/-!
# Inheritance queries with retained witness identities

Finite queries enumerate tagged objects and attributes. Their set semantics
interprets compound terms independently, then tests witness membership. The
existing judgment GSLT supplies query/answer steps; exact evidence equivalence
preserves and reflects them. This specifies witness queries, not the full NARS
inference process. Counting forgets identities, while the answers retain them.
-/

set_option autoImplicit false

namespace Mettapedia.NARS.Bridges.GSLT.InheritanceWitness

open Mettapedia.KR.ConceptGeometry.AbstractInheritance
open Mettapedia.NARS.Logic.Inheritance
open Mettapedia.GSLT.ProofRelevantJudgment

universe u v w

variable {Atom : Type u} {Obj : Type v} {Attr : Type w}
variable [DecidableEq Obj] [DecidableEq Attr]

/-- Computable witness support; roles and source carriers stay distinct.
Finite supports do not require finite object or attribute universes. -/
def witnesses (F : Frame Atom Obj Attr) (q : Term Atom × Term Atom) :
    Finset (DualConcept.WitnessStamp Obj Attr) :=
  (F.positiveExtensionalWitnesses q.1 q.2).map DualConcept.posExtEmbedding ∪
    (F.positiveIntensionalWitnesses q.1 q.2).map DualConcept.posIntEmbedding ∪
    (F.negativeExtensionalWitnesses q.1 q.2).map DualConcept.negExtEmbedding ∪
    (F.negativeIntensionalWitnesses q.1 q.2).map DualConcept.negIntEmbedding

/-- Independent set-based judgment for the same four witness channels. -/
def Holds (meaning : Atom → DualConcept Obj Attr) (q : Term Atom × Term Atom) :
    DualConcept.WitnessStamp Obj Attr → Prop
  | .posExt x => x ∈ DualConcept.positiveExtensionalWitnesses
      (q.1.denote meaning) (q.2.denote meaning)
  | .negExt x => x ∈ DualConcept.negativeExtensionalWitnesses
      (q.1.denote meaning) (q.2.denote meaning)
  | .posInt a => a ∈ DualConcept.positiveIntensionalWitnesses
      (q.1.denote meaning) (q.2.denote meaning)
  | .negInt a => a ∈ DualConcept.negativeIntensionalWitnesses
      (q.1.denote meaning) (q.2.denote meaning)

/-- Exact membership correspondence for arbitrary compound queries. -/
theorem mem_witnesses_iff (F : Frame Atom Obj Attr) (q : Term Atom × Term Atom)
    (stamp : DualConcept.WitnessStamp Obj Attr) :
    stamp ∈ witnesses F q ↔ Holds (fun a => F.interpretation.meaning (.atom a)) q stamp := by
  change stamp ∈ witnesses F q ↔ Holds (fun a => ⟨F.atomExtension a, F.atomIntension a⟩) q stamp
  unfold Holds
  rw [← F.interpretation_meaning_eq_denote q.1, ← F.interpretation_meaning_eq_denote q.2]
  cases stamp <;> simp [witnesses, Frame.interpretation,
    Frame.positiveExtensionalWitnesses, Frame.negativeExtensionalWitnesses,
    Frame.positiveIntensionalWitnesses, Frame.negativeIntensionalWitnesses,
    DualConcept.positiveExtensionalWitnesses, DualConcept.negativeExtensionalWitnesses,
    DualConcept.positiveIntensionalWitnesses, DualConcept.negativeIntensionalWitnesses]

/-- A finite answer provider is exact precisely when it returns this support. -/
theorem answers_exact_iff (F : Frame Atom Obj Attr) (q : Term Atom × Term Atom)
    (answers : Finset (DualConcept.WitnessStamp Obj Attr)) :
    (∀ stamp, stamp ∈ answers ↔
      Holds (fun a => F.interpretation.meaning (.atom a)) q stamp) ↔ answers = witnesses F q := by
  simp only [← mem_witnesses_iff, Finset.ext_iff]

def finiteJudgment (F : Frame Atom Obj Attr) :
    Judgment (ULift.{max v w} (Term Atom × Term Atom))
      (ULift.{u} (DualConcept.WitnessStamp Obj Attr)) where
  Evidence q stamp := ULift.{max u v w} (PLift (stamp.down ∈ witnesses F q.down))

def abstractJudgment (meaning : Atom → DualConcept Obj Attr) :
    Judgment (ULift.{max v w} (Term Atom × Term Atom))
      (ULift.{u} (DualConcept.WitnessStamp Obj Attr)) where
  Evidence q stamp := ULift.{max u v w} (PLift (Holds meaning q.down stamp.down))

/-- Reuse `exactTranslation`, `semanticCover`, and `step_iff` from the judgment
API. Each fixed query/answer evidence fibre is preserved in both directions. -/
def exact (F : Frame Atom Obj Attr) : ExactEquivalence (finiteJudgment F)
    (abstractJudgment (fun a => F.interpretation.meaning (.atom a))) where
  evidenceEquiv q stamp :=
    { toFun h := ⟨⟨(mem_witnesses_iff F q.down stamp.down).mp h.down.down⟩⟩
      invFun h := ⟨⟨(mem_witnesses_iff F q.down stamp.down).mpr h.down.down⟩⟩
      left_inv _ := rfl
      right_inv _ := rfl }

theorem query_step_iff (F : Frame Atom Obj Attr) (q : Term Atom × Term Atom)
    (stamp : DualConcept.WitnessStamp Obj Attr) :
    (finiteJudgment F).theory.Step (.query ⟨q⟩) (.answer ⟨q⟩ ⟨stamp⟩) ↔
      Holds (fun a => F.interpretation.meaning (.atom a)) q stamp := by
  rw [Judgment.query_step_answer_iff]
  exact ⟨fun ⟨h⟩ => (mem_witnesses_iff F q stamp).mp h.down.down,
    fun h => ⟨⟨⟨(mem_witnesses_iff F q stamp).mpr h⟩⟩⟩⟩

theorem witnesses_eq_stamp (F : Frame Atom Obj Attr) (q : Term Atom × Term Atom) :
    witnesses F q =
      (Mettapedia.NARS.Bridges.PLN.InheritanceEvidence.inheritanceStampedEvidence F q.1 q.2).stamp :=
  rfl

namespace Examples

open Mettapedia.NARS.Logic.Inheritance.Examples
open Mettapedia.NARS.Bridges.PLN.InheritanceEvidence

theorem retained_negative_object :
    DualConcept.WitnessStamp.negExt Creature.pingu ∈ witnesses ontologyFrame (bird, flyer) := by
  decide

theorem retained_positive_attribute :
    DualConcept.WitnessStamp.posInt Feature.winged ∈ witnesses ontologyFrame (penguin, bird) := by
  decide

theorem wrong_channel_refused :
    DualConcept.WitnessStamp.posInt Feature.flies ∉ witnesses ontologyFrame (bird, flyer) ∧
      DualConcept.WitnessStamp.negInt Feature.flies ∈ witnesses ontologyFrame (bird, flyer) := by
  decide

theorem omission_changes_answers :
    (witnesses ontologyFrame (bird, flyer)).erase (.negExt Creature.pingu) ≠
      witnesses ontologyFrame (bird, flyer) :=
  Finset.erase_ne_self.mpr retained_negative_object

theorem extra_changes_answers :
    insert (.posInt Feature.flies) (witnesses ontologyFrame (bird, flyer)) ≠
      witnesses ontologyFrame (bird, flyer) :=
  Finset.insert_ne_self.mpr wrong_channel_refused.1

theorem equal_counts_distinct_witnesses :
    evidence ontologyFrame bird bird = evidence ontologyFrame penguin penguin ∧
      witnesses ontologyFrame (bird, bird) ≠ witnesses ontologyFrame (penguin, penguin) := by
  constructor
  · have objects : ({Creature.tweety, Creature.pingu} : Finset Creature).card = 2 := by decide
    have attributes : ({Feature.winged, Feature.aquatic} : Finset Feature).card = 2 := by decide
    ext <;> norm_num [evidence, Frame.positiveExtensionalWitnesses,
      Frame.positiveIntensionalWitnesses, Frame.negativeExtensionalWitnesses,
      Frame.negativeIntensionalWitnesses, Frame.extension, Frame.intension,
      ontologyFrame, bird, penguin, objects, attributes]
  · decide

/-- Empty support over an infinite object universe needs no finite-universe assumption. -/
theorem empty_support :
    witnesses (⟨fun _ => ∅, fun _ => ∅⟩ : Frame Unit Nat Empty) (.atom (), .atom ()) = ∅ := by
  decide

end Examples

end Mettapedia.NARS.Bridges.GSLT.InheritanceWitness
