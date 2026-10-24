import Mettapedia.Evidence.SourceScoped
import Mettapedia.KR.ConceptGeometry.AbstractInheritanceWitness
import Mettapedia.NARS.Bridges.PLN.InheritanceEvidence

/-!
# Stamp-Aware Witness Aggregation for Abstract Inheritance

This module equips finite inheritance witnesses with provenance stamps:

- `StampDisjoint` is `Finset.Disjoint`
- `StampConcat` is union
- positive/negative and extensional/intensional witness channels carry tagged stamps
- aggregated inheritance evidence is built by revising disjoint stamped fragments
-/

namespace Mettapedia.KR.ConceptGeometry.AbstractInheritance

open Mettapedia.PLN.Evidence
open scoped ENNReal

universe u v

/-- Binary evidence paired with a finite provenance stamp. -/
structure StampedBinaryEvidence (Stamp : Type u) where
  evidence : BinaryEvidence
  stamp : Finset Stamp

namespace StampedBinaryEvidence

variable {Stamp : Type u} [DecidableEq Stamp]

open Mettapedia.Evidence

/-- Stamped PLN evidence exposes its provenance stamp through the same neutral
source-scope interface used by path-scoped NARS evidence. -/
instance instSourceScoped :
    SourceScoped (StampedBinaryEvidence Stamp) Stamp where
  sourceScope := StampedBinaryEvidence.stamp

omit [DecidableEq Stamp] in
@[simp] theorem sourceScope_eq_stamp (packet : StampedBinaryEvidence Stamp) :
    sourceScope packet = packet.stamp := rfl

omit [DecidableEq Stamp] in
@[ext] theorem ext {x y : StampedBinaryEvidence Stamp}
    (hEvidence : x.evidence = y.evidence) (hStamp : x.stamp = y.stamp) : x = y := by
  cases x
  cases y
  simp_all

/-- NARS/PLN-style stamp independence. -/
def StampDisjoint (x y : StampedBinaryEvidence Stamp) : Prop :=
  SourceScoped.Independent x y

instance instDecidableStampDisjoint
    (x y : StampedBinaryEvidence Stamp) :
    Decidable (StampDisjoint x y) := by
  unfold StampDisjoint
  infer_instance

/-- NARS/PLN-style stamp concatenation. -/
def StampConcat (x y : StampedBinaryEvidence Stamp) : Finset Stamp :=
  SourceScope.merge x.stamp y.stamp

/-- Revision on stamped evidence carries additive evidence and union provenance. -/
noncomputable def revise (x y : StampedBinaryEvidence Stamp) : StampedBinaryEvidence Stamp where
  evidence := x.evidence + y.evidence
  stamp := StampConcat x y

/-- Guarded revision rejects provenance-overlapping packets. -/
noncomputable def guardedRevise (x y : StampedBinaryEvidence Stamp) :
    Option (StampedBinaryEvidence Stamp) :=
  if _h : StampDisjoint x y then some (revise x y) else none

@[simp] theorem revise_evidence (x y : StampedBinaryEvidence Stamp) :
    (revise x y).evidence = x.evidence + y.evidence := rfl

@[simp] theorem revise_stamp (x y : StampedBinaryEvidence Stamp) :
    (revise x y).stamp = x.stamp ∪ y.stamp := rfl

omit [DecidableEq Stamp] in
theorem stampDisjoint_self_iff_stamp_eq_empty (x : StampedBinaryEvidence Stamp) :
    StampDisjoint x x ↔ x.stamp = ∅ := by
  simpa [StampDisjoint, SourceScoped.Independent] using
    (SourceScope.independent_self_iff_eq_empty x.stamp)

omit [DecidableEq Stamp] in
theorem not_stampDisjoint_of_mem
    {x y : StampedBinaryEvidence Stamp} {a : Stamp}
    (hx : a ∈ x.stamp) (hy : a ∈ y.stamp) :
    ¬ StampDisjoint x y := by
  intro h
  exact (Finset.disjoint_left.mp h hx) hy

@[simp] theorem guardedRevise_eq_some_of_stampDisjoint
    (x y : StampedBinaryEvidence Stamp)
    (h : StampDisjoint x y) :
    guardedRevise x y = some (revise x y) := by
  simp [guardedRevise, h]

@[simp] theorem guardedRevise_eq_none_of_not_stampDisjoint
    (x y : StampedBinaryEvidence Stamp)
    (h : ¬ StampDisjoint x y) :
    guardedRevise x y = none := by
  simp [guardedRevise, h]

theorem guardedRevise_eq_none_iff_not_stampDisjoint
    (x y : StampedBinaryEvidence Stamp) :
    guardedRevise x y = none ↔ ¬ StampDisjoint x y := by
  by_cases h : StampDisjoint x y
  · simp [guardedRevise, h]
  · simp [guardedRevise, h]

theorem guardedRevise_eq_none_of_shared_stamp
    {x y : StampedBinaryEvidence Stamp} {a : Stamp}
    (hx : a ∈ x.stamp) (hy : a ∈ y.stamp) :
    guardedRevise x y = none := by
  exact guardedRevise_eq_none_of_not_stampDisjoint x y
    (not_stampDisjoint_of_mem hx hy)

theorem guardedRevise_self_eq_none_of_stamp_ne_empty
    (x : StampedBinaryEvidence Stamp) (h : x.stamp ≠ ∅) :
    guardedRevise x x = none := by
  apply guardedRevise_eq_none_of_not_stampDisjoint
  rwa [stampDisjoint_self_iff_stamp_eq_empty]

omit [DecidableEq Stamp] in
theorem stampDisjoint_symm (x y : StampedBinaryEvidence Stamp) :
    StampDisjoint x y ↔ StampDisjoint y x := by
  exact SourceScoped.independent_comm x y

/-! ### Iterated revision under pairwise stamp-disjointness

Formal counterpart to PLN's multi-witness Revision: gather many stamped
inheritance / evidence packets, revise them all together, and certify
that the checker accepts exactly pairwise stamp-disjoint packets.
Source separation and stochastic independence are different conditions.
-/

/-- Neutral packet: zero evidence, empty stamp. Identity for `revise`. -/
noncomputable def empty : StampedBinaryEvidence Stamp where
  evidence := 0
  stamp := ∅

omit [DecidableEq Stamp] in
@[simp] theorem empty_evidence :
    (empty : StampedBinaryEvidence Stamp).evidence = 0 := rfl

omit [DecidableEq Stamp] in
@[simp] theorem empty_stamp :
    (empty : StampedBinaryEvidence Stamp).stamp = (∅ : Finset Stamp) := rfl

omit [DecidableEq Stamp] in
theorem stampDisjoint_empty_left (x : StampedBinaryEvidence Stamp) :
    StampDisjoint (empty : StampedBinaryEvidence Stamp) x := by
  simp [StampDisjoint, SourceScoped.Independent]

omit [DecidableEq Stamp] in
theorem stampDisjoint_empty_right (x : StampedBinaryEvidence Stamp) :
    StampDisjoint x (empty : StampedBinaryEvidence Stamp) := by
  simp [StampDisjoint, SourceScoped.Independent]

/-- Iterated revision: chain `revise` across a list of stamped evidence packets.
The order and the finite list of packets are retained. -/
noncomputable def listRevise :
    List (StampedBinaryEvidence Stamp) → StampedBinaryEvidence Stamp
  | [] => empty
  | x :: xs => revise x (listRevise xs)

@[simp] theorem listRevise_nil :
    listRevise ([] : List (StampedBinaryEvidence Stamp)) = empty := rfl

@[simp] theorem listRevise_cons (x : StampedBinaryEvidence Stamp)
    (xs : List (StampedBinaryEvidence Stamp)) :
    listRevise (x :: xs) = revise x (listRevise xs) := rfl

/-- The aggregated evidence is the additive sum of per-packet evidence.
This is the same algebra as classical PLN revision under independence: the
weights sum because the underlying carrier is an `AddCommMonoid`. -/
theorem listRevise_evidence (xs : List (StampedBinaryEvidence Stamp)) :
    (listRevise xs).evidence = (xs.map (·.evidence)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

/-- An element belongs to the aggregated stamp iff it belongs to some input
packet's stamp. -/
theorem mem_listRevise_stamp
    (xs : List (StampedBinaryEvidence Stamp)) {a : Stamp} :
    a ∈ (listRevise xs).stamp ↔ ∃ x ∈ xs, a ∈ x.stamp := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp [revise_stamp, ih]

/-- `x`'s stamp is disjoint from the iterated revision of `xs` iff it is
disjoint from every member of `xs`. This is the key "decompose disjointness"
lemma underlying the pairwise-soundness certificate. -/
theorem stampDisjoint_listRevise_iff
    (x : StampedBinaryEvidence Stamp)
    (xs : List (StampedBinaryEvidence Stamp)) :
    StampDisjoint x (listRevise xs) ↔ ∀ y ∈ xs, StampDisjoint x y := by
  induction xs with
  | nil => simp [StampDisjoint, SourceScoped.Independent]
  | cons y ys ih =>
      simpa only [listRevise_cons, StampDisjoint, SourceScoped.Independent,
        SourceScope.Independent, sourceScope_eq_stamp, revise_stamp,
        Finset.disjoint_union_right, List.forall_mem_cons] using and_congr Iff.rfl ih

/-- Guarded iterated revision: structurally propagates `Option` failure as
soon as any prefix step produces an overlapping stamp, mirroring the binary
`guardedRevise`. -/
noncomputable def guardedListRevise :
    List (StampedBinaryEvidence Stamp) → Option (StampedBinaryEvidence Stamp)
  | [] => some empty
  | x :: xs => (guardedListRevise xs).bind fun r =>
      if StampDisjoint x r then some (revise x r) else none

@[simp] theorem guardedListRevise_nil :
    guardedListRevise ([] : List (StampedBinaryEvidence Stamp)) = some empty := rfl

theorem guardedListRevise_cons (x : StampedBinaryEvidence Stamp)
    (xs : List (StampedBinaryEvidence Stamp)) :
    guardedListRevise (x :: xs) =
      (guardedListRevise xs).bind fun r =>
        if StampDisjoint x r then some (revise x r) else none := rfl

/-- The recursive checker accepts exactly the pairwise source-disjoint lists.
This characterizes its source-overlap guard, not probabilistic independence. -/
theorem guardedListRevise_eq (xs : List (StampedBinaryEvidence Stamp)) :
    guardedListRevise xs =
      if xs.Pairwise StampDisjoint then some (listRevise xs) else none := by
  induction xs with
  | nil => simp [guardedListRevise, listRevise]
  | cons x xs ih =>
      rw [guardedListRevise_cons, ih]
      by_cases h : xs.Pairwise StampDisjoint
      · simp only [if_pos h, Option.bind_some]
        simp [List.pairwise_cons, h, ← stampDisjoint_listRevise_iff, listRevise_cons]
      · simp [h, List.pairwise_cons]

/-- Success determines both the aggregate and the source-separation certificate. -/
theorem guardedListRevise_eq_some_iff
    (xs : List (StampedBinaryEvidence Stamp)) (r : StampedBinaryEvidence Stamp) :
    guardedListRevise xs = some r ↔ xs.Pairwise StampDisjoint ∧ r = listRevise xs := by
  rw [guardedListRevise_eq]
  split_ifs <;> simp_all [eq_comm]

theorem guardedListRevise_eq_some_imp_eq_listRevise
    (xs : List (StampedBinaryEvidence Stamp)) {r : StampedBinaryEvidence Stamp}
    (hr : guardedListRevise xs = some r) : r = listRevise xs :=
  ((guardedListRevise_eq_some_iff xs r).mp hr).2

theorem guardedListRevise_eq_some_iff_pairwise
    (xs : List (StampedBinaryEvidence Stamp)) :
    guardedListRevise xs = some (listRevise xs) ↔ xs.Pairwise StampDisjoint := by
  simp only [guardedListRevise_eq_some_iff, and_true, eq_self]

theorem guardedListRevise_isSome_iff_pairwise
    (xs : List (StampedBinaryEvidence Stamp)) :
    (guardedListRevise xs).isSome ↔ xs.Pairwise StampDisjoint := by
  simp [guardedListRevise_eq]

theorem guardedListRevise_eq_none_iff_not_pairwise
    (xs : List (StampedBinaryEvidence Stamp)) :
    guardedListRevise xs = none ↔ ¬ xs.Pairwise StampDisjoint := by
  simp [guardedListRevise_eq]

/-- A successful guarded aggregation returns the sum of the input counts. -/
theorem evidence_of_guardedListRevise_eq_some
    {xs : List (StampedBinaryEvidence Stamp)}
    {r : StampedBinaryEvidence Stamp}
    (hr : guardedListRevise xs = some r) :
    r.evidence = (xs.map (·.evidence)).sum := by
  have hr' : r = listRevise xs :=
    guardedListRevise_eq_some_imp_eq_listRevise xs hr
  rw [hr', listRevise_evidence]

end StampedBinaryEvidence

namespace DualConcept

variable {Obj : Type u} {Attr : Type v}

section Finite

variable [Fintype Obj] [DecidableEq Obj] [Fintype Attr] [DecidableEq Attr]

/-- Tagged witness identifiers separate witness role as well as source carrier. -/
inductive WitnessStamp (Obj : Type u) (Attr : Type v) where
  | posExt : Obj → WitnessStamp Obj Attr
  | negExt : Obj → WitnessStamp Obj Attr
  | posInt : Attr → WitnessStamp Obj Attr
  | negInt : Attr → WitnessStamp Obj Attr
  deriving DecidableEq

@[simps!] def posExtEmbedding : Obj ↪ WitnessStamp Obj Attr :=
  ⟨WitnessStamp.posExt, fun _ _ => WitnessStamp.posExt.inj⟩

@[simps!] def negExtEmbedding : Obj ↪ WitnessStamp Obj Attr :=
  ⟨WitnessStamp.negExt, fun _ _ => WitnessStamp.negExt.inj⟩

@[simps!] def posIntEmbedding : Attr ↪ WitnessStamp Obj Attr :=
  ⟨WitnessStamp.posInt, fun _ _ => WitnessStamp.posInt.inj⟩

@[simps!] def negIntEmbedding : Attr ↪ WitnessStamp Obj Attr :=
  ⟨WitnessStamp.negInt, fun _ _ => WitnessStamp.negInt.inj⟩

/-- Positive extensional witness packet. -/
noncomputable def positiveExtensionalStampedEvidence
    (A B : DualConcept Obj Attr) :
    StampedBinaryEvidence (WitnessStamp Obj Attr) where
  evidence := ⟨((finitePositiveExtensionalWitnesses A B).card : ℝ≥0∞), 0⟩
  stamp := (finitePositiveExtensionalWitnesses A B).map posExtEmbedding

/-- Negative extensional witness packet. -/
noncomputable def negativeExtensionalStampedEvidence
    (A B : DualConcept Obj Attr) :
    StampedBinaryEvidence (WitnessStamp Obj Attr) where
  evidence := ⟨0, ((finiteNegativeExtensionalWitnesses A B).card : ℝ≥0∞)⟩
  stamp := (finiteNegativeExtensionalWitnesses A B).map negExtEmbedding

/-- Positive intensional witness packet. -/
noncomputable def positiveIntensionalStampedEvidence
    (A B : DualConcept Obj Attr) :
    StampedBinaryEvidence (WitnessStamp Obj Attr) where
  evidence := ⟨((finitePositiveIntensionalWitnesses A B).card : ℝ≥0∞), 0⟩
  stamp := (finitePositiveIntensionalWitnesses A B).map posIntEmbedding

/-- Negative intensional witness packet. -/
noncomputable def negativeIntensionalStampedEvidence
    (A B : DualConcept Obj Attr) :
    StampedBinaryEvidence (WitnessStamp Obj Attr) where
  evidence := ⟨0, ((finiteNegativeIntensionalWitnesses A B).card : ℝ≥0∞)⟩
  stamp := (finiteNegativeIntensionalWitnesses A B).map negIntEmbedding

omit [Fintype Attr] [DecidableEq Attr] in
@[simp] theorem positiveExtensionalStampedEvidence_stamp_card
    (A B : DualConcept Obj Attr) :
    (positiveExtensionalStampedEvidence A B).stamp.card =
      (finitePositiveExtensionalWitnesses A B).card := by
  simp [positiveExtensionalStampedEvidence]

omit [Fintype Attr] [DecidableEq Attr] in
@[simp] theorem negativeExtensionalStampedEvidence_stamp_card
    (A B : DualConcept Obj Attr) :
    (negativeExtensionalStampedEvidence A B).stamp.card =
      (finiteNegativeExtensionalWitnesses A B).card := by
  simp [negativeExtensionalStampedEvidence]

omit [Fintype Obj] [DecidableEq Obj] in
@[simp] theorem positiveIntensionalStampedEvidence_stamp_card
    (A B : DualConcept Obj Attr) :
    (positiveIntensionalStampedEvidence A B).stamp.card =
      (finitePositiveIntensionalWitnesses A B).card := by
  simp [positiveIntensionalStampedEvidence]

omit [Fintype Obj] [DecidableEq Obj] in
@[simp] theorem negativeIntensionalStampedEvidence_stamp_card
    (A B : DualConcept Obj Attr) :
    (negativeIntensionalStampedEvidence A B).stamp.card =
      (finiteNegativeIntensionalWitnesses A B).card := by
  simp [negativeIntensionalStampedEvidence]

theorem posExt_posInt_stampDisjoint
    (A B : DualConcept Obj Attr) :
    StampedBinaryEvidence.StampDisjoint
      (positiveExtensionalStampedEvidence A B)
      (positiveIntensionalStampedEvidence A B) := by
  classical
  rw [StampedBinaryEvidence.StampDisjoint]
  refine Finset.disjoint_left.2 ?_
  intro x hx hy
  cases x <;>
    simp [positiveExtensionalStampedEvidence, positiveIntensionalStampedEvidence,
      posExtEmbedding, posIntEmbedding] at hx hy

theorem negExt_negInt_stampDisjoint
    (A B : DualConcept Obj Attr) :
    StampedBinaryEvidence.StampDisjoint
      (negativeExtensionalStampedEvidence A B)
      (negativeIntensionalStampedEvidence A B) := by
  classical
  rw [StampedBinaryEvidence.StampDisjoint]
  refine Finset.disjoint_left.2 ?_
  intro x hx hy
  cases x <;>
    simp [negativeExtensionalStampedEvidence, negativeIntensionalStampedEvidence,
      negExtEmbedding, negIntEmbedding] at hx hy

/-- Positive witness aggregation is a safe revision of disjoint extensional and
intensional witness packets. -/
noncomputable def positiveStampedEvidence
    (A B : DualConcept Obj Attr) :
    StampedBinaryEvidence (WitnessStamp Obj Attr) :=
  StampedBinaryEvidence.revise
    (positiveExtensionalStampedEvidence A B)
    (positiveIntensionalStampedEvidence A B)

/-- Negative witness aggregation is a safe revision of disjoint extensional and
intensional witness packets. -/
noncomputable def negativeStampedEvidence
    (A B : DualConcept Obj Attr) :
    StampedBinaryEvidence (WitnessStamp Obj Attr) :=
  StampedBinaryEvidence.revise
    (negativeExtensionalStampedEvidence A B)
    (negativeIntensionalStampedEvidence A B)

theorem positiveStampedEvidence_guardedRevise_eq_some
    (A B : DualConcept Obj Attr) :
    StampedBinaryEvidence.guardedRevise
      (positiveExtensionalStampedEvidence A B)
      (positiveIntensionalStampedEvidence A B) =
        some (positiveStampedEvidence A B) := by
  simpa [positiveStampedEvidence] using
    StampedBinaryEvidence.guardedRevise_eq_some_of_stampDisjoint
      (positiveExtensionalStampedEvidence A B)
      (positiveIntensionalStampedEvidence A B)
      (posExt_posInt_stampDisjoint A B)

theorem negativeStampedEvidence_guardedRevise_eq_some
    (A B : DualConcept Obj Attr) :
    StampedBinaryEvidence.guardedRevise
      (negativeExtensionalStampedEvidence A B)
      (negativeIntensionalStampedEvidence A B) =
        some (negativeStampedEvidence A B) := by
  simpa [negativeStampedEvidence] using
    StampedBinaryEvidence.guardedRevise_eq_some_of_stampDisjoint
      (negativeExtensionalStampedEvidence A B)
      (negativeIntensionalStampedEvidence A B)
      (negExt_negInt_stampDisjoint A B)

theorem positive_negative_stampDisjoint
    (A B : DualConcept Obj Attr) :
    StampedBinaryEvidence.StampDisjoint
      (positiveStampedEvidence A B)
      (negativeStampedEvidence A B) := by
  classical
  rw [StampedBinaryEvidence.StampDisjoint]
  simp only [Mettapedia.Evidence.SourceScoped.Independent,
    StampedBinaryEvidence.sourceScope_eq_stamp]
  rw [positiveStampedEvidence, negativeStampedEvidence,
    StampedBinaryEvidence.revise_stamp]
  refine Finset.disjoint_left.2 ?_
  intro x hx hy
  cases x <;>
    simp [positiveExtensionalStampedEvidence, positiveIntensionalStampedEvidence,
      negativeExtensionalStampedEvidence, negativeIntensionalStampedEvidence,
      posExtEmbedding, posIntEmbedding, negExtEmbedding, negIntEmbedding] at hx hy

/-- Full finite stamped inheritance evidence. -/
noncomputable def finiteInheritanceStampedEvidence
    (A B : DualConcept Obj Attr) :
    StampedBinaryEvidence (WitnessStamp Obj Attr) :=
  StampedBinaryEvidence.revise
    (positiveStampedEvidence A B)
    (negativeStampedEvidence A B)

theorem finiteInheritanceStampedEvidence_guardedRevise_eq_some
    (A B : DualConcept Obj Attr) :
    StampedBinaryEvidence.guardedRevise
      (positiveStampedEvidence A B)
      (negativeStampedEvidence A B) =
        some (finiteInheritanceStampedEvidence A B) := by
  simpa [finiteInheritanceStampedEvidence] using
    StampedBinaryEvidence.guardedRevise_eq_some_of_stampDisjoint
      (positiveStampedEvidence A B)
      (negativeStampedEvidence A B)
      (positive_negative_stampDisjoint A B)

theorem finiteInheritanceStampedEvidence_evidence_eq
    (A B : DualConcept Obj Attr) :
    (finiteInheritanceStampedEvidence A B).evidence = finiteInheritanceEvidence A B := by
  ext <;>
    simp [finiteInheritanceStampedEvidence, positiveStampedEvidence,
      negativeStampedEvidence, positiveExtensionalStampedEvidence,
      negativeExtensionalStampedEvidence, positiveIntensionalStampedEvidence,
      negativeIntensionalStampedEvidence, finiteInheritanceEvidence,
      BinaryEvidence.hplus_def]

theorem finiteInheritanceStampedEvidence_stamp
    (A B : DualConcept Obj Attr) :
    (finiteInheritanceStampedEvidence A B).stamp =
      (finitePositiveExtensionalWitnesses A B).map posExtEmbedding ∪
        (finitePositiveIntensionalWitnesses A B).map posIntEmbedding ∪
        (finiteNegativeExtensionalWitnesses A B).map negExtEmbedding ∪
        (finiteNegativeIntensionalWitnesses A B).map negIntEmbedding := by
  simp [finiteInheritanceStampedEvidence, positiveStampedEvidence,
    negativeStampedEvidence, positiveExtensionalStampedEvidence,
    negativeExtensionalStampedEvidence, positiveIntensionalStampedEvidence,
    negativeIntensionalStampedEvidence, StampedBinaryEvidence.revise,
    StampedBinaryEvidence.StampConcat, Mettapedia.Evidence.SourceScope.merge,
    Finset.union_assoc]

theorem negativeStampedEvidence_stamp_eq_empty_of_inherits
    {A B : DualConcept Obj Attr} (hAB : Inherits A B) :
    (negativeStampedEvidence A B).stamp = ∅ := by
  simp [negativeStampedEvidence, negativeExtensionalStampedEvidence,
    negativeIntensionalStampedEvidence,
    (finiteNegativeExtensionalWitnesses_eq_empty_iff _ _).mpr hAB.1,
    (finiteNegativeIntensionalWitnesses_eq_empty_iff _ _).mpr hAB.2]

end Finite

end DualConcept

namespace Interpretation

variable {Carrier : Type u} {Obj : Type v} {Attr : Type w}
variable [Fintype Obj] [DecidableEq Obj] [Fintype Attr] [DecidableEq Attr]

/-- Stamped finite witness-evidence view of an abstract interpretation. -/
noncomputable def finiteInheritanceStampedEvidence
    (I : Interpretation Carrier Obj Attr) (a b : Carrier) :
    StampedBinaryEvidence (DualConcept.WitnessStamp Obj Attr) :=
  DualConcept.finiteInheritanceStampedEvidence (I.meaning a) (I.meaning b)

theorem finiteInheritanceStampedEvidence_evidence_eq
    (I : Interpretation Carrier Obj Attr) (a b : Carrier) :
    (I.finiteInheritanceStampedEvidence a b).evidence =
      I.finiteInheritanceEvidence a b := by
  exact DualConcept.finiteInheritanceStampedEvidence_evidence_eq
    (I.meaning a) (I.meaning b)

theorem finiteInheritanceStampedEvidence_negative_stamp_eq_empty_of_inherits
    (I : Interpretation Carrier Obj Attr) {a b : Carrier}
    (hAB : I.Inherits a b) :
    (DualConcept.negativeStampedEvidence (I.meaning a) (I.meaning b)).stamp = ∅ := by
  exact DualConcept.negativeStampedEvidence_stamp_eq_empty_of_inherits hAB

theorem finiteInheritanceStampedEvidence_stamp
    (I : Interpretation Carrier Obj Attr) (a b : Carrier) :
    (I.finiteInheritanceStampedEvidence a b).stamp =
      (DualConcept.finitePositiveExtensionalWitnesses (I.meaning a) (I.meaning b)).map
          DualConcept.posExtEmbedding ∪
        (DualConcept.finitePositiveIntensionalWitnesses (I.meaning a) (I.meaning b)).map
          DualConcept.posIntEmbedding ∪
        (DualConcept.finiteNegativeExtensionalWitnesses (I.meaning a) (I.meaning b)).map
          DualConcept.negExtEmbedding ∪
        (DualConcept.finiteNegativeIntensionalWitnesses (I.meaning a) (I.meaning b)).map
          DualConcept.negIntEmbedding := by
  exact DualConcept.finiteInheritanceStampedEvidence_stamp (I.meaning a) (I.meaning b)

end Interpretation

end Mettapedia.KR.ConceptGeometry.AbstractInheritance

namespace Mettapedia.NARS.Bridges.PLN.InheritanceEvidence

open Mettapedia.KR.ConceptGeometry.AbstractInheritance

variable {Atom : Type u} {Obj : Type v} {Attr : Type w}
variable [DecidableEq Obj] [DecidableEq Attr]
variable [Fintype Obj] [Fintype Attr]

/-- Stamped witness aggregation for NARS inheritance. -/
noncomputable def inheritanceStampedEvidence
    (F : Mettapedia.NARS.Logic.Inheritance.Frame Atom Obj Attr)
    (s p : Mettapedia.NARS.Logic.Inheritance.Term Atom) :
    StampedBinaryEvidence (DualConcept.WitnessStamp Obj Attr) where
  evidence := evidence F s p
  stamp :=
    (F.positiveExtensionalWitnesses s p).map DualConcept.posExtEmbedding ∪
      (F.positiveIntensionalWitnesses s p).map DualConcept.posIntEmbedding ∪
      (F.negativeExtensionalWitnesses s p).map DualConcept.negExtEmbedding ∪
      (F.negativeIntensionalWitnesses s p).map DualConcept.negIntEmbedding

omit [Fintype Obj] [Fintype Attr] in
theorem inheritanceStampedEvidence_evidence_eq
    (F : Mettapedia.NARS.Logic.Inheritance.Frame Atom Obj Attr)
    (s p : Mettapedia.NARS.Logic.Inheritance.Term Atom) :
    (inheritanceStampedEvidence F s p).evidence = evidence F s p := rfl

theorem inheritanceStampedEvidence_eq_finiteInheritanceStampedEvidence
    (F : Mettapedia.NARS.Logic.Inheritance.Frame Atom Obj Attr)
    (s p : Mettapedia.NARS.Logic.Inheritance.Term Atom) :
    inheritanceStampedEvidence F s p =
      DualConcept.finiteInheritanceStampedEvidence
        ((F.interpretation).meaning s) ((F.interpretation).meaning p) := by
  apply StampedBinaryEvidence.ext
  · rw [inheritanceStampedEvidence_evidence_eq,
      DualConcept.finiteInheritanceStampedEvidence_evidence_eq]
    exact evidence_eq_finiteInheritanceEvidence F s p
  · simp only [inheritanceStampedEvidence, DualConcept.finiteInheritanceStampedEvidence_stamp,
      ← F.positiveExtensionalWitnesses_eq_finite, ← F.negativeExtensionalWitnesses_eq_finite,
      ← F.positiveIntensionalWitnesses_eq_finite, ← F.negativeIntensionalWitnesses_eq_finite]

theorem inheritanceStampedEvidence_negative_stamp_eq_empty_of_inherits
    (F : Mettapedia.NARS.Logic.Inheritance.Frame Atom Obj Attr)
    {s p : Mettapedia.NARS.Logic.Inheritance.Term Atom}
    (hsp : F.Inherits s p) :
    (DualConcept.negativeStampedEvidence
      ((F.interpretation).meaning s) ((F.interpretation).meaning p)).stamp = ∅ := by
  exact DualConcept.negativeStampedEvidence_stamp_eq_empty_of_inherits hsp

end Mettapedia.NARS.Bridges.PLN.InheritanceEvidence

namespace Mettapedia.KR.ConceptGeometry.AbstractInheritance.Interpretation

open Mettapedia.NARS.Logic.Inheritance

variable {Carrier : Type u} {Obj : Type v} {Attr : Type w}
variable [Fintype Obj] [DecidableEq Obj] [Fintype Attr] [DecidableEq Attr]

theorem toNARSFrame_inheritanceStampedEvidence_atom_eq_finiteInheritanceStampedEvidence
    (I : Mettapedia.KR.ConceptGeometry.AbstractInheritance.Interpretation Carrier Obj Attr)
    (a b : Carrier) :
    Mettapedia.NARS.Bridges.PLN.InheritanceEvidence.inheritanceStampedEvidence
        I.toNARSFrame (.atom a) (.atom b) =
      I.finiteInheritanceStampedEvidence a b := by
  simpa [finiteInheritanceStampedEvidence,
    Mettapedia.KR.ConceptGeometry.AbstractInheritance.Interpretation.toNARSFrame_meaning_atom_eq] using
    (Mettapedia.NARS.Bridges.PLN.InheritanceEvidence.inheritanceStampedEvidence_eq_finiteInheritanceStampedEvidence
      I.toNARSFrame (.atom a) (.atom b))

end Mettapedia.KR.ConceptGeometry.AbstractInheritance.Interpretation
