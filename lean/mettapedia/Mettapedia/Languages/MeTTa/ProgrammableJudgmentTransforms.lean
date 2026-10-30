import Mettapedia.GSLT.LanguageDef.CheckedSourceOpen
import Mettapedia.Languages.MeTTa.TransformComposition

/-!
# Checked judgment publication through transform spans

One span reads the selected source, takes one pending application and produces
its exact checked evidence. Source data are retained; the pending occurrence
is consumed. Evidence validity follows from the existing checker, rather than
from the name of a stored record. This models those commits, not arbitrary
space writes, grant authority or the implementation of an atomic C commit.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ProgrammableJudgmentTransforms

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.CheckedSource
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open TransformComposition

/-- The concrete resources of an open-rule checking client. Theory and
judgment data remain in both work and evidence; no tag grants authority. -/
inductive Cell where
  | current (source : GSLTSource)
  | waiting (ticket : Nat) (source : GSLTSource) (premises ambient : List Pattern)
      (goal : Pattern) (program : RawOpenProof)
  | answer (ticket : Nat) (arguments : List RawOpenProof)
  | work (ticket : Nat) (source : GSLTSource) (premises ambient : List Pattern) (goal : Pattern)
      (program : RawOpenProof) (arguments : List RawOpenProof)
  | evidence (ticket : Nat) (source : GSLTSource) (ambient : List Pattern)
      (goal : Pattern) (proof : RawOpenProof)

def publication (source : GSLTSource) (ticket : Nat) (premises ambient : List Pattern)
    (goal : Pattern) (program : RawOpenProof) (arguments : List RawOpenProof)
    (result : RawOpenProof) : Span Cell where
  consume := {Cell.work ticket source premises ambient goal program arguments}
  read := {Cell.current source}
  produce := {Cell.evidence ticket source ambient goal result}

/-- Receiving an untrusted argument proposal only prepares work. It cannot
produce an evidence row. The reply and waiting occurrence are both taken. -/
def preparation (source : GSLTSource) (ticket : Nat) (premises ambient : List Pattern)
    (goal : Pattern) (program : RawOpenProof) (arguments : List RawOpenProof) : Span Cell where
  consume := {Cell.waiting ticket source premises ambient goal program} + {Cell.answer ticket arguments}
  read := 0
  produce := {Cell.work ticket source premises ambient goal program arguments}

def EvidenceValid (source : GSLTSource) (ambient : List Pattern) (goal : Pattern)
    (proof : RawOpenProof) : Prop :=
  ∃ checked : CheckedGSLT, source.validate = .ok checked ∧
    checkOpenRaw checked.definition ambient goal proof = true

def StoreValid (store : Multiset Cell) : Prop :=
  ∀ ticket source ambient goal proof, Cell.evidence ticket source ambient goal proof ∈ store →
    EvidenceValid source ambient goal proof

theorem checked_result_valid {source : GSLTSource} {premises ambient : List Pattern}
    {goal : Pattern} {program result : RawOpenProof} {arguments : List RawOpenProof}
    (accepted : source.applyOpen premises ambient goal program arguments = .ok (some (source, result))) :
    EvidenceValid source ambient goal result := by
  obtain ⟨_, checked, validated, rule, supplied, _, _, output⟩ := GSLTSource.applyOpen_exact accepted
  refine ⟨checked, validated, ?_⟩
  rw [← output]
  exact checkOpenRaw_erase (rule.bind supplied)

section Commits

variable [DecidableEq Cell]

theorem preparation_preserves_validity (source : GSLTSource) (ticket : Nat)
    (premises ambient : List Pattern) (goal : Pattern) (program : RawOpenProof)
    (arguments : List RawOpenProof) (store : Multiset Cell) (valid : StoreValid store) :
    StoreValid ((preparation source ticket premises ambient goal program arguments).fire store) := by
  intro id suppliedSource context conclusion proof member
  simp only [Span.fire, preparation, Multiset.mem_add, Multiset.mem_singleton] at member
  rcases member with retained | impossible
  · exact valid _ _ _ _ _ (Multiset.mem_of_le (Multiset.sub_le_self _ _) retained)
  · cases impossible

/-- Only actual source admission and proof checking authorize a publishing
step. The store must still contain the read source and pending work together. -/
inductive Step : Multiset Cell → Multiset Cell → Prop where
  | publish (source : GSLTSource) (ticket : Nat) (premises ambient : List Pattern)
      (goal : Pattern) (program : RawOpenProof) (arguments : List RawOpenProof)
      (result : RawOpenProof) (store : Multiset Cell)
      (accepted : source.applyOpen premises ambient goal program arguments = .ok (some (source, result)))
      (enabled : (publication source ticket premises ambient goal program arguments result).Enables store) :
      Step store ((publication source ticket premises ambient goal program arguments result).fire store)

theorem publication_preserves_validity (source : GSLTSource) (ticket : Nat)
    (premises ambient : List Pattern) (goal : Pattern) (program : RawOpenProof)
    (arguments : List RawOpenProof) (result : RawOpenProof) (store : Multiset Cell)
    (accepted : source.applyOpen premises ambient goal program arguments = .ok (some (source, result)))
    (valid : StoreValid store) :
    StoreValid ((publication source ticket premises ambient goal program arguments result).fire store) := by
  intro id suppliedSource context conclusion proof member
  simp only [Span.fire, publication, Multiset.mem_add, Multiset.mem_singleton] at member
  rcases member with retained | produced
  · exact valid _ _ _ _ _ (Multiset.mem_of_le (Multiset.sub_le_self _ _) retained)
  · cases produced
    exact checked_result_valid accepted

theorem step_preserves_validity {before after : Multiset Cell}
    (step : Step before after) (valid : StoreValid before) : StoreValid after := by
  cases step with
  | publish source ticket premises ambient goal program arguments result store accepted _ =>
      exact publication_preserves_validity source ticket premises ambient goal program arguments result _ accepted valid

/-- Read sources survive a commit with exactly their previous multiplicity. -/
theorem publication_keeps_sources (source observed : GSLTSource) (ticket : Nat)
    (premises ambient : List Pattern) (goal : Pattern) (program : RawOpenProof)
    (arguments : List RawOpenProof) (result : RawOpenProof) (store : Multiset Cell) :
    ((publication source ticket premises ambient goal program arguments result).fire store).count (.current observed) =
      store.count (.current observed) := by
  simp [Span.fire, publication, Multiset.count_add]

/-- A single pending occurrence cannot authorize the same commit twice. -/
theorem no_second_consumption (source : GSLTSource) (ticket : Nat)
    (premises ambient : List Pattern) (goal : Pattern) (program : RawOpenProof)
    (arguments : List RawOpenProof) (result : RawOpenProof) (store : Multiset Cell)
    (one : store.count (.work ticket source premises ambient goal program arguments) = 1) :
    ¬(publication source ticket premises ambient goal program arguments result).Enables
      ((publication source ticket premises ambient goal program arguments result).fire store) := by
  intro enabled
  have count := Multiset.le_iff_count.mp enabled (.work ticket source premises ambient goal program arguments)
  simp [Span.fire, publication, Multiset.count_add, one] at count

/-- A later source object cannot satisfy the earlier source read merely
because both belong to the same store. -/
theorem changed_source_blocks_commit (source changed : GSLTSource) (different : changed ≠ source)
    (ticket : Nat) (premises ambient : List Pattern) (goal : Pattern)
    (program : RawOpenProof) (arguments : List RawOpenProof) (result : RawOpenProof) :
    ¬(publication source ticket premises ambient goal program arguments result).Enables
      ({Cell.current changed} + {Cell.work ticket source premises ambient goal program arguments}) := by
  intro enabled
  have count := Multiset.le_iff_count.mp enabled (.current source)
  simp [publication, Ne.symm different] at count

omit [DecidableEq Cell] in
/-- Adding another source object does not revoke the old one. Revision
replacement must actually retire its old authority; a new tag alone does not. -/
theorem retaining_source_keeps_old_request_enabled (source changed : GSLTSource)
    (ticket : Nat) (premises ambient : List Pattern) (goal : Pattern)
    (program : RawOpenProof) (arguments : List RawOpenProof) (result : RawOpenProof) :
    (publication source ticket premises ambient goal program arguments result).Enables
      ({Cell.work ticket source premises ambient goal program arguments} +
        {Cell.current source} + {Cell.current changed}) := by
  exact Multiset.le_add_right _ _

omit [DecidableEq Cell] in
/-- An unchecked evidence constructor can violate the invariant. Neither
its data shape nor the presence of a source tag replaces the actual checker. -/
theorem refused_evidence_write_breaks_validity (source : GSLTSource)
    (checked : CheckedGSLT) (validated : source.validate = .ok checked)
    (ambient : List Pattern) (goal : Pattern) (proof : RawOpenProof)
    (refused : checkOpenRaw checked.definition ambient goal proof = false)
    (ticket : Nat) (store : Multiset Cell) :
    ¬ StoreValid ({Cell.evidence ticket source ambient goal proof} + store) := by
  intro valid
  obtain ⟨actual, admission, accepted⟩ :=
    valid ticket source ambient goal proof (by simp)
  have same : actual = checked := Except.ok.inj (admission.symm.trans validated)
  subst actual
  simp [refused] at accepted

/-- The real preparation/publication pipeline satisfies the existing span
fusion contract. Its intermediate work row can remain unmaterialized. -/
theorem prepare_publish_fusion (source : GSLTSource) (ticket : Nat)
    (premises ambient : List Pattern) (goal : Pattern) (program : RawOpenProof)
    (arguments : List RawOpenProof) (result : RawOpenProof) (store : Multiset Cell) :
    let first := preparation source ticket premises ambient goal program arguments
    let second := publication source ticket premises ambient goal program arguments result
    ((first.fuse second).Enables store ↔ first.Enables store ∧ second.Enables (first.fire store)) ∧
      (first.fuse second).fire store = second.fire (first.fire store) ∧
      (first.fuse second).produce = second.produce := by
  exact ⟨Span.fuse_enables_iff _ _ _ le_rfl, Span.fuse_fire _ _ _ le_rfl,
    Span.fuse_produce_of_handoff _ _ rfl⟩

theorem fused_publication_preserves_validity (source : GSLTSource) (ticket : Nat)
    (premises ambient : List Pattern) (goal : Pattern) (program : RawOpenProof)
    (arguments : List RawOpenProof) (result : RawOpenProof) (store : Multiset Cell)
    (accepted : source.applyOpen premises ambient goal program arguments = .ok (some (source, result)))
    (valid : StoreValid store) :
    StoreValid (((preparation source ticket premises ambient goal program arguments).fuse
      (publication source ticket premises ambient goal program arguments result)).fire store) := by
  rw [(prepare_publish_fusion source ticket premises ambient goal program arguments result store).2.1]
  exact publication_preserves_validity source ticket premises ambient goal program arguments result _ accepted
    (preparation_preserves_validity source ticket premises ambient goal program arguments store valid)

omit [DecidableEq Cell] in
/-- The publisher always has a meaningful enabling state for a checked
application: one source occurrence and one actual pending item. -/
theorem initial_publication_enabled (source : GSLTSource) (ticket : Nat)
    (premises ambient : List Pattern) (goal : Pattern) (program : RawOpenProof)
    (arguments : List RawOpenProof) (result : RawOpenProof) :
    (publication source ticket premises ambient goal program arguments result).Enables
      ({Cell.work ticket source premises ambient goal program arguments} + {Cell.current source}) := le_rfl

end Commits

/-- A stored checked result reconstructs a source-indexed derivation, with
the exact raw artifact, rather than trusting its storage tag. -/
theorem stored_evidence_derivation {store : Multiset Cell} (valid : StoreValid store)
    {ticket : Nat} {source : GSLTSource} {ambient : List Pattern} {goal : Pattern} {proof : RawOpenProof}
    (present : Cell.evidence ticket source ambient goal proof ∈ store) :
    ∃ checked : CheckedGSLT, source.validate = .ok checked ∧
      ∃ derivation : OpenDerivation checked.definition ambient goal, derivation.eraseOpen = proof := by
  obtain ⟨checked, validated, accepted⟩ := valid _ _ _ _ _ present
  exact ⟨checked, validated, checkOpenRaw_exact_derivation accepted⟩

#print axioms step_preserves_validity
#print axioms no_second_consumption
#print axioms changed_source_blocks_commit
#print axioms retaining_source_keeps_old_request_enabled
#print axioms refused_evidence_write_breaks_validity
#print axioms stored_evidence_derivation
#print axioms prepare_publish_fusion
#print axioms fused_publication_preserves_validity

end Mettapedia.Languages.MeTTa.ProgrammableJudgmentTransforms
