import Mettapedia.Logic.ConceptOntology.FCARecovery

/-!
# World-Model Formal Concept Analysis

This module supplies the provenance-aware state semantics beneath WM/FCA.
Classical FCA remains the exact late projection, while revision, forgetting,
dependence grouping, and contextual envelopes live at the evidence layer.

The provenance state deliberately uses finite stamp sets rather than pretending
that idempotent revision is an additive monoid. Evidence extraction is additive
for disjoint revisions; overlapping revisions are deduplicated by stamp.
-/

namespace Mettapedia.Logic.ConceptOntology.WMFCA

open scoped BigOperators
open Mettapedia.Logic.AbstractInheritance

universe uStamp uSource uGroup uObj uAttr uEv uModel

/-- Immutable metadata and query-local evidence carried by each provenance
stamp. A stamp has one fixed source, dependence group, and evidence profile, so
reusing a stamp with conflicting content is unrepresentable. -/
structure ProvenanceCatalog
    (Stamp : Type uStamp) (Source : Type uSource) (Group : Type uGroup)
    (Obj : Type uObj) (Attr : Type uAttr) (Ev : Type uEv) where
  source : Stamp → Source
  group : Stamp → Group
  observe : Stamp → Obj → Attr → Ev

/-- A WM/FCA state is the finite set of active provenance stamps. -/
abbrev ProvenanceState (Stamp : Type uStamp) := Finset Stamp

section Provenance

variable {Stamp : Type uStamp} {Source : Type uSource} {Group : Type uGroup}
variable {Obj : Type uObj} {Attr : Type uAttr} {Ev : Type uEv}
variable [DecidableEq Stamp] [AddCommMonoid Ev]

/-- Query-local evidence is the sum of the active stamped contributions. -/
def evidence
    (C : ProvenanceCatalog Stamp Source Group Obj Attr Ev)
    (W : ProvenanceState Stamp) (x : Obj) (a : Attr) : Ev :=
  ∑ stamp ∈ W, C.observe stamp x a

/-- Revision activates every stamp present in either state. -/
def revise (W Δ : ProvenanceState Stamp) : ProvenanceState Stamp := W ∪ Δ

/-- Forgetting removes an explicit finite set of provenance stamps. -/
def forget (S W : ProvenanceState Stamp) : ProvenanceState Stamp := W \ S

@[simp] theorem revise_empty_left (W : ProvenanceState Stamp) :
    revise ∅ W = W := by
  simp [revise]

@[simp] theorem revise_empty_right (W : ProvenanceState Stamp) :
    revise W ∅ = W := by
  simp [revise]

@[simp] theorem revise_self (W : ProvenanceState Stamp) :
    revise W W = W := by
  simp [revise]

theorem revise_comm (W Δ : ProvenanceState Stamp) :
    revise W Δ = revise Δ W := by
  simp [revise, Finset.union_comm]

theorem revise_assoc (W Δ Ξ : ProvenanceState Stamp) :
    revise (revise W Δ) Ξ = revise W (revise Δ Ξ) := by
  simp [revise, Finset.union_assoc]

@[simp] theorem forget_idempotent (S W : ProvenanceState Stamp) :
    forget S (forget S W) = forget S W := by
  ext stamp
  simp [forget]

theorem forget_revision_of_disjoint
    {W Δ : ProvenanceState Stamp} (h : Disjoint W Δ) :
    forget Δ (revise W Δ) = W := by
  ext stamp
  constructor
  · intro hmem
    have hparts := Finset.mem_sdiff.mp hmem
    rcases Finset.mem_union.mp hparts.1 with hW | hΔ
    · exact hW
    · exact False.elim (hparts.2 hΔ)
  · intro hW
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_union_left Δ hW, ?_⟩
    exact fun hΔ => Finset.disjoint_left.mp h hW hΔ

omit [DecidableEq Stamp] in
@[simp] theorem evidence_empty
    (C : ProvenanceCatalog Stamp Source Group Obj Attr Ev) (x : Obj) (a : Attr) :
    evidence C ∅ x a = 0 := by
  simp [evidence]

omit [DecidableEq Stamp] in
@[simp] theorem evidence_singleton
    (C : ProvenanceCatalog Stamp Source Group Obj Attr Ev)
    (stamp : Stamp) (x : Obj) (a : Attr) :
    evidence C {stamp} x a = C.observe stamp x a := by
  simp [evidence]

/-- The ordinary additive revision law is valid exactly on the fresh-stamp
lane. No independence or freshness assumption is hidden. -/
theorem evidence_revise_of_disjoint
    (C : ProvenanceCatalog Stamp Source Group Obj Attr Ev)
    {W Δ : ProvenanceState Stamp} (h : Disjoint W Δ) (x : Obj) (a : Attr) :
    evidence C (revise W Δ) x a = evidence C W x a + evidence C Δ x a := by
  simp [evidence, revise, Finset.sum_union h]

/-- Exact duplicate revision changes neither the state nor extracted evidence. -/
@[simp] theorem evidence_revise_self
    (C : ProvenanceCatalog Stamp Source Group Obj Attr Ev)
    (W : ProvenanceState Stamp) (x : Obj) (a : Attr) :
    evidence C (revise W W) x a = evidence C W x a := by
  rw [revise_self]

/-- Forgetting a fresh revision and recomputing from surviving stamps recovers
the original evidence exactly. -/
theorem evidence_forget_revision_of_disjoint
    (C : ProvenanceCatalog Stamp Source Group Obj Attr Ev)
    {W Δ : ProvenanceState Stamp} (h : Disjoint W Δ) (x : Obj) (a : Attr) :
    evidence C (forget Δ (revise W Δ)) x a = evidence C W x a := by
  rw [forget_revision_of_disjoint h]

/-- Stamps contributing nonzero evidence to one object/attribute cell. -/
noncomputable def contributingStamps
    (C : ProvenanceCatalog Stamp Source Group Obj Attr Ev)
    (W : ProvenanceState Stamp) (x : Obj) (a : Attr) : Finset Stamp :=
  by
    classical
    exact W.filter fun stamp => C.observe stamp x a ≠ 0

omit [DecidableEq Stamp] in
theorem contributingStamps_subset
    (C : ProvenanceCatalog Stamp Source Group Obj Attr Ev)
    (W : ProvenanceState Stamp) (x : Obj) (a : Attr) :
    contributingStamps C W x a ⊆ W := by
  classical
  exact Finset.filter_subset _ _

@[simp] theorem contributingStamps_revise
    (C : ProvenanceCatalog Stamp Source Group Obj Attr Ev)
    (W Δ : ProvenanceState Stamp) (x : Obj) (a : Attr) :
    contributingStamps C (revise W Δ) x a =
      contributingStamps C W x a ∪ contributingStamps C Δ x a := by
  classical
  ext stamp
  simp only [contributingStamps, revise, Finset.mem_filter, Finset.mem_union]
  tauto

@[simp] theorem contributingStamps_forget
    (C : ProvenanceCatalog Stamp Source Group Obj Attr Ev)
    (S W : ProvenanceState Stamp) (x : Obj) (a : Attr) :
    contributingStamps C (forget S W) x a = contributingStamps C W x a \ S := by
  classical
  ext stamp
  simp only [contributingStamps, forget, Finset.mem_filter, Finset.mem_sdiff]
  tauto

variable [DecidableEq Group]

/-- Dependence groups represented among the nonzero contributions to a cell. -/
noncomputable def contributingGroups
    (C : ProvenanceCatalog Stamp Source Group Obj Attr Ev)
    (W : ProvenanceState Stamp) (x : Obj) (a : Attr) : Finset Group :=
  (contributingStamps C W x a).image C.group

@[simp] theorem contributingGroups_revise
    (C : ProvenanceCatalog Stamp Source Group Obj Attr Ev)
    (W Δ : ProvenanceState Stamp) (x : Obj) (a : Attr) :
    contributingGroups C (revise W Δ) x a =
      contributingGroups C W x a ∪ contributingGroups C Δ x a := by
  classical
  rw [contributingGroups, contributingStamps_revise, Finset.image_union]
  rfl

/-- A correlated revision whose groups are already represented cannot inflate
the dependence-group support of a cell. -/
theorem contributingGroups_revise_eq_left_of_subset
    (C : ProvenanceCatalog Stamp Source Group Obj Attr Ev)
    {W Δ : ProvenanceState Stamp} {x : Obj} {a : Attr}
    (h : contributingGroups C Δ x a ⊆ contributingGroups C W x a) :
    contributingGroups C (revise W Δ) x a = contributingGroups C W x a := by
  rw [contributingGroups_revise]
  exact Finset.union_eq_left.mpr h

/-- The dependence-aware cell statistic counts represented groups, not raw
stamps or nominal sources. -/
noncomputable def groupCount
    (C : ProvenanceCatalog Stamp Source Group Obj Attr Ev)
    (W : ProvenanceState Stamp) (x : Obj) (a : Attr) : Nat :=
  (contributingGroups C W x a).card

theorem groupCount_revise_eq_left_of_subset
    (C : ProvenanceCatalog Stamp Source Group Obj Attr Ev)
    {W Δ : ProvenanceState Stamp} {x : Obj} {a : Attr}
    (h : contributingGroups C Δ x a ⊆ contributingGroups C W x a) :
    groupCount C (revise W Δ) x a = groupCount C W x a := by
  unfold groupCount
  rw [contributingGroups_revise_eq_left_of_subset C h]

end Provenance

section FCAProjection

variable {Stamp : Type uStamp} {Source : Type uSource} {Group : Type uGroup}
variable {Obj : Type uObj} {Attr : Type uAttr} {Ev : Type uEv}
variable [DecidableEq Stamp] [AddCommMonoid Ev] [Preorder Ev]
variable [Fintype Obj] [Fintype Attr]

/-- Exact classical concepts extracted from one provenance state and gate. -/
noncomputable def finiteConceptFamily
    (C : ProvenanceCatalog Stamp Source Group Obj Attr Ev)
    (G : EvidenceGate Ev) (W : ProvenanceState Stamp) :
    Finset (DualConcept Obj Attr) :=
  AbstractInheritance.finiteConceptFamily G (evidence C W)

@[simp] theorem finiteConceptFamily_revise_self
    (C : ProvenanceCatalog Stamp Source Group Obj Attr Ev)
    (G : EvidenceGate Ev) (W : ProvenanceState Stamp) :
    finiteConceptFamily C G (revise W W) = finiteConceptFamily C G W := by
  rw [revise_self]

theorem finiteConceptFamily_forget_revision_of_disjoint
    (C : ProvenanceCatalog Stamp Source Group Obj Attr Ev)
    (G : EvidenceGate Ev) {W Δ : ProvenanceState Stamp} (h : Disjoint W Δ) :
    finiteConceptFamily C G (forget Δ (revise W Δ)) = finiteConceptFamily C G W := by
  rw [forget_revision_of_disjoint h]

omit [Fintype Obj] [Fintype Attr] in
/-- On fresh stamps, the revised crisp relation is exactly the gate applied to
the sum of the two evidence profiles. -/
theorem crispRelation_revise_of_disjoint
    (C : ProvenanceCatalog Stamp Source Group Obj Attr Ev)
    (G : EvidenceGate Ev) {W Δ : ProvenanceState Stamp} (h : Disjoint W Δ)
    (x : Obj) (a : Attr) :
    crispRelation G (evidence C (revise W Δ)) x a ↔
      G.accept (evidence C W x a + evidence C Δ x a) := by
  change G.accept (evidence C (revise W Δ) x a) ↔ _
  rw [evidence_revise_of_disjoint C h]

end FCAProjection

section FCAGroupProjection

variable {Stamp : Type uStamp} {Source : Type uSource} {Group : Type uGroup}
variable {Obj : Type uObj} {Attr : Type uAttr} {Ev : Type uEv}
variable [DecidableEq Stamp] [DecidableEq Group] [AddCommMonoid Ev]
variable [Fintype Obj] [Fintype Attr]

/-- FCA formed from a dependence-group threshold is invariant to a correlated
revision when every added group is already represented at every cell. -/
theorem groupCountConceptFamily_revise_eq_left_of_groups_subset
    (C : ProvenanceCatalog Stamp Source Group Obj Attr Ev)
    (threshold : Nat) {W Δ : ProvenanceState Stamp}
    (hgroups : ∀ x a,
      contributingGroups C Δ x a ⊆ contributingGroups C W x a) :
    AbstractInheritance.finiteConceptFamily
        (EvidenceGate.threshold threshold) (groupCount C (revise W Δ)) =
      AbstractInheritance.finiteConceptFamily
        (EvidenceGate.threshold threshold) (groupCount C W) := by
  have hprofile : groupCount C (revise W Δ) = groupCount C W := by
    funext x a
    exact groupCount_revise_eq_left_of_subset C (hgroups x a)
  rw [hprofile]

end FCAGroupProjection

section ContextualEnvelope

variable {Obj : Type uObj} {Attr : Type uAttr} {Ev : Type uEv}
variable [Preorder Ev]

/-- One admissible contextual model chooses both an evidence profile and the
gate used to extract its crisp incidence relation. -/
structure ContextModel where
  membership : Obj → Attr → Ev
  gate : EvidenceGate Ev

namespace ContextModel

/-- Incidence accepted by one contextual model. -/
def accepted (θ : ContextModel (Obj := Obj) (Attr := Attr) (Ev := Ev)) :
    Obj → Attr → Prop :=
  crispRelation θ.gate θ.membership

end ContextModel

/-- Robust incidence is accepted in every retained contextual model. -/
def robustRelation
    (Θ : Set (ContextModel (Obj := Obj) (Attr := Attr) (Ev := Ev))) :
    Obj → Attr → Prop :=
  fun x a => ∀ θ ∈ Θ, θ.accepted x a

/-- Permissive incidence is accepted in at least one retained contextual model. -/
def permissiveRelation
    (Θ : Set (ContextModel (Obj := Obj) (Attr := Attr) (Ev := Ev))) :
    Obj → Attr → Prop :=
  fun x a => ∃ θ ∈ Θ, θ.accepted x a

theorem robustRelation_implies_permissiveRelation
    {Θ : Set (ContextModel (Obj := Obj) (Attr := Attr) (Ev := Ev))}
    (hne : Θ.Nonempty) {x : Obj} {a : Attr} :
    robustRelation Θ x a → permissiveRelation Θ x a := by
  intro hrobust
  rcases hne with ⟨θ, hθ⟩
  exact ⟨θ, hθ, hrobust θ hθ⟩

theorem robustRelation_antitone
    {Θ₁ Θ₂ : Set (ContextModel (Obj := Obj) (Attr := Attr) (Ev := Ev))}
    (hsub : Θ₁ ⊆ Θ₂) {x : Obj} {a : Attr} :
    robustRelation Θ₂ x a → robustRelation Θ₁ x a := by
  intro h θ hθ
  exact h θ (hsub hθ)

theorem permissiveRelation_monotone
    {Θ₁ Θ₂ : Set (ContextModel (Obj := Obj) (Attr := Attr) (Ev := Ev))}
    (hsub : Θ₁ ⊆ Θ₂) {x : Obj} {a : Attr} :
    permissiveRelation Θ₁ x a → permissiveRelation Θ₂ x a := by
  rintro ⟨θ, hθ, hacc⟩
  exact ⟨θ, hsub hθ, hacc⟩

@[simp] theorem robustRelation_singleton
    (θ : ContextModel (Obj := Obj) (Attr := Attr) (Ev := Ev))
    (x : Obj) (a : Attr) :
    robustRelation {θ} x a ↔ θ.accepted x a := by
  simp [robustRelation]

@[simp] theorem permissiveRelation_singleton
    (θ : ContextModel (Obj := Obj) (Attr := Attr) (Ev := Ev))
    (x : Obj) (a : Attr) :
    permissiveRelation {θ} x a ↔ θ.accepted x a := by
  simp [permissiveRelation]

/-- A lower/upper contextual incidence view with its ordering obligation. -/
structure IncidenceEnvelope where
  lower : Obj → Attr → Prop
  upper : Obj → Attr → Prop
  lower_le_upper : ∀ x a, lower x a → upper x a

/-- The robust/permissive envelope of a nonempty contextual model family. -/
def contextualEnvelope
    (Θ : Set (ContextModel (Obj := Obj) (Attr := Attr) (Ev := Ev)))
    (hne : Θ.Nonempty) : IncidenceEnvelope (Obj := Obj) (Attr := Attr) where
  lower := robustRelation Θ
  upper := permissiveRelation Θ
  lower_le_upper := fun _ _ => robustRelation_implies_permissiveRelation hne

section Finite

variable [Fintype Obj] [Fintype Attr]

/-- Exact FCA concepts common to every retained contextual model. -/
noncomputable def robustConceptFamily
    (Θ : Set (ContextModel (Obj := Obj) (Attr := Attr) (Ev := Ev))) :
    Finset (DualConcept Obj Attr) :=
  AbstractInheritance.finiteClosedConceptFamily (robustRelation Θ)

/-- Exact FCA concepts induced by incidence accepted in at least one retained
contextual model. -/
noncomputable def permissiveConceptFamily
    (Θ : Set (ContextModel (Obj := Obj) (Attr := Attr) (Ev := Ev))) :
    Finset (DualConcept Obj Attr) :=
  AbstractInheritance.finiteClosedConceptFamily (permissiveRelation Θ)

@[simp] theorem robustConceptFamily_singleton
    (θ : ContextModel (Obj := Obj) (Attr := Attr) (Ev := Ev)) :
    robustConceptFamily {θ} =
      AbstractInheritance.finiteClosedConceptFamily θ.accepted := by
  have hrelation : robustRelation {θ} = θ.accepted := by
    funext x a
    apply propext
    simp
  rw [robustConceptFamily, hrelation]

@[simp] theorem permissiveConceptFamily_singleton
    (θ : ContextModel (Obj := Obj) (Attr := Attr) (Ev := Ev)) :
    permissiveConceptFamily {θ} =
      AbstractInheritance.finiteClosedConceptFamily θ.accepted := by
  have hrelation : permissiveRelation {θ} = θ.accepted := by
    funext x a
    apply propext
    simp
  rw [permissiveConceptFamily, hrelation]

end Finite

@[simp] theorem contextualEnvelope_singleton_lower
    (θ : ContextModel (Obj := Obj) (Attr := Attr) (Ev := Ev)) :
    (contextualEnvelope {θ} (Set.singleton_nonempty θ)).lower = θ.accepted := by
  funext x a
  simp [contextualEnvelope]

@[simp] theorem contextualEnvelope_singleton_upper
    (θ : ContextModel (Obj := Obj) (Attr := Attr) (Ev := Ev)) :
    (contextualEnvelope {θ} (Set.singleton_nonempty θ)).upper = θ.accepted := by
  funext x a
  simp [contextualEnvelope]

end ContextualEnvelope

/-! ## Executable semantic canaries -/

section Canaries

private def canaryCatalog :
    ProvenanceCatalog (Fin 3) Unit Bool Unit Unit Nat where
  source := fun _ => ()
  group := fun stamp => stamp.val == 2
  observe := fun _ _ _ => 1

private def canaryBase : ProvenanceState (Fin 3) := {0}
private def canaryCorrelated : ProvenanceState (Fin 3) := {1}
private def canaryIndependent : ProvenanceState (Fin 3) := {2}

/-- Positive canary: a distinct stamp in an already represented dependence
group does not inflate the group-count statistic. -/
theorem correlated_copy_group_count_canary :
    groupCount canaryCatalog (revise canaryBase canaryCorrelated) () () = 1 := by
  classical
  norm_num [groupCount, contributingGroups, contributingStamps, revise,
    canaryCatalog, canaryBase, canaryCorrelated]

/-- Negative canary: a genuinely independent dependence group does increase
the group-count statistic. -/
theorem independent_group_count_canary :
    groupCount canaryCatalog (revise canaryBase canaryIndependent) () () = 2 := by
  classical
  norm_num [groupCount, contributingGroups, contributingStamps, revise,
    canaryCatalog, canaryBase, canaryIndependent]

/-- Exact-duplicate canary at the evidence layer. -/
theorem exact_duplicate_evidence_canary :
    evidence canaryCatalog (revise canaryBase canaryBase) () () = 1 := by
  classical
  norm_num [evidence, contributingStamps, revise, canaryCatalog, canaryBase]

end Canaries

end Mettapedia.Logic.ConceptOntology.WMFCA
