import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16LeibnizRelationOperator
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FieldFiveCommutatorSeparator

/-!
# OUR joint rank lower bounds for the Leibniz-corrected relation operator

The certified lower bounds `11557` and `11558` of
`HypercubicDimension16JointTraceCommutatorRank` and
`HypercubicDimension16FieldFiveCommutatorSeparator` concern the joint
submodule built from the earlier commutator row.  This module proves both
bounds for the Leibniz-corrected joint submodule of
`HypercubicDimension16LeibnizRelationOperator`.

* The `11556` field-eight trace rows are not commutator rows, and the
  seven-to-eight commutator site has no outer derivative on its field, so all
  `11557` rows are unchanged; their independence transfers.
* The four-field site of the separator has six outer derivatives on its
  field, so its corrected row differs from the earlier one by the Leibniz
  terms `S ≠ ∅`.  None of them reaches the separator's orbit: for
  `S` a nonempty proper subset two field letters carry derivatives, while the
  target orbit has all six on one letter, and for `S` the full set the planes
  around the differentiated letter differ.  The field-five coordinate of the
  corrected row is therefore the same `-1/24`, and the bound `11558` holds for
  the corrected submodule.

These are lower bounds; they do not determine the full joint rank, the
quotient dimension, a relation census, or a conditioning bound.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16LeibnizJointRank

open scoped BigOperators

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus
open HypercubicRawFDDimension16Census
open HypercubicDimension16AlphaReduction
open HypercubicDimension16RelationEquivariance
open HypercubicDimension16CovariantCommutator
open HypercubicDimension16ContextualQuotient
open HypercubicDimension16AntisymmetryQuotient
open HypercubicDimension16ShuffleQuotient
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16OrbitCarrierBridge
open HypercubicDimension16PhysicalInvariantSpace
open HypercubicDimension16SignedOrbitCoinvariants
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16JointQuotientInvariants
open HypercubicDimension16JointPhysicalQuotient
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16PhysicalTraceQuotient
open HypercubicDimension16IncomingCommutatorTraceCertificate
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16IncomingCommutatorTraceCanonicalProjection
open HypercubicDimension16IncomingCommutatorTraceInvariantWitness
open HypercubicDimension16FieldEightTracePhysicalLift
open HypercubicDimension16JointTraceRankTransfer
open HypercubicDimension16JointTraceCommutatorRank
open HypercubicDimension16FieldFiveCommutatorSeparator
open HypercubicDimension16LeibnizCommutator
open HypercubicDimension16LeibnizRelationOperator

/-! ## Reynolds averages of corrected columns -/

theorem exactFieldOrbitReynolds_leibnizOrbit_mem
    (policy : PhysicalRelationPolicy)
    (value : PhysicalRelationGeneratorSpace policy) :
    exactFieldOrbitReynolds (leibnizOrbitPhysicalRelationOperator policy value) ∈
      leibnizOrbitPhysicalRelationSubmodule policy := by
  unfold exactFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply]
  apply (leibnizOrbitPhysicalRelationSubmodule policy).smul_mem
  apply Submodule.sum_mem
  intro h _
  apply leibnizOrbitPhysicalRelationSubmodule_signed_invariant policy h
  exact ⟨value, rfl⟩

theorem exactFieldOrbitReynolds_orbit_mem_leibniz
    {policy : PhysicalRelationPolicy}
    (generator : PhysicalRelationGenerator policy)
    (hrow : leibnizPhysicalRelationRow generator = physicalRelationRow generator) :
    exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy (Finsupp.single generator 1)) ∈
      leibnizOrbitPhysicalRelationSubmodule policy := by
  rw [← leibnizOrbitPhysicalRelationOperator_single_of_row_eq generator 1 hrow]
  exact exactFieldOrbitReynolds_leibnizOrbit_mem policy _

/-! ## The unchanged `11557` rows -/

theorem leibnizPhysicalRelationRow_liftFieldEightTrace
    (policy : PhysicalRelationPolicy) (generator : FieldEightTraceGenerator) :
    leibnizPhysicalRelationRow (ourLiftFieldEightTraceGenerator policy generator) =
      physicalRelationRow (ourLiftFieldEightTraceGenerator policy generator) := by
  cases generator <;> rfl

theorem outerSameOwnerPositions_ourFieldSevenCommutatorSite :
    outerSameOwnerPositions ourFieldSevenCommutatorSite = ∅ := by
  decide

theorem leibnizPhysicalRelationRow_ourFieldSevenCommutator
    (policy : PhysicalRelationPolicy) :
    leibnizPhysicalRelationRow (ourFieldSevenCommutatorGenerator policy) =
      physicalRelationRow (ourFieldSevenCommutatorGenerator policy) :=
  leibnizCommutatorRow_eq_covariantCommutatorRow _
    outerSameOwnerPositions_ourFieldSevenCommutatorSite

theorem ourInvariantFieldEightTraceRow_mem_leibniz
    (policy : PhysicalRelationPolicy) (generator : FieldEightTraceGenerator) :
    ourInvariantFieldEightTraceRow policy generator ∈
      leibnizJointInvariantRelationSubmodule policy := by
  rw [mem_leibnizJointInvariantRelationSubmodule_iff]
  exact exactFieldOrbitReynolds_orbit_mem_leibniz _
    (leibnizPhysicalRelationRow_liftFieldEightTrace policy generator)

theorem ourInvariantCommutatorRow_mem_leibniz
    (policy : PhysicalRelationPolicy) :
    ourInvariantCommutatorRow policy ∈
      leibnizJointInvariantRelationSubmodule policy := by
  rw [mem_leibnizJointInvariantRelationSubmodule_iff]
  exact exactFieldOrbitReynolds_orbit_mem_leibniz _
    (leibnizPhysicalRelationRow_ourFieldSevenCommutator policy)

/-- The selected field-eight trace rows are independent as vectors of the
ambient invariant space. -/
theorem ourInvariantFieldEightTraceRows_linearIndependent
    (policy : PhysicalRelationPolicy) :
    LinearIndependent ℚ (fun index : Fin 11556 =>
      ourInvariantFieldEightTraceRow policy (selectedPhysicalGenerator index)) := by
  apply LinearIndependent.of_comp ourExactFieldEightInvariantProjection
  have hfamily :
      ourExactFieldEightInvariantProjection ∘
          (fun index : Fin 11556 =>
            ourInvariantFieldEightTraceRow policy (selectedPhysicalGenerator index)) =
        fun index : Fin 11556 =>
          fieldEightReynoldsToInvariant
            (fieldEightPhysicalTraceRow (selectedPhysicalGenerator index)) := by
    funext index
    exact ourJointFieldEightInvariantProjection_traceRelation
      policy (selectedPhysicalGenerator index)
  rw [hfamily]
  exact selectedPhysicalInvariantRows_linearIndependent

/-- OUR exact field-eight trace projection on the ambient invariant space. -/
def ambientFieldEightTraceProjection :
    exactFieldOrbitInvariantSubmodule →ₗ[ℚ] FieldEightPhysicalTraceQuotient :=
  exactFieldEightTraceProjection.comp exactFieldOrbitInvariantSubmodule.subtype

/-- OUR field-five coordinate on the ambient invariant space. -/
def ambientFieldFiveCoordinate : exactFieldOrbitInvariantSubmodule →ₗ[ℚ] ℚ :=
  fieldFiveCoordinate.comp
    (exactFieldFiveProjection.comp exactFieldOrbitInvariantSubmodule.subtype)

theorem ambientFieldEightTraceProjection_traceRow
    (policy : PhysicalRelationPolicy) (generator : FieldEightTraceGenerator) :
    ambientFieldEightTraceProjection
        (ourInvariantFieldEightTraceRow policy generator) = 0 :=
  ourJointExactFieldEightTraceProjection_traceRelation_zero policy generator

theorem ambientFieldEightTraceProjection_commutatorRow
    (policy : PhysicalRelationPolicy) :
    ambientFieldEightTraceProjection (ourInvariantCommutatorRow policy) =
      literalIncomingCommutatorClass :=
  ourJointExactFieldEightTraceProjection_commutator policy

theorem ambientFieldFiveCoordinate_traceRow
    (policy : PhysicalRelationPolicy) (generator : FieldEightTraceGenerator) :
    ambientFieldFiveCoordinate
        (ourInvariantFieldEightTraceRow policy generator) = 0 :=
  ourJointFieldFiveCoordinate_traceRelation_zero policy generator

theorem ambientFieldFiveCoordinate_commutatorRow
    (policy : PhysicalRelationPolicy) :
    ambientFieldFiveCoordinate (ourInvariantCommutatorRow policy) = 0 :=
  ourJointFieldFiveCoordinate_commutator_zero policy

/-- The span of the `11556` trace rows in the ambient invariant space. -/
def ambientTraceSpan (policy : PhysicalRelationPolicy) :
    Submodule ℚ exactFieldOrbitInvariantSubmodule :=
  Submodule.span ℚ (Set.range fun index : Fin 11556 =>
    ourInvariantFieldEightTraceRow policy (selectedPhysicalGenerator index))

theorem ambientTraceSpan_finrank (policy : PhysicalRelationPolicy) :
    Module.finrank ℚ (ambientTraceSpan policy) = 11556 := by
  unfold ambientTraceSpan
  rw [finrank_span_eq_card (ourInvariantFieldEightTraceRows_linearIndependent policy)]
  simp

theorem ourInvariantCommutatorRow_not_mem_ambientTraceSpan
    (policy : PhysicalRelationPolicy) :
    ourInvariantCommutatorRow policy ∉ ambientTraceSpan policy := by
  intro hmem
  have hkernel :
      ambientTraceSpan policy ≤ LinearMap.ker ambientFieldEightTraceProjection := by
    apply Submodule.span_le.mpr
    rintro value ⟨index, rfl⟩
    exact LinearMap.mem_ker.mpr
      (ambientFieldEightTraceProjection_traceRow policy _)
  have hzero := LinearMap.mem_ker.mp (hkernel hmem)
  rw [ambientFieldEightTraceProjection_commutatorRow] at hzero
  exact literalIncomingCommutatorClass_ne_zero hzero

/-- The span of the `11557` unchanged rows in the ambient invariant space. -/
def ambientTraceCommutatorSpan (policy : PhysicalRelationPolicy) :
    Submodule ℚ exactFieldOrbitInvariantSubmodule :=
  ambientTraceSpan policy ⊔ Submodule.span ℚ {ourInvariantCommutatorRow policy}

theorem ambientTraceCommutatorSpan_finrank (policy : PhysicalRelationPolicy) :
    Module.finrank ℚ (ambientTraceCommutatorSpan policy) = 11557 := by
  unfold ambientTraceCommutatorSpan
  rw [Submodule.finrank_sup_span_singleton
    (ourInvariantCommutatorRow_not_mem_ambientTraceSpan policy),
    ambientTraceSpan_finrank]

theorem ambientTraceCommutatorSpan_le_leibniz (policy : PhysicalRelationPolicy) :
    ambientTraceCommutatorSpan policy ≤
      leibnizJointInvariantRelationSubmodule policy := by
  apply sup_le
  · apply Submodule.span_le.mpr
    rintro value ⟨index, rfl⟩
    exact ourInvariantFieldEightTraceRow_mem_leibniz policy _
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact ourInvariantCommutatorRow_mem_leibniz policy

/-- The Leibniz-corrected joint invariant relation submodule has rational rank
at least `11557`, for either physical-relation policy. -/
theorem leibnizJointInvariantRelationSubmodule_rank_lower_bound_trace_commutator
    (policy : PhysicalRelationPolicy) :
    11557 ≤ Module.finrank ℚ (leibnizJointInvariantRelationSubmodule policy) := by
  rw [← ambientTraceCommutatorSpan_finrank policy]
  exact Submodule.finrank_mono (ambientTraceCommutatorSpan_le_leibniz policy)

/-! ## Derivative counts of normalized labeled sectors -/

theorem mem_ownerAxisProjection_of_mem {fieldCount : ℕ}
    {owner : Fin fieldCount} {entries : List (OwnedAxis fieldCount)}
    {entry : OwnedAxis fieldCount}
    (hmem : entry ∈ entries) (howner : entry.1 = owner) :
    entry.2 ∈ ownerAxisProjection owner entries := by
  induction entries with
  | nil => simp at hmem
  | cons head rest ih =>
      rw [ownerAxisProjection_cons]
      rcases List.mem_cons.mp hmem with rfl | hrest
      · simp [howner]
      · split
        · exact List.mem_cons_of_mem _ (ih hrest)
        · exact ih hrest

theorem ownerAxisProjection_eq_nil_of_forall_ne {fieldCount : ℕ}
    {owner : Fin fieldCount} {entries : List (OwnedAxis fieldCount)}
    (hnone : ∀ entry ∈ entries, entry.1 ≠ owner) :
    ownerAxisProjection owner entries = [] := by
  induction entries with
  | nil => rfl
  | cons head rest ih =>
      rw [ownerAxisProjection_cons,
        ite_eq_right (hnone head List.mem_cons_self)]
      exact ih (fun entry hentry => hnone entry (List.mem_cons_of_mem _ hentry))

theorem ownerAxisProjection_length_of_forall_eq {fieldCount : ℕ}
    {owner : Fin fieldCount} {entries : List (OwnedAxis fieldCount)}
    (hall : ∀ entry ∈ entries, entry.1 = owner) :
    (ownerAxisProjection owner entries).length = entries.length := by
  induction entries with
  | nil => rfl
  | cons head rest ih =>
      rw [ownerAxisProjection_cons, ite_eq_left (hall head List.mem_cons_self),
        List.length_cons, List.length_cons,
        ih (fun entry hentry => hall entry (List.mem_cons_of_mem _ hentry))]

theorem sectorGlobalWord_toList {fieldCount derivativeCount : ℕ}
    (sector : DerivativeAlphaReducedSector fieldCount derivativeCount) :
    (sectorGlobalWord sector).toList =
      List.ofFn fun position =>
        (sector.derivativeWord.ownerAtPosition position,
          sector.derivativeWord.axisAtPosition position) := by
  simp [sectorGlobalWord, orderedDerivativeWordEquivGlobal, List.Vector.toList_ofFn]

theorem normalizedLabeled_derivativeCount_val {fieldCount derivativeCount : ℕ}
    (sector : DerivativeAlphaReducedSector fieldCount derivativeCount)
    (field : Fin fieldCount) :
    ((orientedLocalSectorEquivLabeled fieldCount derivativeCount
        (normalizedSectorData sector)).decoration.1 field).derivativeCount.1 =
      (ownerAxisProjection field (sectorGlobalWord sector).toList).length :=
  rfl

/-- A field letter owning some derivative position has a positive derivative
count in the normalized labeled sector. -/
theorem normalizedLabeled_derivativeCount_pos {fieldCount derivativeCount : ℕ}
    (sector : DerivativeAlphaReducedSector fieldCount derivativeCount)
    (position : Fin derivativeCount) :
    0 < ((orientedLocalSectorEquivLabeled fieldCount derivativeCount
        (normalizedSectorData sector)).decoration.1
          (sector.derivativeWord.ownerAtPosition position)).derivativeCount.1 := by
  rw [normalizedLabeled_derivativeCount_val, sectorGlobalWord_toList]
  apply List.length_pos_of_mem
  apply mem_ownerAxisProjection_of_mem
    (entry := (sector.derivativeWord.ownerAtPosition position,
      sector.derivativeWord.axisAtPosition position))
  · exact List.mem_ofFn.mpr ⟨position, rfl⟩
  · rfl

theorem normalizedLabeled_derivativeCount_pos_of_owner {fieldCount derivativeCount : ℕ}
    (sector : DerivativeAlphaReducedSector fieldCount derivativeCount)
    (position : Fin derivativeCount) (field : Fin fieldCount)
    (howner : sector.derivativeWord.ownerAtPosition position = field) :
    0 < ((orientedLocalSectorEquivLabeled fieldCount derivativeCount
        (normalizedSectorData sector)).decoration.1 field).derivativeCount.1 := by
  subst howner
  exact normalizedLabeled_derivativeCount_pos sector position

@[simp] theorem relabel_plane
    (rename : Equiv.Perm (Fin 5))
    (sector : LabeledLocalWordSector 5 6) (field : Fin 5) :
    ((sector.relabel rename).decoration.1 field).plane =
      (sector.decoration.1 (rename.symm field)).plane := rfl

@[simp] theorem hypercubicAct_plane
    (h : Hypercubic4) (sector : LabeledLocalWordSector 5 6)
    (field : Fin 5) :
    ((sector.hypercubicAct h).decoration.1 field).plane =
      planeAction h (sector.decoration.1 field).plane := rfl

theorem derivedBeforeLabeled_derivativeCount_val (field : Fin 5) :
    (derivedBeforeLabeled.decoration.1 field).derivativeCount.1 =
      if field = 0 then 6 else 0 := by
  rw [derivedBeforeLabeled_derivativeCount]
  split <;> rfl

/-- A labeled five-field sector in which two distinct letters carry
derivatives cannot be relabeled onto `derivedBeforeLabeled`, whose letter `0`
carries all six. -/
theorem not_relabel_onto_derivedBefore_of_two_owners
    (sector : LabeledLocalWordSector 5 6) (first second : Fin 5)
    (hne : first ≠ second)
    (hfirst : 0 < (sector.decoration.1 first).derivativeCount.1)
    (hsecond : 0 < (sector.decoration.1 second).derivativeCount.1)
    (h : Hypercubic4) (rename : Equiv.Perm (Fin 5))
    (hrel : (sector.hypercubicAct h).relabel rename = derivedBeforeLabeled) :
    False := by
  have hcount := congrArg
    (fun target : LabeledLocalWordSector 5 6 =>
      (target.decoration.1 0).derivativeCount.1) hrel
  simp only [relabel_derivativeCount, hypercubicAct_derivativeCount,
    derivedBeforeLabeled_derivativeCount_val, ↓reduceIte] at hcount
  obtain ⟨other, hother, hotherne⟩ :
      ∃ other : Fin 5, 0 < (sector.decoration.1 other).derivativeCount.1 ∧
        other ≠ rename.symm 0 := by
    by_cases hfirstEq : first = rename.symm 0
    · exact ⟨second, hsecond, fun hsecondEq => hne (hfirstEq.trans hsecondEq.symm)⟩
    · exact ⟨first, hfirst, hfirstEq⟩
  have hpair := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun field : Fin 5 => (sector.decoration.1 field).derivativeCount.1)
    (Finset.subset_univ {rename.symm 0, other}) (by intros; exact Nat.zero_le _)
  rw [Finset.sum_pair (Ne.symm hotherne), sector.decoration.2] at hpair
  have hsix : (sector.decoration.1 (rename.symm 0)).derivativeCount.1 = 6 := hcount
  omega

/-! ## The Leibniz insertions of the four-field site -/

/-- OUR derivative positions of the four-field source. -/
abbrev FieldFourPosition := Fin (dimension16DerivativeCount fieldFourCarrier.1)

/-- OUR derivative positions retained by a four-field curvature insertion. -/
abbrev FieldFourRetainedPosition :=
  Fin (dimension16DerivativeCount
    (successorFieldCount fieldFourCarrier.1 fieldFourSite.fieldCount_lt_eight))

/-- OUR full set of outer derivatives of the four-field site. -/
abbrev fieldFourOuterPositions : Finset FieldFourPosition :=
  outerSameOwnerPositions fieldFourSite

theorem mem_fieldFourOuterPositions (position : FieldFourPosition) :
    position ∈ fieldFourOuterPositions ↔ position.1 < 6 := by
  rw [mem_outerSameOwnerPositions]
  constructor
  · intro hposition
    exact hposition.1
  · intro hposition
    exact ⟨hposition, rfl⟩

theorem fieldFourRetained_val (position : FieldFourRetainedPosition) :
    (retainedDerivativeOrderEmbedding fieldFourSite position).1 = position.1 := by
  rw [fieldFour_retainedDerivativeOrderEmbedding position]
  rfl

theorem fieldFourLeibnizOwner_of_mem (moved : Finset FieldFourPosition)
    (position : FieldFourRetainedPosition)
    (hmem : retainedDerivativeOrderEmbedding fieldFourSite position ∈ moved) :
    leibnizOwner fieldFourSite moved position = 4 := by
  simp only [leibnizOwner, hmem, ↓reduceIte]
  rfl

theorem fieldFourLeibnizOwner_of_not_mem (moved : Finset FieldFourPosition)
    (position : FieldFourRetainedPosition)
    (hmem : retainedDerivativeOrderEmbedding fieldFourSite position ∉ moved) :
    leibnizOwner fieldFourSite moved position = 0 := by
  simp only [leibnizOwner, hmem, ↓reduceIte]
  rfl

/-- OUR normalized labeled sector of one Leibniz insertion of the four-field
site. -/
abbrev leibnizFieldFiveLabeled (side : CurvatureInsertionSide)
    (moved : Finset FieldFourPosition) : LabeledLocalWordSector 5 6 :=
  orientedLocalSectorEquivLabeled 5 6
    (normalizedSectorData (insertLeibnizCarrier fieldFourSite side moved).2)

/-- OUR field-label orbit of one Leibniz insertion of the four-field site. -/
def leibnizFieldFiveOrbit (side : CurvatureInsertionSide)
    (moved : Finset FieldFourPosition) : FieldFiveOrbitCarrier :=
  Quotient.mk _ (leibnizFieldFiveLabeled side moved)

/-- For a nonempty proper subset of the outer derivatives, both the
differentiated field and the inserted curvature carry derivatives. -/
theorem leibnizFieldFiveLabeled_two_owners (side : CurvatureInsertionSide)
    (moved : Finset FieldFourPosition) (hsubset : moved ⊆ fieldFourOuterPositions)
    (hnonempty : moved ≠ ∅) (hproper : moved ≠ fieldFourOuterPositions) :
    0 < ((leibnizFieldFiveLabeled side moved).decoration.1 4).derivativeCount.1 ∧
      0 < ((leibnizFieldFiveLabeled side moved).decoration.1 0).derivativeCount.1 := by
  constructor
  · obtain ⟨position, hposition⟩ := Finset.nonempty_iff_ne_empty.mpr hnonempty
    have hlt : position.1 < 6 :=
      (mem_fieldFourOuterPositions position).mp (hsubset hposition)
    let retained : FieldFourRetainedPosition := ⟨position.1, hlt⟩
    have hemb : retainedDerivativeOrderEmbedding fieldFourSite retained = position :=
      Fin.ext (fieldFourRetained_val retained)
    exact normalizedLabeled_derivativeCount_pos_of_owner
      (insertLeibnizCarrier fieldFourSite side moved).2 retained (4 : Fin 5)
      (fieldFourLeibnizOwner_of_mem moved retained (hemb ▸ hposition))
  · have hmissing : ∃ position ∈ fieldFourOuterPositions, position ∉ moved := by
      by_contra hall
      simp only [not_exists, not_and, not_not] at hall
      exact hproper (Finset.Subset.antisymm hsubset (fun position hposition =>
        hall position hposition))
    obtain ⟨position, houter, hnot⟩ := hmissing
    have hlt : position.1 < 6 := (mem_fieldFourOuterPositions position).mp houter
    let retained : FieldFourRetainedPosition := ⟨position.1, hlt⟩
    have hemb : retainedDerivativeOrderEmbedding fieldFourSite retained = position :=
      Fin.ext (fieldFourRetained_val retained)
    exact normalizedLabeled_derivativeCount_pos_of_owner
      (insertLeibnizCarrier fieldFourSite side moved).2 retained (0 : Fin 5)
      (fieldFourLeibnizOwner_of_not_mem moved retained (hemb ▸ hnot))

theorem leibnizFieldFiveOrbit_ne_derivedBefore_of_proper
    (side : CurvatureInsertionSide) (moved : Finset FieldFourPosition)
    (hsubset : moved ⊆ fieldFourOuterPositions)
    (hnonempty : moved ≠ ∅) (hproper : moved ≠ fieldFourOuterPositions)
    (h : Hypercubic4) :
    (leibnizFieldFiveOrbit side moved).hypercubicAct h ≠
      derivedBeforeFieldFiveOrbit := by
  intro hequal
  change Quotient.mk _ ((leibnizFieldFiveLabeled side moved).hypercubicAct h) =
    Quotient.mk _ derivedBeforeLabeled at hequal
  have hsame : MulAction.orbitRel (Equiv.Perm (Fin 5))
      (LabeledLocalWordSector 5 6) derivedBeforeLabeled
        ((leibnizFieldFiveLabeled side moved).hypercubicAct h) :=
    (MulAction.orbitRel (Equiv.Perm (Fin 5))
      (LabeledLocalWordSector 5 6)).symm (Quotient.exact hequal)
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hsame
  rcases hsame with ⟨rename, hrel⟩
  change ((leibnizFieldFiveLabeled side moved).hypercubicAct h).relabel rename =
    derivedBeforeLabeled at hrel
  obtain ⟨hfour, hzero⟩ :=
    leibnizFieldFiveLabeled_two_owners side moved hsubset hnonempty hproper
  exact not_relabel_onto_derivedBefore_of_two_owners _ 4 0 (by decide)
    hfour hzero h rename hrel

/-! ## The insertions carrying all six outer derivatives -/

theorem leibnizFull_owner (position : FieldFourRetainedPosition) :
    leibnizOwner fieldFourSite fieldFourOuterPositions position = 4 := by
  apply fieldFourLeibnizOwner_of_mem
  rw [mem_fieldFourOuterPositions, fieldFourRetained_val]
  exact position.isLt

theorem leibnizFieldFiveLabeled_full_derivativeCount
    (side : CurvatureInsertionSide) (field : Fin 5) :
    ((leibnizFieldFiveLabeled side fieldFourOuterPositions).decoration.1
        field).derivativeCount.1 =
      if field = 4 then 6 else 0 := by
  change (ownerAxisProjection field
      (sectorGlobalWord
        (insertLeibnizCarrier fieldFourSite side fieldFourOuterPositions).2).toList).length = _
  rw [sectorGlobalWord_toList]
  by_cases hfield : field = 4
  · rw [ite_eq_left hfield]
    refine (ownerAxisProjection_length_of_forall_eq ?_).trans List.length_ofFn
    intro entry hentry
    obtain ⟨position, rfl⟩ := List.mem_ofFn.mp hentry
    rw [hfield]
    exact leibnizFull_owner position
  · rw [ite_eq_right hfield]
    refine (congrArg List.length (ownerAxisProjection_eq_nil_of_forall_ne ?_)).trans rfl
    intro entry hentry
    obtain ⟨position, rfl⟩ := List.mem_ofFn.mp hentry
    change leibnizOwner fieldFourSite fieldFourOuterPositions position ≠ field
    have howner : leibnizOwner fieldFourSite fieldFourOuterPositions position = 4 :=
      leibnizFull_owner position
    intro hequal
    exact hfield (hequal.symm.trans howner)

theorem leibnizFieldFiveLabeled_before_trace (moved : Finset FieldFourPosition) :
    (leibnizFieldFiveLabeled .before moved).trace = beforeTrace := by
  rw [← derivedBeforeLabeled_trace]
  rfl

theorem leibnizFieldFiveLabeled_after_trace (moved : Finset FieldFourPosition) :
    (leibnizFieldFiveLabeled .after moved).trace = afterTrace := by
  rw [← derivedAfterLabeled_trace]
  rfl

theorem leibnizFull_relabel_forces_four
    (side : CurvatureInsertionSide) (h : Hypercubic4)
    (rename : Equiv.Perm (Fin 5))
    (hrel : ((leibnizFieldFiveLabeled side fieldFourOuterPositions).hypercubicAct h).relabel
        rename = derivedBeforeLabeled) :
    rename 4 = 0 := by
  have hcount := congrArg
    (fun sector : LabeledLocalWordSector 5 6 =>
      (sector.decoration.1 (rename 4)).derivativeCount.1) hrel
  simp only [relabel_derivativeCount, hypercubicAct_derivativeCount,
    Equiv.symm_apply_apply] at hcount
  rw [leibnizFieldFiveLabeled_full_derivativeCount,
    derivedBeforeLabeled_derivativeCount_val] at hcount
  by_contra hne
  simp [hne] at hcount

theorem leibnizFullBefore_relabel_impossible
    (h : Hypercubic4) (rename : Equiv.Perm (Fin 5))
    (hrel : ((leibnizFieldFiveLabeled .before fieldFourOuterPositions).hypercubicAct h).relabel
        rename = derivedBeforeLabeled) :
    False := by
  have hfour := leibnizFull_relabel_forces_four .before h rename hrel
  have htrace : ∀ field, beforeTrace (rename field) = rename (beforeTrace field) := by
    intro field
    have ht := congrArg (fun sector : LabeledLocalWordSector 5 6 => sector.trace) hrel
    change rename.symm.trans
        ((leibnizFieldFiveLabeled .before fieldFourOuterPositions).trace.trans rename) =
      derivedBeforeLabeled.trace at ht
    rw [leibnizFieldFiveLabeled_before_trace, derivedBeforeLabeled_trace] at ht
    have happly := congrArg (fun trace => trace (rename field)) ht
    simpa using happly.symm
  have hzero : rename 0 = 1 := by
    calc
      rename 0 = rename (beforeTrace 4) := by
        rw [show beforeTrace 4 = (0 : Fin 5) by decide]
      _ = beforeTrace (rename 4) := (htrace 4).symm
      _ = beforeTrace 0 := by rw [hfour]
      _ = 1 := by decide
  have hone : rename 1 = 2 := by
    calc
      rename 1 = rename (beforeTrace 0) := by
        rw [show beforeTrace 0 = (1 : Fin 5) by decide]
      _ = beforeTrace (rename 0) := (htrace 0).symm
      _ = beforeTrace 1 := by rw [hzero]
      _ = 2 := by decide
  have htwo : rename 2 = 3 := by
    calc
      rename 2 = rename (beforeTrace 1) := by
        rw [show beforeTrace 1 = (2 : Fin 5) by decide]
      _ = beforeTrace (rename 1) := (htrace 1).symm
      _ = beforeTrace 2 := by rw [hone]
      _ = 3 := by decide
  have hplaneOne := congrArg
    (fun sector : LabeledLocalWordSector 5 6 => (sector.decoration.1 1).plane) hrel
  have hplaneThree := congrArg
    (fun sector : LabeledLocalWordSector 5 6 => (sector.decoration.1 3).plane) hrel
  simp only [relabel_plane, hypercubicAct_plane] at hplaneOne hplaneThree
  have hsymmOne : rename.symm 1 = 0 := by
    rw [Equiv.symm_apply_eq]
    exact hzero.symm
  have hsymmThree : rename.symm 3 = 2 := by
    rw [Equiv.symm_apply_eq]
    exact htwo.symm
  rw [hsymmOne] at hplaneOne
  rw [hsymmThree] at hplaneThree
  change planeAction h (planeLookup 0 3) = planeLookup 2 3 at hplaneOne
  change planeAction h (planeLookup 0 3) = planeLookup 0 2 at hplaneThree
  have hplanes : planeLookup 2 3 = planeLookup 0 2 :=
    hplaneOne.symm.trans hplaneThree
  exact absurd hplanes (by decide +kernel)

theorem leibnizFullAfter_relabel_impossible
    (h : Hypercubic4) (rename : Equiv.Perm (Fin 5))
    (hrel : ((leibnizFieldFiveLabeled .after fieldFourOuterPositions).hypercubicAct h).relabel
        rename = derivedBeforeLabeled) :
    False := by
  have hfour := leibnizFull_relabel_forces_four .after h rename hrel
  have htrace : ∀ field, beforeTrace (rename field) = rename (afterTrace field) := by
    intro field
    have ht := congrArg (fun sector : LabeledLocalWordSector 5 6 => sector.trace) hrel
    change rename.symm.trans
        ((leibnizFieldFiveLabeled .after fieldFourOuterPositions).trace.trans rename) =
      derivedBeforeLabeled.trace at ht
    rw [leibnizFieldFiveLabeled_after_trace, derivedBeforeLabeled_trace] at ht
    have happly := congrArg (fun trace => trace (rename field)) ht
    simpa using happly.symm
  have hone : rename 1 = 1 := by
    calc
      rename 1 = rename (afterTrace 4) := by
        rw [show afterTrace 4 = (1 : Fin 5) by decide]
      _ = beforeTrace (rename 4) := (htrace 4).symm
      _ = beforeTrace 0 := by rw [hfour]
      _ = 1 := by decide
  have htwo : rename 2 = 2 := by
    calc
      rename 2 = rename (afterTrace 1) := by
        rw [show afterTrace 1 = (2 : Fin 5) by decide]
      _ = beforeTrace (rename 1) := (htrace 1).symm
      _ = beforeTrace 1 := by rw [hone]
      _ = 2 := by decide
  have hthree : rename 3 = 3 := by
    calc
      rename 3 = rename (afterTrace 2) := by
        rw [show afterTrace 2 = (3 : Fin 5) by decide]
      _ = beforeTrace (rename 2) := (htrace 2).symm
      _ = beforeTrace 2 := by rw [htwo]
      _ = 3 := by decide
  have hzero : rename 0 = 4 := by
    calc
      rename 0 = rename (afterTrace 3) := by
        rw [show afterTrace 3 = (0 : Fin 5) by decide]
      _ = beforeTrace (rename 3) := (htrace 3).symm
      _ = beforeTrace 3 := by rw [hthree]
      _ = 4 := by decide
  have hplaneTwo := congrArg
    (fun sector : LabeledLocalWordSector 5 6 => (sector.decoration.1 2).plane) hrel
  have hplaneFour := congrArg
    (fun sector : LabeledLocalWordSector 5 6 => (sector.decoration.1 4).plane) hrel
  simp only [relabel_plane, hypercubicAct_plane] at hplaneTwo hplaneFour
  have hsymmTwo : rename.symm 2 = 2 := by
    rw [Equiv.symm_apply_eq]
    exact htwo.symm
  have hsymmFour : rename.symm 4 = 0 := by
    rw [Equiv.symm_apply_eq]
    exact hzero.symm
  rw [hsymmTwo] at hplaneTwo
  rw [hsymmFour] at hplaneFour
  change planeAction h (planeLookup 0 3) = planeLookup 0 3 at hplaneTwo
  change planeAction h (planeLookup 0 3) = planeLookup 0 2 at hplaneFour
  have hplanes : planeLookup 0 3 = planeLookup 0 2 :=
    hplaneTwo.symm.trans hplaneFour
  exact absurd hplanes (by decide +kernel)

theorem leibnizFieldFiveOrbit_full_ne_derivedBefore
    (side : CurvatureInsertionSide) (h : Hypercubic4) :
    (leibnizFieldFiveOrbit side fieldFourOuterPositions).hypercubicAct h ≠
      derivedBeforeFieldFiveOrbit := by
  intro hequal
  change Quotient.mk _
      ((leibnizFieldFiveLabeled side fieldFourOuterPositions).hypercubicAct h) =
    Quotient.mk _ derivedBeforeLabeled at hequal
  have hsame : MulAction.orbitRel (Equiv.Perm (Fin 5))
      (LabeledLocalWordSector 5 6) derivedBeforeLabeled
        ((leibnizFieldFiveLabeled side fieldFourOuterPositions).hypercubicAct h) :=
    (MulAction.orbitRel (Equiv.Perm (Fin 5))
      (LabeledLocalWordSector 5 6)).symm (Quotient.exact hequal)
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hsame
  rcases hsame with ⟨rename, hrel⟩
  change ((leibnizFieldFiveLabeled side fieldFourOuterPositions).hypercubicAct h).relabel
      rename = derivedBeforeLabeled at hrel
  cases side
  · exact leibnizFullBefore_relabel_impossible h rename hrel
  · exact leibnizFullAfter_relabel_impossible h rename hrel

/-- No Leibniz insertion with a moved derivative reaches the separator's
orbit. -/
theorem leibnizFieldFiveOrbit_ne_derivedBefore
    (side : CurvatureInsertionSide) (moved : Finset FieldFourPosition)
    (hmoved : moved ∈ fieldFourOuterPositions.powerset.erase ∅)
    (h : Hypercubic4) :
    (leibnizFieldFiveOrbit side moved).hypercubicAct h ≠
      derivedBeforeFieldFiveOrbit := by
  rw [Finset.mem_erase, Finset.mem_powerset] at hmoved
  by_cases hfull : moved = fieldFourOuterPositions
  · subst moved
    exact leibnizFieldFiveOrbit_full_ne_derivedBefore side h
  · exact leibnizFieldFiveOrbit_ne_derivedBefore_of_proper side moved hmoved.2
      hmoved.1 hfull h

/-! ## The field-five coordinate of the corrected four-field row -/

theorem sectorFieldOrbitReynolds_single_apply_of_not_reach
    (source target : FieldFiveOrbitCarrier) (coefficient : ℚ)
    (hreach : ∀ h : Hypercubic4, source.hypercubicAct h ≠ target) :
    (sectorFieldOrbitReynolds 5 6 (Finsupp.single source coefficient)) target = 0 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, Finsupp.smul_apply,
    Finset.sum_apply']
  simp [signedSectorFieldOrbitAction_single, hreach]

theorem fieldFiveCoordinate_reynolds_single_of_not_reach
    (source : FieldFiveOrbitCarrier) (coefficient : ℚ)
    (hreach : ∀ h : Hypercubic4,
      source.hypercubicAct h ≠ derivedBeforeFieldFiveOrbit) :
    fieldFiveCoordinate
        (sectorFieldOrbitReynolds 5 6 (Finsupp.single source coefficient)) = 0 := by
  unfold fieldFiveCoordinate
  rw [Finsupp.lapply_apply]
  exact sectorFieldOrbitReynolds_single_apply_of_not_reach _ _ _ hreach

theorem exactFieldFiveProjection_single_five
    (orbit : FieldFiveOrbitCarrier) (coefficient : ℚ) :
    exactFieldFiveProjection
        (Finsupp.single (⟨ourFiveFieldCount, orbit⟩ : ExactFieldRelabelOrbitCarrier)
          coefficient) =
      Finsupp.single orbit coefficient := by
  rw [exactFieldFiveProjection_single]
  simp [exactFieldFiveProjectionBasis, exactFieldFiveOrbitCast_self]

theorem exactFieldRelabelOrbitOfOriented_leibnizInsertion
    (side : CurvatureInsertionSide) (moved : Finset FieldFourPosition) :
    exactFieldRelabelOrbitOfOriented
        (exactNormalizedSectorData (insertLeibnizCarrier fieldFourSite side moved)) =
      ⟨ourFiveFieldCount, leibnizFieldFiveOrbit side moved⟩ :=
  rfl

theorem leibnizInsertion_coordinate_zero
    (side : CurvatureInsertionSide) (moved : Finset FieldFourPosition)
    (hmoved : moved ∈ fieldFourOuterPositions.powerset.erase ∅) :
    fieldFiveCoordinate
        (sectorFieldOrbitReynolds 5 6
          (exactFieldFiveProjection
            (normalizeExactFieldRelabel
              (normalizeExactContextualBasis
                (insertLeibnizCarrier fieldFourSite side moved))))) = 0 := by
  have hreach : ∀ h : Hypercubic4,
      (leibnizFieldFiveOrbit side moved).hypercubicAct h ≠ derivedBeforeFieldFiveOrbit :=
    leibnizFieldFiveOrbit_ne_derivedBefore side moved hmoved
  have hproj :
      exactFieldFiveProjection
          (normalizeExactFieldRelabel
            (normalizeExactContextualBasis
              (insertLeibnizCarrier fieldFourSite side moved))) =
        Finsupp.single (leibnizFieldFiveOrbit side moved)
          (fieldAxisOrientationCoefficient
            (sectorFieldAxisAssignment
              (insertLeibnizCarrier fieldFourSite side moved).2)) := by
    rw [normalizeExactContextualBasis_fieldRelabel,
      exactFieldRelabelOrbitOfOriented_leibnizInsertion,
      exactFieldFiveProjection_single_five]
  rw [hproj]
  apply fieldFiveCoordinate_reynolds_single_of_not_reach
  exact hreach

/-- The corrected four-field column is the earlier column minus the Leibniz
insertions with a moved derivative. -/
theorem leibnizOrbitPhysicalRelationOperator_fieldFourCommutator
    (policy : PhysicalRelationPolicy) :
    leibnizOrbitPhysicalRelationOperator policy
        (Finsupp.single (fieldFourCommutatorGenerator policy) 1) =
      orbitPhysicalRelationOperator policy
          (Finsupp.single (fieldFourCommutatorGenerator policy) 1) -
        ∑ moved ∈ fieldFourOuterPositions.powerset.erase ∅,
          (normalizeExactFieldRelabel
              (normalizeExactContextualBasis
                (insertLeibnizCarrier fieldFourSite .before moved)) -
            normalizeExactFieldRelabel
              (normalizeExactContextualBasis
                (insertLeibnizCarrier fieldFourSite .after moved))) := by
  have hleibniz :
      leibnizOrbitPhysicalRelationOperator policy
          (Finsupp.single (fieldFourCommutatorGenerator policy) 1) =
        normalizeExactFieldRelabel
          (normalizeExactContextual (leibnizCommutatorRow fieldFourSite)) := by
    rw [leibnizOrbitPhysicalRelationOperator, LinearMap.comp_apply,
      leibnizNormalizedPhysicalRelationOperator, LinearMap.comp_apply,
      leibnizPhysicalRelationOperator_single, one_smul]
    rfl
  have hold :
      orbitPhysicalRelationOperator policy
          (Finsupp.single (fieldFourCommutatorGenerator policy) 1) =
        normalizeExactFieldRelabel
          (normalizeExactContextual (covariantCommutatorRow fieldFourSite)) := by
    rw [orbitPhysicalRelationOperator, LinearMap.comp_apply,
      normalizedPhysicalRelationOperator, LinearMap.comp_apply,
      physicalRelationOperator_single, one_smul]
    rfl
  rw [hleibniz, hold, leibnizCommutatorRow_eq_covariantCommutatorRow_sub,
    map_sub, map_sub, map_sum, map_sum, sub_right_inj]
  apply Finset.sum_congr rfl
  intro moved _
  rw [map_sub, map_sub, normalizeExactContextual_single,
    normalizeExactContextual_single, one_smul, one_smul]

theorem leibnizFieldFourCommutator_coordinate
    (policy : PhysicalRelationPolicy) :
    fieldFiveCoordinate
        (sectorFieldOrbitReynolds 5 6
          (exactFieldFiveProjection
            (leibnizOrbitPhysicalRelationOperator policy
              (Finsupp.single (fieldFourCommutatorGenerator policy) 1)))) =
      -(1 : ℚ) / 24 := by
  rw [leibnizOrbitPhysicalRelationOperator_fieldFourCommutator,
    map_sub, map_sub, map_sub,
    exactFieldFiveProjection_fieldFourCommutator, fieldFiveCoordinate_reynolds_pair,
    map_sum, map_sum, map_sum, Finset.sum_eq_zero]
  · ring
  · intro moved hmoved
    rw [map_sub, map_sub, map_sub,
      leibnizInsertion_coordinate_zero .before moved hmoved,
      leibnizInsertion_coordinate_zero .after moved hmoved]
    ring

/-! ## The corrected separator and the bound `11558` -/

/-- OUR Reynolds-averaged corrected four-field commutator row. -/
def leibnizFieldFourInvariantCommutatorRow (policy : PhysicalRelationPolicy) :
    exactFieldOrbitInvariantSubmodule :=
  ⟨exactFieldOrbitReynolds
      (leibnizOrbitPhysicalRelationOperator policy
        (Finsupp.single (fieldFourCommutatorGenerator policy) 1)),
    exactFieldOrbitReynolds_invariant _⟩

theorem leibnizFieldFourInvariantCommutatorRow_mem
    (policy : PhysicalRelationPolicy) :
    leibnizFieldFourInvariantCommutatorRow policy ∈
      leibnizJointInvariantRelationSubmodule policy := by
  rw [mem_leibnizJointInvariantRelationSubmodule_iff]
  exact exactFieldOrbitReynolds_leibnizOrbit_mem policy _

theorem ambientFieldFiveCoordinate_leibnizFieldFourRow
    (policy : PhysicalRelationPolicy) :
    ambientFieldFiveCoordinate (leibnizFieldFourInvariantCommutatorRow policy) =
      -(1 : ℚ) / 24 := by
  change fieldFiveCoordinate
      (exactFieldFiveProjection
        (exactFieldOrbitReynolds
          (leibnizOrbitPhysicalRelationOperator policy
            (Finsupp.single (fieldFourCommutatorGenerator policy) 1)))) = _
  rw [exactFieldFiveProjection_exactFieldOrbitReynolds]
  exact leibnizFieldFourCommutator_coordinate policy

theorem leibnizFieldFourRow_not_mem_ambientTraceCommutatorSpan
    (policy : PhysicalRelationPolicy) :
    leibnizFieldFourInvariantCommutatorRow policy ∉
      ambientTraceCommutatorSpan policy := by
  intro hmem
  have hkernel :
      ambientTraceCommutatorSpan policy ≤ LinearMap.ker ambientFieldFiveCoordinate := by
    apply sup_le
    · apply Submodule.span_le.mpr
      rintro value ⟨index, rfl⟩
      exact LinearMap.mem_ker.mpr (ambientFieldFiveCoordinate_traceRow policy _)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact LinearMap.mem_ker.mpr (ambientFieldFiveCoordinate_commutatorRow policy)
  have hzero := LinearMap.mem_ker.mp (hkernel hmem)
  rw [ambientFieldFiveCoordinate_leibnizFieldFourRow] at hzero
  norm_num at hzero

/-- The span of the `11557` unchanged rows and the corrected four-field row. -/
def ambientSeparatedSpan (policy : PhysicalRelationPolicy) :
    Submodule ℚ exactFieldOrbitInvariantSubmodule :=
  ambientTraceCommutatorSpan policy ⊔
    Submodule.span ℚ {leibnizFieldFourInvariantCommutatorRow policy}

/-- The Leibniz-corrected joint invariant relation submodule has rational rank
at least `11558`, for either physical-relation policy. -/
theorem leibnizJointInvariantRelationSubmodule_rank_lower_bound_fieldFiveCommutator
    (policy : PhysicalRelationPolicy) :
    11558 ≤ Module.finrank ℚ (leibnizJointInvariantRelationSubmodule policy) := by
  have hrank : Module.finrank ℚ (ambientSeparatedSpan policy) = 11558 := by
    unfold ambientSeparatedSpan
    rw [Submodule.finrank_sup_span_singleton
      (leibnizFieldFourRow_not_mem_ambientTraceCommutatorSpan policy),
      ambientTraceCommutatorSpan_finrank]
  have hle :
      ambientSeparatedSpan policy ≤ leibnizJointInvariantRelationSubmodule policy := by
    apply sup_le (ambientTraceCommutatorSpan_le_leibniz policy)
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact leibnizFieldFourInvariantCommutatorRow_mem policy
  rw [← hrank]
  exact Submodule.finrank_mono hle

#print axioms leibnizJointInvariantRelationSubmodule_rank_lower_bound_trace_commutator
#print axioms not_relabel_onto_derivedBefore_of_two_owners
#print axioms leibnizFieldFiveOrbit_ne_derivedBefore
#print axioms leibnizFieldFourCommutator_coordinate
#print axioms leibnizJointInvariantRelationSubmodule_rank_lower_bound_fieldFiveCommutator

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16LeibnizJointRank
