import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16JointTraceCommutatorRank
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16OrbitCarrierBridge

/-!
# OUR field-five commutator separator

This module realizes one concrete four-field covariant-commutator source,
normalizes its two five-field curvature insertions, and evaluates a signed
hypercubic Reynolds coordinate of their difference.  The computation is
finite and symbolic: the stabilizer is determined from three oriented planes,
and the surviving reflection signs are reduced from the explicit six-axis
derivative word.

The resulting field-five functional vanishes on the certified field-eight
trace family and the earlier seven-to-eight commutator row, while taking the
exact value `-1/24` on the new physical invariant row.  It therefore raises
the certified joint invariant relation-rank lower bound from `11557` to
`11558`.  It does not determine a complete relation census or the joint
quotient dimension.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FieldFiveCommutatorSeparator

open scoped BigOperators

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus
open HypercubicRawFDCharacterCensus
open HypercubicRawFDDimension16Census
open HypercubicDimension16AlphaReduction
open HypercubicDimension16RelationEquivariance
open HypercubicDimension16CovariantCommutator
open HypercubicDimension16ContextualQuotient
open HypercubicDimension16AntisymmetryQuotient
open HypercubicDimension16OrbitCarrierBridge
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16PhysicalInvariantSpace
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16PhysicalRelationBlocks
open HypercubicDimension16JointQuotientInvariants
open HypercubicDimension16JointPhysicalQuotient
open HypercubicDimension16SignedOrbitCoinvariants
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16IncomingCommutatorTraceProjection
open HypercubicDimension16IncomingCommutatorTraceCoupledColumn
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16IncomingCommutatorTraceInvariantWitness
open HypercubicDimension16FieldEightTracePhysicalLift
open HypercubicDimension16JointTraceRankTransfer
open HypercubicDimension16JointTraceCommutatorRank
open HypercubicDimension16PhysicalTraceQuotient

/-- OUR five-field sector orbit carrier. -/
abbrev FieldFiveOrbitCarrier := FieldRelabelOrbitCarrier 5 6

/-- OUR rational vector space on five-field sector orbits. -/
abbrev FieldFiveOrbitSpace := SectorFieldOrbitSpace 5 6

/-- OUR concrete four-field source with an adjacent derivative pair on
field zero. -/
abbrev fieldFourCarrier : RelationCarrier :=
  ⟨(⟨4, by decide⟩ : Fin 9),
    ({ trace := ⟨finRotate 4⟩
       fieldFirst := fun field =>
         if field = 0 then 0 else if field = 1 then 2 else
           if field = 2 then 0 else 0
       fieldSecond := fun field =>
         if field = 0 then 3 else if field = 1 then 3 else
           if field = 2 then 3 else 2
       derivativeWord :=
         { ownerAtPosition := fun _ => 0
           axisAtPosition := fun position =>
             if position = 0 then 2 else if position = 1 then 0 else
               if position = 2 then 1 else if position = 3 then 3 else
                 if position = 4 then 0 else if position = 5 then 1 else
                   if position = 6 then 0 else 2 } } :
      DerivativeAlphaReducedSector 4 8)⟩

/-- OUR adjacent derivative site in the four-field source. -/
abbrev fieldFourSite : CovariantCommutatorSite fieldFourCarrier where
  field := ⟨0, by decide⟩
  outer := ⟨6, by norm_num [fieldFourCarrier, dimension16DerivativeCount]⟩
  inner := ⟨7, by norm_num [fieldFourCarrier, dimension16DerivativeCount]⟩
  outer_lt_inner := by decide
  owner_outer := rfl
  owner_inner := rfl
  no_same_owner_between := by
    intro position houter hinner
    exfalso
    change 6 < position.1 at houter
    change position.1 < 7 at hinner
    omega

/-- OUR normalized before-insertion sector. -/
abbrev derivedBeforeLabeled : LabeledLocalWordSector 5 6 :=
  orientedLocalSectorEquivLabeled 5 6
    (normalizedSectorData
      (insertCurvatureCarrier fieldFourSite .before).2)

/-- OUR normalized after-insertion sector. -/
abbrev derivedAfterLabeled : LabeledLocalWordSector 5 6 :=
  orientedLocalSectorEquivLabeled 5 6
    (normalizedSectorData
      (insertCurvatureCarrier fieldFourSite .after).2)

def beforeTrace : Equiv.Perm (Fin 5) where
  toFun := fun field => Fin.ofNat 5
    (#[1, 2, 3, 4, 0].getD field.1 0)
  invFun := fun field => Fin.ofNat 5
    (#[4, 0, 1, 2, 3].getD field.1 0)
  left_inv := by intro field; fin_cases field <;> decide +kernel
  right_inv := by intro field; fin_cases field <;> decide +kernel

def afterTrace : Equiv.Perm (Fin 5) where
  toFun := fun field => Fin.ofNat 5
    (#[4, 2, 3, 0, 1].getD field.1 0)
  invFun := fun field => Fin.ofNat 5
    (#[3, 4, 1, 2, 0].getD field.1 0)
  left_inv := by intro field; fin_cases field <;> decide +kernel
  right_inv := by intro field; fin_cases field <;> decide +kernel

def afterToBefore : Equiv.Perm (Fin 5) where
  toFun := fun field => Fin.ofNat 5
    (#[0, 2, 3, 4, 1].getD field.1 0)
  invFun := fun field => Fin.ofNat 5
    (#[0, 4, 1, 2, 3].getD field.1 0)
  left_inv := by intro field; fin_cases field <;> decide +kernel
  right_inv := by intro field; fin_cases field <;> decide +kernel

@[simp] theorem relabel_derivativeCount
    (rename : Equiv.Perm (Fin 5))
    (sector : LabeledLocalWordSector 5 6) (field : Fin 5) :
    ((sector.relabel rename).decoration.1 field).derivativeCount =
      (sector.decoration.1 (rename.symm field)).derivativeCount := rfl

@[simp] theorem hypercubicAct_derivativeCount
    (h : Hypercubic4) (sector : LabeledLocalWordSector 5 6)
    (field : Fin 5) :
    ((sector.hypercubicAct h).decoration.1 field).derivativeCount =
      (sector.decoration.1 field).derivativeCount := rfl

def fieldFivePlaneStabilizerCode (code : Fin 24) : Bool :=
  decide (planeActionPerm (permutationCode code) (planeLookup 0 3) =
    planeLookup 0 3) &&
  decide (planeActionPerm (permutationCode code) (planeLookup 2 3) =
    planeLookup 2 3) &&
  decide (planeActionPerm (permutationCode code) (planeLookup 0 2) =
    planeLookup 0 2)

theorem fieldFivePlaneStabilizerCode_iff (code : Fin 24) :
    fieldFivePlaneStabilizerCode code = true ↔ code = 0 := by
  fin_cases code <;> decide +kernel

theorem plane_stabilizer_rigidity
    (permutation : Equiv.Perm Axis)
    (h03 : planeActionPerm permutation (planeLookup 0 3) = planeLookup 0 3)
    (h23 : planeActionPerm permutation (planeLookup 2 3) = planeLookup 2 3)
    (h02 : planeActionPerm permutation (planeLookup 0 2) = planeLookup 0 2) :
    permutation = 1 := by
  obtain ⟨code, rfl⟩ := permutationCode_bijective.2 permutation
  have hcode : fieldFivePlaneStabilizerCode code = true := by
    simp [fieldFivePlaneStabilizerCode, h03, h23, h02]
  have hzero : code = 0 := fieldFivePlaneStabilizerCode_iff code |>.mp hcode
  subst code
  decide +kernel

theorem hypercubicAct_eq_of_perm_eq_one
    (h : Hypercubic4) (sector : LabeledLocalWordSector 5 6)
    (hperm : h.perm = 1) :
    sector.hypercubicAct h = sector := by
  apply LabeledLocalWordSector.ext
  · rfl
  · apply Subtype.ext
    funext field
    apply LocalFieldLetter.ext
    · change planeActionPerm h.perm _ = _
      rw [hperm]
      generalize (sector.decoration.1 field).plane = plane
      fin_cases plane <;> decide +kernel
    · rfl
    · change (fun position => h.perm
          ((sector.decoration.1 field).derivativeAxis position)) ≍
        (sector.decoration.1 field).derivativeAxis
      rw [hperm]
      apply heq_of_eq
      funext position
      simp

theorem fieldFive_plane03_tensorSign
    (reflection : Fin 16) :
    (planeTensorSign (decodedHypercubicCharacterElement 0 reflection)
      (planeLookup 0 3) : ℚ) =
      (Hypercubic4.axisSign
        (decodedHypercubicCharacterElement 0 reflection) 0 : ℚ) *
      (Hypercubic4.axisSign
        (decodedHypercubicCharacterElement 0 reflection) 3 : ℚ) := by
  have hfirst :
      (SU2LatticeFDCensusNoGo.OrientedPlane.first 2) =
        (0 : Axis) := by decide +kernel
  have hsecond :
      (SU2LatticeFDCensusNoGo.OrientedPlane.second 2) =
        (3 : Axis) := by decide +kernel
  unfold planeTensorSign
  simp [planeReorderSign, hfirst, hsecond,
    decodedHypercubicCharacterElement, permutationCode, planeLookup,
    Hypercubic4.axisSign]

theorem fieldFive_plane23_tensorSign
    (reflection : Fin 16) :
    (planeTensorSign (decodedHypercubicCharacterElement 0 reflection)
      (planeLookup 2 3) : ℚ) =
      (Hypercubic4.axisSign
        (decodedHypercubicCharacterElement 0 reflection) 2 : ℚ) *
      (Hypercubic4.axisSign
        (decodedHypercubicCharacterElement 0 reflection) 3 : ℚ) := by
  have hfirst :
      (SU2LatticeFDCensusNoGo.OrientedPlane.first 5) =
        (2 : Axis) := by decide +kernel
  have hsecond :
      (SU2LatticeFDCensusNoGo.OrientedPlane.second 5) =
        (3 : Axis) := by decide +kernel
  unfold planeTensorSign
  simp [planeReorderSign, hfirst, hsecond,
    decodedHypercubicCharacterElement, permutationCode, planeLookup,
    Hypercubic4.axisSign]

theorem fieldFive_plane02_tensorSign
    (reflection : Fin 16) :
    (planeTensorSign (decodedHypercubicCharacterElement 0 reflection)
      (planeLookup 0 2) : ℚ) =
      (Hypercubic4.axisSign
        (decodedHypercubicCharacterElement 0 reflection) 0 : ℚ) *
      (Hypercubic4.axisSign
        (decodedHypercubicCharacterElement 0 reflection) 2 : ℚ) := by
  have hfirst :
      (SU2LatticeFDCensusNoGo.OrientedPlane.first 1) =
        (0 : Axis) := by decide +kernel
  have hsecond :
      (SU2LatticeFDCensusNoGo.OrientedPlane.second 1) =
        (2 : Axis) := by decide +kernel
  unfold planeTensorSign
  simp [planeReorderSign, hfirst, hsecond,
    decodedHypercubicCharacterElement, permutationCode, planeLookup,
    Hypercubic4.axisSign]

def fieldFiveCoordinateCode (permutation : Fin 24) (_reflection : Fin 16) : ℚ :=
  if permutation = 0 then -1 else 0

def fieldFiveCoordinateCodeSum : ℚ :=
  ∑ permutation : Fin 24, ∑ reflection : Fin 16,
    fieldFiveCoordinateCode permutation reflection

theorem fieldFiveCoordinateCodeSum_exact :
    fieldFiveCoordinateCodeSum = -16 := by
  decide +kernel

@[simp] theorem derivedBeforeLabeled_derivativeCount (field : Fin 5) :
    (derivedBeforeLabeled.decoration.1 field).derivativeCount =
      if field = 0 then (6 : Fin 7) else 0 := by
  fin_cases field <;> rfl

@[simp] theorem derivedAfterLabeled_derivativeCount (field : Fin 5) :
    (derivedAfterLabeled.decoration.1 field).derivativeCount =
      if field = 0 then (6 : Fin 7) else 0 := by
  fin_cases field <;> rfl

theorem derivedBeforeLabeled_trace : derivedBeforeLabeled.trace = beforeTrace := by
  apply Equiv.ext
  intro field
  fin_cases field <;> decide +kernel

theorem derivedAfterLabeled_trace : derivedAfterLabeled.trace = afterTrace := by
  apply Equiv.ext
  intro field
  fin_cases field <;> decide +kernel

theorem fieldFour_retainedDerivativeOrderEmbedding
    (position : Fin 6) :
    retainedDerivativeOrderEmbedding fieldFourSite position =
      Fin.castAdd 2 position := by
  have hemb : (Fin.castAddOrderEmb 2 : Fin 6 ↪o Fin 8) =
      retainedDerivativeOrderEmbedding fieldFourSite := by
    unfold retainedDerivativeOrderEmbedding
    apply Finset.orderEmbOfFin_unique'
    intro index
    fin_cases index <;> decide +kernel
  exact congrArg (fun embedding : Fin 6 ↪o Fin 8 => embedding position)
    hemb.symm

theorem fieldFourBefore_derivativeAxis (position : Fin 6) :
    (insertCurvatureCarrier fieldFourSite .before).2.derivativeWord.axisAtPosition
      position =
      Fin.ofNat 4 (#[2, 0, 1, 3, 0, 1].getD position.1 0) := by
  change fieldFourCarrier.2.derivativeWord.axisAtPosition
    (retainedDerivativeOrderEmbedding fieldFourSite position) = _
  rw [fieldFour_retainedDerivativeOrderEmbedding]
  fin_cases position <;> rfl

theorem fieldFourBefore_derivativeOwner (position : Fin 6) :
    (insertCurvatureCarrier fieldFourSite .before).2.derivativeWord.ownerAtPosition
      position = (0 : Fin 5) := by
  change Fin.castSucc
    (fieldFourCarrier.2.derivativeWord.ownerAtPosition
      (retainedDerivativeOrderEmbedding fieldFourSite position)) = 0
  rfl

theorem derivedBefore_relabel_forces_zero
    (h : Hypercubic4) (rename : Equiv.Perm (Fin 5))
    (hrel : (derivedBeforeLabeled.hypercubicAct h).relabel rename =
      derivedBeforeLabeled) :
    rename 0 = 0 := by
  have hcount := congrArg
    (fun sector : LabeledLocalWordSector 5 6 =>
      (sector.decoration.1 (rename 0)).derivativeCount) hrel
  simp only [relabel_derivativeCount, hypercubicAct_derivativeCount,
    Equiv.symm_apply_apply] at hcount
  rw [derivedBeforeLabeled_derivativeCount,
    derivedBeforeLabeled_derivativeCount] at hcount
  by_contra hne
  simp [hne] at hcount

theorem derivedAfter_relabel_forces_zero
    (h : Hypercubic4) (rename : Equiv.Perm (Fin 5))
    (hrel : (derivedAfterLabeled.hypercubicAct h).relabel rename =
      derivedBeforeLabeled) :
    rename 0 = 0 := by
  have hcount := congrArg
    (fun sector : LabeledLocalWordSector 5 6 =>
      (sector.decoration.1 (rename 0)).derivativeCount) hrel
  simp only [relabel_derivativeCount, hypercubicAct_derivativeCount,
    Equiv.symm_apply_apply] at hcount
  rw [derivedAfterLabeled_derivativeCount,
    derivedBeforeLabeled_derivativeCount] at hcount
  by_contra hne
  simp [hne] at hcount

theorem derivedBefore_relabel_trace_commutes
    (h : Hypercubic4) (rename : Equiv.Perm (Fin 5))
    (hrel : (derivedBeforeLabeled.hypercubicAct h).relabel rename =
      derivedBeforeLabeled)
    (field : Fin 5) :
    beforeTrace (rename field) = rename (beforeTrace field) := by
  have htrace := congrArg
    (fun sector : LabeledLocalWordSector 5 6 => sector.trace) hrel
  change rename.symm.trans (derivedBeforeLabeled.trace.trans rename) =
    derivedBeforeLabeled.trace at htrace
  rw [derivedBeforeLabeled_trace] at htrace
  have happly := congrArg (fun trace => trace (rename field)) htrace
  simpa using happly.symm

theorem derivedAfter_relabel_trace_conjugacy
    (h : Hypercubic4) (rename : Equiv.Perm (Fin 5))
    (hrel : (derivedAfterLabeled.hypercubicAct h).relabel rename =
      derivedBeforeLabeled)
    (field : Fin 5) :
    beforeTrace (rename field) = rename (afterTrace field) := by
  have htrace := congrArg
    (fun sector : LabeledLocalWordSector 5 6 => sector.trace) hrel
  change rename.symm.trans (derivedAfterLabeled.trace.trans rename) =
    derivedBeforeLabeled.trace at htrace
  rw [derivedBeforeLabeled_trace, derivedAfterLabeled_trace] at htrace
  have happly := congrArg (fun trace => trace (rename field)) htrace
  simpa using happly.symm

theorem derivedBefore_relabel_is_identity
    (h : Hypercubic4) (rename : Equiv.Perm (Fin 5))
    (hrel : (derivedBeforeLabeled.hypercubicAct h).relabel rename =
      derivedBeforeLabeled) :
    rename = 1 := by
  have hzero := derivedBefore_relabel_forces_zero h rename hrel
  have hone : rename 1 = 1 := by
    have hcomm := derivedBefore_relabel_trace_commutes h rename hrel 0
    have htrace : beforeTrace 0 = (1 : Fin 5) := by decide
    rw [← htrace]
    calc
      rename (beforeTrace 0) = beforeTrace (rename 0) := hcomm.symm
      _ = beforeTrace 0 := by rw [hzero]
  have htwo : rename 2 = 2 := by
    have hcomm := derivedBefore_relabel_trace_commutes h rename hrel 1
    have htrace : beforeTrace 1 = (2 : Fin 5) := by decide
    rw [← htrace]
    calc
      rename (beforeTrace 1) = beforeTrace (rename 1) := hcomm.symm
      _ = beforeTrace 1 := by rw [hone]
  have hthree : rename 3 = 3 := by
    have hcomm := derivedBefore_relabel_trace_commutes h rename hrel 2
    have htrace : beforeTrace 2 = (3 : Fin 5) := by decide
    rw [← htrace]
    calc
      rename (beforeTrace 2) = beforeTrace (rename 2) := hcomm.symm
      _ = beforeTrace 2 := by rw [htwo]
  have hfour : rename 4 = 4 := by
    have hcomm := derivedBefore_relabel_trace_commutes h rename hrel 3
    have htrace : beforeTrace 3 = (4 : Fin 5) := by decide
    rw [← htrace]
    calc
      rename (beforeTrace 3) = beforeTrace (rename 3) := hcomm.symm
      _ = beforeTrace 3 := by rw [hthree]
  apply Equiv.ext
  intro field
  fin_cases field
  · exact hzero
  · exact hone
  · exact htwo
  · exact hthree
  · exact hfour

theorem derivedAfter_relabel_is_afterToBefore
    (h : Hypercubic4) (rename : Equiv.Perm (Fin 5))
    (hrel : (derivedAfterLabeled.hypercubicAct h).relabel rename =
      derivedBeforeLabeled) :
    rename = afterToBefore := by
  have hzero := derivedAfter_relabel_forces_zero h rename hrel
  have hfour : rename 4 = 1 := by
    have hcomm := derivedAfter_relabel_trace_conjugacy h rename hrel 0
    have hbefore : beforeTrace 0 = (1 : Fin 5) := by decide
    have hafter : afterTrace 0 = (4 : Fin 5) := by decide
    calc
      rename 4 = rename (afterTrace 0) := by rw [hafter]
      _ = beforeTrace (rename 0) := hcomm.symm
      _ = beforeTrace 0 := by rw [hzero]
      _ = 1 := hbefore
  have hone : rename 1 = 2 := by
    have hcomm := derivedAfter_relabel_trace_conjugacy h rename hrel 4
    have hbefore : beforeTrace 1 = (2 : Fin 5) := by decide
    have hafter : afterTrace 4 = (1 : Fin 5) := by decide
    calc
      rename 1 = rename (afterTrace 4) := by rw [hafter]
      _ = beforeTrace (rename 4) := hcomm.symm
      _ = beforeTrace 1 := by rw [hfour]
      _ = 2 := hbefore
  have htwo : rename 2 = 3 := by
    have hcomm := derivedAfter_relabel_trace_conjugacy h rename hrel 1
    have hbefore : beforeTrace 2 = (3 : Fin 5) := by decide
    have hafter : afterTrace 1 = (2 : Fin 5) := by decide
    calc
      rename 2 = rename (afterTrace 1) := by rw [hafter]
      _ = beforeTrace (rename 1) := hcomm.symm
      _ = beforeTrace 2 := by rw [hone]
      _ = 3 := hbefore
  have hthree : rename 3 = 4 := by
    have hcomm := derivedAfter_relabel_trace_conjugacy h rename hrel 2
    have hbefore : beforeTrace 3 = (4 : Fin 5) := by decide
    have hafter : afterTrace 2 = (3 : Fin 5) := by decide
    calc
      rename 3 = rename (afterTrace 2) := by rw [hafter]
      _ = beforeTrace (rename 2) := hcomm.symm
      _ = beforeTrace 3 := by rw [htwo]
      _ = 4 := hbefore
  apply Equiv.ext
  intro field
  fin_cases field
  · calc
      rename 0 = 0 := hzero
      _ = afterToBefore 0 := by decide
  · calc
      rename 1 = 2 := hone
      _ = afterToBefore 1 := by decide
  · calc
      rename 2 = 3 := htwo
      _ = afterToBefore 2 := by decide
  · calc
      rename 3 = 4 := hthree
      _ = afterToBefore 3 := by decide
  · calc
      rename 4 = 1 := hfour
      _ = afterToBefore 4 := by decide

@[simp] theorem derivedBeforeLabeled_plane_zero :
    (derivedBeforeLabeled.decoration.1 (0 : Fin 5)).plane =
      planeLookup 0 3 := by rfl

@[simp] theorem derivedBeforeLabeled_plane_one :
    (derivedBeforeLabeled.decoration.1 (1 : Fin 5)).plane =
      planeLookup 2 3 := by rfl

@[simp] theorem derivedBeforeLabeled_plane_three :
    (derivedBeforeLabeled.decoration.1 (3 : Fin 5)).plane =
      planeLookup 0 2 := by rfl

@[simp] theorem derivedBeforeLabeled_plane_four :
    (derivedBeforeLabeled.decoration.1 (4 : Fin 5)).plane =
      planeLookup 0 2 := by rfl

theorem derivedBefore_action_plane23
    (h : Hypercubic4)
    (hrel : derivedBeforeLabeled.hypercubicAct h = derivedBeforeLabeled) :
    planeAction h (planeLookup 2 3) = planeLookup 2 3 := by
  have hfield := congrArg
    (fun sector : LabeledLocalWordSector 5 6 =>
      (sector.decoration.1 (1 : Fin 5)).plane) hrel
  change planeAction h
      (derivedBeforeLabeled.decoration.1 (1 : Fin 5)).plane =
    (derivedBeforeLabeled.decoration.1 (1 : Fin 5)).plane at hfield
  simpa using hfield

theorem derivedBefore_action_plane03
    (h : Hypercubic4)
    (hrel : derivedBeforeLabeled.hypercubicAct h = derivedBeforeLabeled) :
    planeAction h (planeLookup 0 3) = planeLookup 0 3 := by
  have hfield := congrArg
    (fun sector : LabeledLocalWordSector 5 6 =>
      (sector.decoration.1 (0 : Fin 5)).plane) hrel
  change planeAction h
      (derivedBeforeLabeled.decoration.1 (0 : Fin 5)).plane =
    (derivedBeforeLabeled.decoration.1 (0 : Fin 5)).plane at hfield
  simpa using hfield

theorem derivedBefore_action_plane02
    (h : Hypercubic4)
    (hrel : derivedBeforeLabeled.hypercubicAct h = derivedBeforeLabeled) :
    planeAction h (planeLookup 0 2) = planeLookup 0 2 := by
  have hfield := congrArg
    (fun sector : LabeledLocalWordSector 5 6 =>
      (sector.decoration.1 (3 : Fin 5)).plane) hrel
  change planeAction h
      (derivedBeforeLabeled.decoration.1 (3 : Fin 5)).plane =
    (derivedBeforeLabeled.decoration.1 (3 : Fin 5)).plane at hfield
  simpa using hfield

theorem derivedBefore_action_forces_permutation_code_zero
    (permutation : Fin 24) (reflection : Fin 16)
    (hrel : derivedBeforeLabeled.hypercubicAct
      (decodedHypercubicCharacterElement permutation reflection) =
        derivedBeforeLabeled) :
    permutation = 0 := by
  have h03 := derivedBefore_action_plane03
    (decodedHypercubicCharacterElement permutation reflection) hrel
  have h23 := derivedBefore_action_plane23
    (decodedHypercubicCharacterElement permutation reflection) hrel
  have h02 := derivedBefore_action_plane02
    (decodedHypercubicCharacterElement permutation reflection) hrel
  have hperm : permutationCode permutation = 1 := by
    apply plane_stabilizer_rigidity
    · exact h03
    · exact h23
    · exact h02
  apply characterPermutationCode_injective
  calc
    permutationCode permutation = 1 := hperm
    _ = permutationCode 0 := by decide +kernel

theorem derivedBefore_orbit_forces_permutation_code_zero
    (permutation : Fin 24) (reflection : Fin 16)
    (hsame : MulAction.orbitRel (Equiv.Perm (Fin 5))
      (LabeledLocalWordSector 5 6) derivedBeforeLabeled
      (derivedBeforeLabeled.hypercubicAct
        (decodedHypercubicCharacterElement permutation reflection))) :
    permutation = 0 := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hsame
  rcases hsame with ⟨rename, hrel⟩
  change (derivedBeforeLabeled.hypercubicAct
    (decodedHypercubicCharacterElement permutation reflection)).relabel rename =
      derivedBeforeLabeled at hrel
  have hrename := derivedBefore_relabel_is_identity
    (decodedHypercubicCharacterElement permutation reflection) rename hrel
  rw [hrename] at hrel
  have hraw : derivedBeforeLabeled.hypercubicAct
      (decodedHypercubicCharacterElement permutation reflection) =
        derivedBeforeLabeled := by
    simpa using hrel
  exact derivedBefore_action_forces_permutation_code_zero
    permutation reflection hraw

theorem derivedBefore_orbit_iff_permutation_code_zero
    (permutation : Fin 24) (reflection : Fin 16) :
    MulAction.orbitRel (Equiv.Perm (Fin 5))
      (LabeledLocalWordSector 5 6) derivedBeforeLabeled
      (derivedBeforeLabeled.hypercubicAct
        (decodedHypercubicCharacterElement permutation reflection)) ↔
      permutation = 0 := by
  constructor
  · exact derivedBefore_orbit_forces_permutation_code_zero permutation reflection
  · intro hzero
    subst permutation
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    refine ⟨1, ?_⟩
    change (derivedBeforeLabeled.hypercubicAct
      (decodedHypercubicCharacterElement 0 reflection)).relabel 1 =
        derivedBeforeLabeled
    rw [LabeledLocalWordSector.relabel_one]
    apply hypercubicAct_eq_of_perm_eq_one
    change permutationCode 0 = 1
    decide +kernel

theorem derivedAfter_relabel_impossible
    (h : Hypercubic4) (rename : Equiv.Perm (Fin 5))
    (hrel : (derivedAfterLabeled.hypercubicAct h).relabel rename =
      derivedBeforeLabeled) :
    False := by
  have hrename := derivedAfter_relabel_is_afterToBefore h rename hrel
  rw [hrename] at hrel
  have hfieldThree := congrArg
    (fun sector : LabeledLocalWordSector 5 6 =>
      (sector.decoration.1 (3 : Fin 5)).plane) hrel
  have hfieldFour := congrArg
    (fun sector : LabeledLocalWordSector 5 6 =>
      (sector.decoration.1 (4 : Fin 5)).plane) hrel
  change planeAction h (planeLookup 0 3) = planeLookup 0 2 at hfieldThree
  change planeAction h (planeLookup 0 2) = planeLookup 0 2 at hfieldFour
  have heq : planeAction h (planeLookup 0 3) =
      planeAction h (planeLookup 0 2) :=
    hfieldThree.trans hfieldFour.symm
  have hinjective : Function.Injective (planeAction h) := by
    intro left right hequal
    have hinverse := congrArg (planeAction (Hypercubic4.inverse h)) hequal
    simpa only [planeAction_inverse_left] using hinverse
  have hplanes : planeLookup 0 3 = planeLookup 0 2 := hinjective heq
  have hne : planeLookup 0 3 ≠ planeLookup 0 2 := by decide +kernel
  exact hne hplanes

theorem derivedAfter_orbit_impossible
    (permutation : Fin 24) (reflection : Fin 16)
    (hsame : MulAction.orbitRel (Equiv.Perm (Fin 5))
      (LabeledLocalWordSector 5 6) derivedBeforeLabeled
      (derivedAfterLabeled.hypercubicAct
        (decodedHypercubicCharacterElement permutation reflection))) :
    False := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hsame
  rcases hsame with ⟨rename, hrel⟩
  change (derivedAfterLabeled.hypercubicAct
    (decodedHypercubicCharacterElement permutation reflection)).relabel rename =
      derivedBeforeLabeled at hrel
  exact derivedAfter_relabel_impossible
    (decodedHypercubicCharacterElement permutation reflection) rename hrel

/-- OUR before-insertion field-relabel orbit. -/
def derivedBeforeFieldFiveOrbit : FieldFiveOrbitCarrier :=
  Quotient.mk _ derivedBeforeLabeled

/-- OUR after-insertion field-relabel orbit. -/
def derivedAfterFieldFiveOrbit : FieldFiveOrbitCarrier :=
  Quotient.mk _ derivedAfterLabeled

theorem derivedBeforeFieldFiveOrbit_action_iff
    (permutation : Fin 24) (reflection : Fin 16) :
    derivedBeforeFieldFiveOrbit.hypercubicAct
        (decodedHypercubicCharacterElement permutation reflection) =
      derivedBeforeFieldFiveOrbit ↔ permutation = 0 := by
  change Quotient.mk _ (derivedBeforeLabeled.hypercubicAct
    (decodedHypercubicCharacterElement permutation reflection)) =
      Quotient.mk _ derivedBeforeLabeled ↔ permutation = 0
  constructor
  · intro hequal
    exact derivedBefore_orbit_forces_permutation_code_zero permutation reflection
      ((MulAction.orbitRel (Equiv.Perm (Fin 5))
        (LabeledLocalWordSector 5 6)).symm (Quotient.exact hequal))
  · intro hzero
    exact Quotient.sound ((MulAction.orbitRel (Equiv.Perm (Fin 5))
      (LabeledLocalWordSector 5 6)).symm
      ((derivedBefore_orbit_iff_permutation_code_zero permutation reflection).mpr
        hzero))

theorem derivedAfterFieldFiveOrbit_action_ne_before
    (permutation : Fin 24) (reflection : Fin 16) :
    derivedAfterFieldFiveOrbit.hypercubicAct
        (decodedHypercubicCharacterElement permutation reflection) ≠
      derivedBeforeFieldFiveOrbit := by
  intro hequal
  change Quotient.mk _ (derivedAfterLabeled.hypercubicAct
    (decodedHypercubicCharacterElement permutation reflection)) =
      Quotient.mk _ derivedBeforeLabeled at hequal
  exact derivedAfter_orbit_impossible permutation reflection
    ((MulAction.orbitRel (Equiv.Perm (Fin 5))
      (LabeledLocalWordSector 5 6)).symm (Quotient.exact hequal))

theorem derivedBeforeLabeled_tensorSign_as_normalized (h : Hypercubic4) :
    derivedBeforeLabeled.tensorSign h =
      (normalizedSectorData
        (insertCurvatureCarrier fieldFourSite .before).2).tensorSign h := by
  change LabeledLocalWordSector.tensorSign h
      (orientedLocalSectorEquivLabeled 5 6
        (normalizedSectorData (insertCurvatureCarrier fieldFourSite .before).2)) = _
  exact orientedLocalSectorEquivLabeled_tensorSign h
    (normalizedSectorData (insertCurvatureCarrier fieldFourSite .before).2)

@[simp] theorem fieldFourBefore_plane (field : Fin 5) :
    planeLookup
      ((insertCurvatureCarrier fieldFourSite .before).2.fieldFirst field)
      ((insertCurvatureCarrier fieldFourSite .before).2.fieldSecond field) =
      if field = 0 then planeLookup 0 3 else
        if field = 1 then planeLookup 2 3 else
          if field = 2 then planeLookup 0 3 else planeLookup 0 2 := by
  fin_cases field <;> rfl

theorem derivedBefore_normalized_tensorSign_product (h : Hypercubic4) :
    (normalizedSectorData
      (insertCurvatureCarrier fieldFourSite .before).2).tensorSign h =
      (planeTensorSign h (planeLookup 0 3) : ℚ) *
        (planeTensorSign h (planeLookup 2 3) *
          (planeTensorSign h (planeLookup 0 3) *
            (planeTensorSign h (planeLookup 0 2) *
              planeTensorSign h (planeLookup 0 2)))) *
        ((Hypercubic4.axisSign h (2 : Axis) : ℚ) *
          (Hypercubic4.axisSign h (0 : Axis) *
            (Hypercubic4.axisSign h (1 : Axis) *
              (Hypercubic4.axisSign h (3 : Axis) *
                (Hypercubic4.axisSign h (0 : Axis) *
                  Hypercubic4.axisSign h (1 : Axis)))))) := by
  unfold OrientedLocalSector.tensorSign normalizedSectorData
  rw [localAxisWordFamilyTensorSign_localize]
  change
    (∏ slot : Fin 5, (planeTensorSign h
      (planeLookup
        ((insertCurvatureCarrier fieldFourSite .before).2.fieldFirst slot)
        ((insertCurvatureCarrier fieldFourSite .before).2.fieldSecond slot)) : ℚ)) *
      ∏ position : Fin 6, (Hypercubic4.axisSign h
        ((insertCurvatureCarrier fieldFourSite .before).2.derivativeWord.axisAtPosition
          position) : ℚ) = _
  repeat rw [Fin.prod_univ_succ]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  repeat rw [fieldFourBefore_plane]
  repeat rw [fieldFourBefore_derivativeAxis]
  rfl

theorem derivedBefore_tensorSign_identity_permutation
    (reflection : Fin 16) :
    derivedBeforeLabeled.tensorSign
      (decodedHypercubicCharacterElement 0 reflection) = 1 := by
  rw [derivedBeforeLabeled_tensorSign_as_normalized,
    derivedBefore_normalized_tensorSign_product,
    fieldFive_plane03_tensorSign,
    fieldFive_plane23_tensorSign,
    fieldFive_plane02_tensorSign]
  have hzero : Hypercubic4.axisSign
      (decodedHypercubicCharacterElement 0 reflection) 0 ^ 2 = 1 := by
    unfold Hypercubic4.axisSign
    split <;> norm_num
  have hone : Hypercubic4.axisSign
      (decodedHypercubicCharacterElement 0 reflection) 1 ^ 2 = 1 := by
    unfold Hypercubic4.axisSign
    split <;> norm_num
  have htwo : Hypercubic4.axisSign
      (decodedHypercubicCharacterElement 0 reflection) 2 ^ 2 = 1 := by
    unfold Hypercubic4.axisSign
    split <;> norm_num
  have hthree : Hypercubic4.axisSign
      (decodedHypercubicCharacterElement 0 reflection) 3 ^ 2 = 1 := by
    unfold Hypercubic4.axisSign
    split <;> norm_num
  calc
    _ = Hypercubic4.axisSign
          (decodedHypercubicCharacterElement 0 reflection) 0 ^ 6 *
        Hypercubic4.axisSign
          (decodedHypercubicCharacterElement 0 reflection) 1 ^ 2 *
        Hypercubic4.axisSign
          (decodedHypercubicCharacterElement 0 reflection) 2 ^ 4 *
        Hypercubic4.axisSign
          (decodedHypercubicCharacterElement 0 reflection) 3 ^ 4 := by ring
    _ = 1 := by
      have hzeroSix : Hypercubic4.axisSign
          (decodedHypercubicCharacterElement 0 reflection) 0 ^ 6 = 1 := by
        calc
          Hypercubic4.axisSign
              (decodedHypercubicCharacterElement 0 reflection) 0 ^ 6 =
              (Hypercubic4.axisSign
                (decodedHypercubicCharacterElement 0 reflection) 0 ^ 2) ^ 3 := by ring
          _ = 1 := by rw [hzero]; norm_num
      have htwoFour : Hypercubic4.axisSign
          (decodedHypercubicCharacterElement 0 reflection) 2 ^ 4 = 1 := by
        calc
          Hypercubic4.axisSign
              (decodedHypercubicCharacterElement 0 reflection) 2 ^ 4 =
              (Hypercubic4.axisSign
                (decodedHypercubicCharacterElement 0 reflection) 2 ^ 2) ^ 2 := by ring
          _ = 1 := by rw [htwo]; norm_num
      have hthreeFour : Hypercubic4.axisSign
          (decodedHypercubicCharacterElement 0 reflection) 3 ^ 4 = 1 := by
        calc
          Hypercubic4.axisSign
              (decodedHypercubicCharacterElement 0 reflection) 3 ^ 4 =
              (Hypercubic4.axisSign
                (decodedHypercubicCharacterElement 0 reflection) 3 ^ 2) ^ 2 := by ring
          _ = 1 := by rw [hthree]; norm_num
      rw [hzeroSix, hone, htwoFour, hthreeFour]
      norm_num

theorem derivedBeforeFieldFiveOrbit_tensorSign_identity_permutation
    (reflection : Fin 16) :
    derivedBeforeFieldFiveOrbit.tensorSign
      (decodedHypercubicCharacterElement 0 reflection) = 1 := by
  change FieldRelabelOrbitCarrier.tensorSign
      (decodedHypercubicCharacterElement 0 reflection)
      (Quotient.mk _ derivedBeforeLabeled : FieldFiveOrbitCarrier) = 1
  rw [FieldRelabelOrbitCarrier.tensorSign_mk]
  exact derivedBefore_tensorSign_identity_permutation reflection

/-- OUR signed pair of normalized field-five curvature-insertion orbits. -/
noncomputable def derivedFieldFiveCommutatorVector : FieldFiveOrbitSpace :=
  -Finsupp.single derivedBeforeFieldFiveOrbit 1 +
    Finsupp.single derivedAfterFieldFiveOrbit 1

theorem derivedFieldFiveCommutator_reynolds_coordinate_formula :
    (sectorFieldOrbitReynolds 5 6 derivedFieldFiveCommutatorVector)
        derivedBeforeFieldFiveOrbit =
      (1 / 384 : ℚ) * ∑ h : Hypercubic4,
        (-(if derivedBeforeFieldFiveOrbit.hypercubicAct h =
              derivedBeforeFieldFiveOrbit then
            derivedBeforeFieldFiveOrbit.tensorSign h else 0) +
          if derivedAfterFieldFiveOrbit.hypercubicAct h =
              derivedBeforeFieldFiveOrbit then
            derivedAfterFieldFiveOrbit.tensorSign h else 0) := by
  unfold sectorFieldOrbitReynolds derivedFieldFiveCommutatorVector
  rw [LinearMap.smul_apply, LinearMap.sum_apply,
    Finsupp.smul_apply, Finset.sum_apply']
  simp only [LinearMap.map_add, LinearMap.map_neg,
    signedSectorFieldOrbitAction_single, one_mul, smul_eq_mul]
  apply congrArg (fun total : ℚ => (1 / 384 : ℚ) * total)
  apply Finset.sum_congr rfl
  intro h _
  by_cases hbefore : derivedBeforeFieldFiveOrbit.hypercubicAct h =
      derivedBeforeFieldFiveOrbit
  · simp [Finsupp.single_apply, hbefore]
  · simp [Finsupp.single_apply, hbefore]

noncomputable def derivedFieldFiveCoordinateSummand (h : Hypercubic4) : ℚ :=
  -(if derivedBeforeFieldFiveOrbit.hypercubicAct h = derivedBeforeFieldFiveOrbit then
      derivedBeforeFieldFiveOrbit.tensorSign h else 0) +
    if derivedAfterFieldFiveOrbit.hypercubicAct h = derivedBeforeFieldFiveOrbit then
      derivedAfterFieldFiveOrbit.tensorSign h else 0

theorem derivedFieldFiveCoordinateSummand_code
    (permutation : Fin 24) (reflection : Fin 16) :
    derivedFieldFiveCoordinateSummand
      (decodedHypercubicCharacterElement permutation reflection) =
      if permutation = 0 then (-1 : ℚ) else 0 := by
  by_cases hzero : permutation = 0
  · subst permutation
    rw [derivedFieldFiveCoordinateSummand,
      if_pos ((derivedBeforeFieldFiveOrbit_action_iff 0 reflection).mpr rfl),
      if_neg (derivedAfterFieldFiveOrbit_action_ne_before 0 reflection)]
    rw [derivedBeforeFieldFiveOrbit_tensorSign_identity_permutation]
    norm_num
  · rw [derivedFieldFiveCoordinateSummand,
      if_neg ((derivedBeforeFieldFiveOrbit_action_iff permutation reflection).not.mpr
        hzero),
      if_neg (derivedAfterFieldFiveOrbit_action_ne_before permutation reflection),
      if_neg hzero]
    norm_num

theorem derivedFieldFiveCoordinateSummand_sum_exact :
    (∑ h : Hypercubic4, derivedFieldFiveCoordinateSummand h) = -16 := by
  calc
    (∑ h : Hypercubic4, derivedFieldFiveCoordinateSummand h) =
        ∑ code : Fin 24 × Fin 16,
          derivedFieldFiveCoordinateSummand (hypercubicCharacterCodeEquiv code) := by
      exact (Equiv.sum_comp hypercubicCharacterCodeEquiv
        derivedFieldFiveCoordinateSummand).symm
    _ = ∑ permutation : Fin 24, ∑ reflection : Fin 16,
          fieldFiveCoordinateCode permutation reflection := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro permutation _
      apply Finset.sum_congr rfl
      intro reflection _
      simpa [hypercubicCharacterCodeEquiv, fieldFiveCoordinateCode] using
        (derivedFieldFiveCoordinateSummand_code permutation reflection)
    _ = -16 := fieldFiveCoordinateCodeSum_exact

/-- OUR exact nonzero Reynolds coordinate of the physical insertion pair. -/
theorem derivedFieldFiveCommutator_reynolds_coordinate_exact :
    (sectorFieldOrbitReynolds 5 6 derivedFieldFiveCommutatorVector)
        derivedBeforeFieldFiveOrbit = -(1 : ℚ) / 24 := by
  rw [derivedFieldFiveCommutator_reynolds_coordinate_formula]
  have hsum :
      (∑ h : Hypercubic4,
        (-(if derivedBeforeFieldFiveOrbit.hypercubicAct h =
              derivedBeforeFieldFiveOrbit then
            derivedBeforeFieldFiveOrbit.tensorSign h else 0) +
          if derivedAfterFieldFiveOrbit.hypercubicAct h =
              derivedBeforeFieldFiveOrbit then
            derivedAfterFieldFiveOrbit.tensorSign h else 0)) = -16 := by
    simpa [derivedFieldFiveCoordinateSummand] using
      derivedFieldFiveCoordinateSummand_sum_exact
  rw [hsum]
  norm_num

/-- OUR physical-relation generator induced by the four-field commutator
site. -/
def fieldFourCommutatorGenerator
    (policy : PhysicalRelationPolicy) : PhysicalRelationGenerator policy :=
  .covariantCommutator fieldFourCarrier fieldFourSite

/-- OUR exact target of the unswapped four-field derivative source. -/
def fieldFourCommutatorSourceExactTarget : ExactFieldRelabelOrbitCarrier :=
  exactFieldRelabelOrbitOfOriented
    (exactNormalizedSectorData fieldFourCarrier)

/-- OUR exact target of the swapped four-field derivative source. -/
def fieldFourCommutatorSwappedExactTarget : ExactFieldRelabelOrbitCarrier :=
  exactFieldRelabelOrbitOfOriented
    (exactNormalizedSectorData
      (swapExactDerivativePositions fieldFourCarrier
        fieldFourSite.outer fieldFourSite.inner))

/-- OUR common exact index for the field-five insertion sector. -/
def ourFiveFieldCount : Fin 9 := ⟨5, by decide⟩

/-- OUR exact target of one normalized field-five curvature insertion. -/
abbrev fieldFiveInsertionExactTarget
    (side : CurvatureInsertionSide) : ExactFieldRelabelOrbitCarrier :=
  ⟨ourFiveFieldCount,
    if side = .before then derivedBeforeFieldFiveOrbit else
      derivedAfterFieldFiveOrbit⟩

theorem fieldFourCommutator_source_orientationCoefficient :
    fieldAxisOrientationCoefficient
        (sectorFieldAxisAssignment fieldFourCarrier.2) = 1 := by
  decide +kernel

theorem fieldFourCommutator_swapped_orientationCoefficient :
    fieldAxisOrientationCoefficient
        (sectorFieldAxisAssignment
          (swapExactDerivativePositions fieldFourCarrier
            fieldFourSite.outer fieldFourSite.inner).2) = 1 := by
  decide +kernel

theorem fieldFourCommutator_before_orientationCoefficient :
    fieldAxisOrientationCoefficient
        (sectorFieldAxisAssignment
          (insertCurvatureCarrier fieldFourSite .before).2) = 1 := by
  decide +kernel

theorem fieldFourCommutator_after_orientationCoefficient :
    fieldAxisOrientationCoefficient
        (sectorFieldAxisAssignment
          (insertCurvatureCarrier fieldFourSite .after).2) = 1 := by
  decide +kernel

theorem normalizeExactContextualBasis_fieldRelabel
    (carrier : RelationCarrier) :
    normalizeExactFieldRelabel (normalizeExactContextualBasis carrier) =
      Finsupp.single
        (exactFieldRelabelOrbitOfOriented
          (exactNormalizedSectorData carrier))
        (fieldAxisOrientationCoefficient
          (sectorFieldAxisAssignment carrier.2)) := by
  simp [normalizeExactContextualBasis,
    normalizeExactFieldRelabelBasis]

theorem exactFieldRelabelOrbitOfOriented_fieldFiveInsertion
    (side : CurvatureInsertionSide) :
    exactFieldRelabelOrbitOfOriented
        (exactNormalizedSectorData
          (insertCurvatureCarrier fieldFourSite side)) =
      fieldFiveInsertionExactTarget side := by
  cases side <;> rfl

/-- The full exact physical column of OUR four-field commutator. -/
theorem orbitPhysicalRelationOperator_fieldFourCommutator_full
    (policy : PhysicalRelationPolicy) :
    orbitPhysicalRelationOperator policy
        (Finsupp.single (fieldFourCommutatorGenerator policy) 1) =
      Finsupp.single fieldFourCommutatorSourceExactTarget 1 -
        Finsupp.single fieldFourCommutatorSwappedExactTarget 1 -
          Finsupp.single
            (fieldFiveInsertionExactTarget CurvatureInsertionSide.before) 1 +
            Finsupp.single
              (fieldFiveInsertionExactTarget CurvatureInsertionSide.after) 1 := by
  simp only [orbitPhysicalRelationOperator,
    normalizedPhysicalRelationOperator,
    LinearMap.comp_apply, physicalRelationOperator_single, one_smul,
    fieldFourCommutatorGenerator, physicalRelationRow,
    covariantCommutatorRow, map_sub, map_add,
    normalizeExactContextual_single]
  simp_rw [normalizeExactContextualBasis_fieldRelabel]
  rw [exactFieldRelabelOrbitOfOriented_fieldFiveInsertion,
    exactFieldRelabelOrbitOfOriented_fieldFiveInsertion,
    fieldFourCommutator_source_orientationCoefficient,
    fieldFourCommutator_swapped_orientationCoefficient,
    fieldFourCommutator_before_orientationCoefficient,
    fieldFourCommutator_after_orientationCoefficient]
  simp [fieldFourCommutatorSourceExactTarget,
    fieldFourCommutatorSwappedExactTarget]

/-- OUR dependent cast from an exact field-five fibre to the five-field
orbit fibre. -/
def exactFieldFiveOrbitCast (fieldCount : Fin 9)
    (h : fieldCount = ourFiveFieldCount) :
    FieldRelabelOrbitCarrier fieldCount.1
      (dimension16DerivativeCount fieldCount) →
      FieldFiveOrbitCarrier :=
  cast (by subst fieldCount; rfl)

@[simp] theorem exactFieldFiveOrbitCast_self
    (orbit : FieldFiveOrbitCarrier)
    (h : ourFiveFieldCount = ourFiveFieldCount) :
    exactFieldFiveOrbitCast ourFiveFieldCount h orbit = orbit := by
  cases Subsingleton.elim h rfl
  rfl

@[simp] theorem exactFieldFiveOrbitCast_five
    (orbit : FieldFiveOrbitCarrier)
    (h : (5 : Fin 9) = ourFiveFieldCount) :
    exactFieldFiveOrbitCast (5 : Fin 9) h orbit = orbit := by
  unfold ourFiveFieldCount at h
  cases Subsingleton.elim h rfl
  rfl

/-- OUR exact field-five component of a full orbit-carrier basis vector. -/
def exactFieldFiveProjectionBasis
    (target : ExactFieldRelabelOrbitCarrier) : FieldFiveOrbitSpace :=
  match target with
  | ⟨fieldCount, orbit⟩ =>
      if h : fieldCount = ourFiveFieldCount then
        Finsupp.single (exactFieldFiveOrbitCast fieldCount h orbit) 1
      else 0

/-- OUR linear projection from the full exact carrier to the field-five
sector. -/
def exactFieldFiveProjection : ExactFieldRelabelOrbitSpace →ₗ[ℚ]
    FieldFiveOrbitSpace :=
  Finsupp.linearCombination ℚ exactFieldFiveProjectionBasis

@[simp] theorem exactFieldFiveProjection_single
    (target : ExactFieldRelabelOrbitCarrier) (coefficient : ℚ) :
    exactFieldFiveProjection (Finsupp.single target coefficient) =
      coefficient • exactFieldFiveProjectionBasis target := by
  simp [exactFieldFiveProjection]

theorem exactFieldFiveProjection_single_of_fieldCount_ne
    (target : ExactFieldRelabelOrbitCarrier) (coefficient : ℚ)
    (hne : target.1 ≠ ourFiveFieldCount) :
    exactFieldFiveProjection (Finsupp.single target coefficient) = 0 := by
  rw [exactFieldFiveProjection_single]
  rcases target with ⟨fieldCount, orbit⟩
  simp [exactFieldFiveProjectionBasis, hne]

theorem exactFieldFiveProjection_single_of_fieldCount_val_ne
    (target : ExactFieldRelabelOrbitCarrier) (coefficient : ℚ)
    (hne : target.1.1 ≠ ourFiveFieldCount.1) :
    exactFieldFiveProjection (Finsupp.single target coefficient) = 0 := by
  apply exactFieldFiveProjection_single_of_fieldCount_ne
  intro hequal
  exact hne (congrArg Fin.val hequal)

theorem exactFieldFiveProjection_fieldFourSource_zero :
    exactFieldFiveProjection
      (Finsupp.single fieldFourCommutatorSourceExactTarget 1) = 0 := by
  apply exactFieldFiveProjection_single_of_fieldCount_ne
  change (4 : Fin 9) ≠ ourFiveFieldCount
  intro hequal
  have hvalue := congrArg Fin.val hequal
  change 4 = 5 at hvalue
  omega

theorem exactFieldFiveProjection_fieldFourSwapped_zero :
    exactFieldFiveProjection
      (Finsupp.single fieldFourCommutatorSwappedExactTarget 1) = 0 := by
  apply exactFieldFiveProjection_single_of_fieldCount_ne
  change (swapExactDerivativePositions fieldFourCarrier
    fieldFourSite.outer fieldFourSite.inner).1 ≠ ourFiveFieldCount
  intro hequal
  have hvalue := congrArg Fin.val hequal
  change 4 = 5 at hvalue
  omega

/-
The exact projection is formulated on the dependent orbit fibre.
-/
/-
The four-field derivative targets lie outside the field-five fibre.
-/
/-
The source and insertion fibres have distinct field counts.
-/
theorem exactFieldFiveProjection_fieldFiveInsertion
    (side : CurvatureInsertionSide) :
    exactFieldFiveProjection
      (Finsupp.single (fieldFiveInsertionExactTarget side) 1) =
      if side = .before then
        Finsupp.single derivedBeforeFieldFiveOrbit 1 else
          Finsupp.single derivedAfterFieldFiveOrbit 1 := by
  rw [exactFieldFiveProjection_single]
  cases side <;>
    simp [exactFieldFiveProjectionBasis, ourFiveFieldCount,
      exactFieldFiveOrbitCast_five]

theorem exactFieldFiveProjection_fieldFourCommutator
    (policy : PhysicalRelationPolicy) :
    exactFieldFiveProjection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (fieldFourCommutatorGenerator policy) 1)) =
      derivedFieldFiveCommutatorVector := by
  rw [orbitPhysicalRelationOperator_fieldFourCommutator_full]
  simp only [LinearMap.map_add, LinearMap.map_sub,
    exactFieldFiveProjection_fieldFourSource_zero,
    exactFieldFiveProjection_fieldFourSwapped_zero,
    exactFieldFiveProjection_fieldFiveInsertion]
  simp [derivedFieldFiveCommutatorVector]

theorem exactFieldFiveOrbitCast_hypercubicAct
    (h : Hypercubic4) (fieldCount : Fin 9)
    (hfield : fieldCount = ourFiveFieldCount)
    (orbit : FieldRelabelOrbitCarrier fieldCount.1
      (dimension16DerivativeCount fieldCount)) :
    exactFieldFiveOrbitCast fieldCount hfield (orbit.hypercubicAct h) =
      (exactFieldFiveOrbitCast fieldCount hfield orbit).hypercubicAct h := by
  subst fieldCount
  rfl

theorem exactFieldFiveOrbitCast_tensorSign
    (h : Hypercubic4) (fieldCount : Fin 9)
    (hfield : fieldCount = ourFiveFieldCount)
    (orbit : FieldRelabelOrbitCarrier fieldCount.1
      (dimension16DerivativeCount fieldCount)) :
    (exactFieldFiveOrbitCast fieldCount hfield orbit).tensorSign h =
      orbit.tensorSign h := by
  subst fieldCount
  rfl

theorem exactFieldFiveProjection_signed_action
    (h : Hypercubic4) (value : ExactFieldRelabelOrbitSpace) :
    exactFieldFiveProjection (signedExactFieldRelabelOrbitAction h value) =
      signedSectorFieldOrbitAction h 5 6 (exactFieldFiveProjection value) := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      simp [hleft, hright]
  | single target coefficient =>
      rcases target with ⟨fieldCount, orbit⟩
      by_cases hfield : fieldCount = ourFiveFieldCount
      · subst fieldCount
        simp [exactFieldFiveProjection, exactFieldFiveProjectionBasis,
          signedExactFieldRelabelOrbitAction_single,
          exactFieldRelabelOrbitAct,
          exactFieldRelabelOrbitTensorSign,
          signedSectorFieldOrbitAction_single,
          ourFiveFieldCount]
        apply congrArg (fun target : FieldFiveOrbitCarrier =>
          Finsupp.single target (coefficient * orbit.tensorSign h))
        exact exactFieldFiveOrbitCast_hypercubicAct h _ rfl orbit
      · simp [exactFieldFiveProjection, exactFieldFiveProjectionBasis,
          signedExactFieldRelabelOrbitAction_single,
          exactFieldRelabelOrbitAct,
          exactFieldRelabelOrbitTensorSign,
          hfield]

theorem exactFieldFiveProjection_exactFieldOrbitReynolds
    (value : ExactFieldRelabelOrbitSpace) :
    exactFieldFiveProjection (exactFieldOrbitReynolds value) =
      sectorFieldOrbitReynolds 5 6 (exactFieldFiveProjection value) := by
  unfold exactFieldOrbitReynolds sectorFieldOrbitReynolds
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  simp_rw [exactFieldFiveProjection_signed_action]

/-- OUR coordinate functional at the before-insertion five-field orbit. -/
def fieldFiveCoordinate : FieldFiveOrbitSpace →ₗ[ℚ] ℚ :=
  Finsupp.lapply derivedBeforeFieldFiveOrbit

theorem fieldFiveCoordinate_reynolds_pair :
    fieldFiveCoordinate
      (sectorFieldOrbitReynolds 5 6 derivedFieldFiveCommutatorVector) =
      -(1 : ℚ) / 24 := by
  exact derivedFieldFiveCommutator_reynolds_coordinate_exact

/-- OUR Reynolds-averaged full physical row for the four-field commutator. -/
def fieldFourInvariantCommutatorRow
    (policy : PhysicalRelationPolicy) : exactFieldOrbitInvariantSubmodule :=
  ⟨exactFieldOrbitReynolds
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (fieldFourCommutatorGenerator policy) 1)),
    exactFieldOrbitReynolds_invariant _⟩

theorem fieldFourInvariantCommutatorRow_mem
    (policy : PhysicalRelationPolicy) :
    fieldFourInvariantCommutatorRow policy ∈
      jointInvariantRelationSubmodule policy := by
  rw [mem_jointInvariantRelationSubmodule_iff]
  change exactFieldOrbitReynolds
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (fieldFourCommutatorGenerator policy) 1)) ∈
      orbitPhysicalRelationSubmodule policy
  unfold exactFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply]
  apply (orbitPhysicalRelationSubmodule policy).smul_mem
  apply Submodule.sum_mem
  intro h _
  apply orbitPhysicalRelationSubmodule_signed_invariant policy h
  exact ⟨Finsupp.single (fieldFourCommutatorGenerator policy) 1, rfl⟩

theorem exactFieldFiveProjection_fieldFourInvariantCommutatorRow
    (policy : PhysicalRelationPolicy) :
    exactFieldFiveProjection (fieldFourInvariantCommutatorRow policy).1 =
      sectorFieldOrbitReynolds 5 6 derivedFieldFiveCommutatorVector := by
  change exactFieldFiveProjection
      (exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (fieldFourCommutatorGenerator policy) 1))) = _
  rw [exactFieldFiveProjection_exactFieldOrbitReynolds,
    exactFieldFiveProjection_fieldFourCommutator]

theorem fieldFourInvariantCommutatorRow_ne_zero
    (policy : PhysicalRelationPolicy) :
    fieldFourInvariantCommutatorRow policy ≠ 0 := by
  intro hzero
  have hcoordinate := congrArg
    (fun value : exactFieldOrbitInvariantSubmodule =>
      fieldFiveCoordinate (exactFieldFiveProjection value.1)) hzero
  change fieldFiveCoordinate
      (exactFieldFiveProjection (fieldFourInvariantCommutatorRow policy).1) =
      fieldFiveCoordinate (exactFieldFiveProjection 0) at hcoordinate
  rw [exactFieldFiveProjection_fieldFourInvariantCommutatorRow,
    fieldFiveCoordinate_reynolds_pair] at hcoordinate
  norm_num at hcoordinate

/-- OUR typed nonzero invariant physical commutator relation. -/
def fieldFourInvariantCommutatorRelation
    (policy : PhysicalRelationPolicy) :
    jointInvariantRelationSubmodule policy :=
  ⟨fieldFourInvariantCommutatorRow policy,
    fieldFourInvariantCommutatorRow_mem policy⟩

theorem fieldFourInvariantCommutatorRelation_ne_zero
    (policy : PhysicalRelationPolicy) :
    fieldFourInvariantCommutatorRelation policy ≠ 0 := by
  intro hzero
  apply fieldFourInvariantCommutatorRow_ne_zero policy
  exact congrArg Subtype.val hzero

theorem exactFieldFiveProjection_fieldEightExactEmbed_zero
    (value : FieldEightOrbitSpace) :
    exactFieldFiveProjection (fieldEightExactEmbed value) = 0 := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      simp [hleft, hright]
  | single target coefficient =>
      rw [fieldEightExactEmbed_single]
      apply exactFieldFiveProjection_single_of_fieldCount_val_ne
      change 8 ≠ ourFiveFieldCount.1
      simp [ourFiveFieldCount]

/-- OUR field-five coordinate restricted to the genuine joint invariant
relation submodule. -/
def ourJointFieldFiveCoordinate
    (policy : PhysicalRelationPolicy) :
    jointInvariantRelationSubmodule policy →ₗ[ℚ] ℚ :=
  fieldFiveCoordinate.comp
    (exactFieldFiveProjection.comp
      (exactFieldOrbitInvariantSubmodule.subtype.comp
        (jointInvariantRelationSubmodule policy).subtype))

theorem ourJointFieldFiveCoordinate_fieldFourCommutator
    (policy : PhysicalRelationPolicy) :
    ourJointFieldFiveCoordinate policy
        (fieldFourInvariantCommutatorRelation policy) = -(1 : ℚ) / 24 := by
  change fieldFiveCoordinate
      (exactFieldFiveProjection (fieldFourInvariantCommutatorRow policy).1) = _
  rw [exactFieldFiveProjection_fieldFourInvariantCommutatorRow,
    fieldFiveCoordinate_reynolds_pair]

theorem ourJointFieldFiveCoordinate_traceRelation_zero
    (policy : PhysicalRelationPolicy) (generator : FieldEightTraceGenerator) :
    ourJointFieldFiveCoordinate policy
        (ourInvariantFieldEightTraceRelation policy generator) = 0 := by
  change fieldFiveCoordinate
      (exactFieldFiveProjection
        (exactFieldOrbitReynolds
          (orbitPhysicalRelationOperator policy
            (Finsupp.single (ourLiftFieldEightTraceGenerator policy generator) 1)))) = 0
  rw [exactFieldFiveProjection_exactFieldOrbitReynolds,
    ourOrbitPhysicalRelationOperator_lift,
    exactFieldFiveProjection_fieldEightExactEmbed_zero]
  simp

theorem exactFieldFiveProjection_ourCommutatorSource_zero :
    exactFieldFiveProjection
      (Finsupp.single ourCommutatorSourceExactTarget 1) = 0 := by
  apply exactFieldFiveProjection_single_of_fieldCount_val_ne
  change 7 ≠ ourFiveFieldCount.1
  simp [ourFiveFieldCount]

theorem exactFieldFiveProjection_ourCommutatorSwapped_zero :
    exactFieldFiveProjection
      (Finsupp.single ourCommutatorSwappedExactTarget 1) = 0 := by
  apply exactFieldFiveProjection_single_of_fieldCount_val_ne
  change 7 ≠ ourFiveFieldCount.1
  simp [ourFiveFieldCount]

theorem exactFieldFiveProjection_ourCommutatorInsertion_zero
    (side : CurvatureInsertionSide) :
    exactFieldFiveProjection
      (Finsupp.single (ourCommutatorInsertionExactTarget side) 1) = 0 := by
  apply exactFieldFiveProjection_single_of_fieldCount_val_ne
  change 8 ≠ ourFiveFieldCount.1
  simp [ourFiveFieldCount]

theorem exactFieldFiveProjection_ourCommutator_zero
    (policy : PhysicalRelationPolicy) :
    exactFieldFiveProjection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) = 0 := by
  rw [orbitPhysicalRelationOperator_ourCommutator_full]
  simp only [LinearMap.map_add, LinearMap.map_sub,
    exactFieldFiveProjection_ourCommutatorSource_zero,
    exactFieldFiveProjection_ourCommutatorSwapped_zero,
    exactFieldFiveProjection_ourCommutatorInsertion_zero]
  simp

theorem ourJointFieldFiveCoordinate_commutator_zero
    (policy : PhysicalRelationPolicy) :
    ourJointFieldFiveCoordinate policy
      (ourInvariantCommutatorRelation policy) = 0 := by
  change fieldFiveCoordinate
      (exactFieldFiveProjection
        (exactFieldOrbitReynolds
          (orbitPhysicalRelationOperator policy
            (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)))) = 0
  rw [exactFieldFiveProjection_exactFieldOrbitReynolds,
    exactFieldFiveProjection_ourCommutator_zero]
  simp

/-- OUR field-five invariant row lies outside the span of the certified
field-eight trace family and the earlier seven-to-eight commutator row. -/
theorem fieldFourInvariantCommutator_not_mem_traceCommutatorSpan
    (policy : PhysicalRelationPolicy) :
    fieldFourInvariantCommutatorRelation policy ∉
      (Submodule.span ℚ
        (Set.range fun index : Fin 11556 =>
          ourInvariantFieldEightTraceRelation policy
            (selectedPhysicalGenerator index)) ⊔
        Submodule.span ℚ {ourInvariantCommutatorRelation policy} :
          Submodule ℚ (jointInvariantRelationSubmodule policy)) := by
  intro hmem
  have hkernel :
      (Submodule.span ℚ
        (Set.range fun index : Fin 11556 =>
          ourInvariantFieldEightTraceRelation policy
            (selectedPhysicalGenerator index)) ⊔
        Submodule.span ℚ {ourInvariantCommutatorRelation policy} :
          Submodule ℚ (jointInvariantRelationSubmodule policy)) ≤
        LinearMap.ker (ourJointFieldFiveCoordinate policy) := by
    apply sup_le
    · apply Submodule.span_le.mpr
      rintro value ⟨index, rfl⟩
      exact LinearMap.mem_ker.mpr
        (ourJointFieldFiveCoordinate_traceRelation_zero
          policy (selectedPhysicalGenerator index))
    · apply Submodule.span_le.mpr
      rintro value rfl
      exact LinearMap.mem_ker.mpr
        (ourJointFieldFiveCoordinate_commutator_zero policy)
  have hzero : ourJointFieldFiveCoordinate policy
      (fieldFourInvariantCommutatorRelation policy) = 0 :=
    LinearMap.mem_ker.mp (hkernel hmem)
  rw [ourJointFieldFiveCoordinate_fieldFourCommutator] at hzero
  norm_num at hzero

/-- OUR certified field-five extension raises the joint invariant physical
relation-rank lower bound to `11558`. -/
theorem jointInvariantRelationSubmodule_rank_lower_bound_fieldFiveCommutator
    (policy : PhysicalRelationPolicy) :
    11558 ≤ Module.finrank ℚ (jointInvariantRelationSubmodule policy) := by
  let traceSpan : Submodule ℚ (jointInvariantRelationSubmodule policy) :=
    Submodule.span ℚ
      (Set.range fun index : Fin 11556 =>
        ourInvariantFieldEightTraceRelation policy
          (selectedPhysicalGenerator index))
  let traceCommutatorSpan : Submodule ℚ
      (jointInvariantRelationSubmodule policy) :=
    traceSpan ⊔ Submodule.span ℚ {ourInvariantCommutatorRelation policy}
  have htraceRank : Module.finrank ℚ traceSpan = 11556 := by
    dsimp [traceSpan]
    rw [finrank_span_eq_card
      (ourInvariantFieldEightTraceRelations_linearIndependent policy)]
    simp
  have hcommutatorNotMem : ourInvariantCommutatorRelation policy ∉ traceSpan := by
    dsimp [traceSpan]
    exact ourInvariantCommutator_not_mem_transferredTraceSpan policy
  have htraceCommutatorRank :
      Module.finrank ℚ traceCommutatorSpan = 11557 := by
    dsimp [traceCommutatorSpan]
    rw [Submodule.finrank_sup_span_singleton (p := traceSpan)
      (v := ourInvariantCommutatorRelation policy) hcommutatorNotMem,
      htraceRank]
  have hfieldFiveNotMem :
      fieldFourInvariantCommutatorRelation policy ∉ traceCommutatorSpan := by
    dsimp [traceCommutatorSpan, traceSpan]
    exact fieldFourInvariantCommutator_not_mem_traceCommutatorSpan policy
  have haugmentedRank :
      Module.finrank ℚ
        (traceCommutatorSpan ⊔
          Submodule.span ℚ {fieldFourInvariantCommutatorRelation policy} :
          Submodule ℚ (jointInvariantRelationSubmodule policy)) = 11558 := by
    rw [Submodule.finrank_sup_span_singleton (p := traceCommutatorSpan)
      (v := fieldFourInvariantCommutatorRelation policy) hfieldFiveNotMem,
      htraceCommutatorRank]
  calc
    11558 = Module.finrank ℚ
        (traceCommutatorSpan ⊔
          Submodule.span ℚ {fieldFourInvariantCommutatorRelation policy} :
          Submodule ℚ (jointInvariantRelationSubmodule policy)) :=
      haugmentedRank.symm
    _ ≤ Module.finrank ℚ (jointInvariantRelationSubmodule policy) :=
      Submodule.finrank_le _

#print axioms fieldFour_retainedDerivativeOrderEmbedding
#print axioms derivedBeforeFieldFiveOrbit_action_iff
#print axioms derivedAfterFieldFiveOrbit_action_ne_before
#print axioms derivedFieldFiveCommutator_reynolds_coordinate_exact
#print axioms exactFieldFiveProjection_signed_action
#print axioms fieldFourInvariantCommutatorRelation_ne_zero
#print axioms fieldFourInvariantCommutator_not_mem_traceCommutatorSpan
#print axioms jointInvariantRelationSubmodule_rank_lower_bound_fieldFiveCommutator

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FieldFiveCommutatorSeparator
