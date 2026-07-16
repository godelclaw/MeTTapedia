import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16ContextualQuotient

/-!
# Bridge from the exact quotient target to the local-word orbit carrier

The exact contextual quotient uses a trace layout, one oriented plane per
field, and one owner-local axis list per field.  The finite local-word carrier
packages the same data with each list represented by a bounded function.
This module constructs the explicit sectorwise equivalence and proves that it
commutes with field relabeling and the hypercubic action while preserving the
tensor sign.  It then descends the equivalence to genuine field-label orbit
quotients.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16OrbitCarrierBridge

open HypercubicDimension16ContextualQuotient
open HypercubicDimension16ShuffleQuotient
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16AntisymmetryQuotient
open HypercubicUnpaddedFDSyntax
open V14HypercubicFDCensus
open V14HypercubicQuarticCensus
open SU2LatticeFDCensusNoGo

/-! ## Finite packaging equivalence -/

def localFieldLetterOfDerivativeLetter {derivativeCount : ℕ}
    (plane : OrientedPlane) (letter : LocalDerivativeLetter derivativeCount) :
    LocalFieldLetter derivativeCount where
  plane := plane
  derivativeCount := letter.derivativeCount
  derivativeAxis := letter.derivativeAxis

def planeDerivativeFamilyEquivDecorationFinite
    (fieldCount derivativeCount : ℕ) :
    (OrientedFieldAssignment fieldCount ×
        LocalDerivativeWordFamily fieldCount derivativeCount) ≃
      LocalWordDecoration fieldCount derivativeCount where
  toFun data :=
    ⟨fun field =>
      localFieldLetterOfDerivativeLetter (data.1 field) (data.2.1 field), by
      simpa [localFieldLetterOfDerivativeLetter] using data.2.2⟩
  invFun decoration :=
    (fun field => (decoration.1 field).plane,
      ⟨fun field =>
        { derivativeCount := (decoration.1 field).derivativeCount
          derivativeAxis := (decoration.1 field).derivativeAxis }, by
        simpa using decoration.2⟩)
  left_inv data := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      funext field
      rfl
  right_inv decoration := by
    apply Subtype.ext
    funext field
    rfl

def planeDerivativeFamilyEquivDecoration
    (fieldCount derivativeCount : ℕ) :
    (OrientedFieldAssignment fieldCount ×
        LocalAxisWordFamily fieldCount derivativeCount) ≃
      LocalWordDecoration fieldCount derivativeCount :=
  ((Equiv.refl (OrientedFieldAssignment fieldCount)).prodCongr
      (localAxisWordFamilyEquivDerivativeFamily fieldCount derivativeCount)).trans
    (planeDerivativeFamilyEquivDecorationFinite fieldCount derivativeCount)

def orientedLocalSectorEquivLabeled
    (fieldCount derivativeCount : ℕ) :
    OrientedLocalSector fieldCount derivativeCount ≃
      LabeledLocalWordSector fieldCount derivativeCount where
  toFun sector :=
    { trace := sector.trace.traceOrder
      decoration := planeDerivativeFamilyEquivDecoration
        fieldCount derivativeCount
        (sector.fieldPlanes, sector.derivativeFamily) }
  invFun sector :=
    let data := (planeDerivativeFamilyEquivDecoration
      fieldCount derivativeCount).symm sector.decoration
    { trace := { traceOrder := sector.trace }
      fieldPlanes := data.1
      derivativeFamily := data.2 }
  left_inv sector := by
    have hround :=
      (planeDerivativeFamilyEquivDecoration fieldCount derivativeCount).symm_apply_apply
        (sector.fieldPlanes, sector.derivativeFamily)
    apply OrientedLocalSector.ext
    · cases sector.trace
      rfl
    · exact congrArg Prod.fst hround
    · exact congrArg Prod.snd hround
  right_inv sector := by
    apply LabeledLocalWordSector.ext
    · rfl
    · exact
        (planeDerivativeFamilyEquivDecoration fieldCount derivativeCount).apply_symm_apply
          sector.decoration

/-! ## Field relabeling compatibility -/

def orientedLocalRelabel
    {fieldCount derivativeCount : ℕ}
    (rename : Equiv.Perm (Fin fieldCount))
    (sector : OrientedLocalSector fieldCount derivativeCount) :
    OrientedLocalSector fieldCount derivativeCount where
  trace :=
    { traceOrder := rename.symm.trans
        (sector.trace.traceOrder.trans rename) }
  fieldPlanes := sector.fieldPlanes ∘ rename.symm
  derivativeFamily := sector.derivativeFamily.relabel rename

@[simp] theorem orientedLocalRelabel_one
    {fieldCount derivativeCount : ℕ}
    (sector : OrientedLocalSector fieldCount derivativeCount) :
    orientedLocalRelabel 1 sector = sector := by
  apply OrientedLocalSector.ext
  · apply congrArg (fun traceOrder =>
      ({ traceOrder := traceOrder } : UnpaddedTraceLayout fieldCount))
    apply Equiv.ext
    intro field
    simpa using
      ((1 : Equiv.Perm (Fin fieldCount)).symm_apply_apply field)
  · rfl
  · apply Subtype.ext
    rfl

theorem orientedLocalRelabel_mul
    {fieldCount derivativeCount : ℕ}
    (left right : Equiv.Perm (Fin fieldCount))
    (sector : OrientedLocalSector fieldCount derivativeCount) :
    orientedLocalRelabel (left * right) sector =
      orientedLocalRelabel left (orientedLocalRelabel right sector) := by
  apply OrientedLocalSector.ext
  · cases sector.trace
    rfl
  · rfl
  · apply Subtype.ext
    rfl

instance orientedLocalSectorFieldRelabelMulAction
    (fieldCount derivativeCount : ℕ) :
    MulAction (Equiv.Perm (Fin fieldCount))
      (OrientedLocalSector fieldCount derivativeCount) where
  smul rename sector := orientedLocalRelabel rename sector
  one_smul := orientedLocalRelabel_one
  mul_smul := by
    intro left right sector
    exact orientedLocalRelabel_mul left right sector

theorem orientedLocalSectorEquivLabeled_relabel
    {fieldCount derivativeCount : ℕ}
    (rename : Equiv.Perm (Fin fieldCount))
    (sector : OrientedLocalSector fieldCount derivativeCount) :
    orientedLocalSectorEquivLabeled fieldCount derivativeCount
        (orientedLocalRelabel rename sector) =
      LabeledLocalWordSector.relabel rename
        (orientedLocalSectorEquivLabeled fieldCount derivativeCount sector) := by
  apply LabeledLocalWordSector.ext
  · rfl
  · apply Subtype.ext
    funext field
    apply LocalFieldLetter.ext
    · rfl
    · rfl
    · rfl

/-! ## Hypercubic and sign compatibility -/

theorem localDerivativeLetterOfList_map_hypercubic
    (h : Hypercubic4) {derivativeBudget : ℕ}
    (axes : { axes : List Axis // axes.length ≤ derivativeBudget }) :
    localDerivativeLetterOfList
        ⟨axes.1.map h.perm, by simpa using axes.2⟩ =
      { derivativeCount := (localDerivativeLetterOfList axes).derivativeCount
        derivativeAxis := fun position =>
          h.perm ((localDerivativeLetterOfList axes).derivativeAxis position) } := by
  apply LocalDerivativeLetter.ext
  · apply Fin.ext
    simp [localDerivativeLetterOfList]
  · apply (Fin.heq_fun_iff (by simp [localDerivativeLetterOfList])).2
    intro position
    simp [localDerivativeLetterOfList]

theorem localFieldLetterOfDerivativeLetter_map_hypercubic
    (h : Hypercubic4) {derivativeBudget : ℕ} (plane : OrientedPlane)
    (axes : { axes : List Axis // axes.length ≤ derivativeBudget }) :
    localFieldLetterOfDerivativeLetter (planeAction h plane)
        (localDerivativeLetterOfList
          ⟨axes.1.map h.perm, by simpa using axes.2⟩) =
      (localFieldLetterOfDerivativeLetter plane
        (localDerivativeLetterOfList axes)).hypercubicAct h := by
  rw [localDerivativeLetterOfList_map_hypercubic]
  rfl

theorem orientedLocalSectorEquivLabeled_hypercubicAct
    {fieldCount derivativeCount : ℕ}
    (h : Hypercubic4)
    (sector : OrientedLocalSector fieldCount derivativeCount) :
    orientedLocalSectorEquivLabeled fieldCount derivativeCount
        (sector.hypercubicAct h) =
      LabeledLocalWordSector.hypercubicAct h
        (orientedLocalSectorEquivLabeled fieldCount derivativeCount sector) := by
  apply LabeledLocalWordSector.ext
  · rfl
  · apply Subtype.ext
    funext field
    change localFieldLetterOfDerivativeLetter
        (planeAction h (sector.fieldPlanes field))
        (localDerivativeLetterOfList
          ⟨(sector.derivativeFamily.1 field).map h.perm, by
            simpa using localAxisWord_length_le
              sector.derivativeFamily field⟩) =
      (localFieldLetterOfDerivativeLetter (sector.fieldPlanes field)
        (localDerivativeLetterOfList
          ⟨sector.derivativeFamily.1 field,
            localAxisWord_length_le sector.derivativeFamily field⟩)).hypercubicAct h
    exact localFieldLetterOfDerivativeLetter_map_hypercubic h
      (sector.fieldPlanes field)
      ⟨sector.derivativeFamily.1 field,
        localAxisWord_length_le sector.derivativeFamily field⟩

theorem listTensorSign_localDerivativeLetterOfList
    (h : Hypercubic4) {derivativeBudget : ℕ}
    (axes : { axes : List Axis // axes.length ≤ derivativeBudget }) :
    (∏ position,
        (Hypercubic4.axisSign h
          ((localDerivativeLetterOfList axes).derivativeAxis position) : ℚ)) =
      (axes.1.map
        (fun axis => (Hypercubic4.axisSign h axis : ℚ))).prod := by
  rw [← List.prod_ofFn]
  change (List.ofFn (fun position =>
      (Hypercubic4.axisSign h (axes.1.get position) : ℚ))).prod =
    (axes.1.map (fun axis => (Hypercubic4.axisSign h axis : ℚ))).prod
  conv_rhs => rw [← List.ofFn_get axes.1]
  rw [List.map_ofFn]
  rfl

theorem orientedLocalSectorEquivLabeled_tensorSign
    {fieldCount derivativeCount : ℕ}
    (h : Hypercubic4)
    (sector : OrientedLocalSector fieldCount derivativeCount) :
    LabeledLocalWordSector.tensorSign h
        (orientedLocalSectorEquivLabeled fieldCount derivativeCount sector) =
      sector.tensorSign h := by
  unfold LabeledLocalWordSector.tensorSign
    LocalFieldLetter.tensorSign OrientedLocalSector.tensorSign
    localAxisWordFamilyTensorSign
  change (∏ field,
      (planeTensorSign h (sector.fieldPlanes field) : ℚ) *
        ∏ position,
          (Hypercubic4.axisSign h
            ((localDerivativeLetterOfList
              ⟨sector.derivativeFamily.1 field,
                localAxisWord_length_le sector.derivativeFamily field⟩).derivativeAxis
              position) : ℚ)) = _
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro field _
  rw [listTensorSign_localDerivativeLetterOfList]

/-! ## Descent to genuine field-label orbits -/

abbrev OrientedLocalRelabelOrbitCarrier
    (fieldCount derivativeCount : ℕ) :=
  Quotient (MulAction.orbitRel (Equiv.Perm (Fin fieldCount))
    (OrientedLocalSector fieldCount derivativeCount))

theorem orientedLocalSectorEquivLabeled_preserves_orbit
    {fieldCount derivativeCount : ℕ}
    {left right : OrientedLocalSector fieldCount derivativeCount}
    (hsame : MulAction.orbitRel (Equiv.Perm (Fin fieldCount))
      (OrientedLocalSector fieldCount derivativeCount) left right) :
    MulAction.orbitRel (Equiv.Perm (Fin fieldCount))
      (LabeledLocalWordSector fieldCount derivativeCount)
      (orientedLocalSectorEquivLabeled fieldCount derivativeCount left)
      (orientedLocalSectorEquivLabeled fieldCount derivativeCount right) := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hsame ⊢
  rcases hsame with ⟨rename, hrename⟩
  refine ⟨rename, ?_⟩
  change orientedLocalRelabel rename right = left at hrename
  change LabeledLocalWordSector.relabel rename
      (orientedLocalSectorEquivLabeled fieldCount derivativeCount right) =
    orientedLocalSectorEquivLabeled fieldCount derivativeCount left
  rw [← orientedLocalSectorEquivLabeled_relabel]
  exact congrArg (orientedLocalSectorEquivLabeled fieldCount derivativeCount)
    hrename

theorem orientedLocalSectorEquivLabeled_reflects_orbit
    {fieldCount derivativeCount : ℕ}
    {left right : LabeledLocalWordSector fieldCount derivativeCount}
    (hsame : MulAction.orbitRel (Equiv.Perm (Fin fieldCount))
      (LabeledLocalWordSector fieldCount derivativeCount) left right) :
    MulAction.orbitRel (Equiv.Perm (Fin fieldCount))
      (OrientedLocalSector fieldCount derivativeCount)
      ((orientedLocalSectorEquivLabeled fieldCount derivativeCount).symm left)
      ((orientedLocalSectorEquivLabeled fieldCount derivativeCount).symm right) := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hsame ⊢
  rcases hsame with ⟨rename, hrename⟩
  refine ⟨rename, ?_⟩
  change LabeledLocalWordSector.relabel rename right = left at hrename
  change orientedLocalRelabel rename
      ((orientedLocalSectorEquivLabeled fieldCount derivativeCount).symm right) =
    (orientedLocalSectorEquivLabeled fieldCount derivativeCount).symm left
  apply (orientedLocalSectorEquivLabeled fieldCount derivativeCount).injective
  rw [orientedLocalSectorEquivLabeled_relabel]
  simpa using hrename

def orientedLocalOrbitEquivFieldRelabelOrbit
    (fieldCount derivativeCount : ℕ) :
    OrientedLocalRelabelOrbitCarrier fieldCount derivativeCount ≃
      FieldRelabelOrbitCarrier fieldCount derivativeCount where
  toFun := Quotient.map
    (orientedLocalSectorEquivLabeled fieldCount derivativeCount)
    (fun _ _ hsame =>
      orientedLocalSectorEquivLabeled_preserves_orbit hsame)
  invFun := Quotient.map
    (orientedLocalSectorEquivLabeled fieldCount derivativeCount).symm
    (fun _ _ hsame =>
      orientedLocalSectorEquivLabeled_reflects_orbit hsame)
  left_inv orbit := by
    refine Quotient.inductionOn orbit ?_
    intro sector
    change Quotient.mk _
        ((orientedLocalSectorEquivLabeled fieldCount derivativeCount).symm
          (orientedLocalSectorEquivLabeled fieldCount derivativeCount sector)) =
      Quotient.mk _ sector
    exact congrArg (Quotient.mk _)
      ((orientedLocalSectorEquivLabeled fieldCount derivativeCount).symm_apply_apply
        sector)
  right_inv orbit := by
    refine Quotient.inductionOn orbit ?_
    intro sector
    change Quotient.mk _
        (orientedLocalSectorEquivLabeled fieldCount derivativeCount
          ((orientedLocalSectorEquivLabeled fieldCount derivativeCount).symm
            sector)) = Quotient.mk _ sector
    exact congrArg (Quotient.mk _)
      ((orientedLocalSectorEquivLabeled fieldCount derivativeCount).apply_symm_apply
        sector)

end HypercubicDimension16OrbitCarrierBridge
end YangMills
end QuantumTheory
end Mettapedia
