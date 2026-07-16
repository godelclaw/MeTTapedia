import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16AntisymmetryQuotient
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16ShuffleLinearQuotient

/-!
# Combined antisymmetry and derivative-shuffle quotient with trace context

This module retains the actual trace layout while simultaneously normalizing
every ordered field-strength axis pair and localizing the global derivative
word.  On each fixed `(fieldCount, derivativeCount)` sector, the kernel of
the combined rational map is proved to be exactly the span of two standard
families:

* `F_ab + F_ba` in one field slot;
* one adjacent interchange of derivatives belonging to different fields.

The proof transports the independently exact antisymmetry and shuffle
kernels into a fixed trace context and then adds their two residuals.  No
relation involving Bianchi, EOM, integration by parts, commutators, or trace
identities is imposed here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16ContextualQuotient

open HypercubicDimension16AlphaReduction
open HypercubicDimension16RelationEquivariance
open HypercubicDimension16ShuffleQuotient
open HypercubicDimension16ShuffleLinearQuotient
open HypercubicDimension16AntisymmetryQuotient
open HypercubicUnpaddedFDSyntax
open HypercubicRawFDDimension16Census
open V14HypercubicFDCensus
open V14HypercubicQuarticCensus

/-! ## Contextual source and target sectors -/

structure OrientedLocalSector (fieldCount derivativeCount : ℕ) where
  trace : UnpaddedTraceLayout fieldCount
  fieldPlanes : OrientedFieldAssignment fieldCount
  derivativeFamily : LocalAxisWordFamily fieldCount derivativeCount

@[ext] theorem OrientedLocalSector.ext
    {fieldCount derivativeCount : ℕ}
    (left right : OrientedLocalSector fieldCount derivativeCount)
    (htrace : left.trace = right.trace)
    (hplanes : left.fieldPlanes = right.fieldPlanes)
    (hfamily : left.derivativeFamily = right.derivativeFamily) :
    left = right := by
  cases left
  cases right
  simp_all

abbrev ContextualSourceSpace (fieldCount derivativeCount : ℕ) :=
  DerivativeAlphaReducedSector fieldCount derivativeCount →₀ ℚ

abbrev ContextualTargetSpace (fieldCount derivativeCount : ℕ) :=
  OrientedLocalSector fieldCount derivativeCount →₀ ℚ

def sectorFieldAxisAssignment {fieldCount derivativeCount : ℕ}
    (sector : DerivativeAlphaReducedSector fieldCount derivativeCount) :
    FieldAxisAssignment fieldCount :=
  fun slot => (sector.fieldFirst slot, sector.fieldSecond slot)

def sectorGlobalWord {fieldCount derivativeCount : ℕ}
    (sector : DerivativeAlphaReducedSector fieldCount derivativeCount) :
    GlobalOwnedAxisWord fieldCount derivativeCount :=
  orderedDerivativeWordEquivGlobal fieldCount derivativeCount
    sector.derivativeWord

def normalizedSectorData {fieldCount derivativeCount : ℕ}
    (sector : DerivativeAlphaReducedSector fieldCount derivativeCount) :
    OrientedLocalSector fieldCount derivativeCount where
  trace := sector.trace
  fieldPlanes := fieldAxisPlanes (sectorFieldAxisAssignment sector)
  derivativeFamily := localize (sectorGlobalWord sector)

def normalizeContextualBasis {fieldCount derivativeCount : ℕ}
    (sector : DerivativeAlphaReducedSector fieldCount derivativeCount) :
    ContextualTargetSpace fieldCount derivativeCount :=
  fieldAxisOrientationCoefficient (sectorFieldAxisAssignment sector) •
    Finsupp.single (normalizedSectorData sector) 1

def normalizeContextualSector (fieldCount derivativeCount : ℕ) :
    ContextualSourceSpace fieldCount derivativeCount →ₗ[ℚ]
      ContextualTargetSpace fieldCount derivativeCount :=
  Finsupp.linearCombination ℚ normalizeContextualBasis

@[simp] theorem normalizeContextualSector_single
    {fieldCount derivativeCount : ℕ}
    (sector : DerivativeAlphaReducedSector fieldCount derivativeCount)
    (coefficient : ℚ) :
    normalizeContextualSector fieldCount derivativeCount
        (Finsupp.single sector coefficient) =
      coefficient • normalizeContextualBasis sector := by
  simp [normalizeContextualSector]

/-! ## A canonical simultaneous right inverse -/

def canonicalContextualSector {fieldCount derivativeCount : ℕ}
    (target : OrientedLocalSector fieldCount derivativeCount) :
    DerivativeAlphaReducedSector fieldCount derivativeCount where
  trace := target.trace
  fieldFirst := fun slot => (target.fieldPlanes slot).first
  fieldSecond := fun slot => (target.fieldPlanes slot).second
  derivativeWord :=
    (orderedDerivativeWordEquivGlobal fieldCount derivativeCount).symm
      (globalize target.derivativeFamily)

def embedContextualBasis {fieldCount derivativeCount : ℕ}
    (target : OrientedLocalSector fieldCount derivativeCount) :
    ContextualSourceSpace fieldCount derivativeCount :=
  Finsupp.single (canonicalContextualSector target) 1

def embedContextualSector (fieldCount derivativeCount : ℕ) :
    ContextualTargetSpace fieldCount derivativeCount →ₗ[ℚ]
      ContextualSourceSpace fieldCount derivativeCount :=
  Finsupp.linearCombination ℚ embedContextualBasis

@[simp] theorem embedContextualSector_single
    {fieldCount derivativeCount : ℕ}
    (target : OrientedLocalSector fieldCount derivativeCount)
    (coefficient : ℚ) :
    embedContextualSector fieldCount derivativeCount
        (Finsupp.single target coefficient) =
      coefficient • embedContextualBasis target := by
  simp [embedContextualSector]

theorem sectorFieldAxisAssignment_canonical
    {fieldCount derivativeCount : ℕ}
    (target : OrientedLocalSector fieldCount derivativeCount) :
    sectorFieldAxisAssignment (canonicalContextualSector target) =
      orderedFieldAxisAssignment target.fieldPlanes := by
  rfl

theorem sectorGlobalWord_canonical
    {fieldCount derivativeCount : ℕ}
    (target : OrientedLocalSector fieldCount derivativeCount) :
    sectorGlobalWord (canonicalContextualSector target) =
      globalize target.derivativeFamily := by
  simp [sectorGlobalWord, canonicalContextualSector]

theorem normalizeContextualBasis_canonical
    {fieldCount derivativeCount : ℕ}
    (target : OrientedLocalSector fieldCount derivativeCount) :
    normalizeContextualBasis (canonicalContextualSector target) =
      Finsupp.single target 1 := by
  have hcoefficient : fieldAxisOrientationCoefficient
      (orderedFieldAxisAssignment target.fieldPlanes) = 1 := by
    simp [fieldAxisOrientationCoefficient, orderedFieldAxisAssignment]
  have hplanes : fieldAxisPlanes
      (orderedFieldAxisAssignment target.fieldPlanes) = target.fieldPlanes := by
    funext slot
    simp [fieldAxisPlanes, orderedFieldAxisAssignment]
  have hdata : normalizedSectorData (canonicalContextualSector target) =
      target := by
    apply OrientedLocalSector.ext
    · simp [normalizedSectorData, canonicalContextualSector]
    · simpa [normalizedSectorData, sectorFieldAxisAssignment_canonical] using
        hplanes
    · simp [normalizedSectorData, sectorGlobalWord_canonical,
        localize_globalize]
  simp [normalizeContextualBasis, sectorFieldAxisAssignment_canonical,
    hcoefficient, hdata]

theorem normalizeContextualSector_embedContextualSector
    (fieldCount derivativeCount : ℕ)
    (value : ContextualTargetSpace fieldCount derivativeCount) :
    normalizeContextualSector fieldCount derivativeCount
        (embedContextualSector fieldCount derivativeCount value) = value := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [map_add, hleft, hright]
  | single target coefficient =>
      simp [embedContextualBasis, normalizeContextualBasis_canonical]

/-! ## The two literal contextual relation families -/

def sectorWithFieldAxisAssignment {fieldCount derivativeCount : ℕ}
    (sector : DerivativeAlphaReducedSector fieldCount derivativeCount)
    (assignment : FieldAxisAssignment fieldCount) :
    DerivativeAlphaReducedSector fieldCount derivativeCount where
  trace := sector.trace
  fieldFirst := fun slot => (assignment slot).1
  fieldSecond := fun slot => (assignment slot).2
  derivativeWord := sector.derivativeWord

def sectorWithGlobalWord {fieldCount derivativeCount : ℕ}
    (sector : DerivativeAlphaReducedSector fieldCount derivativeCount)
    (word : GlobalOwnedAxisWord fieldCount derivativeCount) :
    DerivativeAlphaReducedSector fieldCount derivativeCount where
  trace := sector.trace
  fieldFirst := sector.fieldFirst
  fieldSecond := sector.fieldSecond
  derivativeWord :=
    (orderedDerivativeWordEquivGlobal fieldCount derivativeCount).symm word

@[simp] theorem sectorFieldAxisAssignment_sectorWithFieldAxisAssignment
    {fieldCount derivativeCount : ℕ}
    (sector : DerivativeAlphaReducedSector fieldCount derivativeCount)
    (assignment : FieldAxisAssignment fieldCount) :
    sectorFieldAxisAssignment
        (sectorWithFieldAxisAssignment sector assignment) = assignment := by
  rfl

@[simp] theorem sectorGlobalWord_sectorWithFieldAxisAssignment
    {fieldCount derivativeCount : ℕ}
    (sector : DerivativeAlphaReducedSector fieldCount derivativeCount)
    (assignment : FieldAxisAssignment fieldCount) :
    sectorGlobalWord (sectorWithFieldAxisAssignment sector assignment) =
      sectorGlobalWord sector := by
  rfl

@[simp] theorem sectorFieldAxisAssignment_sectorWithGlobalWord
    {fieldCount derivativeCount : ℕ}
    (sector : DerivativeAlphaReducedSector fieldCount derivativeCount)
    (word : GlobalOwnedAxisWord fieldCount derivativeCount) :
    sectorFieldAxisAssignment (sectorWithGlobalWord sector word) =
      sectorFieldAxisAssignment sector := by
  rfl

@[simp] theorem sectorGlobalWord_sectorWithGlobalWord
    {fieldCount derivativeCount : ℕ}
    (sector : DerivativeAlphaReducedSector fieldCount derivativeCount)
    (word : GlobalOwnedAxisWord fieldCount derivativeCount) :
    sectorGlobalWord (sectorWithGlobalWord sector word) = word := by
  simp [sectorGlobalWord, sectorWithGlobalWord]

@[simp] theorem sectorWithFieldAxisAssignment_self
    {fieldCount derivativeCount : ℕ}
    (sector : DerivativeAlphaReducedSector fieldCount derivativeCount) :
    sectorWithFieldAxisAssignment sector
        (sectorFieldAxisAssignment sector) = sector := by
  apply DerivativeAlphaReducedSector.ext <;> rfl

@[simp] theorem sectorWithGlobalWord_self
    {fieldCount derivativeCount : ℕ}
    (sector : DerivativeAlphaReducedSector fieldCount derivativeCount) :
    sectorWithGlobalWord sector (sectorGlobalWord sector) = sector := by
  apply DerivativeAlphaReducedSector.ext
  · rfl
  · rfl
  · rfl
  · exact (orderedDerivativeWordEquivGlobal fieldCount derivativeCount).symm_apply_apply
      sector.derivativeWord

structure ContextualFieldAntisymmetrySite
    (fieldCount derivativeCount : ℕ) where
  sector : DerivativeAlphaReducedSector fieldCount derivativeCount
  slot : Fin fieldCount

structure ContextualDerivativeShuffleSite
    (fieldCount derivativeCount : ℕ) where
  sector : DerivativeAlphaReducedSector fieldCount derivativeCount
  targetWord : GlobalOwnedAxisWord fieldCount derivativeCount
  step : IsAdjacentDifferentOwnerSwap (sectorGlobalWord sector) targetWord

abbrev ContextualRelationSite (fieldCount derivativeCount : ℕ) :=
  ContextualFieldAntisymmetrySite fieldCount derivativeCount ⊕
    ContextualDerivativeShuffleSite fieldCount derivativeCount

def contextualRelationRow {fieldCount derivativeCount : ℕ} :
    ContextualRelationSite fieldCount derivativeCount →
      ContextualSourceSpace fieldCount derivativeCount
  | Sum.inl site =>
      Finsupp.single site.sector 1 +
        Finsupp.single (swapFieldAxes site.sector site.slot) 1
  | Sum.inr site =>
      Finsupp.single site.sector 1 -
        Finsupp.single
          (sectorWithGlobalWord site.sector site.targetWord) 1

def contextualRelationSubmodule (fieldCount derivativeCount : ℕ) :
    Submodule ℚ (ContextualSourceSpace fieldCount derivativeCount) :=
  Submodule.span ℚ
    (Set.range (contextualRelationRow :
      ContextualRelationSite fieldCount derivativeCount →
        ContextualSourceSpace fieldCount derivativeCount))

theorem sectorFieldAxisAssignment_swapFieldAxes
    {fieldCount derivativeCount : ℕ}
    (sector : DerivativeAlphaReducedSector fieldCount derivativeCount)
    (slot : Fin fieldCount) :
    sectorFieldAxisAssignment (swapFieldAxes sector slot) =
      swapFieldAxisAt (sectorFieldAxisAssignment sector) slot := by
  funext current
  by_cases hcurrent : current = slot
  · subst current
    simp [sectorFieldAxisAssignment, swapFieldAxes, swapFieldAxisAt]
  · simp [sectorFieldAxisAssignment, swapFieldAxes, swapFieldAxisAt, hcurrent]

@[simp] theorem sectorGlobalWord_swapFieldAxes
    {fieldCount derivativeCount : ℕ}
    (sector : DerivativeAlphaReducedSector fieldCount derivativeCount)
    (slot : Fin fieldCount) :
    sectorGlobalWord (swapFieldAxes sector slot) = sectorGlobalWord sector := by
  rfl

theorem normalizeContextualBasis_swapFieldAxes
    {fieldCount derivativeCount : ℕ}
    (sector : DerivativeAlphaReducedSector fieldCount derivativeCount)
    (slot : Fin fieldCount) :
    normalizeContextualBasis (swapFieldAxes sector slot) =
      -normalizeContextualBasis sector := by
  have hcoefficient := fieldAxisOrientationCoefficient_swapFieldAxisAt
    (sectorFieldAxisAssignment sector) slot
  have hplanes := fieldAxisPlanes_swapFieldAxisAt
    (sectorFieldAxisAssignment sector) slot
  have hdata : normalizedSectorData (swapFieldAxes sector slot) =
      normalizedSectorData sector := by
    apply OrientedLocalSector.ext
    · rfl
    · simpa [normalizedSectorData,
        sectorFieldAxisAssignment_swapFieldAxes] using hplanes
    · simp [normalizedSectorData]
  rw [normalizeContextualBasis, normalizeContextualBasis,
    sectorFieldAxisAssignment_swapFieldAxes, hcoefficient, hdata]
  module

theorem normalizeContextualBasis_sectorWithGlobalWord
    {fieldCount derivativeCount : ℕ}
    (site : ContextualDerivativeShuffleSite fieldCount derivativeCount) :
    normalizeContextualBasis
        (sectorWithGlobalWord site.sector site.targetWord) =
      normalizeContextualBasis site.sector := by
  have hsemantic := adjacentDifferentOwnerSwap_semanticallyEquivalent site.step
  change localize (sectorGlobalWord site.sector) =
      localize site.targetWord at hsemantic
  have hdata : normalizedSectorData
      (sectorWithGlobalWord site.sector site.targetWord) =
        normalizedSectorData site.sector := by
    apply OrientedLocalSector.ext
    · rfl
    · simp [normalizedSectorData]
    · simpa [normalizedSectorData] using hsemantic.symm
  simp [normalizeContextualBasis, hdata]

theorem normalizeContextualSector_contextualRelationRow
    {fieldCount derivativeCount : ℕ}
    (site : ContextualRelationSite fieldCount derivativeCount) :
    normalizeContextualSector fieldCount derivativeCount
        (contextualRelationRow site) = 0 := by
  rcases site with fieldSite | derivativeSite
  · simp [contextualRelationRow, map_add,
      normalizeContextualBasis_swapFieldAxes]
  · simp [contextualRelationRow, map_sub,
      normalizeContextualBasis_sectorWithGlobalWord]

/-! ## Transport of the exact component kernels into context -/

def contextualFieldEmbedBasis {fieldCount derivativeCount : ℕ}
    (context : DerivativeAlphaReducedSector fieldCount derivativeCount)
    (assignment : FieldAxisAssignment fieldCount) :
    ContextualSourceSpace fieldCount derivativeCount :=
  Finsupp.single (sectorWithFieldAxisAssignment context assignment) 1

def contextualFieldEmbed {fieldCount derivativeCount : ℕ}
    (context : DerivativeAlphaReducedSector fieldCount derivativeCount) :
    FieldAxisAssignmentSpace fieldCount →ₗ[ℚ]
      ContextualSourceSpace fieldCount derivativeCount :=
  Finsupp.linearCombination ℚ (contextualFieldEmbedBasis context)

@[simp] theorem contextualFieldEmbed_single
    {fieldCount derivativeCount : ℕ}
    (context : DerivativeAlphaReducedSector fieldCount derivativeCount)
    (assignment : FieldAxisAssignment fieldCount) (coefficient : ℚ) :
    contextualFieldEmbed context (Finsupp.single assignment coefficient) =
      coefficient • contextualFieldEmbedBasis context assignment := by
  simp [contextualFieldEmbed]

theorem sectorWithFieldAxisAssignment_swap
    {fieldCount derivativeCount : ℕ}
    (context : DerivativeAlphaReducedSector fieldCount derivativeCount)
    (assignment : FieldAxisAssignment fieldCount) (slot : Fin fieldCount) :
    sectorWithFieldAxisAssignment context
        (swapFieldAxisAt assignment slot) =
      swapFieldAxes (sectorWithFieldAxisAssignment context assignment) slot := by
  apply DerivativeAlphaReducedSector.ext
  · rfl
  · funext current
    by_cases hcurrent : current = slot <;>
      simp [sectorWithFieldAxisAssignment, swapFieldAxisAt, swapFieldAxes,
        hcurrent]
  · funext current
    by_cases hcurrent : current = slot <;>
      simp [sectorWithFieldAxisAssignment, swapFieldAxisAt, swapFieldAxes,
        hcurrent]
  · rfl

theorem contextualFieldEmbed_antisymmetry_mem
    {fieldCount derivativeCount : ℕ}
    (context : DerivativeAlphaReducedSector fieldCount derivativeCount)
    (value : FieldAxisAssignmentSpace fieldCount)
    (hvalue : value ∈ fieldAxisAntisymmetrySubmodule fieldCount) :
    contextualFieldEmbed context value ∈
      contextualRelationSubmodule fieldCount derivativeCount := by
  unfold fieldAxisAntisymmetrySubmodule at hvalue
  refine Submodule.span_induction
    (p := fun current : FieldAxisAssignmentSpace fieldCount => fun _ =>
      contextualFieldEmbed context current ∈
        contextualRelationSubmodule fieldCount derivativeCount)
    ?_ ?_ ?_ ?_ hvalue
  · intro current hcurrent
    rcases hcurrent with ⟨site, rfl⟩
    have hrow : contextualRelationRow
        (Sum.inl
          ({ sector := sectorWithFieldAxisAssignment context site.1
             slot := site.2 } :
            ContextualFieldAntisymmetrySite fieldCount derivativeCount)) ∈
        contextualRelationSubmodule fieldCount derivativeCount :=
      Submodule.subset_span ⟨_, rfl⟩
    simpa [fieldAxisAntisymmetryRow, contextualRelationRow,
      contextualFieldEmbedBasis, sectorWithFieldAxisAssignment_swap] using hrow
  · simp
  · intro left right _ _ hleft hright
    simpa using (contextualRelationSubmodule fieldCount derivativeCount).add_mem
      hleft hright
  · intro coefficient current _ hcurrent
    simpa using (contextualRelationSubmodule fieldCount derivativeCount).smul_mem
      coefficient hcurrent

def contextualDerivativeEmbedBasis {fieldCount derivativeCount : ℕ}
    (context : DerivativeAlphaReducedSector fieldCount derivativeCount)
    (word : GlobalOwnedAxisWord fieldCount derivativeCount) :
    ContextualSourceSpace fieldCount derivativeCount :=
  Finsupp.single (sectorWithGlobalWord context word) 1

def contextualDerivativeEmbed {fieldCount derivativeCount : ℕ}
    (context : DerivativeAlphaReducedSector fieldCount derivativeCount) :
    GlobalOwnedAxisWordSpace fieldCount derivativeCount →ₗ[ℚ]
      ContextualSourceSpace fieldCount derivativeCount :=
  Finsupp.linearCombination ℚ (contextualDerivativeEmbedBasis context)

@[simp] theorem contextualDerivativeEmbed_single
    {fieldCount derivativeCount : ℕ}
    (context : DerivativeAlphaReducedSector fieldCount derivativeCount)
    (word : GlobalOwnedAxisWord fieldCount derivativeCount)
    (coefficient : ℚ) :
    contextualDerivativeEmbed context (Finsupp.single word coefficient) =
      coefficient • contextualDerivativeEmbedBasis context word := by
  simp [contextualDerivativeEmbed]

theorem contextualDerivativeEmbed_shuffle_mem
    {fieldCount derivativeCount : ℕ}
    (context : DerivativeAlphaReducedSector fieldCount derivativeCount)
    (value : GlobalOwnedAxisWordSpace fieldCount derivativeCount)
    (hvalue : value ∈ literalShuffleSubmodule fieldCount derivativeCount) :
    contextualDerivativeEmbed context value ∈
      contextualRelationSubmodule fieldCount derivativeCount := by
  unfold literalShuffleSubmodule at hvalue
  refine Submodule.span_induction
    (p := fun current : GlobalOwnedAxisWordSpace fieldCount derivativeCount =>
      fun _ => contextualDerivativeEmbed context current ∈
        contextualRelationSubmodule fieldCount derivativeCount)
    ?_ ?_ ?_ ?_ hvalue
  · intro current hcurrent
    rcases hcurrent with ⟨site, rfl⟩
    have hrow : contextualRelationRow
        (Sum.inr
          ({ sector := sectorWithGlobalWord context site.source
             targetWord := site.target
             step := by simpa using site.step } :
            ContextualDerivativeShuffleSite fieldCount derivativeCount)) ∈
        contextualRelationSubmodule fieldCount derivativeCount :=
      Submodule.subset_span ⟨_, rfl⟩
    simpa [literalShuffleRow, contextualRelationRow,
      contextualDerivativeEmbedBasis, sectorWithGlobalWord] using hrow
  · simp
  · intro left right _ _ hleft hright
    simpa using (contextualRelationSubmodule fieldCount derivativeCount).add_mem
      hleft hright
  · intro coefficient current _ hcurrent
    simpa using (contextualRelationSubmodule fieldCount derivativeCount).smul_mem
      coefficient hcurrent

/-! ## Exact combined kernel -/

theorem contextual_field_residual_mem
    {fieldCount derivativeCount : ℕ}
    (sector : DerivativeAlphaReducedSector fieldCount derivativeCount) :
    let assignment := sectorFieldAxisAssignment sector
    Finsupp.single sector 1 -
        fieldAxisOrientationCoefficient assignment •
          Finsupp.single
            (sectorWithFieldAxisAssignment sector
              (orderedFieldAxisAssignment (fieldAxisPlanes assignment))) 1 ∈
      contextualRelationSubmodule fieldCount derivativeCount := by
  dsimp
  have hgeneric := fieldAxisBasis_residual_mem
    (sectorFieldAxisAssignment sector)
  have hmapped := contextualFieldEmbed_antisymmetry_mem sector _ hgeneric
  simpa [normalizeFieldAxisBasis, orientedFieldAssignmentEmbed,
    orientedFieldAssignmentEmbedBasis, contextualFieldEmbedBasis] using hmapped

theorem contextual_derivative_residual_mem
    {fieldCount derivativeCount : ℕ}
    (context : DerivativeAlphaReducedSector fieldCount derivativeCount) :
    Finsupp.single context 1 -
        Finsupp.single
          (sectorWithGlobalWord context
            (globalize (localize (sectorGlobalWord context)))) 1 ∈
      contextualRelationSubmodule fieldCount derivativeCount := by
  have hgeneric := globalOwnedAxisWord_basis_residual_mem
    (sectorGlobalWord context)
  have hmapped := contextualDerivativeEmbed_shuffle_mem context _ hgeneric
  simpa [linearLocalizeBasis, linearGlobalizeBasis,
    contextualDerivativeEmbedBasis] using hmapped

theorem contextual_basis_residual_mem
    {fieldCount derivativeCount : ℕ}
    (sector : DerivativeAlphaReducedSector fieldCount derivativeCount) :
    Finsupp.single sector 1 -
        embedContextualSector fieldCount derivativeCount
          (normalizeContextualBasis sector) ∈
      contextualRelationSubmodule fieldCount derivativeCount := by
  let assignment := sectorFieldAxisAssignment sector
  let orderedSector := sectorWithFieldAxisAssignment sector
    (orderedFieldAxisAssignment (fieldAxisPlanes assignment))
  have hfield := contextual_field_residual_mem sector
  change Finsupp.single sector 1 -
      fieldAxisOrientationCoefficient assignment •
        Finsupp.single orderedSector 1 ∈
    contextualRelationSubmodule fieldCount derivativeCount at hfield
  have hderivative := contextual_derivative_residual_mem orderedSector
  have hscaled := (contextualRelationSubmodule fieldCount derivativeCount).smul_mem
    (fieldAxisOrientationCoefficient assignment) hderivative
  have hadd := (contextualRelationSubmodule fieldCount derivativeCount).add_mem
    hfield hscaled
  have hcanonical : sectorWithGlobalWord orderedSector
      (globalize (localize (sectorGlobalWord orderedSector))) =
        canonicalContextualSector (normalizedSectorData sector) := by
    apply DerivativeAlphaReducedSector.ext
    · simp [orderedSector, normalizedSectorData, canonicalContextualSector,
        sectorWithGlobalWord, sectorWithFieldAxisAssignment]
    · rfl
    · rfl
    · apply (orderedDerivativeWordEquivGlobal fieldCount derivativeCount).injective
      simp [orderedSector, assignment, sectorGlobalWord,
        canonicalContextualSector, normalizedSectorData,
        sectorWithGlobalWord, sectorWithFieldAxisAssignment]
  rw [hcanonical] at hadd
  have hembed : embedContextualSector fieldCount derivativeCount
      (normalizeContextualBasis sector) =
        fieldAxisOrientationCoefficient assignment •
          Finsupp.single
            (canonicalContextualSector (normalizedSectorData sector)) 1 := by
    unfold normalizeContextualBasis
    rw [map_smul]
    simp [embedContextualBasis, assignment]
  rw [hembed]
  convert hadd using 1
  module

theorem contextual_residual_mem
    {fieldCount derivativeCount : ℕ}
    (value : ContextualSourceSpace fieldCount derivativeCount) :
    value - embedContextualSector fieldCount derivativeCount
        (normalizeContextualSector fieldCount derivativeCount value) ∈
      contextualRelationSubmodule fieldCount derivativeCount := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      have hadd := (contextualRelationSubmodule fieldCount derivativeCount).add_mem
        hleft hright
      convert hadd using 1
      simp [map_add]
      module
  | single sector coefficient =>
      have hscaled := (contextualRelationSubmodule fieldCount derivativeCount).smul_mem
        coefficient (contextual_basis_residual_mem sector)
      simpa [smul_sub] using hscaled

theorem ker_normalizeContextualSector_eq_contextualRelationSubmodule
    (fieldCount derivativeCount : ℕ) :
    LinearMap.ker (normalizeContextualSector fieldCount derivativeCount) =
      contextualRelationSubmodule fieldCount derivativeCount := by
  apply le_antisymm
  · intro value hkernel
    have hresidual := contextual_residual_mem value
    rw [LinearMap.mem_ker.mp hkernel] at hresidual
    simpa using hresidual
  · unfold contextualRelationSubmodule
    rw [Submodule.span_le]
    rintro value ⟨site, rfl⟩
    exact LinearMap.mem_ker.mpr
      (normalizeContextualSector_contextualRelationRow site)

theorem normalizeContextualSector_surjective
    (fieldCount derivativeCount : ℕ) :
    Function.Surjective
      (normalizeContextualSector fieldCount derivativeCount) := by
  intro value
  exact ⟨embedContextualSector fieldCount derivativeCount value,
    normalizeContextualSector_embedContextualSector
      fieldCount derivativeCount value⟩

def contextualRelationQuotientEquiv
    (fieldCount derivativeCount : ℕ) :
    (ContextualSourceSpace fieldCount derivativeCount ⧸
        contextualRelationSubmodule fieldCount derivativeCount) ≃ₗ[ℚ]
      ContextualTargetSpace fieldCount derivativeCount :=
  (Submodule.quotEquivOfEq
      (contextualRelationSubmodule fieldCount derivativeCount)
      (LinearMap.ker (normalizeContextualSector fieldCount derivativeCount))
      (ker_normalizeContextualSector_eq_contextualRelationSubmodule
        fieldCount derivativeCount).symm).trans
    ((normalizeContextualSector fieldCount derivativeCount).quotKerEquivOfSurjective
      (normalizeContextualSector_surjective fieldCount derivativeCount))

/-! ## Lift to the actual dependent dimension-sixteen carrier -/

abbrev ExactOrientedLocalCarrier :=
  (fieldCount : Fin 9) ×'
    OrientedLocalSector fieldCount.1
      (dimension16DerivativeCount fieldCount)

abbrev ExactOrientedLocalSpace := ExactOrientedLocalCarrier →₀ ℚ

def exactNormalizedSectorData (carrier : RelationCarrier) :
    ExactOrientedLocalCarrier :=
  ⟨carrier.1, normalizedSectorData carrier.2⟩

def normalizeExactContextualBasis (carrier : RelationCarrier) :
    ExactOrientedLocalSpace :=
  fieldAxisOrientationCoefficient
      (sectorFieldAxisAssignment carrier.2) •
    Finsupp.single (exactNormalizedSectorData carrier) 1

def normalizeExactContextual : RelationSpace →ₗ[ℚ] ExactOrientedLocalSpace :=
  Finsupp.linearCombination ℚ normalizeExactContextualBasis

@[simp] theorem normalizeExactContextual_single
    (carrier : RelationCarrier) (coefficient : ℚ) :
    normalizeExactContextual (Finsupp.single carrier coefficient) =
      coefficient • normalizeExactContextualBasis carrier := by
  simp [normalizeExactContextual]

def canonicalExactContextualCarrier
    (target : ExactOrientedLocalCarrier) : RelationCarrier :=
  ⟨target.1, canonicalContextualSector target.2⟩

def embedExactContextualBasis
    (target : ExactOrientedLocalCarrier) : RelationSpace :=
  Finsupp.single (canonicalExactContextualCarrier target) 1

def embedExactContextual : ExactOrientedLocalSpace →ₗ[ℚ] RelationSpace :=
  Finsupp.linearCombination ℚ embedExactContextualBasis

@[simp] theorem embedExactContextual_single
    (target : ExactOrientedLocalCarrier) (coefficient : ℚ) :
    embedExactContextual (Finsupp.single target coefficient) =
      coefficient • embedExactContextualBasis target := by
  simp [embedExactContextual]

def exactTargetFiberEmbedBasis (fieldCount : Fin 9)
    (target : OrientedLocalSector fieldCount.1
      (dimension16DerivativeCount fieldCount)) : ExactOrientedLocalSpace :=
  Finsupp.single ⟨fieldCount, target⟩ 1

def exactTargetFiberEmbed (fieldCount : Fin 9) :
    ContextualTargetSpace fieldCount.1
        (dimension16DerivativeCount fieldCount) →ₗ[ℚ]
      ExactOrientedLocalSpace :=
  Finsupp.linearCombination ℚ (exactTargetFiberEmbedBasis fieldCount)

@[simp] theorem exactTargetFiberEmbed_single (fieldCount : Fin 9)
    (target : OrientedLocalSector fieldCount.1
      (dimension16DerivativeCount fieldCount)) (coefficient : ℚ) :
    exactTargetFiberEmbed fieldCount (Finsupp.single target coefficient) =
      coefficient • exactTargetFiberEmbedBasis fieldCount target := by
  simp [exactTargetFiberEmbed]

theorem normalizeExactContextualBasis_eq_fiberEmbed
    (carrier : RelationCarrier) :
    normalizeExactContextualBasis carrier =
      exactTargetFiberEmbed carrier.1
        (normalizeContextualBasis carrier.2) := by
  simp [normalizeExactContextualBasis, normalizeContextualBasis,
    exactTargetFiberEmbedBasis, exactNormalizedSectorData]

def exactSourceFiberEmbedBasis (fieldCount : Fin 9)
    (sector : DerivativeAlphaReducedSector fieldCount.1
      (dimension16DerivativeCount fieldCount)) : RelationSpace :=
  Finsupp.single ⟨fieldCount, sector⟩ 1

def exactSourceFiberEmbed (fieldCount : Fin 9) :
    ContextualSourceSpace fieldCount.1
        (dimension16DerivativeCount fieldCount) →ₗ[ℚ] RelationSpace :=
  Finsupp.linearCombination ℚ (exactSourceFiberEmbedBasis fieldCount)

@[simp] theorem exactSourceFiberEmbed_single (fieldCount : Fin 9)
    (sector : DerivativeAlphaReducedSector fieldCount.1
      (dimension16DerivativeCount fieldCount)) (coefficient : ℚ) :
    exactSourceFiberEmbed fieldCount (Finsupp.single sector coefficient) =
      coefficient • exactSourceFiberEmbedBasis fieldCount sector := by
  simp [exactSourceFiberEmbed]

theorem embedExactContextual_fiberEmbed
    (fieldCount : Fin 9)
    (value : ContextualTargetSpace fieldCount.1
      (dimension16DerivativeCount fieldCount)) :
    embedExactContextual (exactTargetFiberEmbed fieldCount value) =
      exactSourceFiberEmbed fieldCount
        (embedContextualSector fieldCount.1
          (dimension16DerivativeCount fieldCount) value) := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [map_add, hleft, hright]
  | single target coefficient =>
      simp [exactTargetFiberEmbedBasis, embedExactContextualBasis,
        exactSourceFiberEmbedBasis, embedContextualBasis,
        canonicalExactContextualCarrier]

structure ExactContextualFieldAntisymmetrySite where
  carrier : RelationCarrier
  slot : Fin carrier.1.1

structure ExactContextualDerivativeShuffleSite where
  carrier : RelationCarrier
  targetWord : GlobalOwnedAxisWord carrier.1.1
    (dimension16DerivativeCount carrier.1)
  step : IsAdjacentDifferentOwnerSwap
    (sectorGlobalWord carrier.2) targetWord

abbrev ExactContextualRelationSite :=
  ExactContextualFieldAntisymmetrySite ⊕
    ExactContextualDerivativeShuffleSite

def exactContextualRelationRow :
    ExactContextualRelationSite → RelationSpace
  | Sum.inl site => fieldAntisymmetryRow site.carrier site.slot
  | Sum.inr site =>
      Finsupp.single site.carrier 1 -
        Finsupp.single
          ⟨site.carrier.1,
            sectorWithGlobalWord site.carrier.2 site.targetWord⟩ 1

def exactContextualRelationSubmodule : Submodule ℚ RelationSpace :=
  Submodule.span ℚ (Set.range exactContextualRelationRow)

theorem exactSourceFiberEmbed_contextualRelation_mem
    (fieldCount : Fin 9)
    (value : ContextualSourceSpace fieldCount.1
      (dimension16DerivativeCount fieldCount))
    (hvalue : value ∈ contextualRelationSubmodule fieldCount.1
      (dimension16DerivativeCount fieldCount)) :
    exactSourceFiberEmbed fieldCount value ∈
      exactContextualRelationSubmodule := by
  unfold contextualRelationSubmodule at hvalue
  refine Submodule.span_induction
    (p := fun current : ContextualSourceSpace fieldCount.1
      (dimension16DerivativeCount fieldCount) => fun _ =>
        exactSourceFiberEmbed fieldCount current ∈
          exactContextualRelationSubmodule)
    ?_ ?_ ?_ ?_ hvalue
  · intro current hcurrent
    rcases hcurrent with ⟨site, rfl⟩
    rcases site with fieldSite | derivativeSite
    · have hrow : exactContextualRelationRow
          (Sum.inl
            ({ carrier := ⟨fieldCount, fieldSite.sector⟩
               slot := fieldSite.slot } :
              ExactContextualFieldAntisymmetrySite)) ∈
          exactContextualRelationSubmodule :=
        Submodule.subset_span ⟨_, rfl⟩
      simpa [contextualRelationRow, exactContextualRelationRow,
        fieldAntisymmetryRow, exactSourceFiberEmbedBasis,
        swapExactFieldAxes] using hrow
    · have hrow : exactContextualRelationRow
          (Sum.inr
            ({ carrier := ⟨fieldCount, derivativeSite.sector⟩
               targetWord := derivativeSite.targetWord
               step := derivativeSite.step } :
              ExactContextualDerivativeShuffleSite)) ∈
          exactContextualRelationSubmodule :=
        Submodule.subset_span ⟨_, rfl⟩
      simpa [contextualRelationRow, exactContextualRelationRow,
        exactSourceFiberEmbedBasis] using hrow
  · simp
  · intro left right _ _ hleft hright
    simpa using exactContextualRelationSubmodule.add_mem hleft hright
  · intro coefficient current _ hcurrent
    simpa using exactContextualRelationSubmodule.smul_mem coefficient hcurrent

theorem exact_basis_residual_mem (carrier : RelationCarrier) :
    Finsupp.single carrier 1 -
        embedExactContextual (normalizeExactContextualBasis carrier) ∈
      exactContextualRelationSubmodule := by
  have hgeneric := contextual_basis_residual_mem carrier.2
  have hmapped := exactSourceFiberEmbed_contextualRelation_mem
    carrier.1 _ hgeneric
  have hembed : embedExactContextual
      (normalizeExactContextualBasis carrier) =
        exactSourceFiberEmbed carrier.1
          (embedContextualSector carrier.1.1
            (dimension16DerivativeCount carrier.1)
            (normalizeContextualBasis carrier.2)) := by
    rw [normalizeExactContextualBasis_eq_fiberEmbed,
      embedExactContextual_fiberEmbed]
  rw [hembed]
  simpa [exactSourceFiberEmbedBasis] using hmapped

theorem exact_residual_mem (value : RelationSpace) :
    value - embedExactContextual (normalizeExactContextual value) ∈
      exactContextualRelationSubmodule := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      have hadd := exactContextualRelationSubmodule.add_mem hleft hright
      convert hadd using 1
      simp [map_add]
      module
  | single carrier coefficient =>
      have hscaled := exactContextualRelationSubmodule.smul_mem coefficient
        (exact_basis_residual_mem carrier)
      simpa [smul_sub] using hscaled

theorem normalizeExactContextualBasis_swapExactFieldAxes
    (carrier : RelationCarrier) (slot : Fin carrier.1.1) :
    normalizeExactContextualBasis (swapExactFieldAxes carrier slot) =
      -normalizeExactContextualBasis carrier := by
  rw [normalizeExactContextualBasis_eq_fiberEmbed,
    normalizeExactContextualBasis_eq_fiberEmbed]
  rcases carrier with ⟨fieldCount, sector⟩
  change exactTargetFiberEmbed fieldCount
      (normalizeContextualBasis (swapFieldAxes sector slot)) =
    -exactTargetFiberEmbed fieldCount (normalizeContextualBasis sector)
  rw [normalizeContextualBasis_swapFieldAxes, map_neg]

theorem normalizeExactContextualBasis_literalDerivativeSwap
    (site : ExactContextualDerivativeShuffleSite) :
    normalizeExactContextualBasis
        ⟨site.carrier.1,
          sectorWithGlobalWord site.carrier.2 site.targetWord⟩ =
      normalizeExactContextualBasis site.carrier := by
  rw [normalizeExactContextualBasis_eq_fiberEmbed,
    normalizeExactContextualBasis_eq_fiberEmbed]
  change exactTargetFiberEmbed site.carrier.1
      (normalizeContextualBasis
        (sectorWithGlobalWord site.carrier.2 site.targetWord)) =
    exactTargetFiberEmbed site.carrier.1
      (normalizeContextualBasis site.carrier.2)
  let genericSite : ContextualDerivativeShuffleSite site.carrier.1.1
      (dimension16DerivativeCount site.carrier.1) :=
    { sector := site.carrier.2
      targetWord := site.targetWord
      step := site.step }
  rw [normalizeContextualBasis_sectorWithGlobalWord genericSite]

theorem normalizeExactContextual_exactContextualRelationRow
    (site : ExactContextualRelationSite) :
    normalizeExactContextual (exactContextualRelationRow site) = 0 := by
  rcases site with fieldSite | derivativeSite
  · simp [exactContextualRelationRow, fieldAntisymmetryRow, map_add,
      normalizeExactContextualBasis_swapExactFieldAxes]
  · simp [exactContextualRelationRow, map_sub,
      normalizeExactContextualBasis_literalDerivativeSwap]

theorem ker_normalizeExactContextual_eq_exactContextualRelationSubmodule :
    LinearMap.ker normalizeExactContextual =
      exactContextualRelationSubmodule := by
  apply le_antisymm
  · intro value hkernel
    have hresidual := exact_residual_mem value
    rw [LinearMap.mem_ker.mp hkernel] at hresidual
    simpa using hresidual
  · unfold exactContextualRelationSubmodule
    rw [Submodule.span_le]
    rintro value ⟨site, rfl⟩
    exact LinearMap.mem_ker.mpr
      (normalizeExactContextual_exactContextualRelationRow site)

theorem normalizeExactContextual_embedExactContextual
    (value : ExactOrientedLocalSpace) :
    normalizeExactContextual (embedExactContextual value) = value := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [map_add, hleft, hright]
  | single target coefficient =>
      rcases target with ⟨fieldCount, target⟩
      simp [embedExactContextualBasis, canonicalExactContextualCarrier,
        normalizeExactContextualBasis_eq_fiberEmbed,
        normalizeContextualBasis_canonical, exactTargetFiberEmbedBasis]

theorem normalizeExactContextual_surjective :
    Function.Surjective normalizeExactContextual := by
  intro value
  exact ⟨embedExactContextual value,
    normalizeExactContextual_embedExactContextual value⟩

def exactContextualRelationQuotientEquiv :
    (RelationSpace ⧸ exactContextualRelationSubmodule) ≃ₗ[ℚ]
      ExactOrientedLocalSpace :=
  (Submodule.quotEquivOfEq exactContextualRelationSubmodule
      (LinearMap.ker normalizeExactContextual)
      ker_normalizeExactContextual_eq_exactContextualRelationSubmodule.symm).trans
    (normalizeExactContextual.quotKerEquivOfSurjective
      normalizeExactContextual_surjective)

/-! ## Identification with the existing position-indexed operators -/

structure ExactOperatorDerivativeShuffleSite where
  carrier : RelationCarrier
  site : DerivativeShuffleSite carrier

abbrev ExactOperatorRelationSite :=
  ExactContextualFieldAntisymmetrySite ⊕
    ExactOperatorDerivativeShuffleSite

def exactOperatorRelationRow : ExactOperatorRelationSite → RelationSpace
  | Sum.inl site => fieldAntisymmetryRow site.carrier site.slot
  | Sum.inr site => derivativeShuffleRow site.site

def exactOperatorRelationSubmodule : Submodule ℚ RelationSpace :=
  Submodule.span ℚ (Set.range exactOperatorRelationRow)

theorem sectorWithGlobalWord_eq_swapDerivativePositions
    {fieldCount derivativeCount : ℕ}
    (sector : DerivativeAlphaReducedSector fieldCount derivativeCount)
    (targetWord : GlobalOwnedAxisWord fieldCount derivativeCount)
    (firstPosition secondPosition : Fin derivativeCount)
    (htarget : targetWord = List.Vector.ofFn
      ((sectorGlobalWord sector).get ∘
        Equiv.swap firstPosition secondPosition)) :
    sectorWithGlobalWord sector targetWord =
      swapDerivativePositions sector firstPosition secondPosition := by
  apply DerivativeAlphaReducedSector.ext
  · rfl
  · rfl
  · rfl
  · change (orderedDerivativeWordEquivGlobal fieldCount derivativeCount).symm
        targetWord = swapOrderedDerivativeWord sector.derivativeWord
          firstPosition secondPosition
    apply (orderedDerivativeWordEquivGlobal fieldCount derivativeCount).injective
    rw [Equiv.apply_symm_apply]
    exact htarget.trans
      (orderedDerivativeWordEquivGlobal_swap sector.derivativeWord
        firstPosition secondPosition).symm

theorem exactLiteralDerivativeRow_is_operatorRow
    (site : ExactContextualDerivativeShuffleSite) :
    ∃ operatorSite : ExactOperatorDerivativeShuffleSite,
      exactContextualRelationRow (Sum.inr site) =
        exactOperatorRelationRow (Sum.inr operatorSite) := by
  rcases isAdjacentDifferentOwnerSwap_exists_positions
      (sectorGlobalWord site.carrier.2) site.targetWord site.step with
    ⟨firstPosition, secondPosition, hadjacent, hdifferent, htarget⟩
  have hdifferent' :
      site.carrier.2.derivativeWord.ownerAtPosition firstPosition ≠
        site.carrier.2.derivativeWord.ownerAtPosition secondPosition := by
    simpa [sectorGlobalWord, orderedDerivativeWordEquivGlobal,
      List.Vector.get_ofFn] using hdifferent
  let derivativeSite : DerivativeShuffleSite site.carrier :=
    { left := firstPosition
      right := secondPosition
      adjacent := Or.inl hadjacent
      different := hdifferent' }
  refine ⟨{ carrier := site.carrier, site := derivativeSite }, ?_⟩
  have hsector := sectorWithGlobalWord_eq_swapDerivativePositions
    site.carrier.2 site.targetWord firstPosition secondPosition htarget
  simp [exactContextualRelationRow, exactOperatorRelationRow,
    derivativeShuffleRow, swapExactDerivativePositions, derivativeSite,
    hsector]

theorem exactOperatorDerivativeRow_is_literalRow
    (operatorSite : ExactOperatorDerivativeShuffleSite) :
    ∃ literalSite : ExactContextualDerivativeShuffleSite,
      exactOperatorRelationRow (Sum.inr operatorSite) =
        exactContextualRelationRow (Sum.inr literalSite) := by
  let sourceWord := sectorGlobalWord operatorSite.carrier.2
  let targetSector := swapDerivativePositions operatorSite.carrier.2
    operatorSite.site.left operatorSite.site.right
  let targetWord := sectorGlobalWord targetSector
  have hdifferent :
      (sourceWord.get operatorSite.site.left).1 ≠
        (sourceWord.get operatorSite.site.right).1 := by
    simpa [sourceWord, sectorGlobalWord, orderedDerivativeWordEquivGlobal,
      List.Vector.get_ofFn] using operatorSite.site.different
  have hstepRaw := adjacentSwap_isAdjacentDifferentOwnerSwap sourceWord
    operatorSite.site.left operatorSite.site.right
    operatorSite.site.adjacent hdifferent
  have htarget : targetWord = List.Vector.ofFn
      (sourceWord.get ∘
        Equiv.swap operatorSite.site.left operatorSite.site.right) := by
    exact orderedDerivativeWordEquivGlobal_swap
      operatorSite.carrier.2.derivativeWord operatorSite.site.left
        operatorSite.site.right
  have hstep : IsAdjacentDifferentOwnerSwap sourceWord targetWord := by
    rw [htarget]
    exact hstepRaw
  let literalSite : ExactContextualDerivativeShuffleSite :=
    { carrier := operatorSite.carrier
      targetWord := targetWord
      step := hstep }
  refine ⟨literalSite, ?_⟩
  have hsector := sectorWithGlobalWord_eq_swapDerivativePositions
    operatorSite.carrier.2 targetWord operatorSite.site.left
      operatorSite.site.right htarget
  simp [exactOperatorRelationRow, exactContextualRelationRow,
    derivativeShuffleRow, swapExactDerivativePositions, literalSite,
    hsector]

theorem exactContextualRelationSubmodule_eq_exactOperatorRelationSubmodule :
    exactContextualRelationSubmodule = exactOperatorRelationSubmodule := by
  apply le_antisymm
  · unfold exactContextualRelationSubmodule
    rw [Submodule.span_le]
    rintro value ⟨site, rfl⟩
    rcases site with fieldSite | derivativeSite
    · exact Submodule.subset_span
        ⟨(Sum.inl fieldSite : ExactOperatorRelationSite), rfl⟩
    · rcases exactLiteralDerivativeRow_is_operatorRow derivativeSite with
        ⟨operatorSite, heq⟩
      rw [heq]
      exact Submodule.subset_span
        ⟨(Sum.inr operatorSite : ExactOperatorRelationSite), rfl⟩
  · unfold exactOperatorRelationSubmodule
    rw [Submodule.span_le]
    rintro value ⟨site, rfl⟩
    rcases site with fieldSite | operatorSite
    · exact Submodule.subset_span
        ⟨(Sum.inl fieldSite : ExactContextualRelationSite), rfl⟩
    · rcases exactOperatorDerivativeRow_is_literalRow operatorSite with
        ⟨literalSite, heq⟩
      rw [heq]
      exact Submodule.subset_span
        ⟨(Sum.inr literalSite : ExactContextualRelationSite), rfl⟩

/-- On the actual dependent dimension-sixteen carrier, the already defined
position-indexed antisymmetry and adjacent-shuffle operators span exactly the
kernel of simultaneous field orientation and derivative localization. -/
theorem ker_normalizeExactContextual_eq_exactOperatorRelationSubmodule :
    LinearMap.ker normalizeExactContextual =
      exactOperatorRelationSubmodule := by
  rw [ker_normalizeExactContextual_eq_exactContextualRelationSubmodule,
    exactContextualRelationSubmodule_eq_exactOperatorRelationSubmodule]

def exactOperatorRelationQuotientEquiv :
    (RelationSpace ⧸ exactOperatorRelationSubmodule) ≃ₗ[ℚ]
      ExactOrientedLocalSpace :=
  (Submodule.quotEquivOfEq exactOperatorRelationSubmodule
      (LinearMap.ker normalizeExactContextual)
      ker_normalizeExactContextual_eq_exactOperatorRelationSubmodule.symm).trans
    (normalizeExactContextual.quotKerEquivOfSurjective
      normalizeExactContextual_surjective)

/-! ## Signed hypercubic intertwining law on the quotient target -/

def OrientedLocalSector.hypercubicAct (h : Hypercubic4)
    {fieldCount derivativeCount : ℕ}
    (target : OrientedLocalSector fieldCount derivativeCount) :
    OrientedLocalSector fieldCount derivativeCount where
  trace := target.trace
  fieldPlanes := fun slot => planeAction h (target.fieldPlanes slot)
  derivativeFamily := target.derivativeFamily.hypercubicAct h

def localAxisWordFamilyTensorSign (h : Hypercubic4)
    {fieldCount derivativeCount : ℕ}
    (family : LocalAxisWordFamily fieldCount derivativeCount) : ℚ :=
  ∏ owner, ((family.1 owner).map
    (fun axis => (Hypercubic4.axisSign h axis : ℚ))).prod

def OrientedLocalSector.tensorSign (h : Hypercubic4)
    {fieldCount derivativeCount : ℕ}
    (target : OrientedLocalSector fieldCount derivativeCount) : ℚ :=
  (∏ slot, (planeTensorSign h (target.fieldPlanes slot) : ℚ)) *
    localAxisWordFamilyTensorSign h target.derivativeFamily

def exactOrientedLocalAct (h : Hypercubic4)
    (target : ExactOrientedLocalCarrier) : ExactOrientedLocalCarrier :=
  ⟨target.1, target.2.hypercubicAct h⟩

def signedExactOrientedLocalActionBasis (h : Hypercubic4)
    (target : ExactOrientedLocalCarrier) : ExactOrientedLocalSpace :=
  target.2.tensorSign h •
    Finsupp.single (exactOrientedLocalAct h target) 1

def signedExactOrientedLocalAction (h : Hypercubic4) :
    ExactOrientedLocalSpace →ₗ[ℚ] ExactOrientedLocalSpace :=
  Finsupp.linearCombination ℚ (signedExactOrientedLocalActionBasis h)

@[simp] theorem signedExactOrientedLocalAction_single (h : Hypercubic4)
    (target : ExactOrientedLocalCarrier) (coefficient : ℚ) :
    signedExactOrientedLocalAction h
        (Finsupp.single target coefficient) =
      coefficient • signedExactOrientedLocalActionBasis h target := by
  simp [signedExactOrientedLocalAction]

theorem prod_ownerAxisProjection_axisSign (h : Hypercubic4)
    {fieldCount : ℕ} (entries : List (OwnedAxis fieldCount)) :
    (∏ owner, ((ownerAxisProjection owner entries).map
        (fun axis => (Hypercubic4.axisSign h axis : ℚ))).prod) =
      (entries.map (fun entry =>
        (Hypercubic4.axisSign h entry.2 : ℚ))).prod := by
  induction entries with
  | nil => simp
  | cons entry entries ih =>
      calc
        (∏ owner, ((ownerAxisProjection owner (entry :: entries)).map
            (fun axis => (Hypercubic4.axisSign h axis : ℚ))).prod) =
            ∏ owner,
              ((if entry.1 = owner then
                  (Hypercubic4.axisSign h entry.2 : ℚ) else 1) *
                ((ownerAxisProjection owner entries).map
                  (fun axis =>
                    (Hypercubic4.axisSign h axis : ℚ))).prod) := by
              apply Finset.prod_congr rfl
              intro owner _
              by_cases howner : entry.1 = owner <;>
                simp [ownerAxisProjection, howner]
        _ = (∏ owner, if entry.1 = owner then
                (Hypercubic4.axisSign h entry.2 : ℚ) else 1) *
              ∏ owner, ((ownerAxisProjection owner entries).map
                (fun axis =>
                  (Hypercubic4.axisSign h axis : ℚ))).prod := by
              rw [Finset.prod_mul_distrib]
        _ = (Hypercubic4.axisSign h entry.2 : ℚ) *
              ∏ owner, ((ownerAxisProjection owner entries).map
                (fun axis =>
                  (Hypercubic4.axisSign h axis : ℚ))).prod := by
              simp
        _ = ((entry :: entries).map (fun current =>
              (Hypercubic4.axisSign h current.2 : ℚ))).prod := by
              simp [ih]

theorem localAxisWordFamilyTensorSign_localize (h : Hypercubic4)
    {fieldCount derivativeCount : ℕ}
    (word : GlobalOwnedAxisWord fieldCount derivativeCount) :
    localAxisWordFamilyTensorSign h (localize word) =
      ∏ position,
        (Hypercubic4.axisSign h (word.get position).2 : ℚ) := by
  unfold localAxisWordFamilyTensorSign localize
  rw [prod_ownerAxisProjection_axisSign]
  have hofFn : List.ofFn word.get = word.toList := by
    have hvector := congrArg List.Vector.toList (List.Vector.ofFn_get word)
    simpa only [List.Vector.toList_ofFn] using hvector
  rw [← hofFn, List.map_ofFn, List.prod_ofFn]
  rfl

def permuteFieldAxisAssignment (h : Hypercubic4)
    {fieldCount : ℕ} (assignment : FieldAxisAssignment fieldCount) :
    FieldAxisAssignment fieldCount :=
  fun slot => (h.perm (assignment slot).1, h.perm (assignment slot).2)

@[simp] theorem sectorFieldAxisAssignment_act (h : Hypercubic4)
    {fieldCount derivativeCount : ℕ}
    (sector : DerivativeAlphaReducedSector fieldCount derivativeCount) :
    sectorFieldAxisAssignment (derivativeAlphaReducedSectorAct h sector) =
      permuteFieldAxisAssignment h (sectorFieldAxisAssignment sector) := by
  rfl

theorem fieldAxisPlanes_permute
    (h : Hypercubic4) {fieldCount : ℕ}
    (assignment : FieldAxisAssignment fieldCount)
    (hdifferent : ∀ slot, (assignment slot).1 ≠ (assignment slot).2) :
    fieldAxisPlanes (permuteFieldAxisAssignment h assignment) =
      fun slot => planeAction h (fieldAxisPlanes assignment slot) := by
  funext slot
  exact planeLookup_permuted_certificate h
    (assignment slot).1 (assignment slot).2 (hdifferent slot)

theorem fieldAxisOrientationCoefficient_tensorSign
    (h : Hypercubic4) {fieldCount : ℕ}
    (assignment : FieldAxisAssignment fieldCount)
    (hdifferent : ∀ slot, (assignment slot).1 ≠ (assignment slot).2) :
    (((∏ slot, (Hypercubic4.axisSign h (assignment slot).1 : ℚ)) *
        ∏ slot, (Hypercubic4.axisSign h (assignment slot).2 : ℚ)) *
        fieldAxisOrientationCoefficient
          (permuteFieldAxisAssignment h assignment)) =
      fieldAxisOrientationCoefficient assignment *
        ∏ slot,
          (planeTensorSign h (fieldAxisPlanes assignment slot) : ℚ) := by
  unfold fieldAxisOrientationCoefficient
  calc
    ((∏ slot, (Hypercubic4.axisSign h (assignment slot).1 : ℚ)) *
        ∏ slot, (Hypercubic4.axisSign h (assignment slot).2 : ℚ)) *
        ∏ slot, axisPairOrientationCoefficient
          (permuteFieldAxisAssignment h assignment slot) =
      ∏ slot,
        (((Hypercubic4.axisSign h (assignment slot).1 : ℚ) *
          (Hypercubic4.axisSign h (assignment slot).2 : ℚ)) *
          axisPairOrientationCoefficient
            (permuteFieldAxisAssignment h assignment slot)) := by
        rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    _ = ∏ slot,
        (axisPairOrientationCoefficient (assignment slot) *
          (planeTensorSign h (fieldAxisPlanes assignment slot) : ℚ)) := by
        apply Finset.prod_congr rfl
        intro slot _
        exact axisPairOrientationCoefficient_tensorSign_certificate h
          (assignment slot).1 (assignment slot).2 (hdifferent slot)
    _ = (∏ slot, axisPairOrientationCoefficient (assignment slot)) *
          ∏ slot,
            (planeTensorSign h (fieldAxisPlanes assignment slot) : ℚ) := by
        rw [Finset.prod_mul_distrib]

theorem sectorGlobalWord_act (h : Hypercubic4)
    {fieldCount derivativeCount : ℕ}
    (sector : DerivativeAlphaReducedSector fieldCount derivativeCount) :
    sectorGlobalWord (derivativeAlphaReducedSectorAct h sector) =
      (sectorGlobalWord sector).hypercubicAct h := by
  apply List.Vector.eq
  simp [sectorGlobalWord, orderedDerivativeWordEquivGlobal,
    GlobalOwnedAxisWord.hypercubicAct, derivativeAlphaReducedSectorAct,
    orderedDerivativeWordAct, List.map_ofFn]
  funext position
  rfl

theorem normalizedSectorData_act (h : Hypercubic4)
    {fieldCount derivativeCount : ℕ}
    (sector : DerivativeAlphaReducedSector fieldCount derivativeCount)
    (hdifferent : ∀ slot,
      (sectorFieldAxisAssignment sector slot).1 ≠
        (sectorFieldAxisAssignment sector slot).2) :
    normalizedSectorData (derivativeAlphaReducedSectorAct h sector) =
      (normalizedSectorData sector).hypercubicAct h := by
  apply OrientedLocalSector.ext
  · rfl
  · exact fieldAxisPlanes_permute h
      (sectorFieldAxisAssignment sector) hdifferent
  · change localize
        (sectorGlobalWord (derivativeAlphaReducedSectorAct h sector)) =
      (localize (sectorGlobalWord sector)).hypercubicAct h
    rw [sectorGlobalWord_act, localize_hypercubicAct]

theorem normalizeExactContextualBasis_signed_equivariant
    (h : Hypercubic4) (carrier : RelationCarrier) :
    exactDimension16DerivativeAlphaReducedTensorSign h carrier •
        normalizeExactContextualBasis
          (exactDimension16DerivativeAlphaReducedAct h carrier) =
      signedExactOrientedLocalAction h
        (normalizeExactContextualBasis carrier) := by
  let assignment := sectorFieldAxisAssignment carrier.2
  by_cases hdiagonal : ∃ slot, (assignment slot).1 = (assignment slot).2
  · rcases hdiagonal with ⟨slot, hslot⟩
    have hzero : fieldAxisOrientationCoefficient assignment = 0 := by
      unfold fieldAxisOrientationCoefficient
      apply Finset.prod_eq_zero (Finset.mem_univ slot)
      simp [axisPairOrientationCoefficient, hslot]
    have hzeroAct : fieldAxisOrientationCoefficient
        (permuteFieldAxisAssignment h assignment) = 0 := by
      unfold fieldAxisOrientationCoefficient
      apply Finset.prod_eq_zero (Finset.mem_univ slot)
      simp [permuteFieldAxisAssignment, axisPairOrientationCoefficient, hslot]
    simp [normalizeExactContextualBasis, assignment,
      exactDimension16DerivativeAlphaReducedAct, hzero, hzeroAct]
  · have hdifferent : ∀ slot,
        (assignment slot).1 ≠ (assignment slot).2 := by
      intro slot hequal
      exact hdiagonal ⟨slot, hequal⟩
    have hfield := fieldAxisOrientationCoefficient_tensorSign h assignment
      hdifferent
    have hderivative := localAxisWordFamilyTensorSign_localize h
      (sectorGlobalWord carrier.2)
    have hderivative' :
        (∏ position, (Hypercubic4.axisSign h
          (carrier.2.derivativeWord.axisAtPosition position) : ℚ)) =
          localAxisWordFamilyTensorSign h
            (normalizedSectorData carrier.2).derivativeFamily := by
      simpa [normalizedSectorData, sectorGlobalWord,
        orderedDerivativeWordEquivGlobal, List.Vector.get_ofFn] using
          hderivative.symm
    have hdata := normalizedSectorData_act h carrier.2 hdifferent
    have hcoefficient :
        exactDimension16DerivativeAlphaReducedTensorSign h carrier *
          fieldAxisOrientationCoefficient
            (permuteFieldAxisAssignment h assignment) =
        fieldAxisOrientationCoefficient assignment *
          (normalizedSectorData carrier.2).tensorSign h := by
      unfold exactDimension16DerivativeAlphaReducedTensorSign
        derivativeAlphaReducedSectorTensorSign OrientedLocalSector.tensorSign
      dsimp [assignment, sectorFieldAxisAssignment] at hfield ⊢
      rw [hderivative']
      calc
        (((∏ slot, (Hypercubic4.axisSign h
              (carrier.2.fieldFirst slot) : ℚ)) *
            ∏ slot, (Hypercubic4.axisSign h
              (carrier.2.fieldSecond slot) : ℚ)) *
            localAxisWordFamilyTensorSign h
              (normalizedSectorData carrier.2).derivativeFamily) *
          fieldAxisOrientationCoefficient
            (permuteFieldAxisAssignment h
              (sectorFieldAxisAssignment carrier.2)) =
          ((((∏ slot, (Hypercubic4.axisSign h
                (carrier.2.fieldFirst slot) : ℚ)) *
              ∏ slot, (Hypercubic4.axisSign h
                (carrier.2.fieldSecond slot) : ℚ)) *
              fieldAxisOrientationCoefficient
                (permuteFieldAxisAssignment h
                  (sectorFieldAxisAssignment carrier.2))) *
            localAxisWordFamilyTensorSign h
              (normalizedSectorData carrier.2).derivativeFamily) := by ring
        _ = ((fieldAxisOrientationCoefficient
              (sectorFieldAxisAssignment carrier.2) *
                ∏ slot, (planeTensorSign h
                  (fieldAxisPlanes
                    (sectorFieldAxisAssignment carrier.2) slot) : ℚ)) *
              localAxisWordFamilyTensorSign h
                (normalizedSectorData carrier.2).derivativeFamily) := by
            rw [hfield]
        _ = _ := by
            simp [normalizedSectorData, mul_assoc]
    simp only [normalizeExactContextualBasis,
      exactDimension16DerivativeAlphaReducedAct,
      sectorFieldAxisAssignment_act, smul_smul, exactNormalizedSectorData]
    rw [hdata, hcoefficient]
    rw [map_smul]
    simp [signedExactOrientedLocalActionBasis, exactOrientedLocalAct,
      assignment]

/-- The combined exact quotient map intertwines the already defined signed
source action with the literal signed action on oriented planes and local
derivative words. -/
theorem normalizeExactContextual_signed_equivariant
    (h : Hypercubic4) (value : RelationSpace) :
    normalizeExactContextual (signedRelationAction h value) =
      signedExactOrientedLocalAction h
        (normalizeExactContextual value) := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [map_add, hleft, hright]
  | single carrier coefficient =>
      simp only [signedRelationAction_single,
        normalizeExactContextual_single, map_smul]
      rw [mul_smul,
        normalizeExactContextualBasis_signed_equivariant h carrier]

end HypercubicDimension16ContextualQuotient
end YangMills
end QuantumTheory
end Mettapedia
