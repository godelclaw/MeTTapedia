import Mettapedia.QuantumTheory.YangMills.V14BoundaryCochainComplex

/-!
# Derivative-aware extraction on the repaired boundary-coordinate space

This module equips the postponed-IBP complex with a canonical-dimension
filtration and a certified coordinate projection.  The filtration is indexed
by the actual `F,D` dimension assigned to each coordinate, rather than by
radial field-amplitude degree.  In particular, the dimension-six
`∂² Tr(F²)` bulk descendant and its dimension-five boundary current survive
the cutoff, while the dimension-eighteen scalar witness from MOVE 5 is
removed.

Two norm statements are proved on the already-coordinatized
bulk-plus-boundary space.  The first is coefficient `ℓ¹`, used by the existing
finite-matrix transfer machinery.  The second is the literal coefficient-sup
branch of F.3's stated local norm: every coefficient bounded by `C` remains
bounded by `1·C` after extraction.  Both constants are one.  This is not yet a
theorem transferring an arbitrary Wilson analytic functional into these
coordinates.  Such a transfer requires genuine Wilson representatives and
analytic dual jets for the manuscript's full, presently schematic
dimension-sixteen census.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace V14BoundaryCochainExtraction

open V14BoundaryCochainComplex

/-! ## Generic finite canonical filtration -/

/-- Coordinates whose assigned canonical dimension is at most `cutoff`. -/
abbrev CanonicalFilteredCoordinate
    (Coordinate : Type*) (dimension : Coordinate → ℕ) (cutoff : ℕ) :=
  {coordinate : Coordinate // dimension coordinate ≤ cutoff}

/-- Kronecker coordinate basis on a finite coefficient space. -/
def canonicalCoordinateBasis
    {Coordinate : Type*} [DecidableEq Coordinate]
    {dimension : Coordinate → ℕ} {cutoff : ℕ}
    (low : CanonicalFilteredCoordinate Coordinate dimension cutoff) :
    Coordinate → ℝ :=
  fun coordinate => if coordinate = low.1 then 1 else 0

/-- The exact dual coordinate functional.  It is a jet only after an analytic
Wilson functional has separately been mapped into these coefficients. -/
def canonicalCoordinateDual
    {Coordinate : Type*}
    {dimension : Coordinate → ℕ} {cutoff : ℕ}
    (low : CanonicalFilteredCoordinate Coordinate dimension cutoff)
    (coefficients : Coordinate → ℝ) : ℝ :=
  coefficients low.1

theorem canonicalCoordinateDual_basis_biorthogonal
    {Coordinate : Type*} [DecidableEq Coordinate]
    {dimension : Coordinate → ℕ} {cutoff : ℕ}
    (left right : CanonicalFilteredCoordinate Coordinate dimension cutoff) :
    canonicalCoordinateDual left (canonicalCoordinateBasis right) =
      if left = right then 1 else 0 := by
  by_cases h : left = right
  · subst right
    simp [canonicalCoordinateDual, canonicalCoordinateBasis]
  · have hvalues : left.1 ≠ right.1 := by
      intro heq
      exact h (Subtype.ext heq)
    simp [canonicalCoordinateDual, canonicalCoordinateBasis, h, hvalues]

/-- Certified basis/dual matrix. -/
def canonicalCoordinateJetMatrix
    {Coordinate : Type*} [DecidableEq Coordinate]
    {dimension : Coordinate → ℕ} {cutoff : ℕ} :
    Matrix
      (CanonicalFilteredCoordinate Coordinate dimension cutoff)
      (CanonicalFilteredCoordinate Coordinate dimension cutoff) ℝ :=
  fun left right =>
    canonicalCoordinateDual left (canonicalCoordinateBasis right)

theorem canonicalCoordinateJetMatrix_eq_one
    {Coordinate : Type*} [DecidableEq Coordinate]
    {dimension : Coordinate → ℕ} {cutoff : ℕ} :
    canonicalCoordinateJetMatrix
        (Coordinate := Coordinate) (dimension := dimension) (cutoff := cutoff) = 1 := by
  ext left right
  rw [canonicalCoordinateJetMatrix,
    canonicalCoordinateDual_basis_biorthogonal]
  rfl

/-- Hard cutoff by canonical dimension on an already-coordinatized vector. -/
def canonicalDimensionProjection
    {Coordinate : Type*}
    (dimension : Coordinate → ℕ) (cutoff : ℕ)
    [DecidablePred (fun c : Coordinate => dimension c ≤ cutoff)]
    (coefficients : Coordinate → ℝ) : Coordinate → ℝ :=
  fun coordinate =>
    if dimension coordinate ≤ cutoff then coefficients coordinate else 0

theorem canonicalDimensionProjection_idempotent
    {Coordinate : Type*}
    (dimension : Coordinate → ℕ) (cutoff : ℕ)
    [DecidablePred (fun c : Coordinate => dimension c ≤ cutoff)]
    (coefficients : Coordinate → ℝ) :
    canonicalDimensionProjection dimension cutoff
        (canonicalDimensionProjection dimension cutoff coefficients) =
      canonicalDimensionProjection dimension cutoff coefficients := by
  funext coordinate
  by_cases h : dimension coordinate ≤ cutoff <;>
    simp [canonicalDimensionProjection, h]

theorem canonicalDimensionProjection_fixes
    {Coordinate : Type*}
    (dimension : Coordinate → ℕ) (cutoff : ℕ)
    [DecidablePred (fun c : Coordinate => dimension c ≤ cutoff)]
    (coefficients : Coordinate → ℝ) (coordinate : Coordinate)
    (hlow : dimension coordinate ≤ cutoff) :
    canonicalDimensionProjection dimension cutoff coefficients coordinate =
      coefficients coordinate := by
  simp [canonicalDimensionProjection, hlow]

theorem canonicalDimensionProjection_kills
    {Coordinate : Type*}
    (dimension : Coordinate → ℕ) (cutoff : ℕ)
    [DecidablePred (fun c : Coordinate => dimension c ≤ cutoff)]
    (coefficients : Coordinate → ℝ) (coordinate : Coordinate)
    (hhigh : cutoff < dimension coordinate) :
    canonicalDimensionProjection dimension cutoff coefficients coordinate = 0 := by
  simp [canonicalDimensionProjection, Nat.not_le.mpr hhigh]

/-- **Certified repaired-norm bound.**  Coordinate truncation has induced
coefficient-`ℓ¹` norm at most one. -/
theorem coefficientL1_canonicalDimensionProjection_le
    {Coordinate : Type*} [Fintype Coordinate]
    (dimension : Coordinate → ℕ) (cutoff : ℕ)
    [DecidablePred (fun c : Coordinate => dimension c ≤ cutoff)]
    (coefficients : Coordinate → ℝ) :
    coefficientL1
        (canonicalDimensionProjection dimension cutoff coefficients) ≤
      1 * coefficientL1 coefficients := by
  classical
  simp only [one_mul]
  unfold coefficientL1
  apply Finset.sum_le_sum
  intro coordinate _
  by_cases h : dimension coordinate ≤ cutoff <;>
    simp [canonicalDimensionProjection, h]

/-- Pointwise formulation of the coefficient-sup branch of the manuscript's
local analytic norm. -/
def HasManuscriptCoefficientSupBound
    {Coordinate : Type*} (coefficients : Coordinate → ℝ) (C : ℝ) : Prop :=
  ∀ coordinate, |coefficients coordinate| ≤ C

/-- **Manuscript coefficient-sup bound.**  The canonical-dimension cutoff has
operator factor one for the coefficient-sup norm named in F.3.  The theorem
starts after Wilson analytic functions have been expressed in the repaired
coordinates; construction of that expression for the full census remains a
separate transfer obligation. -/
theorem canonicalDimensionProjection_coefficientSup_le
    {Coordinate : Type*}
    (dimension : Coordinate → ℕ) (cutoff : ℕ)
    [DecidablePred (fun c : Coordinate => dimension c ≤ cutoff)]
    (coefficients : Coordinate → ℝ) {C : ℝ}
    (hC : 0 ≤ C)
    (hbound : HasManuscriptCoefficientSupBound coefficients C) :
    HasManuscriptCoefficientSupBound
      (canonicalDimensionProjection dimension cutoff coefficients) (1 * C) := by
  intro coordinate
  by_cases hlow : dimension coordinate ≤ cutoff
  · simpa [canonicalDimensionProjection, hlow] using hbound coordinate
  · simp [canonicalDimensionProjection, hlow, hC]

/-! ## The repaired `F,D` coordinates used by the exact two-block pilot -/

/-- The five templates audited from v14, plus the boundary-sensitive
dimension-six descendant and the dimension-eighteen MOVE-5 witness. -/
inductive BoundaryAwareFDOperator where
  | displayed : V14ActionOperatorTemplate → BoundaryAwareFDOperator
  | actionLaplacian
  | highDerivativeScalar
deriving DecidableEq, Fintype, Repr

def BoundaryAwareFDOperator.canonicalDimension :
    BoundaryAwareFDOperator → ℕ
  | .displayed operator => operator.canonicalDimension
  | .actionLaplacian => 6
  | .highDerivativeScalar => 18

/-- The boundary current whose coboundary is `∂² Tr(F²)`. -/
inductive BoundaryCurrent where
  | actionFlux
deriving DecidableEq, Fintype, Repr

/-- `∂ Tr(F²)` has canonical dimension five. -/
def BoundaryCurrent.canonicalDimension : BoundaryCurrent → ℕ
  | .actionFlux => 5

/-- Bulk operator coefficients on both blocks plus the current crossing their
shared face. -/
inductive BoundaryCochainCoordinate where
  | bulk : Fin 2 → BoundaryAwareFDOperator → BoundaryCochainCoordinate
  | boundary : BoundaryCurrent → BoundaryCochainCoordinate
deriving DecidableEq, Fintype, Repr

def BoundaryCochainCoordinate.canonicalDimension :
    BoundaryCochainCoordinate → ℕ
  | .bulk _ operator => operator.canonicalDimension
  | .boundary current => current.canonicalDimension

abbrev BoundaryCochainLow16 :=
  CanonicalFilteredCoordinate BoundaryCochainCoordinate
    BoundaryCochainCoordinate.canonicalDimension 16

def boundaryCochainProjection16 :
    (BoundaryCochainCoordinate → ℝ) → BoundaryCochainCoordinate → ℝ :=
  canonicalDimensionProjection
    BoundaryCochainCoordinate.canonicalDimension 16

/-- The action current raises canonical dimension by one when its divergence
is taken.  This is the derivative grading absent from the radial extractors. -/
theorem actionFlux_coboundary_dimension :
    (BoundaryCochainCoordinate.bulk 0
        .actionLaplacian).canonicalDimension =
      (BoundaryCochainCoordinate.boundary
        .actionFlux).canonicalDimension + 1 := by
  rfl

theorem actionLaplacian_bulk_is_low (block : Fin 2) :
    (BoundaryCochainCoordinate.bulk block
        .actionLaplacian).canonicalDimension ≤ 16 := by
  norm_num [BoundaryCochainCoordinate.canonicalDimension,
    BoundaryAwareFDOperator.canonicalDimension]

theorem actionFlux_boundary_is_low :
    (BoundaryCochainCoordinate.boundary
        .actionFlux).canonicalDimension ≤ 16 := by
  decide

theorem highDerivativeScalar_is_high (block : Fin 2) :
    16 < (BoundaryCochainCoordinate.bulk block
      .highDerivativeScalar).canonicalDimension := by
  norm_num [BoundaryCochainCoordinate.canonicalDimension,
    BoundaryAwareFDOperator.canonicalDimension]

/-- There are thirteen low coordinates in the explicit audit: two block
copies of six low bulk operators and one shared boundary current.  The two
dimension-eighteen block coordinates are excluded. -/
theorem boundaryCochainLow16_card : Fintype.card BoundaryCochainLow16 = 13 := by
  decide

/-- Coefficients of the exact MOVE-5 assembly together with its retained
shared-face current. -/
def move5BoundaryCochainVector : BoundaryCochainCoordinate → ℝ
  | .bulk 0 .actionLaplacian => 1
  | .bulk 1 .actionLaplacian => -1
  | .boundary .actionFlux => 1
  | _ => 0

theorem boundaryCochainProjection16_fixes_move5Vector :
    boundaryCochainProjection16 move5BoundaryCochainVector =
      move5BoundaryCochainVector := by
  funext coordinate
  cases coordinate with
  | bulk block operator =>
      cases operator with
      | displayed displayed =>
          simp [boundaryCochainProjection16, canonicalDimensionProjection,
            BoundaryCochainCoordinate.canonicalDimension,
            BoundaryAwareFDOperator.canonicalDimension,
            move5BoundaryCochainVector]
      | actionLaplacian =>
          fin_cases block <;>
            simp [boundaryCochainProjection16,
              canonicalDimensionProjection,
              BoundaryCochainCoordinate.canonicalDimension,
              BoundaryAwareFDOperator.canonicalDimension,
              move5BoundaryCochainVector]
      | highDerivativeScalar =>
          fin_cases block <;>
            simp [boundaryCochainProjection16,
              canonicalDimensionProjection,
              BoundaryCochainCoordinate.canonicalDimension,
              BoundaryAwareFDOperator.canonicalDimension,
              move5BoundaryCochainVector]
  | boundary current =>
      cases current
      simp [boundaryCochainProjection16, canonicalDimensionProjection,
        BoundaryCochainCoordinate.canonicalDimension,
        BoundaryCurrent.canonicalDimension, move5BoundaryCochainVector]

def highDerivativeUnitVector (block : Fin 2) :
    BoundaryCochainCoordinate → ℝ :=
  fun coordinate =>
    if coordinate = .bulk block .highDerivativeScalar then 1 else 0

theorem boundaryCochainProjection16_kills_highDerivative
    (block : Fin 2) :
    boundaryCochainProjection16 (highDerivativeUnitVector block) = 0 := by
  funext coordinate
  by_cases hcoordinate :
      coordinate = .bulk block .highDerivativeScalar
  · subst coordinate
    simp [boundaryCochainProjection16, canonicalDimensionProjection,
      BoundaryCochainCoordinate.canonicalDimension,
      BoundaryAwareFDOperator.canonicalDimension,
      highDerivativeUnitVector]
  · by_cases hdim : coordinate.canonicalDimension ≤ 16
    · simp [boundaryCochainProjection16, canonicalDimensionProjection,
        highDerivativeUnitVector, hcoordinate, hdim]
    · simp [boundaryCochainProjection16, canonicalDimensionProjection,
        highDerivativeUnitVector, hcoordinate, hdim]

/-- The exact extraction constant in the labeled repaired coefficient norm. -/
def repairedBoundaryCochainExtractionConstant : ℝ := 1

theorem repairedBoundaryCochainExtractionConstant_lt_two :
    repairedBoundaryCochainExtractionConstant < 2 := by
  norm_num [repairedBoundaryCochainExtractionConstant]

theorem boundaryCochainProjection16_norm_le
    (coefficients : BoundaryCochainCoordinate → ℝ) :
    coefficientL1 (boundaryCochainProjection16 coefficients) ≤
      repairedBoundaryCochainExtractionConstant *
        coefficientL1 coefficients := by
  simpa [boundaryCochainProjection16,
    repairedBoundaryCochainExtractionConstant] using
    coefficientL1_canonicalDimensionProjection_le
      BoundaryCochainCoordinate.canonicalDimension 16 coefficients

theorem boundaryCochainProjection16_manuscriptCoefficientSup_le
    (coefficients : BoundaryCochainCoordinate → ℝ) {C : ℝ}
    (hC : 0 ≤ C)
    (hbound : HasManuscriptCoefficientSupBound coefficients C) :
    HasManuscriptCoefficientSupBound
      (boundaryCochainProjection16 coefficients)
      (repairedBoundaryCochainExtractionConstant * C) := by
  simpa [boundaryCochainProjection16,
    repairedBoundaryCochainExtractionConstant] using
    canonicalDimensionProjection_coefficientSup_le
      BoundaryCochainCoordinate.canonicalDimension 16 coefficients hC hbound

/-- Constructed certificate for the repaired coordinate extraction.  It
contains no claim that the F.3 analytic norm has already been transferred to
these coordinates. -/
structure RepairedBoundaryCochainExtractionCertificate : Prop where
  jetMatrix : canonicalCoordinateJetMatrix
      (Coordinate := BoundaryCochainCoordinate)
      (dimension := BoundaryCochainCoordinate.canonicalDimension)
      (cutoff := 16) = 1
  idempotent : ∀ coefficients,
    boundaryCochainProjection16
        (boundaryCochainProjection16 coefficients) =
      boundaryCochainProjection16 coefficients
  normBound : ∀ coefficients,
    coefficientL1 (boundaryCochainProjection16 coefficients) ≤
      repairedBoundaryCochainExtractionConstant *
        coefficientL1 coefficients
  manuscriptCoefficientSupBound : ∀ coefficients {C},
    0 ≤ C → HasManuscriptCoefficientSupBound coefficients C →
      HasManuscriptCoefficientSupBound
        (boundaryCochainProjection16 coefficients)
        (repairedBoundaryCochainExtractionConstant * C)
  carriesMove5Descendant :
    boundaryCochainProjection16 move5BoundaryCochainVector =
      move5BoundaryCochainVector
  removesDimensionEighteen : ∀ block,
    boundaryCochainProjection16 (highDerivativeUnitVector block) = 0

theorem repairedBoundaryCochainExtractionCertificate :
    RepairedBoundaryCochainExtractionCertificate := by
  refine ⟨canonicalCoordinateJetMatrix_eq_one,
    ?_, boundaryCochainProjection16_norm_le,
    boundaryCochainProjection16_manuscriptCoefficientSup_le,
    boundaryCochainProjection16_fixes_move5Vector,
    boundaryCochainProjection16_kills_highDerivative⟩
  intro coefficients
  exact canonicalDimensionProjection_idempotent
    BoundaryCochainCoordinate.canonicalDimension 16 coefficients

end V14BoundaryCochainExtraction
end YangMills
end QuantumTheory
end Mettapedia
