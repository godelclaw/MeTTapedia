import Mettapedia.Computability.PNP.BadCodeAgreementObstruction
import Mettapedia.Computability.PNP.ExactVisibleImageBudgetFiniteCovers

/-!
# Kpoly polynomial-container agreement obstruction

This file separates two obligations in the Kpoly route.  A finite
polynomial-container presentation gives a finite predictor image, but it does
not by itself supply the bad-code agreement bound needed by the finite recovery
theorem.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

universe u v w

/-- A finite polynomial-container presentation of Boolean predictors.  Its code
type is the polynomial extension `Σ shape, position shape → Bool`. -/
structure FinitePolynomialPredictorContainer (Input : Type u) where
  Shape : Type v
  shapeFintype : Fintype Shape
  Position : Shape → Type w
  positionFintype : ∀ shape, Fintype (Position shape)
  decode : (Sigma fun shape : Shape => Position shape → Bool) → Input → Bool

namespace FinitePolynomialPredictorContainer

variable {Input : Type u}

attribute [instance] shapeFintype positionFintype

/-- The polynomial code type `Σ shape, position shape → Bool`. -/
abbrev Code (C : FinitePolynomialPredictorContainer.{u, v, w} Input) :=
  Sigma fun shape : C.Shape => C.Position shape → Bool

noncomputable instance (C : FinitePolynomialPredictorContainer.{u, v, w} Input) :
    Fintype C.Code := by
  classical
  dsimp [Code]
  infer_instance

/-- View a polynomial-container decoder as an indexed predictor family. -/
def indexedFamily (C : FinitePolynomialPredictorContainer.{u, v, w} Input) :
    IndexedPredictorFamily C.Code Input where
  predict code := C.decode code

/-- Any finite polynomial-container image has a finite predictor-image cover
bounded by its code type. -/
theorem finitePredictorCover
    (C : FinitePolynomialPredictorContainer.{u, v, w} Input) :
    C.indexedFamily.FinitePredictorCover (Fintype.card C.Code) := by
  classical
  refine ⟨Finset.univ.image C.decode, ?_, ?_⟩
  · intro code
    exact Finset.mem_image.mpr ⟨code, Finset.mem_univ code, rfl⟩
  · exact Finset.card_image_le

end FinitePolynomialPredictorContainer

/-- The one-shape, one-position polynomial container used by the obstruction.
The false payload is the all-false predictor; the true payload is a spike at
`y`. -/
def oneBitSpikePolynomialContainer
    (Input : Type u) [DecidableEq Input] (y : Input) :
    FinitePolynomialPredictorContainer Input where
  Shape := Unit
  shapeFintype := inferInstance
  Position := fun _ => Unit
  positionFintype := fun _ => inferInstance
  decode := fun code x => code.2 () && decide (x = y)

/-- The same one-bit spike family as a bit-encoded classifier family, so it can
be tested against the existing finite recovery interface. -/
def oneBitSpikeBitFamily
    (Input : Type u) [DecidableEq Input] (y : Input) :
    BitEncodedClassifierFamily Input 1 where
  decode := fun code x => code 0 && decide (x = y)

/-- The induced indexed family of the one-bit spike decoder. -/
def oneBitSpikeIndexedFamily
    (Input : Type u) [DecidableEq Input] (y : Input) :
    IndexedPredictorFamily (BitCode 1) Input where
  predict code := (oneBitSpikeBitFamily Input y).decode code

/-- The false code of the one-bit spike family. -/
def oneBitFalseCode : BitCode 1 := fun _ => false

/-- The spike code of the one-bit spike family. -/
def oneBitTrueCode : BitCode 1 := fun _ => true

@[simp] theorem oneBitSpikeBitFamily_decode_false
    {Input : Type u} [DecidableEq Input] (y : Input) :
    (oneBitSpikeBitFamily Input y).decode oneBitFalseCode = fun _ => false := by
  funext x
  simp [oneBitSpikeBitFamily, oneBitFalseCode]

@[simp] theorem oneBitSpikeBitFamily_decode_true_at
    {Input : Type u} [DecidableEq Input] (y : Input) :
    (oneBitSpikeBitFamily Input y).decode oneBitTrueCode y = true := by
  simp [oneBitSpikeBitFamily, oneBitTrueCode]

@[simp] theorem oneBitSpikeBitFamily_decode_true_of_ne
    {Input : Type u} [DecidableEq Input] {x y : Input} (hxy : x ≠ y) :
    (oneBitSpikeBitFamily Input y).decode oneBitTrueCode x = false := by
  simp [oneBitSpikeBitFamily, oneBitTrueCode, hxy]

/-- The spike code is a genuine bad code for the all-false target. -/
def oneBitSpikeBadCode
    {Input : Type u} [DecidableEq Input] (y : Input) :
    (oneBitSpikeBitFamily Input y).toEncodedFamily.BadCodes (fun _ => false) :=
  ⟨oneBitTrueCode, by
    intro h
    have hy := congrFun h y
    have htrue :
        (oneBitSpikeBitFamily Input y).toEncodedFamily.decode oneBitTrueCode y = true := by
      simp [BitEncodedClassifierFamily.toEncodedFamily, oneBitSpikeBitFamily, oneBitTrueCode]
    have htf : (true : Bool) = false := htrue.symm.trans hy
    cases htf⟩

/-- The one-bit spike indexed family has a two-predictor finite image. -/
theorem oneBitSpikeIndexedFamily_finitePredictorCover_two
    {Input : Type u} [DecidableEq Input] (y : Input) :
    (oneBitSpikeIndexedFamily Input y).FinitePredictorCover 2 := by
  have hbudget : (oneBitSpikeIndexedFamily Input y).HasBitBudget 1 := by
    refine ⟨oneBitSpikeBitFamily Input y, ?_⟩
    intro code
    exact ⟨code, rfl⟩
  simpa using
    (IndexedPredictorFamily.hasBitBudget_iff_finitePredictorCover
      (G := oneBitSpikeIndexedFamily Input y) (s := 1)).mp hbudget

/-- The one-position polynomial container has a finite image bounded by its
polynomial code type. -/
theorem oneBitSpikePolynomialContainer_finitePredictorCover
    {Input : Type u} [DecidableEq Input] (y : Input) :
    (oneBitSpikePolynomialContainer Input y).indexedFamily.FinitePredictorCover
      (Fintype.card (oneBitSpikePolynomialContainer Input y).Code) :=
  (oneBitSpikePolynomialContainer Input y).finitePredictorCover

/-- Finite polynomial image does not force a strict pure-atom bad-code
agreement bound.  The image has size at most two, but the spike bad code agrees
with the all-false target on all mass of `PMF.pure x` whenever `x ≠ y`. -/
theorem oneBitPolynomialSmallImage_not_strictBadCodeAgreementBound
    {Input : Type u} [Fintype Input] [DecidableEq Input]
    {x y : Input} (hxy : x ≠ y) {q : ℝ≥0∞} (hq_lt : q < 1) :
    (oneBitSpikePolynomialContainer Input y).indexedFamily.FinitePredictorCover
        (Fintype.card (oneBitSpikePolynomialContainer Input y).Code) ∧
      (oneBitSpikeIndexedFamily Input y).FinitePredictorCover 2 ∧
      ¬ (∀ d :
          (oneBitSpikeBitFamily Input y).toEncodedFamily.BadCodes
            (fun _ => false),
          agreementMass (PMF.pure x) (fun _ => false)
            ((oneBitSpikeBitFamily Input y).decode d.1) ≤ q) := by
  refine
    ⟨oneBitSpikePolynomialContainer_finitePredictorCover y,
      oneBitSpikeIndexedFamily_finitePredictorCover_two y, ?_⟩
  exact
    (oneBitSpikeBitFamily Input y).not_badCodeAgreementBound_pure_of_agrees
      (x := x) (target := fun _ => false) (q := q)
      (oneBitSpikeBadCode y)
      (by
        change (oneBitSpikeBitFamily Input y).decode oneBitTrueCode x = false
        exact oneBitSpikeBitFamily_decode_true_of_ne hxy)
      hq_lt

/-- Lab-facing generic packet: any finite input type with two distinct points
has a one-bit polynomial-container image that refutes strict bad-code agreement
from small-image evidence alone. -/
theorem polynomialFunctorSmallImageAgreement_obstruction_packet
    {Input : Type u} [Fintype Input] [DecidableEq Input]
    {x y : Input} (hxy : x ≠ y) {q : ℝ≥0∞} (hq_lt : q < 1) :
    (oneBitSpikePolynomialContainer Input y).indexedFamily.FinitePredictorCover
        (Fintype.card (oneBitSpikePolynomialContainer Input y).Code) ∧
      (oneBitSpikeIndexedFamily Input y).FinitePredictorCover 2 ∧
      ¬ (∀ d :
          (oneBitSpikeBitFamily Input y).toEncodedFamily.BadCodes
            (fun _ => false),
          agreementMass (PMF.pure x) (fun _ => false)
            ((oneBitSpikeBitFamily Input y).decode d.1) ≤ q) :=
  oneBitPolynomialSmallImage_not_strictBadCodeAgreementBound hxy hq_lt

end Mettapedia.Computability.PNP
