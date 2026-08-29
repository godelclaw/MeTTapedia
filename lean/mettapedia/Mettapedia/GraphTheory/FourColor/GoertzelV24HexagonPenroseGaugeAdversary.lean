import Mettapedia.GraphTheory.FourColor.GoertzelV24HexagonPairingInvariantKernel
import Mettapedia.GraphTheory.FourColor.GoertzelV24HexagonPersistentKempeAdversary
import Mettapedia.GraphTheory.FourColor.GoertzelV24HexagonTreeReplacementObstruction

/-!
# The persistent hexagon adversary survives the pairing-cone sign gauge

The Penrose pairing coordinates are signed on an open boundary.  For a
six-port word with even colour multiplicities, pair consecutive occurrences
of each colour in boundary order.  The sign of the resulting chord matching
is the boundary gauge.  (The enumeration of the fifteen matchings below is
ordered so that crossing parity is the parity of its index.)

After this gauge correction, one explicit signed combination of the fifteen
pairing contractions is nonnegative.  Its positive support is exactly the
sixty-word persistent Kempe adversary, it vanishes on the literal hexagon,
and it meets every smaller four-vertex tree support.

This is a negative boundary for a *linear* Penrose-cone repair.  Nothing here
claims that the displayed tensor is the extension-count tensor of an actual
plane cubic tangle.  Physical realizability is a nonlinear/integral
semigroup condition and remains the missing input.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24HexagonPenroseGaugeAdversary

open GoertzelV24RawNooseCountPumping
open GoertzelV24HexCycleBoundarySupport
open GoertzelV24HexagonPairingTargetAwareBoundary
open GoertzelV24HexagonPairingInvariantKernel
open GoertzelV24HexagonPersistentKempeAdversary
open GoertzelV24HexagonTreeReplacementObstruction

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The particular pairing-kernel coordinate found by the exact cone audit:
`delta_4 - delta_5 - delta_9 + delta_10 + delta_12 - delta_13`. -/
def penroseKernelTensor (word : HexagonTaitWord) : Int :=
  pairContraction 4 word - pairContraction 5 word -
    pairContraction 9 word + pairContraction 10 word +
      pairContraction 12 word - pairContraction 13 word

/-- The fifteen pairing indices, in the order used by `pairingMate`. -/
private def pairingIndices : List (Fin 15) :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]

/-- The first perfect matching, in the fixed enumeration, on whose pairs the
word is constant.  When all colour multiplicities are even, this is the
matching obtained by pairing consecutive occurrences of each colour. -/
def firstCompatiblePairing (word : HexagonTaitWord) : Option (Fin 15) :=
  pairingIndices.find? fun index => decide (pairContraction index word = 1)

/-- Crossing-parity sign of a perfect matching in the fixed enumeration. -/
def pairingCrossingSign (index : Fin 15) : Int :=
  if index.val % 2 = 0 then 1 else -1

/-- Canonical boundary sign gauge.  Words with an odd colour multiplicity
have no compatible pairing; every pairing contraction is then zero, so the
default sign is immaterial. -/
def boundaryGauge (word : HexagonTaitWord) : Int :=
  match firstCompatiblePairing word with
  | none => 1
  | some index => pairingCrossingSign index

/-- Gauge-corrected value of the explicit pairing-kernel tensor. -/
def gaugeCorrectedPenroseTensor (word : HexagonTaitWord) : Int :=
  boundaryGauge word * penroseKernelTensor word

private def threeTaitColors : List TaitColor :=
  [⟨red, red_ne_zero⟩, ⟨blue, blue_ne_zero⟩, ⟨purple, purple_ne_zero⟩]

private theorem mem_threeTaitColors (color : TaitColor) :
    color ∈ threeTaitColors := by
  rcases color with ⟨color, hcolor⟩
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero color hcolor with
    rfl | rfl | rfl <;> simp [threeTaitColors]

private def gaugeRow (a b c d e f : TaitColor) : Bool :=
  let word :=
    GoertzelV24HexagonPairingTargetAwareBoundary.explicitWord a b c d e f
  decide
    (0 ≤ gaugeCorrectedPenroseTensor word ∧
      (gaugeCorrectedPenroseTensor word ≠ 0 ↔
        persistentAdversaryBool word = true))

private def allGaugeRows : Bool :=
  threeTaitColors.all fun a =>
    threeTaitColors.all fun b =>
      threeTaitColors.all fun c =>
        threeTaitColors.all fun d =>
          threeTaitColors.all fun e =>
            threeTaitColors.all fun f => gaugeRow a b c d e f

private theorem allGaugeRows_eq_true_iff :
    allGaugeRows = true ↔
      ∀ a b c d e f : TaitColor, gaugeRow a b c d e f = true := by
  simp only [allGaugeRows, List.all_eq_true]
  constructor
  · intro h a b c d e f
    exact h a (mem_threeTaitColors a)
      b (mem_threeTaitColors b)
      c (mem_threeTaitColors c)
      d (mem_threeTaitColors d)
      e (mem_threeTaitColors e)
      f (mem_threeTaitColors f)
  · intro h a _ b _ c _ d _ e _ f _
    exact h a b c d e f

private theorem allGaugeRows_eq_true : allGaugeRows = true := by
  decide

private theorem checkedGaugeRow (word : HexagonTaitWord) :
    0 ≤ gaugeCorrectedPenroseTensor word ∧
      (gaugeCorrectedPenroseTensor word ≠ 0 ↔
        persistentAdversaryBool word = true) := by
  rw [← GoertzelV24HexagonPairingTargetAwareBoundary.explicitWord_of_word word]
  have hrow := (allGaugeRows_eq_true_iff.mp allGaugeRows_eq_true)
    (word 0) (word 1) (word 2) (word 3) (word 4) (word 5)
  exact of_decide_eq_true (by simpa [gaugeRow] using hrow)

/-- The sign-corrected pairing-kernel tensor is nonnegative on every genuine
six-port Tait word. -/
theorem gaugeCorrectedPenroseTensor_nonnegative
    (word : HexagonTaitWord) :
    0 ≤ gaugeCorrectedPenroseTensor word :=
  (checkedGaugeRow word).1

/-- Its positive support is exactly the previously certified sixty-word
persistent adversary. -/
theorem gaugeCorrectedPenroseTensor_ne_zero_iff
    (word : HexagonTaitWord) :
    gaugeCorrectedPenroseTensor word ≠ 0 ↔
      word ∈ persistentAdversary := by
  exact (checkedGaugeRow word).2.trans
    (persistentAdversaryBool_eq_true_iff word)

theorem gaugeCorrectedPenroseTensor_pos_iff
    (word : HexagonTaitWord) :
    0 < gaugeCorrectedPenroseTensor word ↔
      word ∈ persistentAdversary := by
  constructor
  · intro hpos
    exact (gaugeCorrectedPenroseTensor_ne_zero_iff word).1 (ne_of_gt hpos)
  · intro hword
    have hnonnegative := gaugeCorrectedPenroseTensor_nonnegative word
    have hnonzero := (gaugeCorrectedPenroseTensor_ne_zero_iff word).2 hword
    omega

/-- The uncorrected tensor is the difference `kernelOne - kernelThree`, so it
vanishes on the literal hexagon support by the already checked kernel
relations. -/
theorem penroseKernelTensor_eq_zero_of_mem_hexagonSupport
    (word : HexagonTaitWord) (hword : word ∈ hexagonSupport) :
    penroseKernelTensor word = 0 := by
  rcases kernelCoordinates_eq_zero_of_mem_hexagonSupport word hword with
    ⟨_, hone, _, hthree⟩
  change pairContraction 10 word - pairContraction 4 word = 0 at hone
  change -2 * pairContraction 4 word + pairContraction 5 word +
      pairContraction 9 word - pairContraction 12 word +
        pairContraction 13 word = 0 at hthree
  unfold penroseKernelTensor
  omega

theorem gaugeCorrectedPenroseTensor_eq_zero_of_mem_hexagonSupport
    (word : HexagonTaitWord) (hword : word ∈ hexagonSupport) :
    gaugeCorrectedPenroseTensor word = 0 := by
  simp [gaugeCorrectedPenroseTensor,
    penroseKernelTensor_eq_zero_of_mem_hexagonSupport word hword]

/-- Forget the nonzero proof carried by a Tait boundary colour. -/
def forgetTaitWord (word : HexagonTaitWord) : HexagonBoundaryWord :=
  fun port => (word port).1

private theorem forgetTaitWord_explicitWord
    (a b c d e f : TaitColor) :
    forgetTaitWord
        (GoertzelV24HexagonPairingTargetAwareBoundary.explicitWord
          a b c d e f) =
      hexagonColorWord a.1 b.1 c.1 d.1 e.1 f.1 := by
  funext port
  fin_cases port <;> rfl

/-- One positive adversary word for each of the three smaller plane cubic
tree shapes. -/
def treeWitness : PlaneSixPortTreeShape → HexagonTaitWord
  | .pathSeparated =>
      GoertzelV24HexagonPairingTargetAwareBoundary.explicitWord
      ⟨red, red_ne_zero⟩ ⟨red, red_ne_zero⟩ ⟨blue, blue_ne_zero⟩
      ⟨red, red_ne_zero⟩ ⟨red, red_ne_zero⟩ ⟨blue, blue_ne_zero⟩
  | .pathAdjacent =>
      GoertzelV24HexagonPairingTargetAwareBoundary.explicitWord
      ⟨red, red_ne_zero⟩ ⟨blue, blue_ne_zero⟩ ⟨red, red_ne_zero⟩
      ⟨red, red_ne_zero⟩ ⟨red, red_ne_zero⟩ ⟨blue, blue_ne_zero⟩
  | .tripod =>
      GoertzelV24HexagonPairingTargetAwareBoundary.explicitWord
      ⟨red, red_ne_zero⟩ ⟨blue, blue_ne_zero⟩ ⟨red, red_ne_zero⟩
      ⟨purple, purple_ne_zero⟩ ⟨blue, blue_ne_zero⟩ ⟨purple, purple_ne_zero⟩

theorem treeWitness_mem_persistentAdversary
    (shape : PlaneSixPortTreeShape) :
    treeWitness shape ∈ persistentAdversary := by
  cases shape <;> change persistentAdversaryBool _ = true <;> decide

theorem forgetTaitWord_treeWitness_mem_treeSupport
    (shape : PlaneSixPortTreeShape) :
    forgetTaitWord (treeWitness shape) ∈ treeSupport shape := by
  cases shape
  · refine ⟨obstructionInternal .pathSeparated, ?_⟩
    rw [show forgetTaitWord (treeWitness .pathSeparated) =
      obstructionWord .pathSeparated by
        exact forgetTaitWord_explicitWord _ _ _ _ _ _]
    exact obstructionWord_isTreeExtension .pathSeparated
  · refine ⟨obstructionInternal .pathAdjacent, ?_⟩
    rw [show forgetTaitWord (treeWitness .pathAdjacent) =
      obstructionWord .pathAdjacent by
        exact forgetTaitWord_explicitWord _ _ _ _ _ _]
    exact obstructionWord_isTreeExtension .pathAdjacent
  · refine ⟨obstructionInternal .tripod, ?_⟩
    rw [show forgetTaitWord (treeWitness .tripod) =
      obstructionWord .tripod by
        exact forgetTaitWord_explicitWord _ _ _ _ _ _]
    exact obstructionWord_isTreeExtension .tripod

/-- Consumer-facing finite-cone obstruction.  The explicit gauge-positive
pairing-kernel tensor vanishes on the hexagon, has exactly the persistent
adversary as positive support, and is positive on a word accepted by every
one of the three smaller tree shapes. -/
theorem persistentAdversary_is_gaugePositive_pairingKernel :
    (∀ word ∈ hexagonSupport, penroseKernelTensor word = 0) ∧
      (∀ word, 0 ≤ gaugeCorrectedPenroseTensor word) ∧
      (∀ word, 0 < gaugeCorrectedPenroseTensor word ↔
        word ∈ persistentAdversary) ∧
      (∀ shape : PlaneSixPortTreeShape,
        ∃ word : HexagonTaitWord,
          forgetTaitWord word ∈ treeSupport shape ∧
          0 < gaugeCorrectedPenroseTensor word) := by
  refine ⟨penroseKernelTensor_eq_zero_of_mem_hexagonSupport,
    gaugeCorrectedPenroseTensor_nonnegative,
    gaugeCorrectedPenroseTensor_pos_iff, ?_⟩
  intro shape
  exact ⟨treeWitness shape, forgetTaitWord_treeWitness_mem_treeSupport shape,
    (gaugeCorrectedPenroseTensor_pos_iff _).2
      (treeWitness_mem_persistentAdversary shape)⟩

end GoertzelV24HexagonPenroseGaugeAdversary

end Mettapedia.GraphTheory.FourColor
