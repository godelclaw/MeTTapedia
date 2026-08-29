import Mettapedia.GraphTheory.FourColor.GoertzelV24HexagonPairingTargetAwareBoundary

/-!
# A signed pairing invariant with exactly the parity-adversary support

At six boundary ports there are fifteen (not necessarily planar) perfect
pair contractions.  Four small signed combinations vanish on every boundary
word accepted by the literal hexagon.  One radix-weighted combination of
those four functions is nonzero on exactly the parity-admissible words which
the hexagon rejects.

This is a negative boundary for the linear-invariant route.  It does not say
that the signed function is the counting tensor of one planar tangle.  On the
contrary, it isolates positivity/physical realizability as the extra input
which a Penrose-style repair must use.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24HexagonPairingInvariantKernel

open GoertzelV24HexagonPairingTargetAwareBoundary
open GoertzelV24RawNooseCountPumping
open GoertzelV24HexCycleBoundarySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The mate involution for each of the fifteen perfect matchings of six
labelled ports.  The five noncrossing matchings occur at indices
`0, 2, 6, 12, 14`. -/
def pairingMate : Fin 15 → Fin 6 → Fin 6
  | 0 => ![1, 0, 3, 2, 5, 4]
  | 1 => ![1, 0, 4, 5, 2, 3]
  | 2 => ![1, 0, 5, 4, 3, 2]
  | 3 => ![2, 3, 0, 1, 5, 4]
  | 4 => ![2, 4, 0, 5, 1, 3]
  | 5 => ![2, 5, 0, 4, 3, 1]
  | 6 => ![3, 2, 1, 0, 5, 4]
  | 7 => ![3, 4, 5, 0, 1, 2]
  | 8 => ![3, 5, 4, 0, 2, 1]
  | 9 => ![4, 2, 1, 5, 0, 3]
  | 10 => ![4, 3, 5, 1, 0, 2]
  | 11 => ![4, 5, 3, 2, 0, 1]
  | 12 => ![5, 2, 1, 4, 3, 0]
  | 13 => ![5, 3, 4, 1, 2, 0]
  | 14 => ![5, 4, 3, 2, 1, 0]

/-- Indicator tensor of one perfect pairing: it is one exactly when the
boundary word is constant on every matched pair. -/
def pairContraction (index : Fin 15) (word : HexagonTaitWord) : Int :=
  if ∀ port, word port = word (pairingMate index port) then 1 else 0

/-- First signed relation in the kernel of restriction to the hexagon
support. -/
def kernelZero (word : HexagonTaitWord) : Int :=
  pairContraction 8 word - pairContraction 4 word

/-- Second signed relation in the kernel of restriction to the hexagon
support. -/
def kernelOne (word : HexagonTaitWord) : Int :=
  pairContraction 10 word - pairContraction 4 word

/-- Third signed relation in the kernel of restriction to the hexagon
support. -/
def kernelTwo (word : HexagonTaitWord) : Int :=
  -pairContraction 0 word + pairContraction 1 word +
    pairContraction 3 word - 2 * pairContraction 4 word +
      pairContraction 11 word

/-- Fourth signed relation in the kernel of restriction to the hexagon
support. -/
def kernelThree (word : HexagonTaitWord) : Int :=
  -2 * pairContraction 4 word + pairContraction 5 word +
    pairContraction 9 word - pairContraction 12 word +
      pairContraction 13 word

/-- Radix-weighted combination.  The weights prevent cancellation between
the four small kernel coordinates on the finite six-port alphabet. -/
def invariantAdversaryTensor (word : HexagonTaitWord) : Int :=
  kernelZero word + 2 * kernelOne word + 4 * kernelTwo word +
    8 * kernelThree word

private def threeTaitColors : List TaitColor :=
  [⟨red, red_ne_zero⟩, ⟨blue, blue_ne_zero⟩, ⟨purple, purple_ne_zero⟩]

private theorem mem_threeTaitColors (color : TaitColor) :
    color ∈ threeTaitColors := by
  rcases color with ⟨color, hcolor⟩
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero color hcolor with
    rfl | rfl | rfl <;> simp [threeTaitColors]

private def supportRow (a b c d e f : TaitColor) : Bool :=
  let word := explicitWord a b c d e f
  decide
    (invariantAdversaryTensor word ≠ 0 ↔
      parityAdversaryBool word = true)

private def kernelRow (a b c d e f : TaitColor) : Bool :=
  let word := explicitWord a b c d e f
  decide
    (hexBoundaryRealizableBool word = true →
      kernelZero word = 0 ∧ kernelOne word = 0 ∧
        kernelTwo word = 0 ∧ kernelThree word = 0)

private def allSixSupportRows : Bool :=
  threeTaitColors.all fun a =>
    threeTaitColors.all fun b =>
      threeTaitColors.all fun c =>
        threeTaitColors.all fun d =>
          threeTaitColors.all fun e =>
            threeTaitColors.all fun f => supportRow a b c d e f

private def allSixKernelRows : Bool :=
  threeTaitColors.all fun a =>
    threeTaitColors.all fun b =>
      threeTaitColors.all fun c =>
        threeTaitColors.all fun d =>
          threeTaitColors.all fun e =>
            threeTaitColors.all fun f => kernelRow a b c d e f

private theorem allSixSupportRows_eq_true_iff :
    allSixSupportRows = true ↔
      ∀ a b c d e f : TaitColor, supportRow a b c d e f = true := by
  simp only [allSixSupportRows, List.all_eq_true]
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

/-- Closed finite check of all `3^6` genuine boundary words. -/
private theorem allSixKernelRows_eq_true_iff :
    allSixKernelRows = true ↔
      ∀ a b c d e f : TaitColor, kernelRow a b c d e f = true := by
  simp only [allSixKernelRows, List.all_eq_true]
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

theorem allSixSupportRows_eq_true : allSixSupportRows = true := by
  decide

/-- The four displayed signed combinations separately vanish on the literal
hexagon support. -/
theorem kernelCoordinates_eq_zero_of_mem_hexagonSupport
    (word : HexagonTaitWord) (hword : word ∈ hexagonSupport) :
    kernelZero word = 0 ∧ kernelOne word = 0 ∧
      kernelTwo word = 0 ∧ kernelThree word = 0 := by
  have hrealizable : HexBoundaryRealizable word :=
    (exists_hexagonExtension_iff_hexBoundaryRealizable word).1 hword
  have hbool : hexBoundaryRealizableBool word = true :=
    (hexBoundaryRealizableBool_eq_true_iff word).2 hrealizable
  rw [← explicitWord_of_word word] at hbool ⊢
  have hrow := (allSixKernelRows_eq_true_iff.mp (by decide))
    (word 0) (word 1) (word 2) (word 3) (word 4) (word 5)
  have hrow' :
      decide
        (hexBoundaryRealizableBool
              (explicitWord (word 0) (word 1) (word 2)
                (word 3) (word 4) (word 5)) = true →
          kernelZero
              (explicitWord (word 0) (word 1) (word 2)
                (word 3) (word 4) (word 5)) = 0 ∧
          kernelOne
              (explicitWord (word 0) (word 1) (word 2)
                (word 3) (word 4) (word 5)) = 0 ∧
          kernelTwo
              (explicitWord (word 0) (word 1) (word 2)
                (word 3) (word 4) (word 5)) = 0 ∧
          kernelThree
              (explicitWord (word 0) (word 1) (word 2)
                (word 3) (word 4) (word 5)) = 0) = true := by
    simpa [kernelRow] using hrow
  exact (of_decide_eq_true hrow') hbool

/-- The signed invariant tensor has exactly the parity-adversary support. -/
theorem invariantAdversaryTensor_ne_zero_iff
    (word : HexagonTaitWord) :
    invariantAdversaryTensor word ≠ 0 ↔ word ∈ parityAdversary := by
  rw [← explicitWord_of_word word]
  have hrow := (allSixSupportRows_eq_true_iff.mp
    allSixSupportRows_eq_true)
      (word 0) (word 1) (word 2) (word 3) (word 4) (word 5)
  have hrow' :
      decide
        (invariantAdversaryTensor
            (explicitWord (word 0) (word 1) (word 2)
              (word 3) (word 4) (word 5)) ≠ 0 ↔
          parityAdversaryBool
            (explicitWord (word 0) (word 1) (word 2)
              (word 3) (word 4) (word 5)) = true) = true := by
    simpa [supportRow] using hrow
  have hchecked :
      invariantAdversaryTensor
          (explicitWord (word 0) (word 1) (word 2)
            (word 3) (word 4) (word 5)) ≠ 0 ↔
        parityAdversaryBool
          (explicitWord (word 0) (word 1) (word 2)
            (word 3) (word 4) (word 5)) = true :=
    of_decide_eq_true hrow'
  exact hchecked.trans (parityAdversaryBool_eq_true_iff _)

/-- In particular the signed tensor vanishes on every word accepted by the
literal hexagon. -/
theorem invariantAdversaryTensor_eq_zero_of_mem_hexagonSupport
    (word : HexagonTaitWord) (hword : word ∈ hexagonSupport) :
    invariantAdversaryTensor word = 0 := by
  by_contra hnonzero
  have hadversary := (invariantAdversaryTensor_ne_zero_iff word).1 hnonzero
  exact hadversary.2 hword

end GoertzelV24HexagonPairingInvariantKernel

end Mettapedia.GraphTheory.FourColor
