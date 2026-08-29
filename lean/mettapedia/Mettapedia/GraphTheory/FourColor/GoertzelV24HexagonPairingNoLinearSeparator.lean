import Mettapedia.GraphTheory.FourColor.GoertzelV24HexagonPairingInvariantKernel

/-!
# No strict linear pairing separator for the hexagon adversary

The fifteen perfect-pairing contractions do not contain a Penrose-style
strict sign separator between the literal hexagon support and its
parity-admissible complement.

Five explicit adversary words have a sum of pairing-evaluation rows equal
to a signed combination of eleven genuine hexagon rows.  Hence every
integer linear combination of pairing contractions which vanishes on the
hexagon support sums to zero on those five adversary words.  Such a
functional cannot be strictly positive, or strictly negative, on the whole
adversary.

This is committed wreckage for the simplest positivity route.  A successful
planar-algebra argument must use richer common-web tensors or another
physical constraint, rather than the span of pair contractions alone.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24HexagonPairingNoLinearSeparator

open GoertzelV24RawNooseCountPumping
open GoertzelV24HexCycleBoundarySupport
open GoertzelV24HexagonPairingTargetAwareBoundary
open GoertzelV24HexagonPairingInvariantKernel

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private abbrev r : TaitColor := ⟨red, red_ne_zero⟩
private abbrev b : TaitColor := ⟨blue, blue_ne_zero⟩
private abbrev p : TaitColor := ⟨purple, purple_ne_zero⟩

/-- Five parity-adversary words whose pairing-evaluation rows positively
balance to a vector in the span of literal-hexagon rows. -/
def adversaryWitness : Fin 5 → HexagonTaitWord
  | 0 => explicitWord r r b r r b
  | 1 => explicitWord r r b r b r
  | 2 => explicitWord r r b p b p
  | 3 => explicitWord r b r r b r
  | 4 => explicitWord r b r p p b

/-- Eleven literal-hexagon words used by the exact row relation. -/
def hexagonRelationWitness : Fin 11 → HexagonTaitWord
  | 0 => explicitWord r r r r r r
  | 1 => explicitWord r r r r b b
  | 2 => explicitWord r r r b b r
  | 3 => explicitWord r r b b r r
  | 4 => explicitWord r r b b b b
  | 5 => explicitWord r r b p p b
  | 6 => explicitWord r b b r r r
  | 7 => explicitWord r b b r p p
  | 8 => explicitWord r b b b b r
  | 9 => explicitWord r b p r b p
  | 10 => explicitWord r b p p b r

/-- Coefficients of the literal-hexagon side of the row relation. -/
def hexagonRelationCoeff : Fin 11 → Int
  | 0 => 1
  | 1 => -1
  | 2 => 0
  | 3 => -1
  | 4 => 1
  | 5 => -1
  | 6 => -1
  | 7 => 1
  | 8 => 0
  | 9 => 1
  | 10 => 1

/-- Every word in the positive side of the relation is a genuine member of
the parity adversary. -/
theorem adversaryWitness_mem (index : Fin 5) :
    adversaryWitness index ∈ parityAdversary := by
  apply (parityAdversaryBool_eq_true_iff _).1
  fin_cases index <;> decide

/-- Every word in the signed side of the relation is accepted by the
literal hexagon. -/
theorem hexagonRelationWitness_mem (index : Fin 11) :
    hexagonRelationWitness index ∈ hexagonSupport := by
  apply (exists_hexagonExtension_iff_hexBoundaryRealizable _).2
  apply (hexBoundaryRealizableBool_eq_true_iff _).1
  fin_cases index <;> decide

/-- Exact Farkas row relation, checked independently for all fifteen perfect
pair contractions. -/
theorem pairContraction_farkasRelation (pairing : Fin 15) :
    (∑ index : Fin 5,
        pairContraction pairing (adversaryWitness index)) =
      ∑ index : Fin 11,
        hexagonRelationCoeff index *
          pairContraction pairing (hexagonRelationWitness index) := by
  fin_cases pairing <;> decide

/-- An arbitrary integer linear combination of the fifteen pairing
contractions. -/
def pairingLinearCombination (coeff : Fin 15 → Int)
    (word : HexagonTaitWord) : Int :=
  ∑ pairing : Fin 15, coeff pairing * pairContraction pairing word

/-- Negating all coefficients negates the resulting pairing functional. -/
theorem pairingLinearCombination_neg (coeff : Fin 15 → Int)
    (word : HexagonTaitWord) :
    pairingLinearCombination (fun index => -coeff index) word =
      -pairingLinearCombination coeff word := by
  simp only [pairingLinearCombination, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro index _
  ring

/-- The Farkas row relation holds after applying every pairing-linear
functional. -/
theorem pairingLinearCombination_farkasRelation
    (coeff : Fin 15 → Int) :
    (∑ index : Fin 5,
        pairingLinearCombination coeff (adversaryWitness index)) =
      ∑ index : Fin 11,
        hexagonRelationCoeff index *
          pairingLinearCombination coeff (hexagonRelationWitness index) := by
  simp only [pairingLinearCombination]
  calc
    (∑ x : Fin 5, ∑ i : Fin 15,
        coeff i * pairContraction i (adversaryWitness x)) =
        ∑ i : Fin 15, coeff i *
          ∑ x : Fin 5, pairContraction i (adversaryWitness x) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ = ∑ i : Fin 15, coeff i *
          ∑ x : Fin 11, hexagonRelationCoeff x *
            pairContraction i (hexagonRelationWitness x) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [pairContraction_farkasRelation]
    _ = ∑ x : Fin 11, hexagonRelationCoeff x *
          ∑ i : Fin 15, coeff i *
            pairContraction i (hexagonRelationWitness x) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- If a pairing-linear functional vanishes on the literal hexagon support,
then its five adversary-witness values sum to zero. -/
theorem sum_adversaryWitness_eq_zero_of_vanishesOnHexagon
    (coeff : Fin 15 → Int)
    (hvanish :
      ∀ word : HexagonTaitWord,
        word ∈ hexagonSupport → pairingLinearCombination coeff word = 0) :
    (∑ index : Fin 5,
      pairingLinearCombination coeff (adversaryWitness index)) = 0 := by
  rw [pairingLinearCombination_farkasRelation]
  apply Finset.sum_eq_zero
  intro index _
  rw [hvanish _ (hexagonRelationWitness_mem index), mul_zero]

/-- No pairing-linear functional which vanishes on the literal hexagon can
be strictly positive on every parity-adversary word. -/
theorem no_strictlyPositive_pairingLinearSeparator
    (coeff : Fin 15 → Int)
    (hvanish :
      ∀ word : HexagonTaitWord,
        word ∈ hexagonSupport → pairingLinearCombination coeff word = 0) :
    ¬ ∀ word : HexagonTaitWord,
        word ∈ parityAdversary → 0 < pairingLinearCombination coeff word := by
  intro hpositive
  have hpoint :
      ∀ index : Fin 5,
        0 < pairingLinearCombination coeff (adversaryWitness index) :=
    fun index => hpositive _ (adversaryWitness_mem index)
  have hsum :
      0 < ∑ index : Fin 5,
        pairingLinearCombination coeff (adversaryWitness index) :=
    Finset.sum_pos (fun index _ => hpoint index) Finset.univ_nonempty
  rw [sum_adversaryWitness_eq_zero_of_vanishesOnHexagon coeff hvanish] at hsum
  exact lt_irrefl 0 hsum

/-- The negative-sign version follows by negating the coefficients. -/
theorem no_strictlyNegative_pairingLinearSeparator
    (coeff : Fin 15 → Int)
    (hvanish :
      ∀ word : HexagonTaitWord,
        word ∈ hexagonSupport → pairingLinearCombination coeff word = 0) :
    ¬ ∀ word : HexagonTaitWord,
        word ∈ parityAdversary → pairingLinearCombination coeff word < 0 := by
  intro hnegative
  let negCoeff : Fin 15 → Int := fun index => -coeff index
  apply no_strictlyPositive_pairingLinearSeparator negCoeff
  · intro word hword
    rw [show negCoeff = fun index => -coeff index from rfl,
      pairingLinearCombination_neg, hvanish word hword, neg_zero]
  · intro word hword
    simpa [negCoeff, pairingLinearCombination_neg] using
      neg_pos.mpr (hnegative word hword)

end GoertzelV24HexagonPairingNoLinearSeparator

end Mettapedia.GraphTheory.FourColor
