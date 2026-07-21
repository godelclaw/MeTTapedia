import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16OrbitCharacter
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CompressionCensus

/-!
# Signed character of one exact local field letter

This module gives the first semantic factor in the cycle decomposition of the
labeled Burnside numerator.  An exact local letter consists of one oriented
two-form component and an ordered word of a prescribed derivative length.
Its signed fixed-point sum under the literal hypercubic action is proved to be
the two-form character times the corresponding power of the vector character.

The result is independent of field permutations and integer partitions.  It
therefore does not yet identify the complete labeled numerator with the
cycle-index expression.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16LocalLetterCharacter

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus
open HypercubicRawFDCharacterCensus
open HypercubicDimension16CompressionCensus
open HypercubicDimension16LocalWordCarrier
open SU2LatticeFDCensusNoGo

/-! ## Exact local letters -/

/-- A local field-strength letter with exactly `derivativeCount` ordered
derivative axes. -/
abbrev ExactLocalFieldLetter (derivativeCount : ℕ) :=
  OrientedPlane × (Fin derivativeCount → Axis)

/-- Fiber of the dependent local-letter carrier at one exact derivative
length. -/
abbrev LocalFieldLetterFiber (derivativeBudget derivativeCount : ℕ) :=
  { letter : LocalFieldLetter derivativeBudget //
    letter.derivativeCount.1 = derivativeCount }

def exactLocalFieldLetterEquivFiber
    (derivativeBudget derivativeCount : ℕ)
    (countBound : derivativeCount ≤ derivativeBudget) :
    ExactLocalFieldLetter derivativeCount ≃
      LocalFieldLetterFiber derivativeBudget derivativeCount where
  toFun letter :=
    ⟨{ plane := letter.1
       derivativeCount := ⟨derivativeCount, by omega⟩
       derivativeAxis := letter.2 }, rfl⟩
  invFun letter :=
    (letter.1.plane, fun position =>
      letter.1.derivativeAxis (Fin.cast letter.2.symm position))
  left_inv := by
    intro letter
    rfl
  right_inv := by
    rintro ⟨⟨plane, ⟨actualCount, actualCountBound⟩, derivativeAxis⟩,
      countIdentity⟩
    dsimp only at countIdentity
    subst actualCount
    rfl

def ExactLocalFieldLetter.hypercubicAct (h : Hypercubic4)
    {derivativeCount : ℕ} (letter : ExactLocalFieldLetter derivativeCount) :
    ExactLocalFieldLetter derivativeCount :=
  (planeAction h letter.1,
    fun position => h.perm (letter.2 position))

def ExactLocalFieldLetter.tensorSign (h : Hypercubic4)
    {derivativeCount : ℕ} (letter : ExactLocalFieldLetter derivativeCount) : ℚ :=
  (planeTensorSign h letter.1 : ℚ) *
    ∏ position, Hypercubic4.axisSign h (letter.2 position)

/-- Direct signed fixed-point sum on exact local letters. -/
def exactLocalLetterCharacter (h : Hypercubic4)
    (derivativeCount : ℕ) : ℚ :=
  ∑ letter : ExactLocalFieldLetter derivativeCount,
    if letter.hypercubicAct h = letter then letter.tensorSign h else 0

/-- The same fixed-point sum expressed on a fiber of the actual dependent
local-letter carrier. -/
def localFieldLetterFiberCharacter (h : Hypercubic4)
    (derivativeBudget derivativeCount : ℕ) : ℚ :=
  ∑ letter : LocalFieldLetterFiber derivativeBudget derivativeCount,
    if letter.1.hypercubicAct h = letter.1 then
      letter.1.tensorSign h
    else 0

theorem exactLocalFieldLetterEquivFiber_hypercubicAct
    (h : Hypercubic4) (derivativeBudget derivativeCount : ℕ)
    (countBound : derivativeCount ≤ derivativeBudget)
    (letter : ExactLocalFieldLetter derivativeCount) :
    ((exactLocalFieldLetterEquivFiber derivativeBudget derivativeCount
        countBound letter).1.hypercubicAct h) =
      exactLocalFieldLetterEquivFiber derivativeBudget derivativeCount
        countBound (letter.hypercubicAct h) := by
  rfl

theorem exactLocalFieldLetterEquivFiber_tensorSign
    (h : Hypercubic4) (derivativeBudget derivativeCount : ℕ)
    (countBound : derivativeCount ≤ derivativeBudget)
    (letter : ExactLocalFieldLetter derivativeCount) :
    (exactLocalFieldLetterEquivFiber derivativeBudget derivativeCount
        countBound letter).1.tensorSign h =
      letter.tensorSign h := by
  rfl

theorem localFieldLetterFiberCharacter_eq_exact
    (h : Hypercubic4) (derivativeBudget derivativeCount : ℕ)
    (countBound : derivativeCount ≤ derivativeBudget) :
    localFieldLetterFiberCharacter h derivativeBudget derivativeCount =
      exactLocalLetterCharacter h derivativeCount := by
  classical
  symm
  apply Fintype.sum_equiv
    (exactLocalFieldLetterEquivFiber derivativeBudget derivativeCount
      countBound)
  intro letter
  rw [exactLocalFieldLetterEquivFiber_tensorSign]
  congr 1
  rw [exactLocalFieldLetterEquivFiber_hypercubicAct]
  apply propext
  constructor
  · intro heq
    rw [heq]
  · intro heq
    apply (exactLocalFieldLetterEquivFiber derivativeBudget derivativeCount
      countBound).injective
    exact Subtype.ext heq

/-! ## The two independent tensor factors -/

def signedFixedPlaneSum (h : Hypercubic4) : ℚ :=
  ∑ plane : OrientedPlane,
    if planeAction h plane = plane then (planeTensorSign h plane : ℚ) else 0

def signedFixedAxisWordSum (h : Hypercubic4)
    (derivativeCount : ℕ) : ℚ :=
  ∑ word : Fin derivativeCount → Axis,
    if (fun position => h.perm (word position)) = word then
      ∏ position, Hypercubic4.axisSign h (word position)
    else 0

@[simp] theorem axisSign_sq (h : Hypercubic4) (axis : Axis) :
    Hypercubic4.axisSign h axis ^ 2 = 1 := by
  unfold Hypercubic4.axisSign
  split <;> norm_num

theorem planeTensorSign_cast (h : Hypercubic4)
    (plane : OrientedPlane) :
    (planeTensorSign h plane : ℚ) =
      Hypercubic4.axisSign h plane.first *
        Hypercubic4.axisSign h plane.second *
          (planeReorderSign h plane : ℚ) := by
  unfold planeTensorSign Hypercubic4.axisSign
  split <;> split <;> norm_num

/-- The signed fixed-point sum on the six concrete oriented planes is the
exterior-square character.  The only finite split is over the twenty-four
unsigned coordinate permutations; reflection signs remain symbolic and the
resulting identities are closed as rational polynomial identities. -/
theorem signedFixedPlaneSum_eq_twoFormCharacter (h : Hypercubic4) :
    signedFixedPlaneSum h = twoFormCharacter h := by
  rcases h with ⟨permutation, reflected⟩
  obtain ⟨permutationCodeIndex, rfl⟩ :=
    permutationCode_bijective.2 permutation
  fin_cases permutationCodeIndex <;>
    simp [signedFixedPlaneSum, twoFormCharacter, vectorCharacter,
      signedAxisTrace, planeAction,
      planeActionPerm, planeLookup, planeTensorSign_cast,
      planeReorderSign, OrientedPlane.first, OrientedPlane.second,
      pow_two, hypercubic_mul_def, Hypercubic4.axisSign_compose,
      Hypercubic4.compose_perm_apply, permutationCode,
      Fin.sum_univ_succ] <;>
    ring

/-- Ordered derivative words contribute the corresponding tensor power of
the signed vector character. -/
theorem signedFixedAxisWordSum_eq_vectorCharacter_pow
    (h : Hypercubic4) (derivativeCount : ℕ) :
    signedFixedAxisWordSum h derivativeCount =
      vectorCharacter h ^ derivativeCount := by
  classical
  unfold signedFixedAxisWordSum vectorCharacter signedAxisTrace
  calc
    (∑ word : Fin derivativeCount → Axis,
        if (fun position => h.perm (word position)) = word then
          ∏ position, Hypercubic4.axisSign h (word position)
        else 0) =
      ∑ word : Fin derivativeCount → Axis,
        ∏ position,
          (if h.perm (word position) = word position then
            Hypercubic4.axisSign h (word position)
          else 0) := by
        apply Finset.sum_congr rfl
        intro word _
        by_cases hfixed :
            (fun position => h.perm (word position)) = word
        · rw [if_pos hfixed]
          have hpointwise (position : Fin derivativeCount) :
              h.perm (word position) = word position :=
            congrFun hfixed position
          simp [hpointwise]
        · rw [if_neg hfixed]
          have hnotPointwise :
              ¬ ∀ position, h.perm (word position) = word position := by
            intro hall
            apply hfixed
            funext position
            exact hall position
          push Not at hnotPointwise
          obtain ⟨position, hposition⟩ := hnotPointwise
          exact (Finset.prod_eq_zero (Finset.mem_univ position) (by
            rw [if_neg hposition])).symm
    _ = (∑ axis : Axis,
        if h.perm axis = axis then Hypercubic4.axisSign h axis else 0) ^
          derivativeCount := by
        rw [Fintype.sum_pow]

/-! ## Product factorization -/

theorem exactLocalLetterCharacter_eq_mul
    (h : Hypercubic4) (derivativeCount : ℕ) :
    exactLocalLetterCharacter h derivativeCount =
      signedFixedPlaneSum h *
        signedFixedAxisWordSum h derivativeCount := by
  classical
  unfold exactLocalLetterCharacter signedFixedPlaneSum
    signedFixedAxisWordSum
  rw [Fintype.sum_prod_type]
  simp only [ExactLocalFieldLetter.hypercubicAct,
    ExactLocalFieldLetter.tensorSign, Prod.mk.injEq]
  simp_rw [show ∀ (plane : OrientedPlane)
      (word : Fin derivativeCount → Axis),
      (if planeAction h plane = plane ∧
          (fun position => h.perm (word position)) = word then
        (planeTensorSign h plane : ℚ) *
          ∏ position, Hypercubic4.axisSign h (word position)
      else 0) =
      (if planeAction h plane = plane then
        (planeTensorSign h plane : ℚ) else 0) *
      (if (fun position => h.perm (word position)) = word then
        ∏ position, Hypercubic4.axisSign h (word position) else 0) by
    intro plane word
    by_cases hplane : planeAction h plane = plane <;>
      by_cases hword : (fun position => h.perm (word position)) = word <;>
      simp [hplane, hword]]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro plane _
  rw [Finset.mul_sum]

/-- Semantic realization of the cycle-letter factor used by the compression
formula. -/
theorem exactLocalLetterCharacter_eq_cycleLetterCharacter
    (h : Hypercubic4) (cycleLength derivativeCount : ℕ) :
    exactLocalLetterCharacter (h ^ cycleLength) derivativeCount =
      cycleLetterCharacter h cycleLength derivativeCount := by
  rw [exactLocalLetterCharacter_eq_mul,
    signedFixedPlaneSum_eq_twoFormCharacter,
    signedFixedAxisWordSum_eq_vectorCharacter_pow]
  rfl

end HypercubicDimension16LocalLetterCharacter
end YangMills
end QuantumTheory
end Mettapedia
