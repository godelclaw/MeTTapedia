import Mettapedia.PLN.WorldModel.EvidenceSpaces

/-!
# Sharing and resampling under weighted answers

`DemandAgreement` compares a computation bound once and used twice, with
sharing (one observation used twice) and with resampling (one observation per
use), over bags and supports. This module makes the comparison when answers
carry annotations in a commutative semiring `K`
(`WeightedAnswerAlgebra.Ans K X = X →₀ K`).

* Sharing reads the answers once and pairs each with itself: `sharedPair A`
  weighs `(x, x)` by `A x`. Resampling reads them twice: `resampledPair A`
  weighs `(x, y)` by `A x * A y` (`sharedPair_apply`, `resampledPair_apply`).
* They agree exactly when every weight is idempotent and two distinct answers
  have weights with zero product (`sharedPair_eq_resampledPair_iff`).
* Without zero divisors: exactly when there is at most one answer and its weight
  is idempotent (`sharedPair_eq_resampledPair_iff_of_noZeroDivisors`). For bags
  (`K = ℕ`) this is `DemandAgreement`'s "at most one answer" line.
* For evidence counts with the paired-sample product the idempotents are no
  evidence, one positive sample and one negative sample
  (`Evidence.mul_self_eq_self_iff`). So a producer with one answer may be
  shared or resampled alike as a bag, while the evidence it carries tells the
  two apart: `(3, 1)` shared, `(9, 7)` resampled
  (`Controls.one_answer_evidence_differs`).
* For the coordinatewise product of counts, the product used to fuse likelihood
  reports, a choice between an answer with one positive and an answer with one
  negative sample is shared and resampled alike, although the two bags differ,
  two pairs against four (`Controls.fused_choice_hides_resampling`): with zero
  divisors the weights cannot see the correlation that sharing creates.

So a strategy law licensed by answer bags (reuse of a producer of one outcome)
holds for weighted answers only where the weights are idempotent, and a weight
algebra with zero divisors can make sharing and resampling indistinguishable
where the bags are not.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.WeightedDemandAgreement

open Mettapedia.Languages.MeTTa.WeightedAnswerAlgebra
open Mettapedia.PLN.WorldModel.EvidenceSpaces

variable {K : Type*} [CommSemiring K] {X : Type*}

/-- Sharing: one observation, used twice. -/
noncomputable def sharedPair (A : Ans K X) : Ans K (X × X) :=
  Ans.map (fun x => (x, x)) A

/-- Resampling: one observation per use. -/
noncomputable def resampledPair (A : Ans K X) : Ans K (X × X) :=
  Ans.bind A fun x => Ans.map (Prod.mk x) A

theorem sharedPair_apply [DecidableEq X] (A : Ans K X) (x y : X) :
    sharedPair A (x, y) = if x = y then A x else 0 := by
  rw [sharedPair, Ans.map_eq_mapDomain]
  split_ifs with h
  · subst h
    exact Finsupp.mapDomain_apply (fun a b h => (Prod.mk.inj h).1) A x
  · apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨z, hz⟩
    exact h ((Prod.mk.inj hz).1.symm.trans (Prod.mk.inj hz).2)

theorem resampledPair_apply [DecidableEq X] (A : Ans K X) (x y : X) :
    resampledPair A (x, y) = A x * A y := by
  have inner : ∀ z : X, Ans.map (Prod.mk z) A (x, y) = if z = x then A y else 0 := by
    intro z
    rw [Ans.map_eq_mapDomain]
    split_ifs with h
    · subst h
      exact Finsupp.mapDomain_apply (Prod.mk_right_injective z) A y
    · apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨w, hw⟩
      exact h (Prod.mk.inj hw).1
  rw [resampledPair, Ans.bind_apply]
  simp only [inner, mul_ite, mul_zero]
  rw [Finsupp.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [Finsupp.notMem_support_iff.mp h, zero_mul]

/-- **Sharing and resampling agree exactly when every weight is idempotent and
distinct answers have weights with zero product.** -/
theorem sharedPair_eq_resampledPair_iff [DecidableEq X] (A : Ans K X) :
    sharedPair A = resampledPair A ↔
      (∀ x, A x * A x = A x) ∧ ∀ x y, x ≠ y → A x * A y = 0 := by
  constructor
  · intro h
    refine ⟨fun x => ?_, fun x y hxy => ?_⟩
    · have := DFunLike.congr_fun h (x, x)
      rw [sharedPair_apply, resampledPair_apply, if_pos rfl] at this
      exact this.symm
    · have := DFunLike.congr_fun h (x, y)
      rw [sharedPair_apply, resampledPair_apply, if_neg hxy] at this
      exact this.symm
  · rintro ⟨idem, cross⟩
    ext ⟨x, y⟩
    rw [sharedPair_apply, resampledPair_apply]
    split_ifs with hxy
    · subst hxy
      exact (idem x).symm
    · exact (cross x y hxy).symm

/-- **Without zero divisors: at most one answer, with an idempotent weight.** -/
theorem sharedPair_eq_resampledPair_iff_of_noZeroDivisors [DecidableEq X] [NoZeroDivisors K]
    (A : Ans K X) :
    sharedPair A = resampledPair A ↔
      A = 0 ∨ ∃ x w, w ≠ 0 ∧ w * w = w ∧ A = Finsupp.single x w := by
  rw [sharedPair_eq_resampledPair_iff]
  constructor
  · rintro ⟨idem, cross⟩
    by_cases hA : A = 0
    · exact Or.inl hA
    · right
      obtain ⟨x, hx⟩ := Finsupp.ne_iff.mp hA
      refine ⟨x, A x, hx, idem x, ?_⟩
      ext y
      by_cases hy : y = x
      · subst hy
        simp
      · rw [Finsupp.single_apply, if_neg (Ne.symm hy)]
        exact (mul_eq_zero.mp (cross y x hy)).resolve_right hx
  · rintro (rfl | ⟨x, w, -, hw, rfl⟩)
    · exact ⟨fun _ => by rw [Finsupp.zero_apply, mul_zero],
        fun _ _ _ => by rw [Finsupp.zero_apply, zero_mul]⟩
    · refine ⟨fun y => ?_, fun y z hyz => ?_⟩
      · simp only [Finsupp.single_apply]
        split_ifs
        · exact hw
        · exact mul_zero 0
      · simp only [Finsupp.single_apply]
        split_ifs with h1 h2
        · exact absurd (h1.symm.trans h2) hyz
        · exact mul_zero w
        · exact zero_mul _
        · exact zero_mul _

/-! ## Idempotent evidence -/

private theorem nat_mul_self_eq_self {n : ℕ} : n * n = n ↔ n = 0 ∨ n = 1 := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exact Or.inl h0
    · right
      have : n * n = n * 1 := by rw [h, mul_one]
      exact Nat.eq_of_mul_eq_mul_left hpos this
  · rintro (rfl | rfl) <;> rfl

/-- **The idempotent evidence counts are no evidence, one positive sample and one
negative sample**, for the paired-sample product. -/
theorem Evidence.mul_self_eq_self_iff (e : Evidence ℕ) :
    e * e = e ↔ e = 0 ∨ e = Evidence.positive ∨ e = Evidence.negative := by
  obtain ⟨p, n⟩ := e
  have unfold : (⟨p, n⟩ : Evidence ℕ) * ⟨p, n⟩ = ⟨p * p, p * n + n * p + n * n⟩ := rfl
  rw [unfold]
  constructor
  · intro h
    have hp : p * p = p := congrArg Evidence.pos h
    have hn : p * n + n * p + n * n = n := congrArg Evidence.neg h
    rcases nat_mul_self_eq_self.mp hp with rfl | rfl
    · have hn' : n * n = n := by simpa using hn
      rcases nat_mul_self_eq_self.mp hn' with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr rfl)
    · have hn' : n + n + n * n = n := by simpa using hn
      have : n = 0 := by
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · exact h0
        · have : n < n + n + n * n := by omega
          omega
      subst this
      exact Or.inr (Or.inl rfl)
  · rintro (h | h | h) <;> cases h <;> rfl

namespace Controls

/-- The evidence of three positive and one negative sample. -/
def threeOne : Evidence ℕ := ⟨3, 1⟩

/-- **One answer: alike as a bag, apart as evidence.** A producer with one answer
of multiplicity one is shared and resampled alike; the same answer carrying the
evidence `(3, 1)` is weighed `(3, 1)` when shared and `(9, 7)` when resampled. -/
theorem one_answer_evidence_differs :
    sharedPair (Finsupp.single () (1 : ℕ)) = resampledPair (Finsupp.single () 1) ∧
      sharedPair (Finsupp.single () threeOne) ((), ()) = ⟨3, 1⟩ ∧
      resampledPair (Finsupp.single () threeOne) ((), ()) = ⟨9, 7⟩ ∧
      sharedPair (Finsupp.single () threeOne) ≠ resampledPair (Finsupp.single () threeOne) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sharedPair_eq_resampledPair_iff]
    refine ⟨fun _ => ?_, fun x y h => absurd (Subsingleton.elim x y) h⟩
    simp
  · rw [sharedPair_apply, if_pos rfl]
    simp [threeOne]
  · rw [resampledPair_apply]
    simp only [Finsupp.single_eq_same]
    rfl
  · intro h
    have := DFunLike.congr_fun h ((), ())
    rw [sharedPair_apply, if_pos rfl, resampledPair_apply] at this
    simp only [Finsupp.single_eq_same] at this
    have := congrArg Evidence.pos this
    simp [threeOne] at this

/-- A choice between two answers, `true` with one positive sample and `false`
with one negative sample, as counts under the coordinatewise product. -/
noncomputable def fusedChoice : Ans (ℕ × ℕ) Bool :=
  Finsupp.single true (1, 0) + Finsupp.single false (0, 1)

/-- The same choice as a bag. -/
noncomputable def coinBag : Ans ℕ Bool := Finsupp.single true 1 + Finsupp.single false 1

/-- **Zero divisors hide the correlation sharing creates.** Under the
coordinatewise product the two-answer choice is shared and resampled alike,
while as a bag it is not. -/
theorem fused_choice_hides_resampling :
    sharedPair fusedChoice = resampledPair fusedChoice ∧
      sharedPair coinBag ≠ resampledPair coinBag := by
  constructor
  · rw [sharedPair_eq_resampledPair_iff]
    refine ⟨fun x => ?_, fun x y hxy => ?_⟩
    · cases x <;> simp [fusedChoice]
    · cases x <;> cases y <;> simp_all [fusedChoice]
  · rw [Ne, sharedPair_eq_resampledPair_iff]
    rintro ⟨-, cross⟩
    have := cross true false (by decide)
    simp [coinBag] at this

end Controls

end Mettapedia.GSLT.Dynamics.WeightedDemandAgreement
