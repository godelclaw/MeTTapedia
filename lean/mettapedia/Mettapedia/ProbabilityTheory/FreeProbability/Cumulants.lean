import Mettapedia.ProbabilityTheory.FreeProbability.NoncrossingPartitions
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Ordered free cumulants

A normalized linear functional on an associative algebra supplies word moments.
Triangular inversion of the noncrossing moment formula constructs every joint cumulant
as a multilinear map. Block products commute in the scalar ring; arguments within a
block remain in their original order. Neither positivity nor traciality is assumed.

Freeness below means vanishing of every mixed positional cumulant, including interleaved
words. This is the cumulant characterization of freeness; the equivalence with the
centered-alternating-subalgebra formulation is not proved here.

Reference: Nica and Speicher, Chapters 11–12:
https://rolandspeicher.com/wp-content/uploads/2020/06/nica-speicher-book.pdf
-/

namespace Mettapedia.ProbabilityTheory.FreeProbability
open Finset

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Algebraic expectation. Analytic positivity and trace laws are additional properties. -/
structure AlgebraicState (R A : Type*) [CommRing R] [Ring A] [Algebra R A] where
  toLinearMap : A →ₗ[R] R
  map_one : toLinearMap 1 = 1

instance : CoeFun (AlgebraicState R A) (fun _ => A → R) := ⟨fun φ => φ.toLinearMap⟩

@[simp] theorem AlgebraicState.apply_one (φ : AlgebraicState R A) : φ 1 = 1 := φ.map_one

/-- Ordered word moment as a multilinear map, also for a noncommutative algebra. -/
def wordMoment (φ : AlgebraicState R A) (n : ℕ) : MultilinearMap R (fun _ : Fin n => A) R :=
  φ.toLinearMap.compMultilinearMap (MultilinearMap.mkPiAlgebraFin R n A)

@[simp] theorem wordMoment_apply (φ : AlgebraicState R A) {n : ℕ} (a : Fin n → A) :
    wordMoment φ n a = φ (List.ofFn a).prod := rfl

/-- Ordered restrictions of a word are fed to one map per block. -/
def partitionMultilinear {n : ℕ} (P : Partition n)
    (k : (B : P.parts) → MultilinearMap R (fun _ : Fin B.val.card => A) R) :
    MultilinearMap R (fun _ : Fin n => A) R :=
  ((MultilinearMap.mkPiAlgebra R P.parts R).compMultilinearMap k).domDomCongr P.coordinates

@[simp] theorem partitionMultilinear_apply {n : ℕ} (P : Partition n)
    (k : (B : P.parts) → MultilinearMap R (fun _ : Fin B.val.card => A) R) (a : Fin n → A) :
    partitionMultilinear P k a = ∏ B : P.parts, k B (fun i => a (blockPosition B.val i)) := by
  change (∏ B : P.parts, k B (fun i => a (P.coordinates ⟨B, i⟩))) = _
  simp only [Partition.coordinates_apply]

/-- Every order is constructed from moments and strictly lower-order cumulants. -/
def jointCumulant (φ : AlgebraicState R A) (n : ℕ) :
    MultilinearMap R (fun _ : Fin n => A) R :=
  if n = 0 then 0 else wordMoment φ n - ∑ P : properNoncrossingPartitions n,
    partitionMultilinear P.val (fun B => jointCumulant φ B.val.card)
termination_by n
decreasing_by exact P.val.card_lt (mem_erase.mp P.property).1 B.property

/-- A partition's scalar contribution; no variable sorting occurs. -/
def partitionEvaluation {ι : Type*} (k : (n : ℕ) → (Fin n → ι) → R)
    {n : ℕ} (P : Partition n) (a : Fin n → ι) : R :=
  ∏ B ∈ P.parts, k B.card (fun i => a (blockPosition B i))

@[simp] theorem jointCumulant_zero (φ : AlgebraicState R A) : jointCumulant φ 0 = 0 := by
  rw [jointCumulant, if_pos rfl]

theorem jointCumulant_rec (φ : AlgebraicState R A) {n : ℕ} (hn : 0 < n) (a : Fin n → A) :
    jointCumulant φ n a = wordMoment φ n a -
      ∑ P ∈ properNoncrossingPartitions n, partitionEvaluation (fun n => jointCumulant φ n) P a := by
  rw [jointCumulant, if_neg (Nat.ne_of_gt hn)]
  simp only [sub_apply, _root_.sum_apply, partitionMultilinear_apply]
  congr 1
  calc
    _ = ∑ P : properNoncrossingPartitions n,
        partitionEvaluation (fun n => jointCumulant φ n) P.val a := by
      apply Fintype.sum_congr _ _
      intro P
      exact Finset.prod_coe_sort P.val.parts
        (fun B => jointCumulant φ B.card (fun i => a (blockPosition B i)))
    _ = _ := Finset.sum_coe_sort (properNoncrossingPartitions n)
      (fun P => partitionEvaluation (fun n => jointCumulant φ n) P a)

omit [CommRing R] in
private theorem apply_cast {ι : Type*} (k : (n : ℕ) → (Fin n → ι) → R)
    {m n : ℕ} (h : m = n) (a : Fin n → ι) :
    k m (fun i => a (Fin.cast h i)) = k n a := by
  subst n
  rfl

theorem partitionEvaluation_top {ι : Type*} (k : (n : ℕ) → (Fin n → ι) → R)
    {n : ℕ} (hn : 0 < n) (a : Fin n → ι) :
    partitionEvaluation k (⊤ : Partition n) a = k n a := by
  simp only [partitionEvaluation, top_parts hn, prod_singleton]
  simp only [blockPosition_univ]
  exact apply_cast k (by simp) a

/-- Independent moment–cumulant equation, including the empty word. -/
theorem moment_cumulant (φ : AlgebraicState R A) (n : ℕ) (a : Fin n → A) :
    wordMoment φ n a = ∑ P ∈ noncrossingPartitions n,
      partitionEvaluation (fun n => jointCumulant φ n) P a := by
  by_cases hn : n = 0
  · subst n
    have h : noncrossingPartitions 0 = {⊤} := by decide +kernel
    have ht : (⊤ : Partition 0).parts = ∅ := by decide +kernel
    simp [h, partitionEvaluation, ht]
  · have hn' := Nat.pos_of_ne_zero hn
    have he := Finset.sum_erase_add (noncrossingPartitions n)
      (fun P => partitionEvaluation (fun n => jointCumulant φ n) P a)
      ((mem_noncrossingPartitions _).mpr (top_noncrossing n))
    rw [partitionEvaluation_top _ hn'] at he
    rw [jointCumulant_rec φ hn' a] at he
    simpa [properNoncrossingPartitions] using he

/-- A structurally recursive table for kernel evaluation; the requested order is certified
within its bound. No out-of-range cumulant is supplied. -/
def cumulantTable (φ : AlgebraicState R A) : (bound n : ℕ) → n ≤ bound → (Fin n → A) → R
  | 0, _, _, _ => 0
  | bound + 1, n, hn, a =>
    if n = 0 then 0 else wordMoment φ n a - ∑ P : properNoncrossingPartitions n,
      ∏ B : P.val.parts, cumulantTable φ bound B.val.card (by
        have h := P.val.card_lt (mem_erase.mp P.property).1 B.property
        omega) (fun i => a (blockPosition B.val i))

theorem cumulantTable_eq (φ : AlgebraicState R A) (bound n : ℕ) (hn : n ≤ bound)
    (a : Fin n → A) : cumulantTable φ bound n hn a = jointCumulant φ n a := by
  induction bound generalizing n with
  | zero =>
    have : n = 0 := by omega
    subst n
    simp [cumulantTable]
  | succ bound ih =>
    by_cases h : n = 0
    · subst n
      simp [cumulantTable]
    · rw [cumulantTable, if_neg h, jointCumulant, if_neg h]
      simp only [sub_apply, _root_.sum_apply, partitionMultilinear_apply]
      congr 1
      apply Fintype.sum_congr _ _
      intro P
      apply Fintype.prod_congr _ _
      intro B
      exact ih _ _ _

/-- Scalar cumulants are the diagonal of the joint construction, at every order. -/
def freeCumulant (φ : AlgebraicState R A) (X : A) (n : ℕ) : R :=
  jointCumulant φ n (fun _ => X)

@[simp] theorem partitionEvaluation_const (φ : AlgebraicState R A) (X : A)
    {n : ℕ} (P : Partition n) :
    partitionEvaluation (fun m => jointCumulant φ m) P (fun _ => X) =
      ∏ B ∈ P.parts, freeCumulant φ X B.card := rfl

/-- Ordinary moments are retained independently of the inversion. -/
def moment (φ : AlgebraicState R A) (X : A) (n : ℕ) : R := φ (X ^ n)

@[simp] theorem moment_zero (φ : AlgebraicState R A) (X : A) : moment φ X 0 = 1 := by
  simp [moment]

theorem freeCumulant_rec (φ : AlgebraicState R A) (X : A) {n : ℕ} (hn : 0 < n) :
    freeCumulant φ X n = moment φ X n -
      ∑ P ∈ properNoncrossingPartitions n, ∏ B ∈ P.parts, freeCumulant φ X B.card := by
  simpa [freeCumulant, wordMoment, moment, partitionEvaluation] using
    jointCumulant_rec φ hn (fun _ => X)

/-- A finite sum can be grouped by shapes only for diagonal block evaluations. -/
theorem proper_sum_by_shapes (f : ℕ → R) (n : ℕ) :
    (∑ P ∈ properNoncrossingPartitions n, ∏ B ∈ P.parts, f B.card) =
      ((properShapes n).map (fun sizes => (sizes.map f).prod)).sum := by
  simp only [properShapes, Finset.sum, Finset.prod, Multiset.map_map, Function.comp_def]

theorem freeCumulant_one (φ : AlgebraicState R A) (X : A) :
    freeCumulant φ X 1 = moment φ X 1 := by
  rw [freeCumulant_rec φ X (by decide), proper_sum_by_shapes, properShapes_small.1]
  simp

theorem freeCumulant_two_variance (φ : AlgebraicState R A) (X : A) :
    freeCumulant φ X 2 = moment φ X 2 - moment φ X 1 ^ 2 := by
  rw [freeCumulant_rec φ X (by decide), proper_sum_by_shapes, properShapes_small.2.1]
  simp [freeCumulant_one, pow_two]

theorem freeCumulant_two_eq_moment_two_of_mean_zero (φ : AlgebraicState R A) (X : A)
    (h : moment φ X 1 = 0) : freeCumulant φ X 2 = moment φ X 2 := by
  simp [freeCumulant_two_variance, h]

theorem freeCumulant_three (φ : AlgebraicState R A) (X : A) :
    freeCumulant φ X 3 = moment φ X 3 - 3 * moment φ X 2 * moment φ X 1 +
      2 * moment φ X 1 ^ 3 := by
  rw [freeCumulant_rec φ X (by decide), proper_sum_by_shapes, properShapes_small.2.2.1]
  simp [freeCumulant_one, freeCumulant_two_variance]
  ring

theorem freeCumulant_four (φ : AlgebraicState R A) (X : A) :
    freeCumulant φ X 4 = moment φ X 4 - 4 * moment φ X 3 * moment φ X 1 -
      2 * moment φ X 2 ^ 2 + 10 * moment φ X 2 * moment φ X 1 ^ 2 -
      5 * moment φ X 1 ^ 4 := by
  rw [freeCumulant_rec φ X (by decide), proper_sum_by_shapes, properShapes_small.2.2.2.1]
  simp [freeCumulant_one, freeCumulant_two_variance, freeCumulant_three]
  ring

/-- In particular, the fifth-order coefficients are 15, 15, −35, 14. -/
theorem freeCumulant_five (φ : AlgebraicState R A) (X : A) :
    freeCumulant φ X 5 = moment φ X 5 - 5 * moment φ X 4 * moment φ X 1 -
      5 * moment φ X 3 * moment φ X 2 + 15 * moment φ X 3 * moment φ X 1 ^ 2 +
      15 * moment φ X 2 ^ 2 * moment φ X 1 - 35 * moment φ X 2 * moment φ X 1 ^ 3 +
      14 * moment φ X 1 ^ 5 := by
  rw [freeCumulant_rec φ X (by decide), proper_sum_by_shapes, properShapes_small.2.2.2.2.1]
  simp [freeCumulant_one, freeCumulant_two_variance, freeCumulant_three,
    freeCumulant_four]
  ring

/-- All mixed choices of positions must vanish; sorted words alone are insufficient. -/
def FreelyIndependent (φ : AlgebraicState R A) (X Y : A) : Prop :=
  ∀ n (s : Finset (Fin n)), s.Nonempty → s ≠ univ →
    jointCumulant φ n (fun i => if i ∈ s then X else Y) = 0

/-- The moment equation determines all cumulants uniquely, even on a generator alphabet. -/
theorem jointCumulant_unique {ι : Type*} (φ : AlgebraicState R A) (g : ι → A)
    (k : (n : ℕ) → (Fin n → ι) → R) (hzero : ∀ a, k 0 a = 0)
    (hmom : ∀ n (a : Fin n → ι), wordMoment φ n (fun i => g (a i)) =
      ∑ P ∈ noncrossingPartitions n, partitionEvaluation k P a) :
    ∀ n (a : Fin n → ι), jointCumulant φ n (fun i => g (a i)) = k n a := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a
    by_cases hn : n = 0
    · subst n
      simp [hzero]
    · have hp := Nat.pos_of_ne_zero hn
      rw [jointCumulant_rec φ hp, hmom]
      have hs : (∑ P ∈ properNoncrossingPartitions n,
          partitionEvaluation (fun m => jointCumulant φ m) P (fun i => g (a i))) =
          ∑ P ∈ properNoncrossingPartitions n, partitionEvaluation k P a := by
        apply sum_congr rfl
        intro P hP
        apply prod_congr rfl
        intro B hB
        exact ih B.card (P.card_lt (mem_erase.mp hP).1 hB) _
      rw [hs]
      have he := sum_erase_add (noncrossingPartitions n)
        (fun P => partitionEvaluation k P a)
        ((mem_noncrossingPartitions _).mpr (top_noncrossing n))
      rw [partitionEvaluation_top k hp] at he
      rw [← he]
      simp [properNoncrossingPartitions]

/-- Algebra maps preserving the state preserve all ordered joint cumulants. -/
theorem jointCumulant_map {B : Type*} [Ring B] [Algebra R B]
    (φ : AlgebraicState R A) (ψ : AlgebraicState R B) (f : A →ₐ[R] B)
    (hstate : ∀ a, ψ (f a) = φ a) (n : ℕ) (a : Fin n → A) :
    jointCumulant ψ n (fun i => f (a i)) = jointCumulant φ n a := by
  apply jointCumulant_unique ψ f (fun n => jointCumulant φ n)
  · simp
  · intro m b
    rw [wordMoment_apply, List.ofFn_comp', ← map_list_prod, hstate]
    exact moment_cumulant φ m b

/-- Expanding all positions retains only the two pure words under freeness. -/
theorem freeCumulant_additive (φ : AlgebraicState R A) (X Y : A)
    (hfree : FreelyIndependent φ X Y) (n : ℕ) :
    freeCumulant φ (X + Y) n = freeCumulant φ X n + freeCumulant φ Y n := by
  by_cases hn : n = 0
  · subst n
    simp [freeCumulant]
  · have hne : (univ : Finset (Fin n)) ≠ ∅ :=
      (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn))).ne_empty
    change jointCumulant φ n ((fun _ => X) + (fun _ => Y)) = _
    rw [(jointCumulant φ n).map_add_univ]
    have hs := sum_eq_add_of_mem (univ : Finset (Fin n)) ∅ (mem_univ _) (mem_univ _)
      hne (f := fun s => jointCumulant φ n
        (s.piecewise (fun _ => X) (fun _ => Y)))
    refine Eq.trans (hs ?_) ?_
    · intro s _ hne
      exact hfree n s (Finset.nonempty_iff_ne_empty.mpr hne.2) hne.1
    · simp [freeCumulant]

/-- Scalar homogeneity follows from constructed multilinearity, without a separate axiom. -/
theorem freeCumulant_scaling (φ : AlgebraicState R A) (X : A) (c : R) (n : ℕ) :
    freeCumulant φ (c • X) n = c ^ n * freeCumulant φ X n := by
  simpa [freeCumulant] using
    (jointCumulant φ n).map_smul_univ (fun _ => c) (fun _ => X)

/-- A cumulant profile, without claiming identification with an analytic measure. -/
def HasSemicircularCumulants (φ : AlgebraicState R A) (X : A) (variance : R) : Prop :=
  ∀ n, freeCumulant φ X n = if n = 2 then variance else 0

theorem HasSemicircularCumulants.add (φ : AlgebraicState R A) {X Y : A} {v w : R}
    (hX : HasSemicircularCumulants φ X v) (hY : HasSemicircularCumulants φ Y w)
    (hfree : FreelyIndependent φ X Y) : HasSemicircularCumulants φ (X + Y) (v + w) := by
  intro n
  rw [freeCumulant_additive φ X Y hfree, hX n, hY n]
  split_ifs <;> simp

theorem HasSemicircularCumulants.smul (φ : AlgebraicState R A) {X : A} {v : R}
    (hX : HasSemicircularCumulants φ X v) (c : R) :
    HasSemicircularCumulants φ (c • X) (c ^ 2 * v) := by
  intro n
  rw [freeCumulant_scaling, hX n]
  split_ifs with h
  · rw [h]
  · exact mul_zero _

noncomputable section

/-- A word algebra realizes a supplied word-moment function by linear extension. -/
def wordState {ι : Type*} (weights : FreeMonoid ι → R) (hone : weights 1 = 1) :
    AlgebraicState R (MonoidAlgebra R (FreeMonoid ι)) where
  toLinearMap := (Finsupp.linearCombination R weights).comp
    (MonoidAlgebra.coeffLinearEquiv R).toLinearMap
  map_one := by
    simp [MonoidAlgebra.one_def, MonoidAlgebra.coeffLinearEquiv, hone]

/-- Monomials corresponding to single letters of the free word algebra. -/
def letter {ι : Type*} (i : ι) : MonoidAlgebra R (FreeMonoid ι) :=
  MonoidAlgebra.of R (FreeMonoid ι) (FreeMonoid.of i)

@[simp] theorem wordState_of {ι : Type*} (weights : FreeMonoid ι → R)
    (hone : weights 1 = 1) (w : FreeMonoid ι) :
    wordState weights hone (MonoidAlgebra.of R (FreeMonoid ι) w) = weights w := by
  simp [wordState, MonoidAlgebra.of_apply, MonoidAlgebra.coeffLinearEquiv]

theorem wordState_word {ι : Type*} (weights : FreeMonoid ι → R)
    (hone : weights 1 = 1) (w : List ι) :
    wordState weights hone (w.map (letter (R := R))).prod = weights (FreeMonoid.ofList w) := by
  have hp : (w.map FreeMonoid.of).prod = FreeMonoid.ofList w := by
    apply FreeMonoid.toList.injective
    simp only [FreeMonoid.toList_prod, List.map_map, Function.comp_def,
      FreeMonoid.toList_of, FreeMonoid.toList_ofList]
    induction w with
    | nil => rfl
    | cons i w ih => simpa using ih
  have hm := map_list_prod (MonoidAlgebra.of R (FreeMonoid ι)) (w.map FreeMonoid.of)
  rw [hp, List.map_map] at hm
  calc
    _ = wordState weights hone (MonoidAlgebra.of R (FreeMonoid ι) (FreeMonoid.ofList w)) := by
      congr 1
      exact hm.symm
    _ = _ := wordState_of weights hone _

/-- Ordered diagram moments, before any algebraic realization or inversion. -/
def diagramMoment {ι : Type*} (k : (n : ℕ) → (Fin n → ι) → R) (w : List ι) : R :=
  ∑ P ∈ noncrossingPartitions w.length, partitionEvaluation k P w.get

@[simp] theorem diagramMoment_nil {ι : Type*} (k : (n : ℕ) → (Fin n → ι) → R) :
    diagramMoment k [] = 1 := by
  have h : noncrossingPartitions 0 = {⊤} := by decide +kernel
  have ht : (⊤ : Partition 0).parts = ∅ := by decide +kernel
  simp [diagramMoment, h, partitionEvaluation, ht]

theorem diagramMoment_ofFn {ι : Type*} (k : (n : ℕ) → (Fin n → ι) → R)
    {n : ℕ} (a : Fin n → ι) :
    diagramMoment k (List.ofFn a) = ∑ P ∈ noncrossingPartitions n, partitionEvaluation k P a := by
  unfold diagramMoment
  have hg : (List.ofFn a).get = fun i => a (Fin.cast List.length_ofFn i) := by
    funext i
    exact List.get_ofFn a i
  rw [hg]
  exact apply_cast (fun m b => ∑ P ∈ noncrossingPartitions m, partitionEvaluation k P b)
    List.length_ofFn a

/-- Algebraic realization of a cumulant profile on an alphabet.
Positivity of this functional requires additional hypotheses on the profile. -/
def cumulantWordState {ι : Type*} (k : (n : ℕ) → (Fin n → ι) → R) :
    AlgebraicState R (MonoidAlgebra R (FreeMonoid ι)) :=
  wordState (fun w => diagramMoment k w.toList) (diagramMoment_nil k)

theorem cumulantWordState_word {ι : Type*} (k : (n : ℕ) → (Fin n → ι) → R) (w : List ι) :
    cumulantWordState k (w.map (letter (R := R))).prod = diagramMoment k w :=
  wordState_word (fun w => diagramMoment k w.toList) (diagramMoment_nil k) w

/-- Triangular uniqueness recovers the prescribed profile on every generator word. -/
theorem cumulantWordState_cumulant {ι : Type*} (k : (n : ℕ) → (Fin n → ι) → R)
    (hzero : ∀ a, k 0 a = 0) (n : ℕ) (a : Fin n → ι) :
    jointCumulant (cumulantWordState k) n (fun i => letter (a i)) = k n a := by
  apply jointCumulant_unique _ (letter (R := R)) k hzero
  intro m b
  rw [wordMoment_apply, List.ofFn_comp']
  change wordState _ _ ((List.ofFn b).map (letter (R := R))).prod = _
  exact (wordState_word (fun w => diagramMoment k w.toList)
    (diagramMoment_nil k) (List.ofFn b)).trans (diagramMoment_ofFn k b)

end

end Mettapedia.ProbabilityTheory.FreeProbability
