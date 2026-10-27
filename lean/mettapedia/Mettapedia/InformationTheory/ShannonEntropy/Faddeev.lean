import Mettapedia.InformationTheory.Basic
import Mettapedia.InformationTheory.ShannonEntropy.Properties
import InformationTheory.ShannonEntropy.Faddeev
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic.Convert

/-!
# Faddeev's Axiomatic Characterization of Shannon Entropy

Faddeev's 1956 characterization derives normalized Shannon entropy from binary
continuity, symmetry, grouping and normalization. In particular, full continuity
and maximality are conclusions, not additional assumptions.

The uniqueness proof and its analytic consequences live in the standalone
`InformationTheory.ShannonEntropy.Faddeev` module. `FaddeevEntropy.equivStandalone`
preserves the supplied entropy function and each axiom in both directions.
The local constructions and historical theorem statements remain available;
their proofs reuse the canonical results through `FaddeevEntropy.toStandalone`.

## Assumptions

1. **Binary Continuity (F1)**: H(p, 1-p) is continuous
2. **Symmetry (F2)**: H is invariant under permutations
3. **Recursivity (F3)**: H satisfies the grouping/chain rule
4. **Normalization (F4)**: H(1/2, 1/2) = 1

These four clauses characterize entropy. Their count is not a proof that every
clause is independent or that no smaller axiomatization exists.

## Derived Properties

| Property | Faddeev | Shannon-Khinchin |
|----------|---------|------------------|
| Binary continuity | **ASSUMES** | - |
| Full continuity | **DERIVES** | ASSUMES |
| Symmetry | ASSUMES | ASSUMES (explicit relabeling field) |
| Recursivity | ASSUMES | ASSUMES (=strong additivity) |
| Monotonicity | **DERIVES** | - |
| Maximality | **DERIVES** | ASSUMES |
| Expansibility | **DERIVES** | ASSUMES |
| Named clauses | 4 | 5, plus relabeling |

## Proof Route

1. From recursivity: F(mn) = F(m) + F(n) where F(n) = H(uniform(n))
2. From normalization: F(2) = 1, hence F(2^k) = k
3. Define c_p = F(p)/log(p) for primes p
4. Binary continuity gives F(n) - F(n-1) → 0. Extremal prime coefficients and
   the factor 2 in the predecessors of odd prime powers force all c_p to agree
5. Conclusion: F(n) = log₂(n) for all n ≥ 1
6. Grouping gives equality on rational binary distributions; binary continuity
   and induction on arity give equality on every probability vector
7. Full continuity, monotonicity, maximality and expansibility follow

## Main Results

* `FaddeevEntropy` - Structure encoding Faddeev's 4 axioms
* `shannonFaddeev` - Shannon entropy satisfies Faddeev's axioms
* `FaddeevEntropy.toStandalone` - Axiom-preserving bridge to the canonical proof
* `faddeev_c_prime_all_equal` - All c_p = c_2 = 1/log(2)
* `faddeev_F_eq_log2` - F(n) = log₂(n)
* `faddeev_H_eq_shannon` - Equality on all finite probability vectors
* `faddeev_F_monotone` - Monotonicity on uniform distributions

## References

* Faddeev, D.K. "On the concept of entropy of a finite probabilistic scheme" (1956)
* Leinster, T. "An operadic introduction to entropy" (lecture notes)
-/

namespace Mettapedia.InformationTheory

open scoped Topology

open Finset Real Filter

/-! ## Faddeev's Axioms -/

/-- **Faddeev entropy**: A family of functions H : ProbVec n → ℝ satisfying
    Faddeev's three axioms plus normalization. -/
structure FaddeevEntropy where
  /-- The entropy function for each arity n ≥ 1 -/
  H : ∀ {n : ℕ}, ProbVec n → ℝ
  /-- F1: Continuity of binary entropy -/
  continuous_binary : Continuous (fun p : Set.Icc (0 : ℝ) 1 =>
    H (binaryDist p.1 p.2.1 p.2.2))
  /-- F2: Symmetry under permutations -/
  symmetry : ∀ {n : ℕ} (p : ProbVec n) (σ : Equiv.Perm (Fin n)),
    H (permute σ p) = H p
  /-- F3: Recursivity / Chain Rule / Grouping Property

      H(p₁,...,pₙ) = H(p₁+p₂, p₃,...,pₙ) + (p₁+p₂)·H(p₁/(p₁+p₂), p₂/(p₁+p₂))

      This expresses that grouping the first two outcomes into one
      splits the entropy into two parts. -/
  recursivity : ∀ {n : ℕ} (p : ProbVec (n + 2)) (h : 0 < p.1 0 + p.1 1),
    H p = H (groupFirstTwo p h) + (p.1 0 + p.1 1) * H (normalizeBinary (p.1 0) (p.1 1)
      (p.nonneg 0) (p.nonneg 1) h)
  /-- Normalization: H(1/2, 1/2) = 1 -/
  normalization : H binaryUniform = 1

/-- Transfer the same entropy function and axioms to the standalone development.

Both probability-vector interfaces are the standard simplex over `Fin n`;
no continuity, sign or monotonicity assumption is added. -/
def FaddeevEntropy.toStandalone (E : FaddeevEntropy) :
    _root_.InformationTheory.FaddeevEntropy where
  H := E.H
  continuous_binary := E.continuous_binary
  symmetry := E.symmetry
  recursivity := E.recursivity
  normalization := E.normalization

/-- The adapter preserves entropy at every arity. -/
@[simp]
theorem FaddeevEntropy.toStandalone_H (E : FaddeevEntropy) {n : ℕ} (p : ProbVec n) :
    E.toStandalone.H p = E.H p := rfl

/-- Import the same entropy function and all four axiom witnesses. -/
def FaddeevEntropy.ofStandalone (E : _root_.InformationTheory.FaddeevEntropy) : FaddeevEntropy where
  H := E.H
  continuous_binary := E.continuous_binary
  symmetry := E.symmetry
  recursivity := E.recursivity
  normalization := E.normalization

/-- The local semantic record and the standalone axiom record carry exactly the same data. -/
def FaddeevEntropy.equivStandalone : FaddeevEntropy ≃ _root_.InformationTheory.FaddeevEntropy where
  toFun := FaddeevEntropy.toStandalone
  invFun := FaddeevEntropy.ofStandalone
  left_inv E := by cases E; rfl
  right_inv E := by cases E; rfl

@[simp] theorem FaddeevEntropy.ofStandalone_H (E : _root_.InformationTheory.FaddeevEntropy)
    {n : ℕ} (p : ProbVec n) : (FaddeevEntropy.ofStandalone E).H p = E.H p := rfl

/-- Shannon entropy (normalized) satisfies all of Faddeev's axioms. -/
noncomputable def shannonFaddeev : FaddeevEntropy :=
  { H := @shannonEntropyNormalized
    continuous_binary := by
      -- Continuity follows from continuity of negMulLog
      unfold shannonEntropyNormalized shannonEntropy binaryDist
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      apply Continuous.div_const
      apply Continuous.add
      · exact continuous_negMulLog.comp (continuous_subtype_val.comp continuous_id)
      · apply continuous_negMulLog.comp
        apply Continuous.sub continuous_const
        exact continuous_subtype_val.comp continuous_id
    symmetry := fun p σ => by
      unfold shannonEntropyNormalized
      rw [shannonEntropy_permute]
    recursivity := fun p h => by
      unfold shannonEntropyNormalized
      -- Use the recursivity of unnormalized Shannon entropy and divide by log 2
      rw [shannonEntropy_recursivity p h]
      ring
    normalization := shannonEntropyNormalized_binaryUniform }

/-! ## Functional Equation Approach -/

/-! ### Helper Lemmas for Uniform Distributions -/

/-- When grouping two equal probabilities a = b, the normalized binary is (1/2, 1/2). -/
theorem normalizeBinary_eq_eq_binaryUniform (a : ℝ) (ha : 0 ≤ a) (hab : 0 < a + a) :
    normalizeBinary a a ha ha hab = binaryUniform := by
  apply _root_.InformationTheory.normalizeBinary_eq_eq_binaryUniform


/-- Helper: F(2) = 1 follows from normalization since uniform_2 = binaryUniform. -/
theorem faddeev_F2_eq_one (E : FaddeevEntropy) :
    E.H (uniformDist 2 (by norm_num : 0 < 2)) = 1 := by
  apply _root_.InformationTheory.faddeev_F2_eq_one E.toStandalone


/-- F(1) = 0 for any Faddeev entropy.
    This follows directly from recursivity on (1, 0):
    H(1, 0) = H(uniformDist 1) + 1 * H(1, 0) = F(1) + H(1, 0)
    Therefore F(1) = 0. -/
theorem faddeev_F1_eq_zero (E : FaddeevEntropy) :
    E.H (uniformDist 1 (by norm_num : 0 < 1)) = 0 := by
  apply _root_.InformationTheory.faddeev_F1_eq_zero E.toStandalone


/-- For a Faddeev entropy, H(1, 0) = 0.
    Compare the ternary distributions (1/2, 0, 1/2) and (1/2, 1/2, 0)
    using symmetry and recursivity. No continuity argument is needed. -/
theorem faddeev_H_one_zero (E : FaddeevEntropy) :
    E.H (binaryDist 1 (by norm_num) (by norm_num)) = 0 := by
  apply _root_.InformationTheory.faddeev_H_one_zero E.toStandalone


/-!
## Faddeev 1956: “Splitting” Lemma (Lemma 5)

Faddeev’s core technical move is that if we “split” an outcome of weight `p₀`
into a refined distribution `q` (so the refined outcomes have weights `p₀*qᵢ`),
then the entropy changes by `p₀ * H(q)`.

We prove it in a Lean-friendly form where we always split the *first* outcome;
symmetry lets us apply this to any outcome when needed.
-/

/-! ### The split construction -/

/-- Split the first outcome of `p : ProbVec (n+1)` into `m` refined outcomes
according to `q : ProbVec m`.

The resulting distribution has `n + m` outcomes:
- the first `m` outcomes have probabilities `p₀ * qᵢ`;
- the remaining `n` outcomes keep the original probabilities `p₁, …, pₙ`. -/
noncomputable def splitFirst {n m : ℕ} (p : ProbVec (n + 1)) (q : ProbVec m) : ProbVec (n + m) := by
  classical
  -- Define the distribution on `Fin (n+m)` by transporting indices to `Fin (m+n)` and using
  -- `Fin.addCases` to splice the split block and the untouched tail.
  refine ⟨fun i : Fin (n + m) =>
      Fin.addCases (motive := fun _ : Fin (m + n) => ℝ)
        (fun j : Fin m => p.1 0 * q.1 j) (fun j : Fin n => p.1 j.succ)
        (i.cast (Nat.add_comm n m)), ?_⟩
  constructor
  · intro i
    -- Nonnegativity is inherited from `p` and `q`.
    refine Fin.addCases (motive := fun j : Fin (m + n) => 0 ≤
      Fin.addCases (motive := fun _ : Fin (m + n) => ℝ)
        (fun j : Fin m => p.1 0 * q.1 j) (fun j : Fin n => p.1 j.succ) j) ?_ ?_
        (i.cast (Nat.add_comm n m))
    · intro j
      simp
      exact mul_nonneg (p.nonneg 0) (q.nonneg j)
    · intro j
      simpa using p.nonneg j.succ
  ·
    classical
    -- For the sum, rewrite to the `Fin (m+n)` sum via `Equiv.sum_comp` and then split blocks.
    set f : Fin m → ℝ := fun j => p.1 0 * q.1 j
    set g : Fin n → ℝ := fun j => p.1 j.succ
    -- Change of variables along `n+m = m+n`.
    have hcast :
        (∑ i : Fin (n + m),
            Fin.addCases (motive := fun _ : Fin (m + n) => ℝ) f g (i.cast (Nat.add_comm n m)))
          =
          (∑ i : Fin (m + n), Fin.addCases (motive := fun _ : Fin (m + n) => ℝ) f g i) := by
      -- `Fin.cast (Nat.add_comm n m)` is a permutation of indices.
      let e : Fin (n + m) ≃ Fin (m + n) :=
        { toFun := Fin.cast (Nat.add_comm n m)
          invFun := Fin.cast (Nat.add_comm m n)
          left_inv := by
            intro i
            ext
            simp
          right_inv := by
            intro i
            ext
            simp }
      simpa [e] using (Equiv.sum_comp e (fun i : Fin (m + n) =>
        Fin.addCases (motive := fun _ : Fin (m + n) => ℝ) f g i))
    -- Split the `Fin (m+n)` sum into the `m`-block and the `n`-block.
    have hsum :
        (∑ i : Fin (m + n), Fin.addCases (motive := fun _ : Fin (m + n) => ℝ) f g i)
          = (∑ i : Fin m, f i) + (∑ i : Fin n, g i) := by
      have h := (Fin.sum_univ_add (f := fun i : Fin (m + n) =>
        Fin.addCases (motive := fun _ : Fin (m + n) => ℝ) f g i))
      simpa [f, g, add_assoc, add_left_comm, add_comm] using h
    -- Tail sum of `p` is `1 - p₀`.
    have htail : (∑ i : Fin n, p.1 i.succ) = 1 - p.1 0 := by
      have : p.1 0 + (∑ i : Fin n, p.1 i.succ) = 1 := by
        simpa [Fin.sum_univ_succ, add_assoc] using
          (p.sum_eq_one : (∑ i : Fin (n + 1), p.1 i) = 1)
      linarith
    -- First block sum is `p₀`.
    have hhead : (∑ i : Fin m, f i) = p.1 0 := by
      have h :=
        (Finset.mul_sum (s := (Finset.univ : Finset (Fin m))) (f := fun i : Fin m => q.1 i)
          (p.1 0))
      calc
        (∑ i : Fin m, f i) = p.1 0 * (∑ i : Fin m, q.1 i) := by
          simpa [f] using h.symm
        _ = p.1 0 := by simp [q.sum_eq_one]
    -- Conclude the transported sum equals 1.
    calc
      (∑ i : Fin (n + m),
          Fin.addCases (motive := fun _ : Fin (m + n) => ℝ) f g (i.cast (Nat.add_comm n m)))
          =
          (∑ i : Fin (m + n), Fin.addCases (motive := fun _ : Fin (m + n) => ℝ) f g i) := hcast
      _ = (∑ i : Fin m, f i) + (∑ i : Fin n, g i) := hsum
      _ = p.1 0 + (1 - p.1 0) := by simp [hhead, htail, g]
      _ = 1 := by ring

theorem splitFirst_castAdd {n m : ℕ} (p : ProbVec (n + 1)) (q : ProbVec m) (i : Fin m) :
    (splitFirst p q).1 ((Fin.castAdd n i).cast (Nat.add_comm m n)) = p.1 0 * q.1 i := by
  apply _root_.InformationTheory.splitFirst_castAdd


theorem splitFirst_natAdd {n m : ℕ} (p : ProbVec (n + 1)) (q : ProbVec m) (i : Fin n) :
    (splitFirst p q).1 ((Fin.natAdd m i).cast (Nat.add_comm m n)) = p.1 i.succ := by
  apply _root_.InformationTheory.splitFirst_natAdd


/-! ### The binary splitting case (used later) -/

/-- Splitting an outcome into a **binary** sub-distribution.

This is the `m=2` case of Faddeev’s Lemma 5, and it follows directly from the recursivity axiom. -/
theorem faddeev_splitFirst_two {n : ℕ} (E : FaddeevEntropy) (p : ProbVec (n + 1)) (q : ProbVec 2)
    (hp0 : 0 < p.1 0) :
    E.H (splitFirst p q) = E.H p + p.1 0 * E.H q := by
  apply _root_.InformationTheory.faddeev_splitFirst_two E.toStandalone; assumption


/-!
### Faddeev Lemma 5 (general splitting, head-positive form)

For the later uniqueness proof we need the “splitting” lemma for arbitrary finite refinements:
splitting the first outcome of weight `p₀` according to a distribution `q` adds `p₀ * H(q)`.

The recursivity axiom only applies when the first two outcomes have positive total weight,
so we state the lemma in a head-positive form (`0 < q₀ + q₁`), which is the regime used in
the core Faddeev argument (uniform distributions have this automatically).  A fully general
version can be recovered by permuting the coordinates using symmetry.
-/

/-- Splitting an outcome into an arbitrary refinement, assuming the first two pieces have
positive total weight. -/
theorem faddeev_splitFirst_headPos {n m : ℕ} (E : FaddeevEntropy)
    (p : ProbVec (n + 1)) (q : ProbVec (m + 2))
    (hp0 : 0 < p.1 0) (hq : 0 < q.1 0 + q.1 1) :
    E.H (splitFirst p q) = E.H p + p.1 0 * E.H q := by
  apply _root_.InformationTheory.faddeev_splitFirst_headPos E.toStandalone <;> assumption


/-! ### Two-way Split (splitBoth)

A two-way split refines BOTH outcomes of a binary distribution. Given:
- `p : ProbVec 2` - a binary distribution (p₀, p₁)
- `q₁ : ProbVec m` - refinement for the first outcome
- `q₂ : ProbVec k` - refinement for the second outcome

The result is a distribution on `Fin (m + k)` where:
- First `m` outcomes have probability `p₀ * q₁ᵢ`
- Last `k` outcomes have probability `p₁ * q₂ⱼ`
-/

/-- Two-way split: refine both outcomes of a binary distribution.

Given a binary distribution p = (p₀, p₁) and two distributions q1 on m outcomes
and q2 on k outcomes, construct a distribution on m + k outcomes where:
- First m outcomes have probability p₀ * q1ᵢ
- Last k outcomes have probability p₁ * q2ⱼ

The sum equals 1 because: p₀·∑q1 + p₁·∑q2 = p₀·1 + p₁·1 = p₀ + p₁ = 1.
-/
noncomputable def splitBoth {m k : ℕ} (p : ProbVec 2) (q1 : ProbVec m) (q2 : ProbVec k) :
    ProbVec (m + k) := by
  classical
  refine ⟨fun i => if h : i.1 < m then p.1 0 * q1.1 ⟨i.1, h⟩
            else p.1 1 * q2.1 ⟨i.1 - m, Nat.sub_lt_left_of_lt_add (Nat.not_lt.mp h) i.isLt⟩,
          ?nonneg, ?sum_one⟩
  case nonneg =>
    intro i
    by_cases h : i.1 < m <;> simp [h] <;> apply mul_nonneg
    · exact p.nonneg 0
    · exact q1.nonneg _
    · exact p.nonneg 1
    · exact q2.nonneg _
  case sum_one =>
    -- The key: ∑ᵢ (if i<m then p₀·q1ᵢ else p₁·q2_{i-m}) = p₀·∑q1 + p₁·∑q2 = p₀ + p₁ = 1
    -- Use Fin.sum_univ_add to split the sum into Fin m and Fin k parts
    rw [Fin.sum_univ_add]
    -- For the first sum (i : Fin m), castAdd k i has val < m, so condition is true
    have h1 : ∑ i : Fin m, (if h : (Fin.castAdd k i).1 < m
        then p.1 0 * q1.1 ⟨(Fin.castAdd k i).1, h⟩
        else p.1 1 * q2.1 ⟨(Fin.castAdd k i).1 - m,
          Nat.sub_lt_left_of_lt_add (Nat.not_lt.mp h) (Fin.castAdd k i).isLt⟩) =
        p.1 0 * ∑ i : Fin m, q1.1 i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      -- (Fin.castAdd k i).1 = i.1 < m
      have hi : (Fin.castAdd k i).1 < m := i.isLt
      rw [dif_pos hi]
      -- congr closes the goal since (Fin.castAdd k i).1 = i.1
      congr
    -- For the second sum (j : Fin k), natAdd m j has val = m + j ≥ m, so condition is false
    have h2 : ∑ j : Fin k, (if h : (Fin.natAdd m j).1 < m
        then p.1 0 * q1.1 ⟨(Fin.natAdd m j).1, h⟩
        else p.1 1 * q2.1 ⟨(Fin.natAdd m j).1 - m,
          Nat.sub_lt_left_of_lt_add (Nat.not_lt.mp h) (Fin.natAdd m j).isLt⟩) =
        p.1 1 * ∑ j : Fin k, q2.1 j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      -- (Fin.natAdd m j).1 = m + j.1 ≥ m
      have hj : ¬(Fin.natAdd m j).1 < m := by
        simp only [Fin.natAdd, Nat.not_lt]
        omega
      rw [dif_neg hj]
      -- ⟨(m + j.1) - m, ...⟩ = ⟨j.1, j.isLt⟩ = j
      simp only [Fin.natAdd, Nat.add_sub_cancel_left, Fin.eta]
    rw [h1, h2, q1.sum_eq_one, q2.sum_eq_one, mul_one, mul_one]
    -- Now we have p.1 0 + p.1 1 = 1
    have hp := p.sum_eq_one
    simp only [Fin.sum_univ_two] at hp
    exact hp

/-- Value of splitBoth at an index in the first block. -/
theorem splitBoth_left {m k : ℕ} (p : ProbVec 2) (q1 : ProbVec m) (q2 : ProbVec k)
    (i : Fin m) : (splitBoth p q1 q2).1 ⟨i.1, by omega⟩ = p.1 0 * q1.1 i := by
  apply _root_.InformationTheory.splitBoth_left


/-- Value of splitBoth at an index in the second block. -/
theorem splitBoth_right {m k : ℕ} (p : ProbVec 2) (q1 : ProbVec m) (q2 : ProbVec k)
    (j : Fin k) : (splitBoth p q1 q2).1 ⟨m + j.1, by omega⟩ = p.1 1 * q2.1 j := by
  apply _root_.InformationTheory.splitBoth_right


/-- splitBoth with two uniform distributions gives uniform distribution. -/
theorem splitBoth_uniform_eq_uniform {m k : ℕ} (hm : 0 < m) (hk : 0 < k) :
    splitBoth (binaryDist ((m : ℝ) / (m + k))
        (div_nonneg (Nat.cast_nonneg m) (by positivity))
        (div_le_one_of_le₀ (by simp) (by positivity)))
      (uniformDist m hm) (uniformDist k hk) =
    uniformDist (m + k) (Nat.add_pos_left hm k) := by
  apply _root_.InformationTheory.splitBoth_uniform_eq_uniform

    -- `field_simp` closes the goal.

/-! ### F Infrastructure: Binary Distributions and Uniform Entropy

Moved from later in the file (originally lines 1457-1750) to avoid forward references.
These definitions and theorems are needed by `faddeev_splitBoth_uniform` below.
-/

private theorem one_div_le_one_of_posNat {m : ℕ} (hm : 0 < m) : (1 : ℝ) / m ≤ 1 := by
  have hm1 : (1 : ℝ) ≤ m := by
    exact_mod_cast (Nat.succ_le_iff.2 hm)
  simpa [one_div] using (inv_le_one_of_one_le₀ hm1)

private noncomputable def binaryOneDiv (m : ℕ) (hm : 0 < m) : ProbVec 2 :=
  binaryDist ((1 : ℝ) / m) (by positivity) (one_div_le_one_of_posNat hm)

@[simp] private theorem binaryOneDiv_apply_zero (m : ℕ) (hm : 0 < m) :
    (binaryOneDiv m hm).1 0 = (1 : ℝ) / m := by
  simp [binaryOneDiv, binaryDist]

@[simp] private theorem binaryOneDiv_apply_one (m : ℕ) (hm : 0 < m) :
    (binaryOneDiv m hm).1 1 = 1 - (1 : ℝ) / m := by
  simp [binaryOneDiv, binaryDist]

@[simp] private theorem binaryOneDiv_congr (m : ℕ) (hm hm' : 0 < m) :
    binaryOneDiv m hm = binaryOneDiv m hm' := by
  apply Subtype.ext
  funext i
  fin_cases i <;> simp [binaryOneDiv, binaryDist]







private noncomputable def F (E : FaddeevEntropy) (n : ℕ) (hn : 0 < n) : ℝ :=
  E.H (uniformDist n hn)

@[simp] private theorem uniformDist_congr (n : ℕ) (hn hn' : 0 < n) :
    uniformDist n hn = uniformDist n hn' := by
  apply Subtype.ext
  funext i
  rfl











/-! ### Recursion for `F` coming from splitting `(1/m, (m-1)/m)` -/





/-! ### splitBoth: Strong Additivity for a Two-Way Split -/



/-! ### The main multiplicativity lemma `F(m*n) = F(m) + F(n)` -/

/-- **Special case: Entropy splitting for uniform distributions.**

For uniform distributions, the splitBoth chain rule takes the form:
H(uniform(m+k)) = H(binaryDist(m/(m+k))) + (m/(m+k))·H(uniform(m)) + (k/(m+k))·H(uniform(k))

This is precisely what's needed to prove ηE_rat_eq_ηSh. -/
theorem faddeev_splitBoth_uniform (E : FaddeevEntropy) {m k : ℕ} (hm : 0 < m) (hk : 0 < k) :
    let p := binaryDist ((m : ℝ) / (m + k))
        (div_nonneg (Nat.cast_nonneg m) (by positivity))
        (div_le_one_of_le₀ (by simp) (by positivity))
    E.H (uniformDist (m + k) (Nat.add_pos_left hm k)) =
      E.H p + ((m : ℝ) / (m + k)) * E.H (uniformDist m hm) +
             ((k : ℝ) / (m + k)) * E.H (uniformDist k hk) := by
  apply _root_.InformationTheory.faddeev_splitBoth_uniform E.toStandalone


/-- **Binary entropy formula**: For 0 < m < n, the binary entropy η(m/n) can be expressed
    in terms of F values via the splitting lemma.

    η(m/n) = F(n) - (m/n)·F(m) - ((n-m)/n)·F(n-m)

    This is the key formula connecting binary entropy to uniform entropy (F values). -/
theorem faddeev_binary_entropy_formula (E : FaddeevEntropy) (m n : ℕ)
    (hm_pos : 0 < m) (hn_pos : 0 < n) (hm_lt : m < n) :
    E.H (binaryDist ((m : ℝ) / n)
      (div_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n))
      (div_le_one_of_le₀ (by exact_mod_cast (le_of_lt hm_lt)) (Nat.cast_nonneg n))) =
    F E n hn_pos - (m / n) * F E m hm_pos - ((n - m) / n) * F E (n - m) (Nat.sub_pos_of_lt hm_lt) := by
  apply _root_.InformationTheory.faddeev_binary_entropy_formula E.toStandalone; assumption




theorem faddeev_splitBoth (E : FaddeevEntropy) {m k : ℕ}
    (p : ProbVec 2) (q1 : ProbVec (m + 2)) (q2 : ProbVec (k + 2))
    (hp0 : 0 < p.1 0) (hp1 : 0 < p.1 1)
    (hq1 : 0 < q1.1 0 + q1.1 1) (hq2 : 0 < q2.1 0 + q2.1 1) :
    E.H (splitBoth p q1 q2) = E.H p + p.1 0 * E.H q1 + p.1 1 * E.H q2 := by
  apply _root_.InformationTheory.faddeev_splitBoth E.toStandalone <;> assumption


/-- For n = 1, the point mass equals the uniform distribution -/
theorem pointMass_eq_uniformDist_one : pointMass (0 : Fin 1) = uniformDist 1 (by norm_num) := by
  apply _root_.InformationTheory.pointMass_eq_uniformDist_one


/-- For a Faddeev entropy, H(point mass) = 0.
    Proof structure:
    - For n = 1: pointMass 0 = uniformDist 1, so H = F(1) = 0
    - For n = 2: pointMass 0 = (1, 0), use faddeev_H_one_zero
    - For n ≥ 3: By recursivity, H(pointMass 0 on n) = H(pointMass 0 on n-1) + H(1, 0)
                 By induction, this reduces to (n-1) * H(1, 0) = 0
    - For general i: By symmetry, H(pointMass i) = H(pointMass 0) -/
theorem faddeev_pointMass_eq_zero (E : FaddeevEntropy) {n : ℕ} (i : Fin n) :
    E.H (pointMass i) = 0 := by
  apply _root_.InformationTheory.faddeev_pointMass_eq_zero E.toStandalone


/-- The swap permutation (0 ↔ 2) on Fin 3 -/
def swap02 : Equiv.Perm (Fin 3) :=
  Equiv.swap 0 2

/-- Helper: ternaryDist (1/2) (1/4) (1/4) -/
noncomputable def ternary_half_quarter_quarter : ProbVec 3 :=
  ternaryDist (1/2) (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Helper: ternaryDist (1/4) (1/4) (1/2) -/
noncomputable def ternary_quarter_quarter_half : ProbVec 3 :=
  ternaryDist (1/4) (1/4) (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Permuting (1/2, 1/4, 1/4) by swap02 gives (1/4, 1/4, 1/2) -/
theorem permute_swap02_ternary :
    permute swap02 ternary_half_quarter_quarter = ternary_quarter_quarter_half := by
  apply _root_.InformationTheory.permute_swap02_ternary


/-- H(1/4, 1/4, 1/2) = 3/2 for any Faddeev entropy.
    Proof: Apply recursivity to group (1/4, 1/4) → 1/2
    H(1/4, 1/4, 1/2) = H(1/2, 1/2) + (1/2) * H(1/2, 1/2) = 1 + 1/2 = 3/2 -/
theorem faddeev_ternary_quarter_quarter_half (E : FaddeevEntropy) :
    E.H ternary_quarter_quarter_half = 3/2 := by
  apply _root_.InformationTheory.faddeev_ternary_quarter_quarter_half E.toStandalone


/-- Concrete case: F(4) = 2 = F(2) + F(2).
    This demonstrates the pairing technique used in multiplicativity. -/
theorem faddeev_F4_eq_2 (E : FaddeevEntropy) :
    E.H (uniformDist 4 (by norm_num : 0 < 4)) = 2 := by
  apply _root_.InformationTheory.faddeev_F4_eq_2 E.toStandalone


/-
## Faddeev 1956: multiplicativity on uniforms

The original paper defines `F(n) := H(1/n, …, 1/n)` and proves `F(mn) = F(m) + F(n)`.
We follow the paper’s proof pattern, but package it as a Lean lemma for later use.
-/

section UniformMultiplicativity

open scoped Topology

set_option maxHeartbeats 1000000 in
theorem faddeev_F_mul (E : FaddeevEntropy) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    F E (m * n) (Nat.mul_pos hm hn) = F E m hm + F E n hn := by
  apply _root_.InformationTheory.faddeev_F_mul E.toStandalone


end UniformMultiplicativity

/-! ## Power Laws from Multiplicativity -/

section PowerLaws

/-- F(n^k) = k * F(n) for any Faddeev entropy.
    This follows by induction from the multiplicativity `faddeev_F_mul`. -/
theorem faddeev_F_pow (E : FaddeevEntropy) {n : ℕ} (hn : 0 < n) (k : ℕ) :
    E.H (uniformDist (n ^ k) (by positivity : 0 < n ^ k)) = (k : ℝ) * E.H (uniformDist n hn) := by
  apply _root_.InformationTheory.faddeev_F_pow E.toStandalone


/-- F(2^k) = k for any Faddeev entropy.
    This combines the power law with the normalization F(2) = 1. -/
theorem faddeev_F_pow2 (E : FaddeevEntropy) (k : ℕ) :
    E.H (uniformDist (2 ^ k) (by positivity : 0 < 2 ^ k)) = (k : ℝ) := by
  apply _root_.InformationTheory.faddeev_F_pow2 E.toStandalone


end PowerLaws

/-! ## Continuity and Vanishing Increments

Binary continuity gives H(1/n, 1-1/n) → 0. The grouping identity then gives
F(n)/n → 0 by a weighted Cesàro argument, and hence F(n) - F(n-1) → 0.
These limits are proved before identifying F with a logarithm; they do not
assume monotonicity or a growth estimate for F.
-/

section ContinuityProof

/-- Binary entropy at 0: H(0, 1) = H(1, 0) = 0.
    This is the same as `faddeev_H_one_zero` with symmetry. -/
theorem binaryEntropy_at_zero (E : FaddeevEntropy) :
    E.H (binaryDist 0 (by norm_num) (by norm_num)) = 0 := by
  apply _root_.InformationTheory.binaryEntropy_at_zero E.toStandalone


/-- The recursion formula for binary entropy:
    φ(1/n) = F(n) - (n-1)/n * F(n-1)

    This is derived from `F_succ_eq`. -/
theorem binary_entropy_recursion (E : FaddeevEntropy) (n : ℕ) (hn : 1 < n) :
    E.H (binaryOneDiv n (Nat.lt_trans Nat.zero_lt_one hn)) =
    F E n (Nat.lt_trans Nat.zero_lt_one hn) -
      (1 - (1 : ℝ) / n) * F E (n - 1) (Nat.sub_pos_of_lt hn) := by
  apply _root_.InformationTheory.binary_entropy_recursion E.toStandalone; assumption


/-- For the sequence n_k = 3^k + 1, the position 1/n_k approaches 0. -/
theorem inv_three_pow_succ_tendsto_zero :
    Filter.Tendsto (fun k : ℕ => (1 : ℝ) / (3 ^ k + 1)) Filter.atTop (nhds 0) := by
  apply _root_.InformationTheory.inv_three_pow_succ_tendsto_zero


/-- F(3^k) = k * F(3) by the power law. -/
theorem F_three_pow (E : FaddeevEntropy) (k : ℕ) :
    F E (3 ^ k) (by positivity : 0 < 3 ^ k) =
    (k : ℝ) * F E 3 (by norm_num : 0 < 3) :=
  faddeev_F_pow E (by norm_num : 0 < 3) k

/-! ### Faddeev's Lemma 7: Key Convergence Results

From the recursion η_n = F(n) - (n-1)/n · F(n-1), Faddeev derives:
1. η_n → 0 (from continuity of binary entropy at 0)
2. μ_n = F(n)/n → 0 (via Cesàro mean argument)
3. λ_n = F(n) - F(n-1) → 0 (combines 1 and 2)

These results are crucial for proving uniqueness. -/

/-- η_n = H(1/n, (n-1)/n) = F(n) - (n-1)/n · F(n-1).
    This is the binary entropy at probability 1/n. -/
noncomputable def η (E : FaddeevEntropy) (n : ℕ) (hn : 1 < n) : ℝ :=
  E.H (binaryOneDiv n (Nat.lt_trans Nat.zero_lt_one hn))

/-- μ_n = F(n)/n, the normalized entropy of the uniform distribution. -/
noncomputable def μ (E : FaddeevEntropy) (n : ℕ) (hn : 0 < n) : ℝ :=
  F E n hn / n

/-- λ_n = F(n) - F(n-1), the entropy increment. -/
noncomputable def entropyIncrement (E : FaddeevEntropy) (n : ℕ) (hn : 1 < n) : ℝ :=
  F E n (Nat.lt_trans Nat.zero_lt_one hn) - F E (n - 1) (Nat.sub_pos_of_lt hn)

/-- **Faddeev's Lemma 7, Part 1**: η_n → 0 as n → ∞.
    This follows from continuity of H(p, 1-p) at p = 0.

    Proof: η_n = H(1/n, (n-1)/n), and as n → ∞, 1/n → 0, so by
    continuity of binary entropy, H(1/n, (n-1)/n) → H(0, 1) = 0.

    See `binary_entropy_tendsto_zero` for an equivalent formulation. -/
theorem faddeev_eta_tendsto_zero (E : FaddeevEntropy) :
    Filter.Tendsto (fun n : ℕ => η E (n + 2) (by omega : 1 < n + 2))
      Filter.atTop (nhds 0) := by
  apply _root_.InformationTheory.faddeev_eta_tendsto_zero E.toStandalone


/-- The key recursion: n·η_n = n·F(n) - (n-1)·F(n-1).
    Rearranging: n·F(n) = (n-1)·F(n-1) + n·η_n.

    Proof: From η_n = F(n) - (n-1)/n · F(n-1), multiply by n:
    n·η_n = n·F(n) - (n-1)·F(n-1). -/
theorem n_eta_eq (E : FaddeevEntropy) (n : ℕ) (hn : 1 < n) :
    (n : ℝ) * η E n hn = (n : ℝ) * F E n (Nat.lt_trans Nat.zero_lt_one hn) -
      ((n : ℝ) - 1) * F E (n - 1) (Nat.sub_pos_of_lt hn) := by
  apply _root_.InformationTheory.n_eta_eq E.toStandalone; assumption


/-- **Telescoping recursion**: n·F(n) = (n-1)·F(n-1) + n·η_n for n ≥ 2.

    This is a rearrangement of n_eta_eq. -/
theorem nF_recursion (E : FaddeevEntropy) (n : ℕ) (hn : 1 < n) :
    (n : ℝ) * F E n (Nat.lt_trans Nat.zero_lt_one hn) =
    ((n : ℝ) - 1) * F E (n - 1) (Nat.sub_pos_of_lt hn) + (n : ℝ) * η E n hn := by
  apply _root_.InformationTheory.nF_recursion E.toStandalone; assumption


/-- Base case: 2·F(2) = 2·η_2.

    Since F(1) = 0, we have 2·F(2) = 1·F(1) + 2·η_2 = 2·η_2. -/
theorem nF_base (E : FaddeevEntropy) :
    (2 : ℝ) * F E 2 (by norm_num : 0 < 2) = (2 : ℝ) * η E 2 (by norm_num : 1 < 2) := by
  apply _root_.InformationTheory.nF_base E.toStandalone


/-- Extended η function: returns 0 for k ≤ 1, otherwise η E k.
    This makes it easier to sum over intervals without proof obligations. -/
noncomputable def ηExt (E : FaddeevEntropy) (k : ℕ) : ℝ :=
  if hk : 1 < k then η E k hk else 0

/-- ηExt agrees with η when k > 1. -/
theorem ηExt_eq (E : FaddeevEntropy) (k : ℕ) (hk : 1 < k) :
    ηExt E k = η E k hk := by
  apply _root_.InformationTheory.ηExt_eq E.toStandalone; assumption


/-- **Telescoping sum identity**: n·F(n) = Σ_{k=2}^n k·ηExt(k) for n ≥ 2.

    Proof by strong induction using nF_recursion and nF_base. -/
theorem telescoping_nF_sum (E : FaddeevEntropy) (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) * F E n (Nat.lt_of_lt_of_le Nat.zero_lt_two hn) =
    ∑ k ∈ Finset.Icc 2 n, (k : ℝ) * ηExt E k := by
  apply _root_.InformationTheory.telescoping_nF_sum E.toStandalone; assumption


/-- **Faddeev's Lemma 7, Part 2**: μ_n = F(n)/n → 0 as n → ∞.

    The proof uses a bound from the telescoping sum: |μ_n| ≤ Σ|η_k|/n.
    Since η_k → 0, the Cesàro-type argument shows the weighted average → 0.

    Key insight: From telescoping, (n+1)·F(n+1) = Σ_{k=2}^{n+1} k·η_k.
    We have |Σ k·η_k| ≤ (n+1)·Σ|η_k|, so |μ(n+1)| ≤ Σ|η_k|/(n+1) → 0.

    Mathematical proof is verified; Lean formalization requires careful handling
    of type coercions between ℕ and ℝ. -/
theorem faddeev_mu_tendsto_zero (E : FaddeevEntropy) :
    Filter.Tendsto (fun n : ℕ => μ E (n + 1) (Nat.succ_pos n))
      Filter.atTop (nhds 0) := by
  apply _root_.InformationTheory.faddeev_mu_tendsto_zero E.toStandalone


/-- Key algebraic identity: entropyIncrement(n) = η(n) - F(n-1)/n.

    From binary_entropy_recursion: η_n = F(n) - (1-1/n)·F(n-1)
    Rearranging: F(n) = η_n + (n-1)/n · F(n-1)
    So: λ_n = F(n) - F(n-1) = η_n - F(n-1)/n -/
theorem entropyIncrement_eq_eta_sub_mu (E : FaddeevEntropy) (n : ℕ) (hn : 1 < n) :
    entropyIncrement E n hn = η E n hn - F E (n - 1) (Nat.sub_pos_of_lt hn) / n := by
  apply _root_.InformationTheory.entropyIncrement_eq_eta_sub_mu E.toStandalone; assumption


/-- **Faddeev's Lemma 7, Part 3**: λ_n = F(n) - F(n-1) → 0 as n → ∞.

    This follows from the algebraic identity: λ_n = η_n - F(n-1)/n.
    Since η_n → 0 (Part 1) and μ_n = F(n)/n → 0 (Part 2), we have:
    - F(n-1)/n = μ_{n-1} · (n-1)/n → 0 · 1 = 0
    - Therefore λ_n = η_n - F(n-1)/n → 0 - 0 = 0

    The proof uses Filter.Tendsto arithmetic (subtraction and bounded multiplication). -/
theorem faddeev_lambda_tendsto_zero (E : FaddeevEntropy) :
    Filter.Tendsto (fun n : ℕ => entropyIncrement E (n + 2) (by omega : 1 < n + 2))
      Filter.atTop (nhds 0) := by
  apply _root_.InformationTheory.faddeev_lambda_tendsto_zero E.toStandalone


/-! ### Faddeev's Lemmas 8-9: Uniqueness WITHOUT Monotonicity

This is the correct approach to break the circular dependency!

**The Hinge Lemma**: If F satisfies multiplicativity (M) and the limit conditions (L7),
then F(n) = c·log(n) for a constant c.

**Strategy** (following Faddeev's original paper):
1. Define c_p := F(p)/log(p) for each prime p
2. **Lemma 8**: The set {c_p | p prime} has a maximum and a minimum
3. **Lemma 9**: All c_p are equal (to c_2)
4. Therefore F(n) = c·log(n), and by normalization F(2)=1, we get F(n)=log₂(n)
5. Monotonicity follows trivially since log is monotone

**Key Innovation**: Uses only λ_n → 0 (which we derived from continuity), NOT monotonicity.
This breaks the circle: we prove F = log₂ first, THEN get monotonicity for free.

**Lemma 8 Proof Sketch**:
Assume {c_p} has no maximum. Build increasing sequence p₁ < p₂ < ... with c_{p₁} < c_{p₂} < ...
For p_i - 1 = ∏ q_j^{α_j}, all q_j < p_i, so c_{q_j} < c_{p_i}.
Write exact identity: λ_{p_i} = c_{p_i}(log p_i - log(p_i-1)) + Σ_j α_j(c_{p_i} - c_{q_j})log q_j
Since 2 | (p_i - 1), the sum ≥ (c_{p_i} - c_2)log 2 > 0 (uniform lower bound).
But λ_{p_i} → 0 by Lemma 7, contradiction!

**Lemma 9 Proof Sketch**:
Similar argument on p^m - 1 shows c_{p_max} ≤ c_2 and c_{p_min} ≥ c_2.
Hence all c_p = c_2. -/

/-- The "slope coefficient" for a prime: c_p = F(p)/log(p).

    By multiplicativity, F is determined by its values on primes.
    Faddeev's strategy: prove all c_p are equal, hence F(n) = c·log(n). -/
noncomputable def c_prime (E : FaddeevEntropy) (p : ℕ) (hp : Nat.Prime p) : ℝ :=
  F E p (Nat.Prime.pos hp) / Real.log p

/-- Prime coefficients agree with the standalone coefficients under the adapter. -/
@[simp]
theorem c_prime_toStandalone (E : FaddeevEntropy) (p : ℕ) (hp : Nat.Prime p) :
    _root_.InformationTheory.c_prime E.toStandalone p hp = c_prime E p hp := rfl

/-! ### Helper Lemmas for Faddeev's Argument -/

/-- For odd primes p > 2, we have 2 | (p - 1).
    This is crucial for the uniform lower bound in Lemma 8. -/
theorem prime_odd_pred_even {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) : Even (p - 1) := by
  apply _root_.InformationTheory.prime_odd_pred_even <;> assumption


/-- For any n ≥ 2, log(n) > 0. -/
theorem log_pos_of_two_le {n : ℕ} (hn : 2 ≤ n) : 0 < Real.log n := by
  apply _root_.InformationTheory.log_pos_of_two_le; assumption


/-- c_p is well-defined: log(p) ≠ 0 for primes p. -/
theorem log_prime_ne_zero {p : ℕ} (hp : Nat.Prime p) : Real.log p ≠ 0 := by
  apply _root_.InformationTheory.log_prime_ne_zero; assumption


/-- Express F(p) in terms of c_p. -/
theorem F_prime_eq_c_times_log (E : FaddeevEntropy) {p : ℕ} (hp : Nat.Prime p) :
    F E p (Nat.Prime.pos hp) = c_prime E p hp * Real.log p := by
  apply _root_.InformationTheory.F_prime_eq_c_times_log E.toStandalone; assumption


/-- c_2 = 1/log(2) follows from F(2) = 1. -/
theorem c_prime_two (E : FaddeevEntropy) :
    c_prime E 2 Nat.prime_two = 1 / Real.log 2 := by
  apply _root_.InformationTheory.c_prime_two E.toStandalone


/-- For primes p ≥ 3, c_p is positive if F(p) > 0. -/
theorem c_prime_pos_of_F_pos (E : FaddeevEntropy) {p : ℕ} (hp : Nat.Prime p) (hFp : 0 < F E p (Nat.Prime.pos hp)) :
    0 < c_prime E p hp := by
  apply _root_.InformationTheory.c_prime_pos_of_F_pos E.toStandalone <;> assumption


/-- log 2 is positive and nonzero. -/
theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)

theorem log_two_ne_zero : Real.log 2 ≠ 0 := log_two_pos.ne'

/-- c_2 equals 1/log(2), which is well-defined and positive. -/
theorem c_prime_two_pos (E : FaddeevEntropy) : 0 < c_prime E 2 Nat.prime_two := by
  apply _root_.InformationTheory.c_prime_two_pos E.toStandalone


/-- If all c_p are equal to c_2, then F(n) = c_2 · log(n) for all n ≥ 1.

    This is the payoff of Lemma 9: once we know all c_p are equal,
    multiplicativity gives us F on all of ℕ. -/
theorem F_eq_c2_times_log_of_c_prime_const (E : FaddeevEntropy)
    (h_const : ∀ p : ℕ, ∀ hp : Nat.Prime p, c_prime E p hp = c_prime E 2 Nat.prime_two)
    {n : ℕ} (hn : 0 < n) :
    F E n hn = c_prime E 2 Nat.prime_two * Real.log n := by
  apply _root_.InformationTheory.F_eq_c2_times_log_of_c_prime_const E.toStandalone; assumption


/-- F(2^a * m) = a + F(m) for any m > 0. This uses multiplicativity and F(2^a) = a. -/
theorem F_two_pow_mul (E : FaddeevEntropy) (a : ℕ) {m : ℕ} (hm : 0 < m) :
    F E (2 ^ a * m) (by positivity : 0 < 2 ^ a * m) = a + F E m hm := by
  apply _root_.InformationTheory.F_two_pow_mul E.toStandalone


/-- For odd n > 0, if c ≥ c_q for all odd primes q | n, then F(n) ≤ c · log(n).
    Proof by strong induction using multiplicativity.

    This is the key technical lemma for lambda_prime_lower_bound.
    The proof uses strong induction: factor out the smallest prime q from n,
    write n = q^b * m, and apply IH to m. -/
theorem F_odd_upper_bound (E : FaddeevEntropy) {n : ℕ} (hn : 0 < n) (h_odd : Odd n)
    (c : ℝ) (h_dom : ∀ q : ℕ, ∀ hq : q.Prime, q ∣ n → Odd q → c_prime E q hq ≤ c) :
    F E n hn ≤ c * Real.log n := by
  apply _root_.InformationTheory.F_odd_upper_bound E.toStandalone <;> assumption


/-- **F_odd_lower_bound**: Symmetric to F_odd_upper_bound.
    If c ≤ c_prime E q hq for all odd primes q dividing n, then c * log(n) ≤ F(n).

    This is the key lemma for the symmetric argument in Step 4 of faddeev_c_prime_all_equal. -/
theorem F_odd_lower_bound (E : FaddeevEntropy) {n : ℕ} (hn : 0 < n) (h_odd : Odd n)
    (c : ℝ) (h_dom : ∀ q : ℕ, ∀ hq : q.Prime, q ∣ n → Odd q → c ≤ c_prime E q hq) :
    c * Real.log n ≤ F E n hn := by
  apply _root_.InformationTheory.F_odd_lower_bound E.toStandalone <;> assumption


/-- For an odd prime p whose coefficient dominates those of all prime divisors
    of p-1, the entropy increment is at least (c_p - c_2) * log(2).

    Write p-1 = 2^a * m with m odd and a ≥ 1. Multiplicativity gives
    F(p-1) = a + F(m), while coefficient domination bounds F(m) by
    c_p * log(m). The compulsory factor 2 supplies the stated margin. -/
theorem lambda_prime_lower_bound (E : FaddeevEntropy) {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2)
    (h_dom : ∀ q : ℕ, ∀ hq : Nat.Prime q, q ∣ (p - 1) → c_prime E q hq ≤ c_prime E p hp) :
    entropyIncrement E p hp.one_lt ≥ (c_prime E p hp - c_prime E 2 Nat.prime_two) * Real.log 2 := by
  apply _root_.InformationTheory.lambda_prime_lower_bound E.toStandalone <;> assumption


/-! ### Record-Holder Primes for Lemma 8

A "record-holder" prime is one where c_p strictly exceeds all c_q for smaller primes q.
Key property: for record-holders p ≠ 2, the domination hypothesis of `lambda_prime_lower_bound` holds.
If {c_p} has no maximum, there are infinitely many record-holders. -/

/-- A prime p is a "record-holder" if c_p > c_q for all primes q < p.
    For such primes, any prime divisor of p-1 satisfies the domination hypothesis. -/
def isRecordHolder (E : FaddeevEntropy) (p : ℕ) (hp : Nat.Prime p) : Prop :=
  ∀ q : ℕ, ∀ hq : Nat.Prime q, q < p → c_prime E q hq < c_prime E p hp

/-- 2 is always a record-holder (vacuously: no smaller primes). -/
theorem isRecordHolder_two (E : FaddeevEntropy) :
    isRecordHolder E 2 Nat.prime_two := by
  apply _root_.InformationTheory.isRecordHolder_two E.toStandalone


/-- For a record-holder p ≠ 2, any prime q dividing p-1 satisfies c_q < c_p.
    This is the key property connecting record-holders to lambda_prime_lower_bound. -/
theorem recordHolder_dominates_divisors (E : FaddeevEntropy) {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2)
    (h_rec : isRecordHolder E p hp) :
    ∀ q : ℕ, ∀ hq : Nat.Prime q, q ∣ (p - 1) → c_prime E q hq ≤ c_prime E p hp := by
  apply _root_.InformationTheory.recordHolder_dominates_divisors E.toStandalone <;> assumption


/-- If {c_p} has no maximum, then for any prime p, there exists a record-holder q > p.

    Proof sketch: Build sequence of record-holders r₁ = 2 < r₂ < r₃ < ... by well-ordering.
    Each rₙ is a record-holder (c_{rₙ} > c_q for all primes q < rₙ).
    Since {c_p} has no max, this sequence is infinite and unbounded.

    Key steps:
    1. For any record-holder r, if c_r were maximal, h_no_max would be violated.
       So there exists a prime q > r with c_q > c_r.
    2. Take r' = min{q : q > r, q.Prime, c_q > c_r}. This r' is a record-holder because:
       - For primes q < r: c_q < c_r (by r being a record-holder) < c_{r'}
       - For primes r ≤ q < r': c_q ≤ c_r (by minimality of r') < c_{r'}
    3. Starting from r₁ = 2 (a record-holder vacuously), iterate to build an infinite
       strictly increasing sequence of record-holders.
    4. Since rₙ₊₁ > rₙ for all n, we have rₙ → ∞, so eventually rₙ > p. -/
theorem exists_recordHolder_gt (E : FaddeevEntropy)
    (h_no_max : ∀ p : ℕ, ∀ hp : Nat.Prime p, ∃ q : ℕ, ∃ hq : Nat.Prime q, c_prime E p hp < c_prime E q hq)
    (p : ℕ) (hp : Nat.Prime p) :
    ∃ q : ℕ, ∃ hq : Nat.Prime q, p < q ∧ isRecordHolder E q hq := by
  apply _root_.InformationTheory.exists_recordHolder_gt E.toStandalone <;> assumption



/-- **Faddeev's Lemma 8**: The set {c_p | p prime} has a maximum.

    Proof by contradiction:
    1. If no max exists, build sequence p₁ < p₂ < ... where c_{p_i} > c_q for all primes q < p_i
    2. For each p_i > 2: λ_{p_i} ≥ (c_{p_i} - c_2) · log(2) ≥ δ · log(2) > 0 (uniform bound)
    3. But λ_n → 0 (faddeev_lambda_tendsto_zero), contradiction!

    This proves {c_p} has a maximum WITHOUT using monotonicity of F! -/
theorem faddeev_c_prime_has_max (E : FaddeevEntropy) :
    ∃ p : ℕ, ∃ hp : Nat.Prime p, ∀ q : ℕ, ∀ hq : Nat.Prime q,
      c_prime E q hq ≤ c_prime E p hp := by
  apply _root_.InformationTheory.faddeev_c_prime_has_max E.toStandalone


/-! ### Symmetric Infrastructure for Minimum (Step 4) -/

/-- A prime p is a "downward record-holder" if c_p < c_q for all primes q < p.
    This is symmetric to isRecordHolder (which uses > instead of <). -/
def isDownwardRecordHolder (E : FaddeevEntropy) (p : ℕ) (hp : Nat.Prime p) : Prop :=
  ∀ q : ℕ, ∀ hq : Nat.Prime q, q < p → c_prime E q hq > c_prime E p hp

/-- For a downward record-holder p ≠ 2, any prime q dividing p-1 satisfies c_p ≤ c_q.
    Symmetric to recordHolder_dominates_divisors. -/
theorem downwardRecordHolder_dominated_by_divisors (E : FaddeevEntropy) {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2)
    (h_rec : isDownwardRecordHolder E p hp) :
    ∀ q : ℕ, ∀ hq : Nat.Prime q, q ∣ (p - 1) → c_prime E p hp ≤ c_prime E q hq := by
  apply _root_.InformationTheory.downwardRecordHolder_dominated_by_divisors E.toStandalone <;> assumption


/-- If {c_p} has no minimum, then for any prime p, there exists a downward record-holder q > p.
    Symmetric to exists_recordHolder_gt. -/
theorem exists_downwardRecordHolder_gt (E : FaddeevEntropy)
    (h_no_min : ∀ p : ℕ, ∀ hp : Nat.Prime p, ∃ q : ℕ, ∃ hq : Nat.Prime q, c_prime E q hq < c_prime E p hp)
    (p : ℕ) (hp : Nat.Prime p) :
    ∃ q : ℕ, ∃ hq : Nat.Prime q, p < q ∧ isDownwardRecordHolder E q hq := by
  apply _root_.InformationTheory.exists_downwardRecordHolder_gt E.toStandalone <;> assumption


/-- **lambda_prime_upper_bound**: Symmetric to lambda_prime_lower_bound.
    For a downward record-holder p ≠ 2 (where c_p ≤ c_q for all primes q | (p-1)),
    we have λ_p ≤ (c_p - c_2) * log(2) + c_p * log(p/(p-1)).

    A fixed gap below c_2 supplies a negative margin. The second term is
    nonpositive when c_p ≤ 0; otherwise it becomes small for large p. -/
theorem lambda_prime_upper_bound (E : FaddeevEntropy) {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2)
    (h_dom : ∀ q : ℕ, ∀ hq : Nat.Prime q, q ∣ (p - 1) → c_prime E p hp ≤ c_prime E q hq) :
    entropyIncrement E p hp.one_lt ≤ (c_prime E p hp - c_prime E 2 Nat.prime_two) * Real.log 2 +
        c_prime E p hp * Real.log (p / (p - 1)) := by
  apply _root_.InformationTheory.lambda_prime_upper_bound E.toStandalone <;> assumption


/-- **Lemma 8'**: The set {c_p | p prime} has a minimum.

    This is proven independently of Lemma 9 (all c_p equal), using the λ → 0 argument.

    Proof by contradiction:
    1. If no minimum exists, find arbitrarily large downward record-holder primes,
       whose coefficients stay below one fixed coefficient smaller than c_2.
    2. For such p > 2, λ_p ≤ (c_p - c_2)·log(2) + correction.
       The correction tends to zero, leaving a fixed negative margin.
    3. But λ_n → 0, so |λ_n| < ε for large n. Contradiction! -/
theorem faddeev_c_prime_has_min_aux (E : FaddeevEntropy) :
    ∃ p : ℕ, ∃ hp : Nat.Prime p, ∀ q : ℕ, ∀ hq : Nat.Prime q,
      c_prime E p hp ≤ c_prime E q hq := by
  apply _root_.InformationTheory.faddeev_c_prime_has_min_aux E.toStandalone


/-- **Faddeev's Lemma 9**: All c_p are equal.

    The standalone proof compares extremal prime coefficients with c_2.
    For an odd prime p, p^k - 1 is even: a single factor of 2 gives a fixed
    discrepancy if c_p differs from c_2, contradicting vanishing increments.
    The adapter transports that proof without strengthening the axioms. -/
theorem faddeev_c_prime_all_equal (E : FaddeevEntropy) :
    ∀ p q : ℕ, ∀ hp : Nat.Prime p, ∀ hq : Nat.Prime q,
      c_prime E p hp = c_prime E q hq := by
  apply _root_.InformationTheory.faddeev_c_prime_all_equal E.toStandalone



/-- **Faddeev's Lemma 8'**: The set {c_p | p prime} has a minimum.

    Note: This follows directly from Lemma 9 (all c_p equal). -/
theorem faddeev_c_prime_has_min (E : FaddeevEntropy) :
    ∃ p : ℕ, ∃ hp : Nat.Prime p, ∀ q : ℕ, ∀ hq : Nat.Prime q,
      c_prime E p hp ≤ c_prime E q hq := by
  apply _root_.InformationTheory.faddeev_c_prime_has_min E.toStandalone


/-! ### Deriving F(n) = log₂(n) from Lemmas 8-9 -/

/-- F(n) = log₂(n) for all n ≥ 1.

    Proof: By Lemma 9, all c_p = c_2 = 1/log(2).
    By the prime factorization theorem, F(n) = c_2 · log(n) = log(n)/log(2) = log₂(n).

    This derives F = log₂ without assuming monotonicity. -/
theorem faddeev_F_eq_log2 (E : FaddeevEntropy) {n : ℕ} (hn : 0 < n) :
    F E n hn = Real.log n / Real.log 2 := by
  apply _root_.InformationTheory.faddeev_F_eq_log2 E.toStandalone


/-- **COROLLARY**: Monotonicity follows trivially!

    Once we have F(n) = log₂(n), monotonicity is immediate since log is monotone.
    This completes the circle-breaking: prove F = log₂ first, THEN get monotonicity. -/
theorem faddeev_F_monotone (E : FaddeevEntropy) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≤ n) :
    F E m hm ≤ F E n hn := by
  apply _root_.InformationTheory.faddeev_F_monotone E.toStandalone; assumption


end ContinuityProof

/-! ## The Error Function and Convergence Properties

The error function Err(n) = F(n) - log₂(n) measures deviation from Shannon entropy.
The result `faddeev_F_eq_log2` shows Err ≡ 0 downstream of Lemma 9.

This section contains supporting infrastructure for analyzing convergence. -/

section Sandwich

/-! ### Direct Proof of F = log₂ Using Convergence

The key insight: we can prove F(n) = log₂(n) directly from the convergence results
without needing monotonicity. Then non-negativity follows trivially.

**Mathematical Argument:**
1. Define Err(n) = F(n) - log₂(n) as the "deviation from Shannon entropy".
2. By multiplicativity: Err(n) = Σ_{p|n} v_p(n) · ε_p where ε_p = F(p) - log₂(p).
3. We know ε_2 = 0 (since F(2) = 1 = log₂(2)).
4. From λ_n → 0 and log₂(n/(n-1)) → 0, we get Err(n) - Err(n-1) → 0.
5. For the sequence n = p^k (prime power):
   - λ_{p^k} = F(p^k) - F(p^k - 1) = k·F(p) - F(p^k - 1)
   - For this to go to 0, the growth of k·ε_p must be compensated by F(p^k - 1)
6. The only consistent solution across all primes is ε_p = 0 for all p.
7. Therefore F(n) = log₂(n) ≥ 0.

This avoids the circularity of needing monotonicity for the sandwich argument. -/

/-- The error function: deviation of F from log₂. -/
noncomputable def Err (E : FaddeevEntropy) (n : ℕ) (hn : 0 < n) : ℝ :=
  F E n hn - Real.log n / Real.log 2

/-- `Err` does not depend on the proof argument `hn : 0 < n`. -/
theorem Err_congr (E : FaddeevEntropy) {n : ℕ} (hn hn' : 0 < n) :
    Err E n hn = Err E n hn' := by
  apply _root_.InformationTheory.Err_congr E.toStandalone


/-- Error at powers of 2 is zero. -/
theorem Err_pow2_eq_zero (E : FaddeevEntropy) (k : ℕ) :
    Err E (2 ^ k) (by positivity : 0 < 2 ^ k) = 0 := by
  apply _root_.InformationTheory.Err_pow2_eq_zero E.toStandalone


/-- Consequence of λ_n → 0: the error changes vanishingly.
    Since λ_n = F(n) - F(n-1) → 0 and log₂(n/(n-1)) → 0, we have
    Err(n) - Err(n-1) = [F(n) - F(n-1)] - [log₂(n) - log₂(n-1)] → 0. -/
theorem Err_diff_tendsto_zero (E : FaddeevEntropy) :
    Filter.Tendsto (fun n : ℕ => Err E (n + 2) (by omega) - Err E (n + 1) (by omega))
      Filter.atTop (nhds 0) := by
  apply _root_.InformationTheory.Err_diff_tendsto_zero E.toStandalone




/-- Err at 2^k + 1 converges to 0.
    From Err(n+2) - Err(n+1) → 0 and Err(2^k) = 0, we get Err(2^k + 1) → 0. -/
theorem Err_pow2_succ_tendsto_zero (E : FaddeevEntropy) :
    Filter.Tendsto (fun k : ℕ => Err E (2 ^ k + 1) (by positivity))
      Filter.atTop (nhds 0) := by
  apply _root_.InformationTheory.Err_pow2_succ_tendsto_zero E.toStandalone




/-- Helper: 0 < 2^(k+1) - 1 for all k ∈ ℕ -/
private theorem pow2_pred_pos (k : ℕ) : 0 < 2 ^ (k + 1) - 1 := by
  have h : 2 ^ (k + 1) ≥ 2 := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (Nat.le_add_left 1 k)
  omega

/-- Err at 2^k - 1 converges to 0 for k ≥ 1.
    From Err(n+2) - Err(n+1) → 0 and Err(2^k) = 0, we get Err(2^k - 1) → 0. -/
theorem Err_pow2_pred_tendsto_zero (E : FaddeevEntropy) :
    Filter.Tendsto (fun k : ℕ => Err E (2 ^ (k + 1) - 1) (pow2_pred_pos k))
      Filter.atTop (nhds 0) := by
  apply _root_.InformationTheory.Err_pow2_pred_tendsto_zero E.toStandalone


/-- Alias for `faddeev_F_eq_log2`. -/
theorem faddeev_F_eq_log2' (E : FaddeevEntropy) {n : ℕ} (hn : 0 < n) :
    E.H (uniformDist n hn) = Real.log n / Real.log 2 :=
  faddeev_F_eq_log2 E hn

/-- **Key uniqueness step**: From F = log₂, we have Err ≡ 0.

    This follows directly from the definition Err(n) = F(n) - log₂(n)
    and the uniqueness theorem faddeev_F_eq_log2'. -/
theorem faddeev_Err_eq_zero (E : FaddeevEntropy) {n : ℕ} (hn : 0 < n) :
    Err E n hn = 0 := by
  apply _root_.InformationTheory.faddeev_Err_eq_zero E.toStandalone


/-- F(n) = log₂(n) implies F(n) ≥ 0 for n ≥ 1. -/
theorem faddeev_F_nonneg (E : FaddeevEntropy) {n : ℕ} (hn : 0 < n) :
    0 ≤ E.H (uniformDist n hn) := by
  apply _root_.InformationTheory.faddeev_F_nonneg E.toStandalone


end Sandwich

/-! ## Full Uniqueness: E.H = shannonEntropyNormalized

This section states and proves the full uniqueness theorem downstream of the
uniform-distribution result: any Faddeev entropy equals Shannon entropy on all
distributions, not just uniform ones.

The argument:
1. Define binary entropy functions ηE and ηSh
2. Prove equality on rationals m/n via the splitting lemma
3. Extend to all of [0,1] via continuity
4. Lift to all ProbVec n by induction using recursivity
-/

section FullUniqueness

/-- The binary entropy function for a Faddeev entropy. -/
noncomputable def ηE (E : FaddeevEntropy) : Set.Icc (0 : ℝ) 1 → ℝ :=
  fun x => E.H (binaryDist x.1 x.2.1 x.2.2)

/-- The binary Shannon entropy function. -/
noncomputable def ηSh : Set.Icc (0 : ℝ) 1 → ℝ :=
  fun x => shannonEntropyNormalized (binaryDist x.1 x.2.1 x.2.2)

/-- ηE is continuous (this is Faddeev's axiom F1). -/
theorem continuous_ηE (E : FaddeevEntropy) : Continuous (ηE E) :=
  E.continuous_binary

/-- ηSh is continuous (from continuity of negMulLog). -/
theorem continuous_ηSh : Continuous ηSh := by
  apply _root_.InformationTheory.continuous_ηSh


/-- Key algebraic identity: For m ≤ n with n > 0, the binary entropy at m/n can be
    computed from F(n), F(m), F(n-m) via the splitting lemma.

    η(m/n) = F(n) - (m/n)·F(m) - ((n-m)/n)·F(n-m)

    Since F(k) = log₂(k), this equals the Shannon binary entropy. -/
theorem ηE_rat_eq_ηSh (E : FaddeevEntropy) (m n : ℕ) (hn : 0 < n) (hm : m ≤ n) :
    ηE E ⟨(m : ℝ) / n, by
      constructor
      · exact div_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n)
      · exact div_le_one_of_le₀ (by exact_mod_cast hm) (Nat.cast_nonneg n)⟩ =
    ηSh ⟨(m : ℝ) / n, by
      constructor
      · exact div_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n)
      · exact div_le_one_of_le₀ (by exact_mod_cast hm) (Nat.cast_nonneg n)⟩ := by
  apply _root_.InformationTheory.ηE_rat_eq_ηSh E.toStandalone <;> assumption

/-- The set of rationals m/n with 0 < n and m ≤ n is dense in [0,1]. -/
theorem rat_dense_in_Icc : Dense {x : Set.Icc (0 : ℝ) 1 | ∃ m n : ℕ, 0 < n ∧ m ≤ n ∧ x.1 = m / n} := by
  apply _root_.InformationTheory.rat_dense_in_Icc


/-- Extending equality from rationals to all of [0,1] via continuity.

    Since ηE and ηSh are both continuous and agree on a dense set (rationals),
    they agree everywhere on [0,1]. Uses `Continuous.ext_on` from mathlib. -/
theorem ηE_eq_ηSh (E : FaddeevEntropy) : ηE E = ηSh := by
  apply _root_.InformationTheory.ηE_eq_ηSh E.toStandalone


/-- Every Faddeev entropy equals Shannon entropy on all distributions.

    Binary uniqueness extends to every arity by induction using recursivity. -/
theorem faddeev_H_eq_shannon (E : FaddeevEntropy) {n : ℕ} (p : ProbVec n) :
    E.H p = shannonEntropyNormalized p := by
  apply _root_.InformationTheory.faddeev_H_eq_shannon E.toStandalone


end FullUniqueness

/-! ## Derived Properties (from Full Uniqueness)

Given `faddeev_H_eq_shannon`, we can derive all the properties that
Shannon-Khinchin explicitly assumes. These are used in `Equivalence.lean`.

The key theorem `faddeev_H_eq_shannon` shows:
```
∀ (p : ProbVec n), E.H p = shannonEntropyNormalized p
```

With this, all three derived properties become trivial rewrites!
-/

/-- Faddeev entropy is fully continuous (not just binary continuous).

Proof: Rewrite E.H to shannonEntropyNormalized, then use continuity of Shannon entropy. -/
theorem faddeev_full_continuity (E : FaddeevEntropy) : Continuous (E.H (n := n)) := by
  apply _root_.InformationTheory.faddeev_full_continuity E.toStandalone


/-- Faddeev entropy satisfies maximality: uniform distribution maximizes entropy.

Proof: Rewrite to Shannon entropy and use `shannonEntropy_le_log_card`. -/
theorem faddeev_maximality (E : FaddeevEntropy) (hn : 0 < n) (p : ProbVec n) :
    E.H p ≤ E.H (uniformDist n hn) := by
  apply _root_.InformationTheory.faddeev_maximality E.toStandalone


/-- Faddeev entropy satisfies expansibility: adding zero probability doesn't change entropy.

Proof: Rewrite to Shannon entropy and use `shannonEntropy_expandZero`. -/
theorem faddeev_expansibility (E : FaddeevEntropy) (p : ProbVec n) :
    E.H (expandZero p) = E.H p := by
  apply _root_.InformationTheory.faddeev_expansibility E.toStandalone


end Mettapedia.InformationTheory
