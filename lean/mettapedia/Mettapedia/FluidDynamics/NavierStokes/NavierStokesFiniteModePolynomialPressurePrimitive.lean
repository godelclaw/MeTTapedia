import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeReconstructionCore

/-!
# Finite-mode polynomial pressure primitives
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Set
open scoped BigOperators
open scoped ContDiff
open scoped Laplacian

/-- Polynomial pressure primitives for homogeneous curl-free vector fields.
For a homogeneous degree-`n` polynomial vector field `F`, Euler's identity
turns the radial antiderivative `(n + 1)⁻¹ ∑ i X_i F_i` into a genuine
pressure primitive whenever the mixed partials agree. -/
def finiteModeHomogeneousPolynomialPressurePrimitive
    (n : ℕ) (F : Fin 3 → MvPolynomial (Fin 3) ℝ) :
    MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.C (((n + 1 : ℕ) : ℝ)⁻¹) *
    ∑ i : Fin 3, MvPolynomial.X i * F i

/-- Degree-independent polynomial Poincare lemma for homogeneous curl-free
vector polynomials on `ℝ^3`: the radial primitive differentiates back to each
component.  This is the algebraic core needed before a finite-mode polynomial
pressure basis can solve the non-pressure residual instead of taking closure
as an input hypothesis. -/
theorem finiteModeHomogeneousPolynomialPressurePrimitive_pderiv
    (n : ℕ) (F : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hhom : ∀ j, (F j).IsHomogeneous n)
    (hcurl : ∀ i j, MvPolynomial.pderiv i (F j) =
      MvPolynomial.pderiv j (F i))
    (j : Fin 3) :
    MvPolynomial.pderiv j
        (finiteModeHomogeneousPolynomialPressurePrimitive n F) =
      F j := by
  classical
  have hdelta :
      (∑ i : Fin 3,
          MvPolynomial.pderiv j (MvPolynomial.X i : MvPolynomial (Fin 3) ℝ) *
            F i) =
        F j := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _hi hij
      rw [MvPolynomial.pderiv_X_of_ne hij]
      simp
    · intro hj
      exact False.elim (hj (Finset.mem_univ j))
  have hcurlsum :
      (∑ i : Fin 3,
          MvPolynomial.X i * MvPolynomial.pderiv j (F i)) =
        ∑ i : Fin 3, MvPolynomial.X i * MvPolynomial.pderiv i (F j) := by
    refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [hcurl j i]
  have heuler :
      (∑ i : Fin 3, MvPolynomial.X i * MvPolynomial.pderiv i (F j)) =
        n • F j := by
    simpa using (hhom j).sum_X_mul_pderiv
  have hsum :
      MvPolynomial.pderiv j
          (∑ i : Fin 3, MvPolynomial.X i * F i) =
        (n + 1) • F j := by
    calc
      MvPolynomial.pderiv j
          (∑ i : Fin 3, MvPolynomial.X i * F i) =
        ∑ i : Fin 3,
          MvPolynomial.pderiv j (MvPolynomial.X i * F i) := by
          exact
            map_sum (MvPolynomial.pderiv j)
              (fun i : Fin 3 => MvPolynomial.X i * F i) Finset.univ
      _ = ∑ i : Fin 3,
          (MvPolynomial.pderiv j (MvPolynomial.X i) * F i +
            MvPolynomial.X i * MvPolynomial.pderiv j (F i)) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [MvPolynomial.pderiv_mul]
      _ =
        (∑ i : Fin 3,
          MvPolynomial.pderiv j (MvPolynomial.X i : MvPolynomial (Fin 3) ℝ) *
            F i) +
          ∑ i : Fin 3, MvPolynomial.X i * MvPolynomial.pderiv j (F i) := by
          rw [Finset.sum_add_distrib]
      _ = F j + ∑ i : Fin 3,
          MvPolynomial.X i * MvPolynomial.pderiv i (F j) := by
          rw [hdelta, hcurlsum]
      _ = F j + n • F j := by
          rw [heuler]
      _ = (n + 1) • F j := by
          simpa [Nat.succ_eq_add_one, add_comm] using
            ((succ_nsmul (F j) n).symm)
  unfold finiteModeHomogeneousPolynomialPressurePrimitive
  rw [MvPolynomial.pderiv_C_mul, hsum]
  have hnpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos n
  have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := ne_of_gt hnpos
  rw [nsmul_eq_mul]
  change
    MvPolynomial.C (((n + 1 : ℕ) : ℝ)⁻¹) *
        (((n + 1 : ℕ) : MvPolynomial (Fin 3) ℝ) * F j) =
      F j
  rw [← mul_assoc]
  have hcast :
      ((n + 1 : ℕ) : MvPolynomial (Fin 3) ℝ) =
        MvPolynomial.C (((n + 1 : ℕ) : ℝ)) := by
    norm_num
  rw [hcast]
  have hscale :
      MvPolynomial.C (((n + 1 : ℕ) : ℝ)⁻¹) *
          MvPolynomial.C (((n + 1 : ℕ) : ℝ)) =
        (1 : MvPolynomial (Fin 3) ℝ) := by
    calc
      MvPolynomial.C (((n + 1 : ℕ) : ℝ)⁻¹) *
          MvPolynomial.C (((n + 1 : ℕ) : ℝ)) =
        MvPolynomial.C
          ((((n + 1 : ℕ) : ℝ)⁻¹) * (((n + 1 : ℕ) : ℝ))) := by
          rw [← MvPolynomial.C_mul]
      _ = (1 : MvPolynomial (Fin 3) ℝ) := by
          have hreal :
              (((n + 1 : ℕ) : ℝ)⁻¹ * (((n + 1 : ℕ) : ℝ))) = 1 :=
            inv_mul_cancel₀ hn
          rw [hreal]
          simp
  rw [hscale, one_mul]

/-- Finite sum of homogeneous polynomial pressure primitives. -/
def finiteModeFiniteHomogeneousPolynomialPressurePrimitive
    (s : Finset ℕ) (F : ℕ → Fin 3 → MvPolynomial (Fin 3) ℝ) :
    MvPolynomial (Fin 3) ℝ :=
  s.sum fun n => finiteModeHomogeneousPolynomialPressurePrimitive n (F n)

/-- A finite sum of homogeneous curl-free polynomial vector fields has a
polynomial pressure primitive obtained by summing the radial primitives of the
homogeneous pieces. -/
theorem finiteModeFiniteHomogeneousPolynomialPressurePrimitive_pderiv
    (s : Finset ℕ) (F : ℕ → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hhom : ∀ n ∈ s, ∀ j, (F n j).IsHomogeneous n)
    (hcurl : ∀ n ∈ s, ∀ i j,
      MvPolynomial.pderiv i (F n j) =
        MvPolynomial.pderiv j (F n i))
    (j : Fin 3) :
    MvPolynomial.pderiv j
        (finiteModeFiniteHomogeneousPolynomialPressurePrimitive s F) =
      s.sum fun n => F n j := by
  unfold finiteModeFiniteHomogeneousPolynomialPressurePrimitive
  calc
    MvPolynomial.pderiv j
        (s.sum fun n => finiteModeHomogeneousPolynomialPressurePrimitive n (F n)) =
      s.sum fun n =>
        MvPolynomial.pderiv j
          (finiteModeHomogeneousPolynomialPressurePrimitive n (F n)) := by
        exact
          map_sum (MvPolynomial.pderiv j)
            (fun n => finiteModeHomogeneousPolynomialPressurePrimitive n (F n)) s
    _ = s.sum fun n => F n j := by
        refine Finset.sum_congr rfl ?_
        intro n hn
        exact finiteModeHomogeneousPolynomialPressurePrimitive_pderiv
          n (F n) (hhom n hn) (hcurl n hn) j

/-- Repackaged finite homogeneous pressure solve against a named target vector
polynomial.  The remaining general-polynomial task is to supply the homogeneous
decomposition and prove its pieces inherit curl-freeness. -/
theorem finiteModeFiniteHomogeneousPolynomialPressurePrimitive_pderiv_of_sum
    (s : Finset ℕ) (F : ℕ → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (G : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hhom : ∀ n ∈ s, ∀ j, (F n j).IsHomogeneous n)
    (hcurl : ∀ n ∈ s, ∀ i j,
      MvPolynomial.pderiv i (F n j) =
        MvPolynomial.pderiv j (F n i))
    (hsum : ∀ j, (s.sum fun n => F n j) = G j)
    (j : Fin 3) :
    MvPolynomial.pderiv j
        (finiteModeFiniteHomogeneousPolynomialPressurePrimitive s F) =
      G j := by
  rw [finiteModeFiniteHomogeneousPolynomialPressurePrimitive_pderiv
    s F hhom hcurl j, hsum j]

/-- Coefficient formula for formal partial derivatives on the polynomial ring
used for finite-mode pressure algebra. -/
theorem finiteModePolynomial_coeff_pderiv
    (i : Fin 3) (d : Fin 3 →₀ ℕ) (φ : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial.coeff d (MvPolynomial.pderiv i φ) =
      MvPolynomial.coeff (d + Finsupp.single i 1) φ *
        ((d i + 1 : ℕ) : ℝ) := by
  induction φ using MvPolynomial.induction_on' with
  | monomial u a =>
      rw [MvPolynomial.pderiv_monomial]
      simp only [MvPolynomial.coeff_monomial]
      by_cases h : u = d + Finsupp.single i 1
      · subst u
        simp [add_comm]
      · simp [h]
        intro hsub
        have hui : u i = 0 := by
          by_contra hne
          have hadd : u = d + Finsupp.single i 1 := by
            rw [← hsub]
            exact (Finsupp.sub_add_single_one_cancel hne).symm
          exact h hadd
        simp [hui]
  | add p q hp hq =>
      rw [map_add]
      simp [MvPolynomial.coeff_add, hp, hq, add_mul]

/-- Formal partial derivatives commute with homogeneous projection, with the
expected degree shift. -/
theorem finiteModeHomogeneousComponent_pderiv_succ
    (n : ℕ) (i : Fin 3) (φ : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial.pderiv i (MvPolynomial.homogeneousComponent (n + 1) φ) =
      MvPolynomial.homogeneousComponent n (MvPolynomial.pderiv i φ) := by
  ext d
  rw [finiteModePolynomial_coeff_pderiv]
  rw [MvPolynomial.coeff_homogeneousComponent]
  rw [MvPolynomial.coeff_homogeneousComponent]
  rw [finiteModePolynomial_coeff_pderiv]
  by_cases hd : d.degree = n <;> simp [hd]

/-- Curl-freeness passes to every homogeneous component of a polynomial vector
field. -/
theorem finiteModeHomogeneousComponent_curlFree
    (G : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hcurl : ∀ i j,
      MvPolynomial.pderiv i (G j) =
        MvPolynomial.pderiv j (G i))
    (n : ℕ) (i j : Fin 3) :
    MvPolynomial.pderiv i (MvPolynomial.homogeneousComponent n (G j)) =
      MvPolynomial.pderiv j (MvPolynomial.homogeneousComponent n (G i)) := by
  cases n with
  | zero =>
      simp [MvPolynomial.homogeneousComponent_zero]
  | succ n =>
      rw [finiteModeHomogeneousComponent_pderiv_succ n i (G j)]
      rw [finiteModeHomogeneousComponent_pderiv_succ n j (G i)]
      rw [hcurl i j]

/-- Homogeneous components up to any degree bound summing past the total degree
still reconstruct the original polynomial. -/
theorem finiteModePolynomial_sum_homogeneousComponent_of_totalDegree_le
    (φ : MvPolynomial (Fin 3) ℝ) {N : ℕ} (hN : φ.totalDegree ≤ N) :
    (Finset.range (N + 1)).sum
        (fun n => MvPolynomial.homogeneousComponent n φ) =
      φ := by
  calc
    (∑ n ∈ Finset.range (N + 1), MvPolynomial.homogeneousComponent n φ) =
        ∑ n ∈ Finset.range (φ.totalDegree + 1),
          MvPolynomial.homogeneousComponent n φ := by
      exact (Finset.sum_subset
        (s₁ := Finset.range (φ.totalDegree + 1))
        (s₂ := Finset.range (N + 1))
        (f := fun n => MvPolynomial.homogeneousComponent n φ)
        (by
          intro n hn
          rw [Finset.mem_range] at hn ⊢
          exact lt_of_lt_of_le hn (Nat.succ_le_succ hN))
        (by
          intro n _hnBig hnSmall
          rw [Finset.mem_range] at hnSmall
          have hlt : φ.totalDegree < n := Nat.le_of_not_gt hnSmall
          exact MvPolynomial.homogeneousComponent_eq_zero n φ hlt)).symm
    _ = φ := MvPolynomial.sum_homogeneousComponent (φ := φ)

/-- Uniform total-degree bound for a three-component polynomial vector field. -/
def finiteModePolynomialVectorTotalDegree
    (G : Fin 3 → MvPolynomial (Fin 3) ℝ) : ℕ :=
  Finset.univ.sup fun j : Fin 3 => (G j).totalDegree

/-- General polynomial pressure primitive for a curl-free polynomial vector
field, obtained by summing the radial primitives of its homogeneous
components. -/
def finiteModePolynomialPressurePrimitive
    (G : Fin 3 → MvPolynomial (Fin 3) ℝ) :
    MvPolynomial (Fin 3) ℝ :=
  finiteModeFiniteHomogeneousPolynomialPressurePrimitive
    (Finset.range (finiteModePolynomialVectorTotalDegree G + 1))
    (fun n j => MvPolynomial.homogeneousComponent n (G j))

/-- Polynomial Helmholtz/Poincare pressure solve on `ℝ^3`: every curl-free
polynomial vector field is the formal gradient of the explicit polynomial
pressure primitive above. -/
theorem finiteModePolynomialPressurePrimitive_pderiv
    (G : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hcurl : ∀ i j,
      MvPolynomial.pderiv i (G j) =
        MvPolynomial.pderiv j (G i))
    (j : Fin 3) :
    MvPolynomial.pderiv j (finiteModePolynomialPressurePrimitive G) =
      G j := by
  unfold finiteModePolynomialPressurePrimitive
  rw [finiteModeFiniteHomogeneousPolynomialPressurePrimitive_pderiv]
  · exact finiteModePolynomial_sum_homogeneousComponent_of_totalDegree_le
      (G j)
      (Finset.le_sup
        (f := fun k : Fin 3 => (G k).totalDegree) (Finset.mem_univ j))
  · intro n _hn k
    exact MvPolynomial.homogeneousComponent_isHomogeneous n (G k)
  · intro n _hn i k
    exact finiteModeHomogeneousComponent_curlFree G hcurl n i k

/-- Formal mixed partial derivatives commute for three-variable real
polynomials. -/
theorem finiteModePolynomial_pderiv_comm
    (i j : Fin 3) (p : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  ext d
  repeat rw [finiteModePolynomial_coeff_pderiv]
  by_cases hij : i = j
  · subst j
    ring
  · have hji : j ≠ i := Ne.symm hij
    simp [Finsupp.single_eq_of_ne, hij, hji, Finsupp.add_apply,
      add_comm, add_left_comm, mul_assoc, mul_comm, mul_left_comm]

/-- Polynomial Helmholtz/Poincare exactness in coefficient form: a polynomial
vector field is a formal gradient exactly when its mixed partials commute. -/
theorem finiteModePolynomialPressurePrimitive_exists_iff_curlFree
    (G : Fin 3 → MvPolynomial (Fin 3) ℝ) :
    (∃ p : MvPolynomial (Fin 3) ℝ,
        ∀ j, MvPolynomial.pderiv j p = G j) ↔
      ∀ i j, MvPolynomial.pderiv i (G j) =
        MvPolynomial.pderiv j (G i) := by
  constructor
  · rintro ⟨p, hp⟩ i j
    rw [← hp j, ← hp i]
    exact finiteModePolynomial_pderiv_comm i j p
  · intro hcurl
    exact ⟨finiteModePolynomialPressurePrimitive G,
      finiteModePolynomialPressurePrimitive_pderiv G hcurl⟩


end NavierStokes
end FluidDynamics
end Mettapedia
