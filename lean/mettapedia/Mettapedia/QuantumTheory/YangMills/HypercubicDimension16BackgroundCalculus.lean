import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceEvaluation

/-!
# Gauge backgrounds over a differential scalar ring

A background consists of a commutative `ℚ`-algebra of scalar functions with four commuting
derivations and a linear integral that vanishes on every total derivative, together with a
traceless connection in `2 × 2` matrices over it.  Covariant derivatives and the curvature
satisfy the commutator identity `[D_μ, D_ν] X = [F_μν, X]` and the Bianchi identity, and the
trace contraction of a product of fields obeys the covariant product rule.  These are the
identities that make evaluation on a background annihilate the off-shell physical relations.

Examples are constant connections (the scalars are `ℚ`, every derivation is zero and the
integral is the identity) and connections whose entries are Laurent polynomials on the torus
(`∂_μ z^k = k_μ z^k`, the integral is the constant term).
-/

set_option autoImplicit false

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16BackgroundCalculus

open HypercubicDimension16TraceEvaluation

/-- `2 × 2` matrices over the scalar functions. -/
abbrev Mat (S : Type*) := Matrix (Fin 2) (Fin 2) S

/-- Scalar functions with four commuting derivations and an integral that kills total
derivatives. -/
structure DifferentialScalars (S : Type*) [CommRing S] [Algebra ℚ S] where
  deriv : Fin 4 → S →ₗ[ℚ] S
  deriv_mul : ∀ μ f g, deriv μ (f * g) = deriv μ f * g + f * deriv μ g
  deriv_comm : ∀ μ ν f, deriv μ (deriv ν f) = deriv ν (deriv μ f)
  integral : S →ₗ[ℚ] ℚ
  integral_deriv : ∀ μ f, integral (deriv μ f) = 0

variable {S : Type*} [CommRing S] [Algebra ℚ S]

namespace DifferentialScalars

variable (sc : DifferentialScalars S)

/-- A derivation of a finite product. -/
theorem deriv_prod {ι : Type*} [DecidableEq ι] (μ : Fin 4) (s : Finset ι) (f : ι → S) :
    sc.deriv μ (∏ i ∈ s, f i) =
      ∑ i ∈ s, sc.deriv μ (f i) * ∏ j ∈ s.erase i, f j := by
  induction s using Finset.induction_on with
  | empty =>
    have h := sc.deriv_mul μ 1 1
    simp only [mul_one, one_mul] at h
    simp only [Finset.prod_empty, Finset.sum_empty]
    linear_combination -h
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, sc.deriv_mul, ih, Finset.sum_insert ha, Finset.erase_insert ha,
      Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hia : i ≠ a := fun h => ha (h ▸ hi)
    rw [Finset.erase_insert_of_ne hia.symm, Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
    ring

/-- Entrywise derivative of a matrix of scalar functions. -/
def mderiv (μ : Fin 4) (X : Mat S) : Mat S := X.map (sc.deriv μ)

@[simp] theorem mderiv_apply (μ : Fin 4) (X : Mat S) (i j : Fin 2) :
    sc.mderiv μ X i j = sc.deriv μ (X i j) := rfl

theorem mderiv_add (μ : Fin 4) (X Y : Mat S) :
    sc.mderiv μ (X + Y) = sc.mderiv μ X + sc.mderiv μ Y := by
  ext i j; simp [mderiv]

theorem mderiv_sub (μ : Fin 4) (X Y : Mat S) :
    sc.mderiv μ (X - Y) = sc.mderiv μ X - sc.mderiv μ Y := by
  ext i j; simp [mderiv]

theorem mderiv_neg (μ : Fin 4) (X : Mat S) : sc.mderiv μ (-X) = -sc.mderiv μ X := by
  ext i j; simp [mderiv]

theorem mderiv_zero (μ : Fin 4) : sc.mderiv μ (0 : Mat S) = 0 := by
  ext i j; simp [mderiv]

theorem mderiv_mul (μ : Fin 4) (X Y : Mat S) :
    sc.mderiv μ (X * Y) = sc.mderiv μ X * Y + X * sc.mderiv μ Y := by
  ext i k
  simp only [mderiv_apply, Matrix.mul_apply, Matrix.add_apply, map_sum, sc.deriv_mul,
    Finset.sum_add_distrib]

theorem mderiv_comm (μ ν : Fin 4) (X : Mat S) :
    sc.mderiv μ (sc.mderiv ν X) = sc.mderiv ν (sc.mderiv μ X) := by
  ext i j; simp [mderiv, sc.deriv_comm]

theorem trace_mderiv (μ : Fin 4) (X : Mat S) :
    (sc.mderiv μ X).trace = sc.deriv μ X.trace := by
  simp [Matrix.trace, mderiv]

end DifferentialScalars

/-- A traceless connection on a differential scalar ring. -/
structure GaugeBackground (S : Type*) [CommRing S] [Algebra ℚ S] where
  scalars : DifferentialScalars S
  connection : Fin 4 → Mat S
  connection_traceless : ∀ μ, (connection μ).trace = 0

namespace GaugeBackground

variable (bg : GaugeBackground S)

/-- Covariant derivative in the adjoint representation. -/
def covDeriv (μ : Fin 4) (X : Mat S) : Mat S :=
  bg.scalars.mderiv μ X + bg.connection μ * X - X * bg.connection μ

/-- Curvature of the connection. -/
def curvature (μ ν : Fin 4) : Mat S :=
  bg.scalars.mderiv μ (bg.connection ν) - bg.scalars.mderiv ν (bg.connection μ) +
    bg.connection μ * bg.connection ν - bg.connection ν * bg.connection μ

theorem curvature_antisymm (μ ν : Fin 4) : bg.curvature ν μ = -bg.curvature μ ν := by
  unfold curvature; abel

theorem curvature_self (μ : Fin 4) : bg.curvature μ μ = 0 := by
  unfold curvature; abel

theorem covDeriv_add (μ : Fin 4) (X Y : Mat S) :
    bg.covDeriv μ (X + Y) = bg.covDeriv μ X + bg.covDeriv μ Y := by
  unfold covDeriv; rw [bg.scalars.mderiv_add]; noncomm_ring

theorem covDeriv_sub (μ : Fin 4) (X Y : Mat S) :
    bg.covDeriv μ (X - Y) = bg.covDeriv μ X - bg.covDeriv μ Y := by
  unfold covDeriv; rw [bg.scalars.mderiv_sub]; noncomm_ring

theorem covDeriv_neg (μ : Fin 4) (X : Mat S) : bg.covDeriv μ (-X) = -bg.covDeriv μ X := by
  unfold covDeriv; rw [bg.scalars.mderiv_neg]; noncomm_ring

theorem covDeriv_zero (μ : Fin 4) : bg.covDeriv μ 0 = 0 := by
  unfold covDeriv; rw [bg.scalars.mderiv_zero]; noncomm_ring

/-- The commutator of covariant derivatives is the adjoint action of the curvature. -/
theorem covDeriv_comm (μ ν : Fin 4) (X : Mat S) :
    bg.covDeriv μ (bg.covDeriv ν X) - bg.covDeriv ν (bg.covDeriv μ X) =
      bg.curvature μ ν * X - X * bg.curvature μ ν := by
  unfold covDeriv curvature
  simp only [bg.scalars.mderiv_add, bg.scalars.mderiv_sub, bg.scalars.mderiv_mul]
  rw [bg.scalars.mderiv_comm μ ν X]
  noncomm_ring

/-- The Bianchi identity. -/
theorem bianchi (l μ ν : Fin 4) :
    bg.covDeriv l (bg.curvature μ ν) + bg.covDeriv μ (bg.curvature ν l) +
      bg.covDeriv ν (bg.curvature l μ) = 0 := by
  unfold covDeriv curvature
  simp only [bg.scalars.mderiv_add, bg.scalars.mderiv_sub, bg.scalars.mderiv_mul]
  rw [bg.scalars.mderiv_comm l μ (bg.connection ν), bg.scalars.mderiv_comm μ ν (bg.connection l),
    bg.scalars.mderiv_comm l ν (bg.connection μ)]
  noncomm_ring

theorem trace_covDeriv (μ : Fin 4) (X : Mat S) :
    (bg.covDeriv μ X).trace = bg.scalars.deriv μ X.trace := by
  unfold covDeriv
  rw [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_mul_comm (bg.connection μ) X,
    bg.scalars.trace_mderiv]
  ring

theorem covDeriv_traceless (μ : Fin 4) (X : Mat S) (hX : X.trace = 0) :
    (bg.covDeriv μ X).trace = 0 := by
  rw [bg.trace_covDeriv, hX, map_zero]

theorem curvature_traceless (μ ν : Fin 4) : (bg.curvature μ ν).trace = 0 := by
  unfold curvature
  rw [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_sub, bg.scalars.trace_mderiv,
    bg.scalars.trace_mderiv, bg.connection_traceless, bg.connection_traceless,
    Matrix.trace_mul_comm (bg.connection μ)]
  simp

end GaugeBackground

/-! ## The trace contraction under derivatives and insertions -/

section Contraction

variable {Label : Type*} [Fintype Label] [DecidableEq Label]

/-- The contraction depends additively on the matrix at one label. -/
theorem contraction_update_add (X : Label → Mat S) (σ : Equiv.Perm Label) (i : Label)
    (Y Z : Mat S) :
    tracePermutationContraction (Function.update X i (Y + Z)) σ =
      tracePermutationContraction (Function.update X i Y) σ +
        tracePermutationContraction (Function.update X i Z) σ := by
  unfold tracePermutationContraction
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro state _
  rw [← Finset.prod_mul_prod_compl {i}, ← Finset.prod_mul_prod_compl {i},
    ← Finset.prod_mul_prod_compl {i}]
  simp only [Finset.prod_singleton, Function.update_self, Matrix.add_apply]
  have hrest : ∀ W : Mat S,
      (∏ x ∈ ({i} : Finset Label)ᶜ, Function.update X i W x (state x) (state (σ x))) =
        ∏ x ∈ ({i} : Finset Label)ᶜ, X x (state x) (state (σ x)) := by
    intro W
    apply Finset.prod_congr rfl
    intro x hx
    rw [Function.update_of_ne (by simpa using hx)]
  rw [hrest, hrest, hrest]
  ring

theorem contraction_update_neg (X : Label → Mat S) (σ : Equiv.Perm Label) (i : Label)
    (Y : Mat S) :
    tracePermutationContraction (Function.update X i (-Y)) σ =
      -tracePermutationContraction (Function.update X i Y) σ := by
  have h := contraction_update_add X σ i Y (-Y)
  rw [add_neg_cancel] at h
  have h0 : tracePermutationContraction (Function.update X i (0 : Mat S)) σ = 0 := by
    unfold tracePermutationContraction
    apply Finset.sum_eq_zero
    intro state _
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  rw [h0] at h
  linear_combination -h

theorem contraction_update_sub (X : Label → Mat S) (σ : Equiv.Perm Label) (i : Label)
    (Y Z : Mat S) :
    tracePermutationContraction (Function.update X i (Y - Z)) σ =
      tracePermutationContraction (Function.update X i Y) σ -
        tracePermutationContraction (Function.update X i Z) σ := by
  rw [sub_eq_add_neg, contraction_update_add, contraction_update_neg, ← sub_eq_add_neg]

theorem contraction_update_self (X : Label → Mat S) (σ : Equiv.Perm Label) (i : Label) :
    tracePermutationContraction (Function.update X i (X i)) σ =
      tracePermutationContraction X σ := by
  rw [Function.update_eq_self]

/-- A derivation of the contraction is the sum of the contractions with one matrix
differentiated. -/
theorem deriv_contraction (sc : DifferentialScalars S) (μ : Fin 4) (X : Label → Mat S)
    (σ : Equiv.Perm Label) :
    sc.deriv μ (tracePermutationContraction X σ) =
      ∑ i, tracePermutationContraction (Function.update X i (sc.mderiv μ (X i))) σ := by
  unfold tracePermutationContraction
  rw [map_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro state _
  rw [sc.deriv_prod]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [Function.update_self, DifferentialScalars.mderiv_apply]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- The contraction with the matrix at `c` replaced by a product, written with the extra
matrix-index sum of that product. -/
theorem contraction_update_mul (X : Label → Mat S) (σ : Equiv.Perm Label) (c : Label)
    (Y Z : Mat S) :
    tracePermutationContraction (Function.update X c (Y * Z)) σ =
      ∑ state : Label → Fin 2, ∑ u : Fin 2,
        Y (state c) u * Z u (state (σ c)) *
          ∏ i ∈ Finset.univ.erase c, X i (state i) (state (σ i)) := by
  unfold tracePermutationContraction
  apply Finset.sum_congr rfl
  intro state _
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c)]
  simp only [Function.update_self, Matrix.mul_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

/-- Moving an inserted matrix across one trace edge: right multiplication at `c` equals left
multiplication at its trace successor. -/
theorem contraction_move_across_edge (X : Label → Mat S) (σ : Equiv.Perm Label) (c : Label)
    (B : Mat S) :
    tracePermutationContraction (Function.update X c (X c * B)) σ =
      tracePermutationContraction (Function.update X (σ c) (B * X (σ c))) σ := by
  rw [contraction_update_mul, contraction_update_mul]
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  let φ : (Label → Fin 2) × Fin 2 ≃ (Label → Fin 2) × Fin 2 :=
    { toFun := fun p => (Function.update p.1 (σ c) p.2, p.1 (σ c))
      invFun := fun p => (Function.update p.1 (σ c) p.2, p.1 (σ c))
      left_inv := fun p => by
        rcases p with ⟨t, u⟩
        simp [Function.update_idem]
      right_inv := fun p => by
        rcases p with ⟨t, u⟩
        simp [Function.update_idem] }
  conv_rhs => rw [← Equiv.sum_comp φ]
  apply Finset.sum_congr rfl
  rintro ⟨t, u⟩ _
  simp only [φ, Equiv.coe_fn_mk, Function.update_self]
  by_cases hfix : σ c = c
  · -- a fixed trace point: the two sides are the two orders of one trace
    have hrest : ∀ i ∈ Finset.univ.erase c,
        X i (Function.update t c u i) (Function.update t c u (σ i)) = X i (t i) (t (σ i)) := by
      intro i hi
      have hic : i ≠ c := Finset.ne_of_mem_erase hi
      have hσi : σ i ≠ c := fun h => hic (σ.injective (h.trans hfix.symm))
      rw [Function.update_of_ne hic, Function.update_of_ne hσi]
    simp only [hfix, Function.update_self]
    rw [Finset.prod_congr rfl hrest]
    ring
  · -- a genuine trace edge `c → σ c`
    have hσσ : σ (σ c) ≠ σ c := fun h => hfix (σ.injective h)
    have hleft : ∏ i ∈ Finset.univ.erase c, X i (t i) (t (σ i)) =
        X (σ c) (t (σ c)) (t (σ (σ c))) *
          ∏ i ∈ (Finset.univ.erase c).erase (σ c), X i (t i) (t (σ i)) :=
      (Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hfix, Finset.mem_univ _⟩)).symm
    have hright : ∏ i ∈ Finset.univ.erase (σ c),
        X i (Function.update t (σ c) u i) (Function.update t (σ c) u (σ i)) =
        X c (t c) u * ∏ i ∈ (Finset.univ.erase c).erase (σ c), X i (t i) (t (σ i)) := by
      rw [← Finset.mul_prod_erase (Finset.univ.erase (σ c)) _
        (Finset.mem_erase.mpr ⟨fun h => hfix h.symm, Finset.mem_univ c⟩)]
      rw [Function.update_of_ne (fun h => hfix h.symm), Function.update_self,
        Finset.erase_right_comm]
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      have hid : i ≠ σ c := Finset.ne_of_mem_erase hi
      have hic : i ≠ c := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
      have hσi : σ i ≠ σ c := fun h => hic (σ.injective h)
      rw [Function.update_of_ne hid, Function.update_of_ne hσi]
    rw [hleft, hright, Function.update_of_ne hσσ]
    ring

/-- Commutators with a fixed matrix telescope around every trace cycle. -/
theorem contraction_commutator_sum (X : Label → Mat S) (σ : Equiv.Perm Label) (B : Mat S) :
    ∑ i, tracePermutationContraction (Function.update X i (B * X i - X i * B)) σ = 0 := by
  simp only [contraction_update_sub, Finset.sum_sub_distrib]
  have hmove : ∑ i, tracePermutationContraction (Function.update X i (X i * B)) σ =
      ∑ i, tracePermutationContraction (Function.update X (σ i) (B * X (σ i))) σ :=
    Finset.sum_congr rfl fun i _ => contraction_move_across_edge X σ i B
  rw [hmove, Equiv.sum_comp σ (fun j =>
    tracePermutationContraction (Function.update X j (B * X j)) σ), sub_self]

end Contraction

/-- The covariant product rule: summing the contraction over one covariant derivative of each
factor gives a total derivative. -/
theorem GaugeBackground.sum_contraction_covDeriv (bg : GaugeBackground S)
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    (μ : Fin 4) (X : Label → Mat S) (σ : Equiv.Perm Label) :
    ∑ i, tracePermutationContraction (Function.update X i (bg.covDeriv μ (X i))) σ =
      bg.scalars.deriv μ (tracePermutationContraction X σ) := by
  have hsplit : ∀ i, tracePermutationContraction (Function.update X i (bg.covDeriv μ (X i))) σ =
      tracePermutationContraction (Function.update X i (bg.scalars.mderiv μ (X i))) σ +
        tracePermutationContraction
          (Function.update X i (bg.connection μ * X i - X i * bg.connection μ)) σ := by
    intro i
    rw [← contraction_update_add]
    congr 2
    unfold GaugeBackground.covDeriv
    noncomm_ring
  simp only [hsplit, Finset.sum_add_distrib, contraction_commutator_sum, add_zero]
  exact (deriv_contraction bg.scalars μ X σ).symm

/-- Integrated IBP: the integral of that sum vanishes. -/
theorem GaugeBackground.integral_sum_contraction_covDeriv (bg : GaugeBackground S)
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    (μ : Fin 4) (X : Label → Mat S) (σ : Equiv.Perm Label) :
    bg.scalars.integral
        (∑ i, tracePermutationContraction (Function.update X i (bg.covDeriv μ (X i))) σ) = 0 := by
  rw [bg.sum_contraction_covDeriv, bg.scalars.integral_deriv]


end HypercubicDimension16BackgroundCalculus
end YangMills
end QuantumTheory
end Mettapedia
