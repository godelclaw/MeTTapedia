import Mettapedia.QuantumTheory.YangMills.TwistCost
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Twist eaters: in `SU(2)` a centre twist costs no classical action

The matrices `iσ₁` and `iσ₂` lie in `SU(2)` and anticommute, so their group
commutator is the centre element `-1` (`commutator_eaterA_eaterB`).  Put `iσ₁` on
the links of direction `0` in the last column and `iσ₂` on the links of direction
`1` in the last row, and the identity on all other links.  Then every
`(0,1)`-plaquette is `1`, except the plaquette `(-1, -1)` of every plane, which is
`-1` (`plaquette_twistEater`).  With the Wilson sign flipped at exactly those
plaquettes, the twisted action vanishes (`twistedActionSU2_twistEater`).  It is
nonnegative for every `SU(2)` configuration (`twistedActionSU2_nonneg`), so a
centre twist costs `SU(2)` no classical action at all.  In `U(1)` every twisted
configuration costs at least `2 |Y| / L²` (`TwistCost.twistedAction_ge`).

So the twist free energy of `SU(2)` is not a classical energy proportional to the
coupling: it is set by fluctuations around configurations of this kind.
-/

set_option autoImplicit false
noncomputable section

open Matrix Complex

namespace Mettapedia.QuantumTheory.YangMills.TwistEater

open Mettapedia.QuantumTheory.YangMills.TwistCost

/-- `i σ₁`. -/
def eaterA : Matrix (Fin 2) (Fin 2) ℂ := !![0, I; I, 0]

/-- `i σ₂`. -/
def eaterB : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

theorem star_eaterA : star eaterA = -eaterA := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eaterA]

theorem star_eaterB : star eaterB = -eaterB := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eaterB]

theorem eaterA_mul_star : eaterA * star eaterA = 1 := by
  rw [star_eaterA]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eaterA, Matrix.mul_apply, Fin.sum_univ_two]

theorem eaterB_mul_star : eaterB * star eaterB = 1 := by
  rw [star_eaterB]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eaterB, Matrix.mul_apply, Fin.sum_univ_two]

theorem eaterA_mem : eaterA ∈ specialUnitaryGroup (Fin 2) ℂ := by
  rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff]
  refine ⟨eaterA_mul_star, ?_⟩
  simp [eaterA, Matrix.det_fin_two]

theorem eaterB_mem : eaterB ∈ specialUnitaryGroup (Fin 2) ℂ := by
  rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff]
  refine ⟨eaterB_mul_star, ?_⟩
  simp [eaterB, Matrix.det_fin_two]

/-- The group commutator of `iσ₁` and `iσ₂` is the centre element `-1`. -/
theorem commutator_eaterA_eaterB : eaterA * eaterB * star eaterA * star eaterB = -1 := by
  rw [star_eaterA, star_eaterB]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eaterA, eaterB, Matrix.mul_apply, Fin.sum_univ_two]

variable {L : ℕ} [NeZero L] {Y : Type*}

/-- The `(0,1)`-plaquette variable `U₀(x) U₁(x + e₀) U₀(x + e₁)⁻¹ U₁(x)⁻¹`, with
inverses written as conjugate transposes. -/
def plaquette (U₀ U₁ : ZMod L × ZMod L × Y → Matrix (Fin 2) (Fin 2) ℂ) (a b : ZMod L)
    (y : Y) : Matrix (Fin 2) (Fin 2) ℂ :=
  U₀ (a, b, y) * U₁ (a + 1, b, y) * star (U₀ (a, b + 1, y)) * star (U₁ (a, b, y))

/-- The twist eater, direction `0`: `iσ₁` in the last column. -/
def eaterU₀ (p : ZMod L × ZMod L × Y) : Matrix (Fin 2) (Fin 2) ℂ :=
  if p.1 = -1 then eaterA else 1

/-- The twist eater, direction `1`: `iσ₂` in the last row. -/
def eaterU₁ (p : ZMod L × ZMod L × Y) : Matrix (Fin 2) (Fin 2) ℂ :=
  if p.2.1 = -1 then eaterB else 1

omit [NeZero L] in
theorem plaquette_twistEater (a b : ZMod L) (y : Y) :
    plaquette (eaterU₀ (L := L) (Y := Y)) eaterU₁ a b y =
      if a = -1 ∧ b = -1 then -1 else 1 := by
  by_cases ha : a = -1
  · by_cases hb : b = -1
    · simp only [plaquette, eaterU₀, eaterU₁, ha, hb, ↓reduceIte, and_self]
      exact commutator_eaterA_eaterB
    · simp only [plaquette, eaterU₀, eaterU₁, ha, hb, ↓reduceIte, and_false, mul_one, star_one]
      exact eaterA_mul_star
  · by_cases hb : b = -1
    · simp only [plaquette, eaterU₀, eaterU₁, ha, hb, ↓reduceIte, false_and, one_mul, mul_one,
        star_one]
      exact eaterB_mul_star
    · simp [plaquette, eaterU₀, eaterU₁, ha, hb]

/-- The twisted `SU(2)` Wilson action of the `(0,1)`-plaquettes, per unit coupling,
with the sign flipped at the plaquette `(-1, -1)` of every plane. -/
def twistedActionSU2 [Fintype Y] (U₀ U₁ : ZMod L × ZMod L × Y → Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  ∑ y : Y, ∑ a : ZMod L, ∑ b : ZMod L,
    (1 - twistSign a b * ((plaquette U₀ U₁ a b y).trace.re / 2))

/-- **The twist eater has zero twisted action.** -/
theorem twistedActionSU2_twistEater [Fintype Y] :
    twistedActionSU2 (eaterU₀ (L := L) (Y := Y)) eaterU₁ = 0 := by
  unfold twistedActionSU2
  refine Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun a _ =>
    Finset.sum_eq_zero fun b _ => ?_
  rw [plaquette_twistEater]
  by_cases h : a = -1 ∧ b = -1
  · simp [h, twistSign]
  · simp [h, twistSign]

/-- The real part of half the trace of a unitary `2 × 2` matrix lies in `[-1, 1]`. -/
theorem abs_re_trace_div_two_le {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ unitaryGroup (Fin 2) ℂ) : |U.trace.re / 2| ≤ 1 := by
  have h0 := entry_norm_bound_of_unitary hU 0 0
  have h1 := entry_norm_bound_of_unitary hU 1 1
  rw [Matrix.trace_fin_two, Complex.add_re]
  have hr0 : |(U 0 0).re| ≤ 1 := (Complex.abs_re_le_norm _).trans h0
  have hr1 : |(U 1 1).re| ≤ 1 := (Complex.abs_re_le_norm _).trans h1
  rw [abs_div, abs_two, div_le_one (by norm_num)]
  exact (abs_add_le _ _).trans (by linarith)

/-- **No twisted `SU(2)` configuration has negative action**, so the twist eater
minimizes it. -/
theorem twistedActionSU2_nonneg [Fintype Y]
    (U₀ U₁ : ZMod L × ZMod L × Y → Matrix (Fin 2) (Fin 2) ℂ)
    (h₀ : ∀ p, U₀ p ∈ unitaryGroup (Fin 2) ℂ) (h₁ : ∀ p, U₁ p ∈ unitaryGroup (Fin 2) ℂ) :
    0 ≤ twistedActionSU2 U₀ U₁ := by
  unfold twistedActionSU2
  refine Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun a _ =>
    Finset.sum_nonneg fun b _ => ?_
  have hP : plaquette U₀ U₁ a b y ∈ unitaryGroup (Fin 2) ℂ := by
    unfold plaquette
    exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _ (h₀ _) (h₁ _))
      (Unitary.star_mem (h₀ _))) (Unitary.star_mem (h₁ _))
  have hb := abs_re_trace_div_two_le hP
  rw [abs_le] at hb
  unfold twistSign
  split_ifs <;> linarith

#print axioms commutator_eaterA_eaterB
#print axioms twistedActionSU2_twistEater
#print axioms twistedActionSU2_nonneg

end Mettapedia.QuantumTheory.YangMills.TwistEater
