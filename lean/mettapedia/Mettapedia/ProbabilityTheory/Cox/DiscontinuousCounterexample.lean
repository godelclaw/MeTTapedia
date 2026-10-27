import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Module.Rat
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.Order.Basic
import Mettapedia.ProbabilityTheory.Cox.Basic

import KnuthSkilling.Multiplicative.FunctionalEquation

/-!
# Algebraic nonuniqueness and the order boundary

Hamel-basis additive maps can be discontinuous; strict monotonicity rules them
out. The independently constructed swap operations below are associative and
unital, but omit range and monotonicity as well as continuity. They do not
isolate continuity as a necessary Cox hypothesis. Their explicit range and
order failures make that boundary observable.
-/

namespace Mettapedia.ProbabilityTheory.Cox.DiscontinuousCounterexample

open Classical Filter

open scoped Topology

noncomputable section

/-- Continuous additive maps are linear, using the canonical Cauchy theorem. -/
theorem continuous_additive_is_linear (f : ℝ →+ ℝ) (hc : Continuous f) :
    ∃ c : ℝ, ∀ x, f x = c * x :=
  KnuthSkilling.Multiplicative.continuous_additive_eq_mul f (map_add f) hc

/-- Strict monotonicity already rules out discontinuous additive maps. -/
theorem discontinuous_additive_not_strictMono (f : ℝ →+ ℝ) (hdisc : ¬Continuous f) :
    ¬StrictMono f := by
  intro hmono
  obtain ⟨c, _, hc⟩ :=
    KnuthSkilling.Multiplicative.AdditiveOnPos.exists_mul_const_of_add_of_pos f
      (fun _ _ => map_add f _ _) (fun hu => by simpa using hmono hu)
  have hlinear : ∀ x, f x = c * x := by
    intro x
    rcases lt_trichotomy 0 x with hx | hx | hx
    · exact hc hx
    · subst x; simp
    · have h := hc (neg_pos.mpr hx)
      rw [map_neg] at h
      linarith
  exact hdisc ((continuous_const.mul continuous_id).congr (fun x => (hlinear x).symm))

/-- **Hamel (1905)**: There exist discontinuous additive functions.

We give a concrete construction using a ℚ-basis of ℝ. The key idea:
1. `{1, √2}` is ℚ-linearly independent (since √2 is irrational).
2. Extend this set to a basis `B` of ℝ over ℚ.
3. Define a ℚ-linear map `f` that sends the basis element `√2` to `1`
   and all other basis elements to `0`.
4. Then `f` is additive but not of the form `c·x`, hence not continuous.
-/
theorem discontinuousAdditive_exists : ∃ f : ℝ →+ ℝ, ¬Continuous f := by
  classical
  let s : Set ℝ := {(1 : ℝ), Real.sqrt 2}
  have hlin : LinearIndepOn ℚ id s := by
    refine linearIndepOn_id_pair (K := ℚ) (x := (1 : ℝ)) (y := Real.sqrt 2) ?_ ?_
    · norm_num
    · intro a
      have hrat : (Real.sqrt 2) ≠ (a : ℝ) := (irrational_sqrt_two.ne_rat a)
      have hrat' : (a : ℝ) ≠ (Real.sqrt 2) := hrat.symm
      simpa [smul_eq_mul] using hrat'
  let B : Module.Basis (hlin.extend (Set.subset_univ s)) ℚ ℝ :=
    Module.Basis.extend (K := ℚ) (V := ℝ) hlin
  have hsubset : s ⊆ hlin.extend (Set.subset_univ s) :=
    Module.Basis.subset_extend (K := ℚ) (V := ℝ) hlin
  have h1 : (1 : ℝ) ∈ hlin.extend (Set.subset_univ s) := hsubset (by simp [s])
  have h2 : (Real.sqrt 2) ∈ hlin.extend (Set.subset_univ s) := hsubset (by simp [s])
  let x1 : hlin.extend (Set.subset_univ s) := ⟨1, h1⟩
  let x2 : hlin.extend (Set.subset_univ s) := ⟨Real.sqrt 2, h2⟩
  have hx12 : x1 ≠ x2 := by
    intro h
    have h' : (1 : ℝ) = Real.sqrt 2 := by
      simpa [x1, x2] using congrArg Subtype.val h
    exact (irrational_sqrt_two.ne_rat (1 : ℚ)) (by simpa using h'.symm)
  let g : hlin.extend (Set.subset_univ s) → ℝ := fun x => if x = x2 then 1 else 0
  let fLin : ℝ →ₗ[ℚ] ℝ := B.constr ℚ g
  let f : ℝ →+ ℝ := fLin.toAddMonoidHom
  have hf1 : f 1 = 0 := by
    have hfx1 : f 1 = g x1 := by
      simpa [f, fLin, B, x1] using
        (B.constr_basis (S := ℚ) (f := g) (i := x1))
    have hgx1 : g x1 = 0 := by
      simp [g, x1, x2, hx12]
    simpa [hgx1] using hfx1
  have hf2 : f (Real.sqrt 2) = 1 := by
    have hfx2 : f (Real.sqrt 2) = g x2 := by
      simpa [f, fLin, B, x2] using
        (B.constr_basis (S := ℚ) (f := g) (i := x2))
    have hgx2 : g x2 = 1 := by
      simp [g, x2]
    simpa [hgx2] using hfx2
  have hnot : ¬Continuous f := by
    intro hcont
    obtain ⟨c, hc⟩ := continuous_additive_is_linear f hcont
    have hc1 : f 1 = c := by simpa using hc 1
    have hc0 : c = 0 := by simpa [hf1] using hc1.symm
    have hfs : f (Real.sqrt 2) = 0 := by
      simpa [hc0] using hc (Real.sqrt 2)
    have : (1 : ℝ) = 0 := by
      have hfs' := hfs
      rw [hf2] at hfs'
      exact hfs'
    exact one_ne_zero this
  exact ⟨f, hnot⟩

/-- Associativity and identity only; no probability range or order is asserted. -/
structure AssociativeUnitalRule where
  F : ℝ → ℝ → ℝ
  F_assoc : ∀ x y z, F (F x y) z = F x (F y z)
  F_one_left : ∀ y, F 1 y = y
  F_one_right : ∀ x, F x 1 = x

/-- The standard product rule x · y -/
def standardF : ℝ → ℝ → ℝ := fun x y => x * y

/-- Standard product satisfies the axioms -/
def standardUnitalRule : AssociativeUnitalRule where
  F := standardF
  F_assoc := fun x y z => by simp [standardF, mul_assoc]
  F_one_left := fun y => by simp [standardF]
  F_one_right := fun x => by simp [standardF]

/-! ### Swap-based conjunction rules (explicit discontinuous models) -/

private def swapF (b : ℝ) : ℝ → ℝ → ℝ := fun x y =>
  (Equiv.swap (0 : ℝ) b).symm ((Equiv.swap (0 : ℝ) b) x + (Equiv.swap (0 : ℝ) b) y - 1)

private lemma swapF_assoc (b : ℝ) : ∀ x y z, swapF b (swapF b x y) z = swapF b x (swapF b y z) := by
  intro x y z
  let ψ : ℝ ≃ ℝ := Equiv.swap (0 : ℝ) b
  have hψ : ∀ x y, ψ (swapF b x y) = ψ x + ψ y - 1 := by
    intro x y
    simp [swapF, ψ]
  apply ψ.injective
  have h1 : ψ (swapF b (swapF b x y) z) = ψ x + ψ y + ψ z - 2 := by
    calc
      ψ (swapF b (swapF b x y) z) = ψ (swapF b x y) + ψ z - 1 := by
        simp [swapF, ψ]
      _ = (ψ x + ψ y - 1) + ψ z - 1 := by simp [hψ]
      _ = ψ x + ψ y + ψ z - 2 := by ring
  have h2 : ψ (swapF b x (swapF b y z)) = ψ x + ψ y + ψ z - 2 := by
    calc
      ψ (swapF b x (swapF b y z)) = ψ x + ψ (swapF b y z) - 1 := by
        simp [swapF, ψ]
      _ = ψ x + (ψ y + ψ z - 1) - 1 := by simp [hψ]
      _ = ψ x + ψ y + ψ z - 2 := by ring
  simp [h1, h2]

private lemma swapF_one_left (b : ℝ) (hb : b ≠ 1) : ∀ y, swapF b 1 y = y := by
  intro y
  let ψ : ℝ ≃ ℝ := Equiv.swap (0 : ℝ) b
  have h1 : ψ 1 = (1 : ℝ) := by
    have h10 : (1 : ℝ) ≠ 0 := by norm_num
    have h1b : (1 : ℝ) ≠ b := by simpa using hb.symm
    simp [ψ, Equiv.swap_apply_of_ne_of_ne, h10, h1b]
  apply ψ.injective
  simp [swapF, ψ, h1]

private lemma swapF_one_right (b : ℝ) (hb : b ≠ 1) : ∀ x, swapF b x 1 = x := by
  intro x
  let ψ : ℝ ≃ ℝ := Equiv.swap (0 : ℝ) b
  have h1 : ψ 1 = (1 : ℝ) := by
    have h10 : (1 : ℝ) ≠ 0 := by norm_num
    have h1b : (1 : ℝ) ≠ b := by simpa using hb.symm
    simp [ψ, Equiv.swap_apply_of_ne_of_ne, h10, h1b]
  apply ψ.injective
  simp [swapF, ψ, h1]

private lemma swapF_discontinuous (b : ℝ) (hb : 1 < b) :
    ¬Continuous (Function.uncurry (swapF b)) := by
  intro hcont
  let g : ℝ → ℝ := fun x => swapF b x b
  have hg_cont : Continuous g := by
    have hpair : Continuous fun x : ℝ => (x, b) := continuous_id.prodMk continuous_const
    simpa [g] using! hcont.comp hpair
  have hbpos : (0 : ℝ) < b := lt_trans (by norm_num) hb
  have hb1ne0 : b - 1 ≠ 0 := by linarith
  have hb1neb : b - 1 ≠ b := by linarith
  have hswap_b1 : Equiv.swap (0 : ℝ) b (b - 1) = b - 1 := by
    exact Equiv.swap_apply_of_ne_of_ne hb1ne0 hb1neb
  have hg0 : g 0 = b - 1 := by
    calc
      g 0 = Equiv.swap (0 : ℝ) b (b + 0 - 1) := by
        simp [g, swapF, Equiv.swap_apply_left, Equiv.swap_apply_right]
      _ = Equiv.swap (0 : ℝ) b (b - 1) := by simp
      _ = b - 1 := hswap_b1
  have hseq_val : ∀ n : ℕ, g ((n : ℝ) + 2)⁻¹ = ((n : ℝ) + 2)⁻¹ - 1 := by
    intro n
    have hden : 0 < (n : ℝ) + 2 := by nlinarith
    have hxpos : 0 < ((n : ℝ) + 2)⁻¹ := by
      have hxpos' : 0 < (1 : ℝ) / ((n : ℝ) + 2) := one_div_pos.mpr hden
      simpa [one_div] using hxpos'
    have hxlt1 : ((n : ℝ) + 2)⁻¹ < 1 := by
      have hpos : (0 : ℝ) < 1 := by norm_num
      have hlt : (1 : ℝ) < (n : ℝ) + 2 := by nlinarith
      have h := one_div_lt_one_div_of_lt hpos hlt
      simpa [one_div] using h
    have hx0 : ((n : ℝ) + 2)⁻¹ ≠ 0 := ne_of_gt hxpos
    have hxb : ((n : ℝ) + 2)⁻¹ ≠ b := by
      exact ne_of_lt (lt_trans hxlt1 hb)
    have hxneg : ((n : ℝ) + 2)⁻¹ - 1 < 0 := sub_lt_zero.mpr hxlt1
    have hx1ne0 : ((n : ℝ) + 2)⁻¹ - 1 ≠ 0 := ne_of_lt hxneg
    have hx1neb : ((n : ℝ) + 2)⁻¹ - 1 ≠ b := by
      have hx1ltb : ((n : ℝ) + 2)⁻¹ - 1 < b := lt_trans hxneg hbpos
      exact ne_of_lt hx1ltb
    have hswap_x : Equiv.swap (0 : ℝ) b ((n : ℝ) + 2)⁻¹ = ((n : ℝ) + 2)⁻¹ := by
      exact Equiv.swap_apply_of_ne_of_ne hx0 hxb
    have hswap_b : Equiv.swap (0 : ℝ) b b = (0 : ℝ) := by
      simp [Equiv.swap_apply_right]
    have hswap_x1 :
        Equiv.swap (0 : ℝ) b (((n : ℝ) + 2)⁻¹ - 1) = ((n : ℝ) + 2)⁻¹ - 1 := by
      simpa using (Equiv.swap_apply_of_ne_of_ne hx1ne0 hx1neb)
    calc
      g ((n : ℝ) + 2)⁻¹
          = Equiv.swap (0 : ℝ) b
              (Equiv.swap (0 : ℝ) b ((n : ℝ) + 2)⁻¹ + Equiv.swap (0 : ℝ) b b - 1) := by
                simp [g, swapF]
      _ = Equiv.swap (0 : ℝ) b (((n : ℝ) + 2)⁻¹ + 0 - 1) := by
        simp [hswap_x, hswap_b]
      _ = Equiv.swap (0 : ℝ) b (((n : ℝ) + 2)⁻¹ - 1) := by simp
      _ = ((n : ℝ) + 2)⁻¹ - 1 := hswap_x1
  have hx : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (𝓝 0) := by
    have hbase : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hshift :=
      (tendsto_add_atTop_iff_nat (f := fun n : ℕ => ((n : ℝ) + 1)⁻¹) 1).2 hbase
    simpa [one_add_one_eq_two, add_assoc, add_comm, add_left_comm] using hshift
  have hx' : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹ - 1) atTop (𝓝 (-1)) := by
    simpa using (hx.sub tendsto_const_nhds)
  have hseq : Tendsto (fun n : ℕ => g ((n : ℝ) + 2)⁻¹) atTop (𝓝 (-1)) := by
    have hfun :
        (fun n : ℕ => g ((n : ℝ) + 2)⁻¹) =
          fun n : ℕ => ((n : ℝ) + 2)⁻¹ - 1 := funext hseq_val
    simpa [hfun] using hx'
  have hcont0 : Tendsto (fun n : ℕ => g ((n : ℝ) + 2)⁻¹) atTop (𝓝 (g 0)) :=
    (hg_cont.tendsto 0).comp hx
  have hg0eq' : (-1 : ℝ) = g 0 :=
    tendsto_nhds_unique (l := atTop) (f := fun n : ℕ => g ((n : ℝ) + 2)⁻¹) hseq hcont0
  have hg0eq : g 0 = (-1 : ℝ) := hg0eq'.symm
  have hg0ne : g 0 ≠ (-1 : ℝ) := by
    have hb1pos : (0 : ℝ) < b - 1 := by linarith
    have hb1ne : b - 1 ≠ (-1 : ℝ) := by
      exact ne_of_gt (lt_trans (by norm_num : (-1 : ℝ) < 0) hb1pos)
    simpa [hg0] using hb1ne
  exact (hg0ne hg0eq).elim

/-- Transport the unital operation `x + y - 1` through a swap bijection. -/
private def swapRule (b : ℝ) (hb : b ≠ 1) : AssociativeUnitalRule where
  F := swapF b
  F_assoc := swapF_assoc b
  F_one_left := swapF_one_left b hb
  F_one_right := swapF_one_right b hb

/-- An associative unital rule can be discontinuous and different from multiplication. -/
theorem nonstandard_unital_rule_exists :
    ∃ C : AssociativeUnitalRule, ¬Continuous (Function.uncurry C.F) ∧ C.F ≠ standardF := by
  refine ⟨swapRule 2 (by norm_num), swapF_discontinuous 2 (by norm_num), ?_⟩
  intro h
  have hv := congrArg (fun F => F 0 2) h
  norm_num [swapRule, swapF, standardF, Equiv.swap_apply_def] at hv

/-- Pure associativity and identity admit distinct discontinuous operations. -/
theorem associative_unital_nonuniqueness :
    ∃ C₁ C₂ : AssociativeUnitalRule,
      ¬Continuous (Function.uncurry C₁.F) ∧ ¬Continuous (Function.uncurry C₂.F) ∧ C₁.F ≠ C₂.F := by
  refine ⟨swapRule 2 (by norm_num), swapRule 3 (by norm_num),
    swapF_discontinuous 2 (by norm_num), swapF_discontinuous 3 (by norm_num), ?_⟩
  intro h
  have hv := congrArg (fun F => F 0 2) h
  norm_num [swapRule, swapF, Equiv.swap_apply_def] at hv

/-- This example fails the Cox probability-range hypothesis on valid inputs. -/
theorem swap_violates_range : swapF 2 (1 / 2) (1 / 2) > 1 := by
  norm_num [swapF, Equiv.swap_apply_def]

/-- It also fails strict monotonicity on valid inputs, independently of continuity. -/
theorem swap_violates_order :
    ¬StrictMonoOn (fun x => swapF 2 x (1 / 2)) (Set.Ioc 0 1) := by
  intro h
  have hv := h (by norm_num : (1 / 2 : ℝ) ∈ Set.Ioc 0 1)
    (by norm_num : (1 : ℝ) ∈ Set.Ioc 0 1) (by norm_num)
  norm_num [swapF, Equiv.swap_apply_def] at hv

/-- The graph of any discontinuous additive function is dense in ℝ² -/
theorem discontinuousAdditive_graph_dense (f : ℝ →+ ℝ) (hdisc : ¬Continuous f) :
    Dense {p : ℝ × ℝ | p.2 = f p.1} := by
  classical
  have hf_rat : ∀ q : ℚ, ∀ x, f (q • x) = q • f x := by
    intro q x
    exact map_rat_smul f q x
  have hf_rat_mul : ∀ q : ℚ, ∀ x, f ((q : ℝ) * x) = (q : ℝ) * f x := by
    intro q x
    have hcast_x : (q : ℝ) * x = q • x := by
      simpa [smul_eq_mul] using (Rat.cast_smul_eq_qsmul (R := ℝ) (q := q) (x := x))
    have hcast_fx : (q : ℝ) * f x = q • f x := by
      simpa [smul_eq_mul] using (Rat.cast_smul_eq_qsmul (R := ℝ) (q := q) (x := f x))
    calc
      f ((q : ℝ) * x) = f (q • x) := by
        simp [hcast_x]
      _ = q • f x := hf_rat q x
      _ = (q : ℝ) * f x := by
        simp [hcast_fx]
  have hx0 : ∃ x, f x ≠ f 1 * x := by
    by_contra h
    push Not at h
    have hcont : Continuous f := by
      have hfun : f = fun x => f 1 * x := funext h
      refine hfun ▸ (continuous_const.mul continuous_id)
    exact hdisc hcont
  rcases hx0 with ⟨x0, hx0⟩
  let det : ℝ := f x0 - f 1 * x0
  have hdet : det ≠ 0 := sub_ne_zero.mpr hx0
  let L : ℝ × ℝ → ℝ × ℝ :=
    fun p => (p.1 + p.2 * x0, p.1 * f 1 + p.2 * f x0)
  have hL_cont : Continuous L := by
    refine (continuous_fst.add (continuous_snd.mul continuous_const)).prodMk ?_
    exact (continuous_fst.mul continuous_const).add (continuous_snd.mul continuous_const)
  have hL_surj : Function.Surjective L := by
    intro p
    let b : ℝ := (p.2 - p.1 * f 1) / det
    let a : ℝ := p.1 - b * x0
    refine ⟨(a, b), ?_⟩
    ext
    · simp [L, a, add_comm, add_left_comm, sub_eq_add_neg]
    ·
      have hbdet : b * det = p.2 - p.1 * f 1 := by
        simp [b, det, hdet]
      calc
        a * f 1 + b * f x0
            = (p.1 - b * x0) * f 1 + b * f x0 := by simp [a]
        _ = p.1 * f 1 + b * (f x0 - x0 * f 1) := by ring
        _ = p.1 * f 1 + b * det := by simp [det, mul_comm]
        _ = p.1 * f 1 + (p.2 - p.1 * f 1) := by simp [hbdet]
        _ = p.2 := by ring
  have hL_dense : DenseRange L := Function.Surjective.denseRange hL_surj
  let f_rat : ℚ × ℚ → ℝ × ℝ :=
    fun q => ((q.1 : ℝ), (q.2 : ℝ))
  have hRat : DenseRange f_rat := by
    have hQ : DenseRange (fun q : ℚ => (q : ℝ)) := Rat.denseRange_cast
    simpa [f_rat] using! (DenseRange.prodMap hQ hQ)
  have hDenseRange : DenseRange (L ∘ f_rat) :=
    DenseRange.comp hL_dense hRat hL_cont
  have hDense : Dense (Set.range (L ∘ f_rat)) := by
    simpa [DenseRange] using hDenseRange
  have hsubset : Set.range (L ∘ f_rat) ⊆ {p : ℝ × ℝ | p.2 = f p.1} := by
    rintro p ⟨q, rfl⟩
    have h1 : f (q.1 : ℝ) = (q.1 : ℝ) * f 1 := by
      simpa using (hf_rat_mul q.1 1)
    have h2 : f ((q.2 : ℝ) * x0) = (q.2 : ℝ) * f x0 := by
      simpa using (hf_rat_mul q.2 x0)
    dsimp [L, f_rat]
    calc
      (q.1 : ℝ) * f 1 + (q.2 : ℝ) * f x0
          = f (q.1 : ℝ) + f ((q.2 : ℝ) * x0) := by
            simp [h1, h2]
      _ = f ((q.1 : ℝ) + (q.2 : ℝ) * x0) := by
            symm
            exact map_add f (q.1 : ℝ) ((q.2 : ℝ) * x0)
  exact Dense.mono hsubset hDense

end

end Mettapedia.ProbabilityTheory.Cox.DiscontinuousCounterexample
