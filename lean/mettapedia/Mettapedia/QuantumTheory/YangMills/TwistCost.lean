import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.ZMod.Basic

/-!
# The classical cost of a twist

Take a lattice torus with two cyclic directions of length `L` and a finite set `Y`
of transverse positions, `U(1)` link angles `θ₀`, `θ₁` in the two cyclic
directions, and flip the sign of the Wilson weight of the plaquette `(-1, -1)` in
every `(0,1)`-plane.  The plaquette angles of a plane sum to zero
(`sum_plaquetteAngle`), so after the flip the shifted angles sum to `π`.  Reducing
each one to `(-π, π]` keeps their sum at an odd multiple of `π`, Jordan's
inequality gives `1 - cos x ≥ 2x²/π²` there, and Cauchy–Schwarz spreads the sum
over the `L²` plaquettes.  So every configuration has twisted action at least
`2 |Y| / L²` in those planes (`twistedAction_ge`), while the configuration with
uniform field strength `π/L²` has action at most `π² |Y| / (2 L²)`
(`exists_twistedAction_le`).

On `(ℤ/L)^d` the transverse set has `L^{d-2}` elements
(`twistedAction_torus_bounds`): the minimal classical cost of the twist, in units of
the coupling, lies between `2 L^{d-4}` and `π² L^{d-4}/2`.  It is bounded in four
dimensions and grows linearly in the side in five.  Only the `(0,1)`-planes are
modelled: the plaquettes of the other planes add nonnegative terms to the full
Wilson action, and they vanish for the uniform configuration, whose link angles do
not depend on the transverse position.  In `SU(2)` the same twist costs no
classical action (`TwistEater`).
-/

set_option autoImplicit false
noncomputable section

open Finset Real

namespace Mettapedia.QuantumTheory.YangMills.TwistCost

variable {L : ℕ} [NeZero L] {Y : Type*} [Fintype Y]

/-- The `(0,1)`-plaquette angle with corner `(a, b)` at the transverse position `y`. -/
def plaquetteAngle (θ₀ θ₁ : ZMod L × ZMod L × Y → ℝ) (a b : ZMod L) (y : Y) : ℝ :=
  θ₀ (a, b, y) + θ₁ (a + 1, b, y) - θ₀ (a, b + 1, y) - θ₁ (a, b, y)

/-- The sign of the Wilson weight, flipped at the plaquette `(-1, -1)` of every plane. -/
def twistSign (a b : ZMod L) : ℝ :=
  if a = -1 ∧ b = -1 then -1 else 1

/-- The twisted Wilson action of the `(0,1)`-plaquettes, per unit coupling. -/
def twistedAction (θ₀ θ₁ : ZMod L × ZMod L × Y → ℝ) : ℝ :=
  ∑ y : Y, ∑ a : ZMod L, ∑ b : ZMod L,
    (1 - twistSign a b * Real.cos (plaquetteAngle θ₀ θ₁ a b y))

omit [Fintype Y] in
/-- The plaquette angles of a plane sum to zero. -/
theorem sum_plaquetteAngle (θ₀ θ₁ : ZMod L × ZMod L × Y → ℝ) (y : Y) :
    ∑ a : ZMod L, ∑ b : ZMod L, plaquetteAngle θ₀ θ₁ a b y = 0 := by
  have h1 : ∑ a : ZMod L, ∑ b : ZMod L, θ₁ (a + 1, b, y) =
      ∑ a : ZMod L, ∑ b : ZMod L, θ₁ (a, b, y) :=
    Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun _ => rfl)
  have h0 : ∑ a : ZMod L, ∑ b : ZMod L, θ₀ (a, b + 1, y) =
      ∑ a : ZMod L, ∑ b : ZMod L, θ₀ (a, b, y) :=
    Finset.sum_congr rfl fun _ _ => Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun _ => rfl)
  simp only [plaquetteAngle, Finset.sum_add_distrib, Finset.sum_sub_distrib, h1, h0]
  ring

/-- Jordan's inequality in the form `2x²/π² ≤ 1 - cos x` for `|x| ≤ π`. -/
theorem two_mul_sq_div_le_one_sub_cos {x : ℝ} (hx : |x| ≤ π) :
    2 * x ^ 2 / π ^ 2 ≤ 1 - Real.cos x := by
  have hpi := Real.pi_pos
  have hc2 : Real.cos (2 * (|x| / 2)) = 1 - 2 * Real.sin (|x| / 2) ^ 2 := by
    rw [Real.cos_two_mul, Real.cos_sq']
    ring
  rw [show 2 * (|x| / 2) = |x| by ring, Real.cos_abs] at hc2
  have hj := Real.mul_le_sin (x := |x| / 2) (by positivity) (by linarith)
  have h2 : |x| / π ≤ Real.sin (|x| / 2) := by
    calc |x| / π = 2 / π * (|x| / 2) := by field_simp
      _ ≤ _ := hj
  have h3 : (|x| / π) ^ 2 ≤ Real.sin (|x| / 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h2 2
  rw [hc2, ← sq_abs x]
  rw [div_pow] at h3
  have h4 : 2 * |x| ^ 2 / π ^ 2 = 2 * (|x| ^ 2 / π ^ 2) := by ring
  rw [h4]
  linarith

/-- An integer multiple of `2π` shifted by `π` has absolute value at least `π`. -/
theorem pi_le_abs_pi_sub_int_mul (m : ℤ) : π ≤ |π - 2 * π * m| := by
  have hpi := Real.pi_pos
  rcases le_or_gt m 0 with hm | hm
  · have : (m : ℝ) ≤ 0 := by exact_mod_cast hm
    rw [abs_of_nonneg (by nlinarith)]
    nlinarith
  · have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    rw [abs_of_nonpos (by nlinarith)]
    nlinarith

/-- **The cost of a flux `π` spread over `n` plaquettes.**  If real angles sum to `π`
over a set of `n > 0` indices, the sum of `1 - cos` is at least `2 / n`. -/
theorem two_div_le_sum_one_sub_cos {ι : Type*} (s : Finset ι) (hs : 0 < s.card) (φ : ι → ℝ)
    (hφ : ∑ i ∈ s, φ i = π) : 2 / s.card ≤ ∑ i ∈ s, (1 - Real.cos (φ i)) := by
  have hpi := Real.pi_pos
  have h2pi : (0 : ℝ) < 2 * π := by positivity
  set ψ : ι → ℝ := fun i => toIocMod h2pi (-π) (φ i) with hψ
  set k : ι → ℤ := fun i => toIocDiv h2pi (-π) (φ i) with hk
  have hdiff : ∀ i, φ i - ψ i = k i * (2 * π) := fun i => by
    rw [hψ, hk, self_sub_toIocMod, zsmul_eq_mul]
  have hcos : ∀ i, Real.cos (ψ i) = Real.cos (φ i) := fun i => by
    have : ψ i = φ i - k i * (2 * π) := by linarith [hdiff i]
    rw [this, Real.cos_sub_int_mul_two_pi]
  have habs : ∀ i, |ψ i| ≤ π := fun i => by
    have hmem := toIocMod_mem_Ioc h2pi (-π) (φ i)
    rw [abs_le]
    constructor
    · exact hmem.1.le
    · linarith [hmem.2]
  have hsum : ∑ i ∈ s, ψ i = π - 2 * π * ((∑ i ∈ s, k i : ℤ) : ℝ) := by
    have : ∑ i ∈ s, ψ i = ∑ i ∈ s, φ i - ∑ i ∈ s, (k i : ℝ) * (2 * π) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by linarith [hdiff i]
    rw [this, hφ, ← Finset.sum_mul]
    push_cast
    ring
  have hpiabs : π ≤ |∑ i ∈ s, ψ i| := by
    rw [hsum]
    exact pi_le_abs_pi_sub_int_mul _
  have hsq : π ^ 2 ≤ (∑ i ∈ s, ψ i) ^ 2 := by
    rw [← sq_abs (∑ i ∈ s, ψ i)]
    exact pow_le_pow_left₀ hpi.le hpiabs 2
  have hcs := sq_sum_le_card_mul_sum_sq (s := s) (f := ψ)
  have hn : (0 : ℝ) < s.card := by exact_mod_cast hs
  have hsum2 : π ^ 2 / s.card ≤ ∑ i ∈ s, ψ i ^ 2 := by
    rw [div_le_iff₀ hn]
    linarith
  calc 2 / (s.card : ℝ) = 2 / π ^ 2 * (π ^ 2 / s.card) := by field_simp
    _ ≤ 2 / π ^ 2 * ∑ i ∈ s, ψ i ^ 2 :=
        mul_le_mul_of_nonneg_left hsum2 (by positivity)
    _ = ∑ i ∈ s, 2 * ψ i ^ 2 / π ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ ∑ i ∈ s, (1 - Real.cos (ψ i)) :=
        Finset.sum_le_sum fun i _ => two_mul_sq_div_le_one_sub_cos (habs i)
    _ = ∑ i ∈ s, (1 - Real.cos (φ i)) := Finset.sum_congr rfl fun i _ => by rw [hcos i]

/-- **Lower bound.**  Every configuration has twisted action at least `2 |Y| / L²`. -/
theorem twistedAction_ge (θ₀ θ₁ : ZMod L × ZMod L × Y → ℝ) :
    2 * Fintype.card Y / (L : ℝ) ^ 2 ≤ twistedAction θ₀ θ₁ := by
  classical
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hslice : ∀ y : Y, 2 / (L : ℝ) ^ 2 ≤ ∑ a : ZMod L, ∑ b : ZMod L,
      (1 - twistSign a b * Real.cos (plaquetteAngle θ₀ θ₁ a b y)) := by
    intro y
    set φ : ZMod L × ZMod L → ℝ := fun p =>
      plaquetteAngle θ₀ θ₁ p.1 p.2 y + (if p.1 = -1 ∧ p.2 = -1 then π else 0) with hφ
    have hterm : ∀ p : ZMod L × ZMod L,
        1 - twistSign p.1 p.2 * Real.cos (plaquetteAngle θ₀ θ₁ p.1 p.2 y) =
          1 - Real.cos (φ p) := by
      intro p
      simp only [hφ, twistSign]
      split_ifs
      · rw [Real.cos_add_pi]
        ring
      · rw [add_zero, one_mul]
    have hsumφ : ∑ p : ZMod L × ZMod L, φ p = π := by
      simp only [hφ, Finset.sum_add_distrib]
      rw [Fintype.sum_prod_type' (fun a b => plaquetteAngle θ₀ θ₁ a b y),
        sum_plaquetteAngle, zero_add]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
      have : (Finset.univ.filter fun p : ZMod L × ZMod L => p.1 = -1 ∧ p.2 = -1) =
          {((-1 : ZMod L), (-1 : ZMod L))} := by
        ext p
        simp [Prod.ext_iff]
      rw [this, Finset.card_singleton, one_smul]
    have hcard : (Finset.univ : Finset (ZMod L × ZMod L)).card = L * L := by
      rw [Finset.card_univ, Fintype.card_prod, ZMod.card]
    have hpos : 0 < (Finset.univ : Finset (ZMod L × ZMod L)).card := by
      rw [hcard]
      exact Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (Nat.pos_of_ne_zero (NeZero.ne L))
    have h := two_div_le_sum_one_sub_cos Finset.univ hpos φ hsumφ
    rw [hcard] at h
    push_cast at h
    calc 2 / (L : ℝ) ^ 2 = 2 / ((L : ℝ) * L) := by ring
      _ ≤ ∑ p : ZMod L × ZMod L, (1 - Real.cos (φ p)) := h
      _ = ∑ p : ZMod L × ZMod L,
            (1 - twistSign p.1 p.2 * Real.cos (plaquetteAngle θ₀ θ₁ p.1 p.2 y)) :=
          Finset.sum_congr rfl fun p _ => (hterm p).symm
      _ = _ := Fintype.sum_prod_type' (fun a b =>
            1 - twistSign a b * Real.cos (plaquetteAngle θ₀ θ₁ a b y))
  calc 2 * Fintype.card Y / (L : ℝ) ^ 2 = ∑ _y : Y, 2 / (L : ℝ) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
    _ ≤ twistedAction θ₀ θ₁ := Finset.sum_le_sum fun y _ => hslice y

section Upper

variable [Fact (1 < L)]

theorem val_neg_one_eq : (-1 : ZMod L).val = L - 1 := by
  simp [ZMod.neg_val, ZMod.val_one]

theorem val_add_one_of_ne {a : ZMod L} (ha : a ≠ -1) : (a + 1).val = a.val + 1 := by
  rw [ZMod.val_add, ZMod.val_one]
  apply Nat.mod_eq_of_lt
  have hlt := ZMod.val_lt a
  rcases Nat.lt_or_ge (a.val + 1) L with h | h
  · exact h
  · exfalso
    apply ha
    apply ZMod.val_injective
    rw [val_neg_one_eq]
    omega

/-- The configuration with uniform field strength `π/L²`: `θ₁` grows along the first
direction, and `θ₀` carries the return flux on the last column. -/
def uniformθ₀ (p : ZMod L × ZMod L × Y) : ℝ :=
  if p.1 = -1 then -(π / L) * (p.2.1.val : ℝ) else 0

/-- See `uniformθ₀`. -/
def uniformθ₁ (p : ZMod L × ZMod L × Y) : ℝ :=
  π / (L : ℝ) ^ 2 * (p.1.val : ℝ)

omit [Fintype Y] in
theorem twistSign_mul_cos_uniform (a b : ZMod L) (y : Y) :
    twistSign a b * Real.cos (plaquetteAngle (uniformθ₀ (L := L) (Y := Y)) uniformθ₁ a b y) =
      Real.cos (π / (L : ℝ) ^ 2) := by
  have hL1 : 1 ≤ L := (Fact.out : 1 < L).le
  have hL : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hcastL : ((L - 1 : ℕ) : ℝ) = L - 1 := by rw [Nat.cast_sub hL1, Nat.cast_one]
  by_cases ha : a = -1
  · subst ha
    have hz : (-1 + 1 : ZMod L) = 0 := by ring
    by_cases hb : b = -1
    · subst hb
      have hP : plaquetteAngle (uniformθ₀ (L := L) (Y := Y)) uniformθ₁ (-1) (-1) y =
          π / (L : ℝ) ^ 2 - π := by
        simp only [plaquetteAngle, uniformθ₀, uniformθ₁, hz, ↓reduceIte, ZMod.val_zero,
          Nat.cast_zero, val_neg_one_eq, hcastL]
        field_simp
        ring
      rw [hP, Real.cos_sub_pi]
      simp [twistSign]
    · have hP : plaquetteAngle (uniformθ₀ (L := L) (Y := Y)) uniformθ₁ (-1) b y =
          π / (L : ℝ) ^ 2 := by
        simp only [plaquetteAngle, uniformθ₀, uniformθ₁, hz, ↓reduceIte, ZMod.val_zero,
          Nat.cast_zero, val_neg_one_eq, hcastL, val_add_one_of_ne hb]
        push_cast
        field_simp
        ring
      rw [hP]
      simp [twistSign, hb]
  · have hP : plaquetteAngle (uniformθ₀ (L := L) (Y := Y)) uniformθ₁ a b y = π / (L : ℝ) ^ 2 := by
      simp only [plaquetteAngle, uniformθ₀, uniformθ₁, ha, ↓reduceIte, val_add_one_of_ne ha]
      push_cast
      ring
    rw [hP]
    simp [twistSign, ha]

/-- **Upper bound.**  The uniform configuration has twisted action at most
`π² |Y| / (2 L²)`. -/
theorem exists_twistedAction_le :
    ∃ θ₀ θ₁ : ZMod L × ZMod L × Y → ℝ,
      twistedAction θ₀ θ₁ ≤ π ^ 2 * Fintype.card Y / (2 * (L : ℝ) ^ 2) := by
  refine ⟨uniformθ₀, uniformθ₁, ?_⟩
  have hL : (0 : ℝ) < L := by
    exact_mod_cast (show 0 < L from lt_trans Nat.zero_lt_one (Fact.out : 1 < L))
  have hval : twistedAction (uniformθ₀ (L := L) (Y := Y)) uniformθ₁ =
      Fintype.card Y * ((L : ℝ) * L) * (1 - Real.cos (π / (L : ℝ) ^ 2)) := by
    simp only [twistedAction, twistSign_mul_cos_uniform, Finset.sum_const, Finset.card_univ,
      ZMod.card, nsmul_eq_mul]
    ring
  rw [hval]
  have hcos := Real.one_sub_sq_div_two_le_cos (x := π / (L : ℝ) ^ 2)
  have hY : (0 : ℝ) ≤ Fintype.card Y := Nat.cast_nonneg _
  calc (Fintype.card Y : ℝ) * ((L : ℝ) * L) * (1 - Real.cos (π / (L : ℝ) ^ 2))
      ≤ Fintype.card Y * ((L : ℝ) * L) * ((π / (L : ℝ) ^ 2) ^ 2 / 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
    _ = π ^ 2 * Fintype.card Y / (2 * (L : ℝ) ^ 2) := by
        field_simp

/-- **On `(ℤ/L)^d`.**  With `m = d - 2` transverse directions, the minimal twisted
action lies between `2 L^m / L²` and `π² L^m / (2 L²)`. -/
theorem twistedAction_torus_bounds (m : ℕ) :
    (∀ θ₀ θ₁ : ZMod L × ZMod L × (Fin m → ZMod L) → ℝ,
      2 * (L : ℝ) ^ m / (L : ℝ) ^ 2 ≤ twistedAction θ₀ θ₁) ∧
    ∃ θ₀ θ₁ : ZMod L × ZMod L × (Fin m → ZMod L) → ℝ,
      twistedAction θ₀ θ₁ ≤ π ^ 2 * (L : ℝ) ^ m / (2 * (L : ℝ) ^ 2) := by
  have hcard : (Fintype.card (Fin m → ZMod L) : ℝ) = (L : ℝ) ^ m := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    push_cast
    ring
  refine ⟨fun θ₀ θ₁ => ?_, ?_⟩
  · have h := twistedAction_ge θ₀ θ₁
    rwa [hcard] at h
  · obtain ⟨θ₀, θ₁, h⟩ := exists_twistedAction_le (L := L) (Y := Fin m → ZMod L)
    exact ⟨θ₀, θ₁, by rwa [hcard] at h⟩

end Upper

#print axioms twistedAction_ge
#print axioms exists_twistedAction_le
#print axioms twistedAction_torus_bounds

end Mettapedia.QuantumTheory.YangMills.TwistCost
