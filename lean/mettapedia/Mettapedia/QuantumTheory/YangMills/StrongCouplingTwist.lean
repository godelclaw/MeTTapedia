import Mettapedia.QuantumTheory.YangMills.StrongCouplingCrossing
import Mettapedia.QuantumTheory.YangMills.TwistDiagnostic

/-!
# Centre twists at strong coupling

A central involution acts on link variables by measure-preserving left
multiplication. Flipping a slice of links moves a plaquette twist by one lattice
step. The connected plaquette expansion therefore has position-independent
integrated twisted activities, while activities away from the stack are unchanged.
The dimension is `d + 2`, where `d` counts transverse directions. At the explicit
strong-coupling threshold, these activities form a twist-compatible crossing
family, and the real Wilson twist free energy tends to zero with the volume.
-/

set_option autoImplicit false
noncomputable section

open Finset MeasureTheory Filter Topology
open Mettapedia.Combinatorics.PolymerGas
open Mettapedia.QuantumTheory.YangMills.StrongCouplingCrossing

namespace Mettapedia.QuantumTheory.YangMills.StrongCouplingTwist

variable {E : Type*} [Group E]

/-- The positively oriented plaquette product in boundary order. -/
def holonomy (v : Fin 4 → E) : E := v 0 * v 1 * (v 2)⁻¹ * (v 3)⁻¹

/-- Plaquettes of the `(0,1)` stack at the specified first coordinate. -/
def onStack {d n : ℕ} (a : ZMod (n + 3)) (p : Plaquette (d + 2) n) : Prop :=
  p.2.1.1 = 0 ∧ p.2.1.2 = 1 ∧ p.1 0 = a ∧ p.1 1 = 0

instance {d n : ℕ} (a : ZMod (n + 3)) (p : Plaquette (d + 2) n) :
    Decidable (onStack a p) := by unfold onStack; infer_instance

/-- Links on the slice that moves the twist from `a` to `a + 1`. -/
def onSlice {d n : ℕ} (a : ZMod (n + 3)) (l : Link (d + 2) n) : Prop :=
  l.2 = 1 ∧ l.1 0 = a + 1 ∧ l.1 1 = 0

instance {d n : ℕ} (a : ZMod (n + 3)) (l : Link (d + 2) n) :
    Decidable (onSlice a l) := by unfold onSlice; infer_instance

/-- Multiply each selected link by the centre element. -/
def move {d n : ℕ} (z : E) (a : ZMod (n + 3)) (ω : Link (d + 2) n → E) :
    Link (d + 2) n → E := fun l => if onSlice a l then z * ω l else ω l

/-- The plaquette product with a centre twist on one stack. -/
def twistedHolonomy {d n : ℕ} (z : E) (a : ZMod (n + 3))
    (p : Plaquette (d + 2) n) (ω : Link (d + 2) n → E) : E :=
  if onStack a p then z * holonomy (fun i => ω (linkAt p i))
  else holonomy (fun i => ω (linkAt p i))

theorem central_pull {z : E} (hz : ∀ g, z * g = g * z) (g h : E) :
    g * (z * h) = z * (g * h) := by rw [← mul_assoc, ← hz g, mul_assoc]

theorem involution_inv {z : E} (hzz : z * z = 1) : z⁻¹ = z := by
  exact inv_eq_of_mul_eq_one_right hzz

theorem involution_cancel {z : E} (hzz : z * z = 1) (g : E) : z * (z * g) = g := by
  rw [← mul_assoc, hzz, one_mul]

theorem twistedHolonomy_move {d n : ℕ} {z : E}
    (hz : ∀ g, z * g = g * z) (hzz : z * z = 1)
    (a : ZMod (n + 3)) (p : Plaquette (d + 2) n) (ω : Link (d + 2) n → E) :
    twistedHolonomy z a p (move z a ω) = twistedHolonomy z (a + 1) p ω := by
  have h01 : (0 : Fin (d + 2)) ≠ 1 := by norm_num
  have hpull := central_pull hz
  have hright : ∀ g, g * z = z * g := fun g => (hz g).symm
  clear hz
  have ha : a + 1 ≠ a := by
    intro h
    have : (1 : ZMod (n + 3)) = 0 := by linear_combination h
    have hv := congrArg ZMod.val this
    rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega), ZMod.val_zero] at hv
    omega
  have hμν : p.2.1.1 ≠ p.2.1.2 := ne_of_lt p.2.2
  by_cases hν : p.2.1.2 = 1
  · have hμ : p.2.1.1 = 0 := by
      apply Fin.ext
      have := p.2.2
      rw [hν] at this
      simpa only [Fin.lt_def, Fin.val_one, Fin.val_zero, Nat.lt_one_iff] using this
    by_cases hy : p.1 1 = 0 <;> by_cases hx : p.1 0 = a <;>
      by_cases hx' : p.1 0 = a + 1 <;>
      simp_all [twistedHolonomy, holonomy, move, onStack, onSlice, linkAt, step,
        mul_inv_rev, involution_inv hzz, mul_assoc, involution_cancel hzz]
  · by_cases hμ : p.2.1.1 = 1
    · have hν0 : p.2.1.2 ≠ 0 := by
        intro h
        have := p.2.2
        rw [h, hμ] at this
        exact (by simp : ¬ (1 : Fin (d + 2)) < 0) this
      by_cases hy : p.1 1 = 0 <;> by_cases hx' : p.1 0 = a + 1 <;>
        simp_all [twistedHolonomy, holonomy, move, onStack, onSlice, linkAt, step,
          Ne.symm hν0, mul_inv_rev, involution_inv hzz, mul_assoc,
          involution_cancel hzz]
    · simp [twistedHolonomy, holonomy, move, onStack, onSlice, linkAt, hν, hμ]

/-- All links belonging to a plaquette of the twist stack. -/
def stack (d n : ℕ) (a : ZMod (n + 3)) : Finset (Link (d + 2) n) :=
  (univ.filter (onStack a)).biUnion support

/-- The twisted local perturbation. -/
def twistedPerturbation {d n : ℕ} (z : E) (a : ZMod (n + 3)) (ψ : E → ℝ)
    (β : ℝ) (p : Plaquette (d + 2) n) (ω : Link (d + 2) n → E) : ℂ :=
  (Real.exp (-β * ψ (twistedHolonomy z a p ω)) : ℂ) - 1

/-- Connected activities of the twisted plaquette density. -/
def twistedActivity (d : ℕ) (z : E) (ψ : E → ℝ) (β : ℝ) (n : ℕ)
    (a : ZMod (n + 3)) (S : Finset (Link (d + 2) n)) : (S → E) → ℂ :=
  plaquetteActivity support 1 (twistedPerturbation z a ψ β) S

theorem twistedPerturbation_local {d n : ℕ} (z : E) (a : ZMod (n + 3))
    (ψ : E → ℝ) (β : ℝ) : PlaquetteLocal (support (d := d + 2) (n := n))
      (twistedPerturbation z a ψ β) := by
  intro p ω ω' h
  have he : (fun i => ω (linkAt p i)) = (fun i => ω' (linkAt p i)) := by
    funext i
    exact h _ (mem_image.mpr ⟨i, mem_univ _, rfl⟩)
  simp only [twistedPerturbation, twistedHolonomy, he]

theorem twistedPerturbation_move {d n : ℕ} {z : E}
    (hz : ∀ g, z * g = g * z) (hzz : z * z = 1)
    (a : ZMod (n + 3)) (ψ : E → ℝ) (β : ℝ) (p : Plaquette (d + 2) n)
    (ω : Link (d + 2) n → E) :
    twistedPerturbation z a ψ β p (move z a ω) =
      twistedPerturbation z (a + 1) ψ β p ω := by
  simp only [twistedPerturbation, twistedHolonomy_move hz hzz]

/-- Away from the stack the twisted activity is the ordinary Wilson activity. -/
theorem twistedActivity_eq_of_disjoint {d n : ℕ} (z : E) (a : ZMod (n + 3))
    (ψ : E → ℝ) (β : ℝ) (S : Finset (Link (d + 2) n)) (hS : Disjoint (stack d n a) S) :
    twistedActivity d z ψ β n a S = activity (d + 2) 1 (ψ ∘ holonomy) β n S := by
  funext v
  apply sum_congr rfl
  intro C hC
  have hCS := (mem_filter.mp hC).2
  apply prod_congr rfl
  intro p hp
  have hpnot : ¬ onStack a p := by
    intro hpa
    obtain ⟨l, hl⟩ := support_nonempty p
    have hlstack : l ∈ stack d n a :=
      mem_biUnion.mpr ⟨p, mem_filter.mpr ⟨mem_univ _, hpa⟩, hl⟩
    have hlS : l ∈ S := hCS ▸ mem_biUnion.mpr ⟨p, hp, hl⟩
    exact disjoint_left.mp hS hlstack hlS
  simp [twistedPerturbation, twistedHolonomy, hpnot, perturbation, potential]

/-- The stack lies within one unit of its first-coordinate circle position. -/
theorem stack_coordinate_dist {d n : ℕ} (a : ZMod (n + 3))
    {l : Link (d + 2) n} (hl : l ∈ stack d n a) :
    dist (coordinateCircle n a) (coordinateCircle n (l.1 0)) ≤ 1 := by
  obtain ⟨p, hp, hlp⟩ := mem_biUnion.mp hl
  have hpa := (mem_filter.mp hp).2
  obtain ⟨i, _, rfl⟩ := mem_image.mp hlp
  apply dist_coordinateCircle_le_one (Or.inl rfl)
  simpa only [hpa.2.2.1] using linkAt_coordinate p i 0

/-- A stack on the opposite side of the first cyclic coordinate. -/
def opposite (n : ℕ) : ZMod (n + 3) := ((n + 3) / 2 : ℕ)

/-- A lower bound for the separation of the two stacks. -/
def separation (n : ℕ) : ℝ := ((n + 3) / 2 : ℕ) - 2

theorem dist_opposite (n : ℕ) :
    dist (coordinateCircle n 0) (coordinateCircle n (opposite n)) = ((n + 3) / 2 : ℕ) := by
  have hlt : (n + 3) / 2 < n + 3 := Nat.div_lt_self (by omega) (by omega)
  have hle : (2 : ℝ) * ((n + 3) / 2 : ℕ) ≤ (n + 3 : ℝ) := by
    exact_mod_cast (show 2 * ((n + 3) / 2) ≤ n + 3 by omega)
  rw [map_zero, dist_zero_left, coordinateCircle_apply, opposite, ZMod.val_cast_of_lt hlt]
  rw [(AddCircle.norm_coe_eq_abs_iff (n + 3 : ℝ) (by positivity : (n + 3 : ℝ) ≠ 0)).mpr]
  · exact abs_of_nonneg (Nat.cast_nonneg _)
  · rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_pos (by positivity : (0 : ℝ) < n + 3)]
    linarith

/-- Opposite stacks have distance growing linearly with the torus side. -/
theorem stack_separation (d n : ℕ) (l : Link (d + 2) n) (hl : l ∈ stack d n 0)
    (m : Link (d + 2) n) (hm : m ∈ stack d n (opposite n)) :
    separation n ≤ dist l m := by
  have hl' := stack_coordinate_dist 0 hl
  have hm' := stack_coordinate_dist (opposite n) hm
  have ht := dist_triangle4 (coordinateCircle n 0) (coordinateCircle n (l.1 0))
    (coordinateCircle n (m.1 0)) (coordinateCircle n (opposite n))
  rw [dist_opposite, dist_comm (coordinateCircle n (m.1 0))] at ht
  have hc : dist (coordinateCircle n (l.1 0)) (coordinateCircle n (m.1 0)) ≤ dist l m :=
    dist_le_pi_dist (position l) (position m) 0
  unfold separation
  linarith

theorem separation_linear (n : ℕ) : (1 / 2 : ℝ) * n - 2 ≤ separation n := by
  have h : (n : ℝ) ≤ 2 * ((n + 3) / 2 : ℕ) := by
    exact_mod_cast (show n ≤ 2 * ((n + 3) / 2) by omega)
  unfold separation
  linarith

/-- A polynomial bound for the number of links touched by a stack. -/
theorem card_stack_le (d n : ℕ) (a : ZMod (n + 3)) :
    (stack d n a).card ≤ (n + 3) ^ (d + 2) * (d + 2) := by
  simpa only [Link, Site, Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    using card_le_univ (stack d n a)

/-- Polynomial stack size is dominated by the exponential separation factor. -/
theorem tendsto_stack_exp (d : ℕ) : ∀ κ > 0,
    Tendsto (fun n => ((stack d n 0).card : ℝ) * Real.exp (-κ * separation n)) atTop (𝓝 0) := by
  let Y : ∀ n, Finset (Link (d + 2) n) := fun n => if n = 0 then ∅ else stack d n 0
  have hY : ∀ n, ((Y n).card : ℝ) ≤
      ((d + 2 : ℝ) * 4 ^ (d + 2)) * (n : ℝ) ^ (d + 2) := by
    intro n
    by_cases hn : n = 0
    · simp [Y, hn]
    · have hc : ((stack d n 0).card : ℝ) ≤ (n + 3 : ℝ) ^ (d + 2) * (d + 2) := by
        exact_mod_cast card_stack_le d n 0
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ n + 3)
        (show (n + 3 : ℝ) ≤ 4 * n by linarith) (d + 2)
      simp only [Y, hn, ↓reduceIte]
      calc
        _ ≤ (n + 3 : ℝ) ^ (d + 2) * (d + 2) := hc
        _ ≤ (4 * (n : ℝ)) ^ (d + 2) * (d + 2) := mul_le_mul_of_nonneg_right hp (by positivity)
        _ = _ := by rw [mul_pow]; ring
  have hlim := TwistDiagnostic.tendsto_card_mul_exp_of_poly_linear
    (Blocks := fun n => Link (d + 2) n) (Y := Y) (D := separation)
    ((d + 2 : ℝ) * 4 ^ (d + 2)) (d + 2) (1 / 2) 2 (by norm_num) hY separation_linear
  intro κ hκ
  apply (hlim κ hκ).congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  simp [Y, ne_of_gt hn]

/-- The twisted perturbation obeys the same uniform bound as the untwisted one. -/
theorem norm_twistedPerturbation_le {d n : ℕ} (z : E) (a : ZMod (n + 3))
    {ψ : E → ℝ} (hψ0 : ∀ g, 0 ≤ ψ g) (hψ2 : ∀ g, ψ g ≤ 2)
    {β : ℝ} (hβ : 0 ≤ β) (p : Plaquette (d + 2) n) (ω : Link (d + 2) n → E) :
    ‖twistedPerturbation z a ψ β p ω‖ ≤ 2 * β := by
  have hp0 := hψ0 (twistedHolonomy z a p ω)
  have hp2 := hψ2 (twistedHolonomy z a p ω)
  have he : Real.exp (-β * ψ (twistedHolonomy z a p ω)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  unfold twistedPerturbation
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonpos (by linarith)]
  have := Real.add_one_le_exp (-β * ψ (twistedHolonomy z a p ω))
  nlinarith

/-- The common majorant satisfies volume-independent smallness. -/
theorem commonSmallness (d n : ℕ) {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 (d + 2)) :
    ActivitySmall (plaquetteMajorant (support (d := d + 2) (n := n)) (2 * β))
      1 (Real.exp (-1)) := by
  apply activitySmall_plaquetteMajorant support
    (δ := 2 * β) (κ := 1) (r := 1) (ε := Real.exp (-1))
    (s := 4) (Δ := 16 * ((d + 2) * (d + 2))) (D := 4 * ((d + 2) * (d + 2)))
    (by positivity) (by norm_num) (by norm_num) (Real.exp_pos _).le
  · rw [← Real.exp_add]
    norm_num
  · exact card_support_le
  · exact diam_support_le
  · intro p
    convert degree_plaquetteGraph_le (d + 2) n p using 1
    congr 1
    exact Subsingleton.elim _ _
  · exact card_incident_le (d + 2) n
  · unfold beta0 at hβ0
    linarith

section Measure

variable [MeasurableSpace E] [MeasurableMul₂ E] [MeasurableInv E]

theorem measurable_holonomy : Measurable (holonomy (E := E)) := by
  exact (((measurable_pi_apply 0).mul (measurable_pi_apply 1)).mul
    (measurable_pi_apply 2).inv).mul (measurable_pi_apply 3).inv

theorem measurable_twistedPerturbation {d n : ℕ} (z : E) (a : ZMod (n + 3))
    {ψ : E → ℝ} (hψ : Measurable ψ) (β : ℝ) (p : Plaquette (d + 2) n) :
    Measurable (twistedPerturbation z a ψ β p) := by
  have hh : Measurable (fun ω : Link (d + 2) n → E => holonomy (fun i => ω (linkAt p i))) :=
    measurable_holonomy.comp (measurable_pi_lambda _ fun _ => measurable_pi_apply _)
  have ht : Measurable (twistedHolonomy z a p) := by
    unfold twistedHolonomy
    split_ifs
    · exact measurable_const.mul hh
    · exact hh
  exact (Complex.measurable_ofReal.comp ((measurable_const.mul (hψ.comp ht)).exp)).sub
    measurable_const

theorem measurable_twistedActivity (d : ℕ) (z : E) {ψ : E → ℝ} (hψ : Measurable ψ)
    (β : ℝ) (n : ℕ) (a : ZMod (n + 3)) (S : Finset (Link (d + 2) n)) :
    Measurable (twistedActivity d z ψ β n a S) :=
  measurable_plaquetteActivity support 1 _ (measurable_twistedPerturbation z a hψ β) S

omit [MeasurableInv E] in
/-- Flipping a slice preserves the product reference measure. -/
theorem measurePreserving_move {d n : ℕ} (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (z : E) (hν : ν₀.map (fun g => z * g) = ν₀) (a : ZMod (n + 3)) :
    MeasurePreserving (move (d := d) z a) (Measure.pi fun _ => ν₀) (Measure.pi fun _ => ν₀) := by
  exact measurePreserving_pi (fun _ : Link (d + 2) n => ν₀) (fun _ => ν₀)
    (f := fun l g => if onSlice a l then z * g else g) (fun l => by
      by_cases hl : onSlice a l
      · simpa only [hl, ↓reduceIte] using
          (⟨measurable_const.mul measurable_id, hν⟩ :
            MeasurePreserving (fun g => z * g) ν₀ ν₀)
      · simp only [hl, ↓reduceIte]
        exact MeasurePreserving.id ν₀)

/-- One-step movement of the twist leaves every integrated activity unchanged. -/
theorem integratedActivity_step {d n : ℕ} (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    {z : E} (hz : ∀ g, z * g = g * z) (hzz : z * z = 1)
    (hν : ν₀.map (fun g => z * g) = ν₀) {ψ : E → ℝ} (hψ : Measurable ψ)
    (β : ℝ) (a : ZMod (n + 3)) (S : Finset (Link (d + 2) n)) :
    integratedActivity ν₀ (twistedActivity d z ψ β n a) S =
      integratedActivity ν₀ (twistedActivity d z ψ β n (a + 1)) S := by
  have hm := measurePreserving_move (d := d) ν₀ z hν a
  have hmeas := (measurable_twistedActivity d z hψ β n a S).comp (measurable_restrictTo S)
  have hi := integral_map hm.aemeasurable hmeas.aestronglyMeasurable
  rw [hm.map_eq] at hi
  simp only [Function.comp_apply] at hi
  unfold integratedActivity
  rw [hi]
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [twistedActivity, plaquetteActivity_restrictTo support 1 _
    (twistedPerturbation_local z a ψ β)]
  rw [twistedActivity, plaquetteActivity_restrictTo support 1 _
    (twistedPerturbation_local z (a + 1) ψ β)]
  apply sum_congr rfl
  intro C _
  exact prod_congr rfl fun p _ => twistedPerturbation_move hz hzz a ψ β p ω

/-- Moving the twist to any other position preserves its integrated activities. -/
theorem integratedActivity_movable {d n : ℕ} (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    {z : E} (hz : ∀ g, z * g = g * z) (hzz : z * z = 1)
    (hν : ν₀.map (fun g => z * g) = ν₀) {ψ : E → ℝ} (hψ : Measurable ψ)
    (β : ℝ) (a b : ZMod (n + 3)) (S : Finset (Link (d + 2) n)) :
    integratedActivity ν₀ (twistedActivity d z ψ β n a) S =
      integratedActivity ν₀ (twistedActivity d z ψ β n b) S := by
  have h : ∀ k : ℕ, integratedActivity ν₀ (twistedActivity d z ψ β n 0) S =
      integratedActivity ν₀ (twistedActivity d z ψ β n (k : ZMod (n + 3))) S := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      simpa only [Nat.cast_add, Nat.cast_one] using
        ih.trans (integratedActivity_step ν₀ hz hzz hν hψ β (k : ZMod (n + 3)) S)
  simpa using (h a.val).symm.trans (h b.val)

/-- The untwisted and centre-twisted gases form a twist-compatible crossing family. -/
theorem twistCompatibleCrossing (d : ℕ) (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    {z : E} (hz : ∀ g, z * g = g * z) (hzz : z * z = 1)
    (hν : ν₀.map (fun g => z * g) = ν₀) {ψ : E → ℝ} (hψ : Measurable ψ)
    (hψ0 : ∀ g, 0 ≤ ψ g) (hψ2 : ∀ g, ψ g ≤ 2)
    {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 (d + 2)) :
    TwistDiagnostic.TwistCompatibleCrossing (Link (d + 2)) E ν₀
      (activity (d + 2) 1 (ψ ∘ holonomy) β)
      (fun n => twistedActivity d z ψ β n 0) (fun n => stack d n 0) separation := by
  constructor
  · refine ⟨fun n => plaquetteMajorant (support (d := d + 2) (n := n)) (2 * β),
      1, Real.exp (-1), by norm_num, (Real.exp_pos _).le, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← Real.exp_add]
      norm_num
    · intro n S v
      exact norm_plaquetteActivity_le support 1 _
        (norm_perturbation_le (fun v => hψ0 _) (fun v => hψ2 _) hβ) S v
    · intro n S v
      exact norm_plaquetteActivity_le support 1 _
        (norm_twistedPerturbation_le z 0 hψ0 hψ2 hβ) S v
    · intro n
      exact plaquetteMajorant_empty support support_nonempty _
    · exact fun n => commonSmallness d n hβ hβ0
  · intro n γ hne
    exact TwistDiagnostic.differ_of_movable
      (activity (d + 2) 1 (ψ ∘ holonomy) β n) (twistedActivity d z ψ β n) (stack d n)
      (integratedActivity_movable ν₀ hz hzz hν hψ β)
      (fun a S hS => twistedActivity_eq_of_disjoint z a ψ β S hS)
      0 (opposite n) (stack_separation d n) γ hne

/-- The polymer logarithmic twist ratio tends to zero at strong coupling. -/
theorem tendsto_logTwistRatio (d : ℕ) (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    {z : E} (hz : ∀ g, z * g = g * z) (hzz : z * z = 1)
    (hν : ν₀.map (fun g => z * g) = ν₀) {ψ : E → ℝ} (hψ : Measurable ψ)
    (hψ0 : ∀ g, 0 ≤ ψ g) (hψ2 : ∀ g, ψ g ≤ 2)
    {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 (d + 2))
    (Λ : ∀ n, Finset (Finset (Link (d + 2) n))) :
    Tendsto (fun n => TwistDiagnostic.logTwistRatio (ν₀ := ν₀)
      (activity (d + 2) 1 (ψ ∘ holonomy) β) (fun n => twistedActivity d z ψ β n 0)
      n (Λ n)) atTop (𝓝 0) :=
  TwistDiagnostic.tendsto_logTwistRatio
    (twistCompatibleCrossing d ν₀ hz hzz hν hψ hψ0 hψ2 hβ hβ0) (tendsto_stack_exp d) Λ

/-- The twisted Wilson Boltzmann density. -/
def twistedDensity {d n : ℕ} (z : E) (a : ZMod (n + 3)) (ψ : E → ℝ)
    (β : ℝ) (ω : Link (d + 2) n → E) : ℂ :=
  ∏ p : Plaquette (d + 2) n, (Real.exp (-β * ψ (twistedHolonomy z a p ω)) : ℂ)

omit [MeasurableSpace E] [MeasurableMul₂ E] [MeasurableInv E] in
/-- The twisted density also has the exact connected polymer representation. -/
theorem twistedDensity_eq_polymerDensity (d n : ℕ) (z : E) (a : ZMod (n + 3))
    (ψ : E → ℝ) (β : ℝ) (ω : Link (d + 2) n → E) :
    twistedDensity z a ψ β ω = polymerDensity (twistedActivity d z ψ β n a) univ ω := by
  unfold twistedActivity
  convert prod_one_add_eq_polymerDensity support support_nonempty 1
    (twistedPerturbation z a ψ β) (twistedPerturbation_local z a ψ β) ω using 1
  simp [twistedDensity, twistedPerturbation]

/-- The ordinary finite-volume partition function, as a real Wilson integral. -/
def wilsonPartition (d n : ℕ) (ν₀ : Measure E) (ψ : E → ℝ) (β : ℝ) : ℝ :=
  ∫ ω : Link (d + 2) n → E,
    ∏ p : Plaquette (d + 2) n, Real.exp (-β * ψ (holonomy (fun i => ω (linkAt p i))))
      ∂(Measure.pi fun _ => ν₀)

/-- The partition function with one centre twist. -/
def twistedPartition (d n : ℕ) (ν₀ : Measure E) (z : E) (ψ : E → ℝ) (β : ℝ) : ℝ :=
  ∫ ω : Link (d + 2) n → E,
    ∏ p : Plaquette (d + 2) n, Real.exp (-β * ψ (twistedHolonomy z 0 p ω))
      ∂(Measure.pi fun _ => ν₀)

/-- The physical twist free energy `-log (Z_tw / Z)`. -/
def twistFreeEnergy (d n : ℕ) (ν₀ : Measure E) (z : E) (ψ : E → ℝ) (β : ℝ) : ℝ :=
  -Real.log (twistedPartition d n ν₀ z ψ β / wilsonPartition d n ν₀ ψ β)

omit [Group E] [MeasurableMul₂ E] [MeasurableInv E] in
theorem norm_integral_exp_product {X Pl : Type*} [Fintype X] [Fintype Pl]
    (ν₀ : Measure E) (f : Pl → (X → E) → ℝ) :
    ‖∫ ω, ∏ p, (Real.exp (f p ω) : ℂ) ∂(Measure.pi fun _ : X => ν₀)‖ =
      ∫ ω, ∏ p, Real.exp (f p ω) ∂(Measure.pi fun _ : X => ν₀) := by
  have hcast : (fun ω => ∏ p, (Real.exp (f p ω) : ℂ)) =
      (fun ω => ((∏ p, Real.exp (f p ω) : ℝ) : ℂ)) := by
    funext ω
    simp
  rw [hcast, integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (integral_nonneg fun ω => prod_nonneg fun p _ => (Real.exp_pos _).le)

/-- The real untwisted partition function equals the modulus of its polymer partition function. -/
theorem wilsonPartition_eq_norm (d n : ℕ) (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    {ψ : E → ℝ} (hψ : Measurable ψ) (hψ0 : ∀ g, 0 ≤ ψ g) (hψ2 : ∀ g, ψ g ≤ 2)
    {β : ℝ} (hβ : 0 ≤ β) :
    wilsonPartition d n ν₀ ψ β =
      ‖partitionFunction (overlapGraph (Link (d + 2) n))
        (integratedActivity ν₀ (activity (d + 2) 1 (ψ ∘ holonomy) β n)) univ‖ := by
  rw [← integral_polymerDensity ν₀ (activity (d + 2) 1 (ψ ∘ holonomy) β n)
    (fun S => measurable_plaquetteActivity support 1 _
      (measurable_perturbation (hψ.comp measurable_holonomy) β) S)
    (plaquetteMajorant support (2 * β))
    (norm_plaquetteActivity_le support 1 _
      (norm_perturbation_le (fun v => hψ0 _) (fun v => hψ2 _) hβ))]
  have hd := wilsonDensity_eq_polymerDensity (d + 2) n (1 : E) (ψ ∘ holonomy) β
  simp_rw [← hd]
  exact (norm_integral_exp_product ν₀ _).symm

/-- The real twisted partition function equals the modulus of its polymer partition function. -/
theorem twistedPartition_eq_norm (d n : ℕ) (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (z : E) {ψ : E → ℝ} (hψ : Measurable ψ) (hψ0 : ∀ g, 0 ≤ ψ g) (hψ2 : ∀ g, ψ g ≤ 2)
    {β : ℝ} (hβ : 0 ≤ β) :
    twistedPartition d n ν₀ z ψ β =
      ‖partitionFunction (overlapGraph (Link (d + 2) n))
        (integratedActivity ν₀ (twistedActivity d z ψ β n 0)) univ‖ := by
  rw [← integral_polymerDensity ν₀ (twistedActivity d z ψ β n 0)
    (measurable_twistedActivity d z hψ β n 0) (plaquetteMajorant support (2 * β))
    (norm_plaquetteActivity_le support 1 _ (norm_twistedPerturbation_le z 0 hψ0 hψ2 hβ))]
  simp_rw [← twistedDensity_eq_polymerDensity d n z 0]
  exact (norm_integral_exp_product ν₀ _).symm

/-- Both real Wilson partition functions are strictly positive in the stated regime. -/
theorem partitions_pos (d n : ℕ) (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    {z : E} (hz : ∀ g, z * g = g * z) (hzz : z * z = 1)
    (hν : ν₀.map (fun g => z * g) = ν₀) {ψ : E → ℝ} (hψ : Measurable ψ)
    (hψ0 : ∀ g, 0 ≤ ψ g) (hψ2 : ∀ g, ψ g ≤ 2)
    {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 (d + 2)) :
    0 < wilsonPartition d n ν₀ ψ β ∧ 0 < twistedPartition d n ν₀ z ψ β := by
  rw [wilsonPartition_eq_norm d n ν₀ hψ hψ0 hψ2 hβ,
    twistedPartition_eq_norm d n ν₀ z hψ hψ0 hψ2 hβ]
  obtain ⟨bound, rate, ε, hr, he0, he, hb, hbt, hempty, hsmall⟩ :=
    (twistCompatibleCrossing d ν₀ hz hzz hν hψ hψ0 hψ2 hβ hβ0).exists_bounds
  exact ⟨norm_pos_iff.mpr (partitionFunction_ne_zero
      (dobrushin_of_activitySmall ν₀ _ (bound n) (hb n) (hempty n) hr.le he0 he (hsmall n)) univ),
    norm_pos_iff.mpr (partitionFunction_ne_zero
      (dobrushin_of_activitySmall ν₀ _ (bound n) (hbt n) (hempty n) hr.le he0 he (hsmall n)) univ)⟩

/-- The centre-twist free energy of the Wilson measure tends to zero at strong coupling. -/
theorem tendsto_twistFreeEnergy (d : ℕ) (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    {z : E} (hz : ∀ g, z * g = g * z) (hzz : z * z = 1)
    (hν : ν₀.map (fun g => z * g) = ν₀) {ψ : E → ℝ} (hψ : Measurable ψ)
    (hψ0 : ∀ g, 0 ≤ ψ g) (hψ2 : ∀ g, ψ g ≤ 2)
    {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 (d + 2)) :
    Tendsto (fun n => twistFreeEnergy d n ν₀ z ψ β) atTop (𝓝 0) := by
  have h := (tendsto_logTwistRatio d ν₀ hz hzz hν hψ hψ0 hψ2 hβ hβ0 (fun _ => univ)).neg
  simp only [neg_zero] at h
  convert h using 1
  funext n
  simp only [twistFreeEnergy, wilsonPartition_eq_norm d n ν₀ hψ hψ0 hψ2 hβ,
    twistedPartition_eq_norm d n ν₀ z hψ hψ0 hψ2 hβ, TwistDiagnostic.logTwistRatio]

end Measure

#print axioms twistedHolonomy_move
#print axioms twistedActivity_eq_of_disjoint
#print axioms integratedActivity_movable
#print axioms stack_separation
#print axioms tendsto_stack_exp
#print axioms twistCompatibleCrossing
#print axioms twistedDensity_eq_polymerDensity
#print axioms partitions_pos
#print axioms tendsto_twistFreeEnergy

end Mettapedia.QuantumTheory.YangMills.StrongCouplingTwist
