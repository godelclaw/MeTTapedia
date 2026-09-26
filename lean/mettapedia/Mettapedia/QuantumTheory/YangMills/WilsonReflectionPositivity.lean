import Mettapedia.QuantumTheory.YangMills.StrongCouplingTwist
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Site reflection positivity of the Wilson density

The reflection planes of an even periodic lattice are sites. Boundary plaquettes
contribute half their action to each closed half. After fixing the variables on
the two planes, the two remaining sets of variables are independent copies, and
the reflection form is an integral of squared absolute values.

`Lattice.wilson_reflection_positive` gives the unnormalized integral statement
at every real coupling. `Lattice.wilson_conditional_square` gives its exact
conditional-square formula under integrability. For bounded measurable
potentials and observables, `Lattice.bounded_wilson_reflection_positive` supplies
integrability and the real, nonnegative reflection form; the partition function
is strictly positive, and the same positivity holds for the Wilson expectation
used in the strong-coupling clustering theorem.
-/

set_option autoImplicit false
noncomputable section

open Finset MeasureTheory
open scoped ComplexConjugate

namespace Mettapedia.QuantumTheory.YangMills.WilsonReflectionPositivity

section ConditionalSquare

variable {B P Ω : Type*} [MeasurableSpace B] [MeasurableSpace P] [MeasurableSpace Ω]
  (ρ : Measure B) (ν : Measure P) [SigmaFinite ρ] [SigmaFinite ν]

/-- The conditional-square identity, with the boundary variables kept outside. -/
theorem integral_conditional_square (g : B → P → ℂ)
    (hi : Integrable (fun x : B × (P × P) => conj (g x.1 x.2.2) * g x.1 x.2.1)
      (ρ.prod (ν.prod ν))) :
    (∫ x : B × (P × P), conj (g x.1 x.2.2) * g x.1 x.2.1 ∂ρ.prod (ν.prod ν)) =
      (↑(∫ b, Complex.normSq (∫ u, g b u ∂ν) ∂ρ : ℝ) : ℂ) := by
  rw [integral_prod _ hi, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [] with b
  rw [show (fun y : P × P => conj (g b y.2) * g b y.1) =
      (fun y => g b y.1 * conj (g b y.2)) from funext (fun _ => mul_comm _ _),
    integral_prod_mul (g b) (fun u => conj (g b u)), integral_conj, mul_comm]
  exact Complex.normSq_eq_conj_mul_self.symm

/-- Reflection positivity transported from independent halves sharing a boundary.
The integrable case is the conditional-square identity. As usual for the Bochner
integral, a nonintegrable integrand has integral zero. -/
theorem reflection_positive_of_split (μ : Measure Ω)
    (join : B × (P × P) → Ω)
    (hj : MeasurePreserving join (ρ.prod (ν.prod ν)) μ)
    (H : Ω → ℂ) (g : B → P → ℂ)
    (he : ∀ x, H (join x) = conj (g x.1 x.2.2) * g x.1 x.2.1) :
    ∃ r : ℝ, 0 ≤ r ∧ (∫ ω, H ω ∂μ) = (r : ℂ) := by
  by_cases hi : Integrable H μ
  · refine ⟨∫ b, Complex.normSq (∫ u, g b u ∂ν) ∂ρ,
      integral_nonneg (fun _ => Complex.normSq_nonneg _), ?_⟩
    have hc := hj.integrable_comp_of_integrable hi
    have hm := integral_map hj.aemeasurable (hj.map_eq.symm ▸ hi.aestronglyMeasurable)
    rw [hj.map_eq] at hm
    rw [hm]
    simp only [Function.comp_def, he] at hc ⊢
    exact integral_conditional_square ρ ν g hc
  · exact ⟨0, le_rfl, by rw [integral_undef hi]; rfl⟩

end ConditionalSquare

namespace Lattice

open StrongCouplingCrossing

/-- There are `d` spatial directions and one reflected direction. The side is
`2 * (n + 2)`, expressed in the volume indexing of the plaquette expansion. -/
abbrev Site (d n : ℕ) := StrongCouplingCrossing.Site (d + 1) (2 * n + 1)
abbrev Link (d n : ℕ) := StrongCouplingCrossing.Link (d + 1) (2 * n + 1)
abbrev Plaquette (d n : ℕ) := StrongCouplingCrossing.Plaquette (d + 1) (2 * n + 1)

/-- Reflection in the two site planes at first coordinate `0` and `n + 2`. -/
def reflectSite {d n : ℕ} (x : Site d n) : Site d n :=
  fun i => if i = 0 then -x i else x i

@[simp] theorem reflectSite_apply_zero {d n : ℕ} (x : Site d n) :
    reflectSite x 0 = -x 0 := by simp [reflectSite]

@[simp] theorem reflectSite_involutive {d n : ℕ} (x : Site d n) :
    reflectSite (reflectSite x) = x := by
  funext i
  by_cases hi : i = 0 <;> simp [reflectSite, hi]

theorem reflectSite_add {d n : ℕ} (x y : Site d n) :
    reflectSite (x + y) = reflectSite x + reflectSite y := by
  funext i
  by_cases hi : i = 0 <;> simp [reflectSite, hi, add_comm]

theorem reflectSite_sub {d n : ℕ} (x y : Site d n) :
    reflectSite (x - y) = reflectSite x - reflectSite y := by
  funext i
  by_cases hi : i = 0 <;> simp [reflectSite, hi]
  abel

theorem reflectSite_step {d n : ℕ} (μ : Fin (d + 1)) :
    reflectSite (step (n := 2 * n + 1) μ) = if μ = 0 then -step μ else step μ := by
  funext i
  by_cases hμ : μ = 0 <;> by_cases hi : i = 0 <;>
    simp_all [reflectSite, step, Ne.symm]

/-- A temporal link is reflected with reversed orientation. -/
def reflectLink {d n : ℕ} (l : Link d n) : Link d n :=
  (if l.2 = 0 then reflectSite l.1 - step 0 else reflectSite l.1, l.2)

@[simp] theorem reflectLink_direction {d n : ℕ} (l : Link d n) :
    (reflectLink l).2 = l.2 := rfl

@[simp] theorem reflectLink_involutive {d n : ℕ} (l : Link d n) :
    reflectLink (reflectLink l) = l := by
  rcases l with ⟨x, μ⟩
  by_cases hμ : μ = 0
  · simp [reflectLink, hμ, reflectSite_sub, reflectSite_step]
  · simp [reflectLink, hμ]

/-- Positive links excluding the variables on the two reflection planes. -/
def interior {d n : ℕ} (l : Link d n) : Prop :=
  (l.1 0).val < n + 2 ∧ (l.2 = 0 ∨ 0 < (l.1 0).val)

/-- Links on the two fixed planes. These necessarily have spatial direction. -/
def boundary {d n : ℕ} (l : Link d n) : Prop :=
  l.2 ≠ 0 ∧ ((l.1 0).val = 0 ∨ (l.1 0).val = n + 2)

/-- Both ends of a link lie in the closed positive half. -/
def closedHalf {d n : ℕ} (l : Link d n) : Prop :=
  (l.1 0).val ≤ n + 2 ∧ ((l.1 + step (n := 2 * n + 1) l.2) 0).val ≤ n + 2

instance {d n : ℕ} (l : Link d n) : Decidable (interior l) := by
  unfold interior; infer_instance
instance {d n : ℕ} (l : Link d n) : Decidable (boundary l) := by
  unfold boundary; infer_instance
instance {d n : ℕ} (l : Link d n) : Decidable (closedHalf l) := by
  unfold closedHalf; infer_instance

theorem neg_val {n : ℕ} (x : ZMod (2 * n + 1 + 3)) :
    (-x).val = if x.val = 0 then 0 else 2 * n + 4 - x.val := by
  by_cases hx : x = 0
  · simp [hx]
  · have hval : x.val ≠ 0 := (ZMod.val_eq_zero x).not.mpr hx
    simp [ZMod.neg_val, hx, hval, Nat.add_assoc]

theorem neg_sub_one_val {n : ℕ} (x : ZMod (2 * n + 1 + 3)) :
    (-x - 1).val = 2 * n + 3 - x.val := by
  have hx := ZMod.val_lt x
  have he : -x - 1 = -(x + 1) := by ring
  rw [he, neg_val, ZMod.val_add, ZMod.val_one_eq_one_mod]
  rw [Nat.mod_eq_of_lt (show 1 < 2 * n + 1 + 3 by omega)]
  by_cases hh : x.val + 1 < 2 * n + 1 + 3
  · rw [Nat.mod_eq_of_lt hh, ite_eq_right (by omega)]
    omega
  · have hh' : x.val + 1 = 2 * n + 1 + 3 := by omega
    rw [hh', Nat.mod_self, ite_eq_left rfl]
    omega

theorem reflectLink_time {d n : ℕ} (l : Link d n) :
    ((reflectLink l).1 0).val =
      if l.2 = 0 then 2 * n + 3 - (l.1 0).val
      else if (l.1 0).val = 0 then 0 else 2 * n + 4 - (l.1 0).val := by
  by_cases h : l.2 = 0 <;> simp [reflectLink, h, step, neg_val, neg_sub_one_val]

theorem interior_reflect_disjoint {d n : ℕ} {l : Link d n} (h : interior l) :
    ¬ interior (reflectLink l) := by
  have hx := ZMod.val_lt (l.1 0)
  simp only [interior, reflectLink_direction, reflectLink_time] at *
  split_ifs <;> omega

theorem boundary_or_interior {d n : ℕ} (l : Link d n) :
    boundary l ∨ interior l ∨ interior (reflectLink l) := by
  have hx := ZMod.val_lt (l.1 0)
  simp only [boundary, interior, reflectLink_direction, reflectLink_time]
  split_ifs <;> omega

theorem boundary_not_interior {d n : ℕ} {l : Link d n} (h : boundary l) :
    ¬ interior l := by
  rintro ⟨hlt, hμ | hpos⟩
  · exact h.1 hμ
  · rcases h.2 with h | h <;> omega

theorem reflectLink_boundary {d n : ℕ} {l : Link d n} (h : boundary l) :
    reflectLink l = l := by
  apply Prod.ext
  · funext i
    rcases h with ⟨hμ, hx⟩
    simp only [reflectLink, hμ, ↓reduceIte, reflectSite]
    split_ifs with hi
    · subst i
      apply ZMod.val_injective
      rw [neg_val]
      rcases hx with hx | hx <;> rw [hx] <;> split_ifs <;> omega
    · rfl
  · rfl

theorem closedHalf_iff {d n : ℕ} (l : Link d n) :
    closedHalf l ↔ boundary l ∨ interior l := by
  have hx := ZMod.val_lt (l.1 0)
  by_cases hμ : l.2 = 0
  · simp only [closedHalf, boundary, interior, hμ,
      true_or, and_true, Pi.add_apply, step, ↓reduceIte,
      ZMod.val_add, ZMod.val_one_eq_one_mod]
    rw [Nat.mod_eq_of_lt (show 1 < 2 * n + 1 + 3 by omega)]
    by_cases hh : (l.1 0).val + 1 < 2 * n + 1 + 3
    · rw [Nat.mod_eq_of_lt hh]; omega
    · have he : (l.1 0).val + 1 = 2 * n + 1 + 3 := by omega
      rw [he, Nat.mod_self]; omega
  · simp only [closedHalf, boundary, interior, hμ,
      false_or, Pi.add_apply, step, Ne.symm hμ, ↓reduceIte, add_zero, and_self]
    omega

abbrev Boundary (d n : ℕ) := {l : Link d n // boundary l}
abbrev Interior (d n : ℕ) := {l : Link d n // interior l}

def indexJoin {d n : ℕ} : Boundary d n ⊕ (Interior d n ⊕ Interior d n) → Link d n
  | .inl b => b.1
  | .inr (.inl p) => p.1
  | .inr (.inr p) => reflectLink p.1

theorem indexJoin_bijective (d n : ℕ) : Function.Bijective (indexJoin (d := d) (n := n)) := by
  constructor
  · intro x y h
    rcases x with b | p
    · rcases y with c | q
      · exact congrArg Sum.inl (Subtype.ext h)
      · rcases q with q | q
        · change b.1 = q.1 at h
          exact False.elim (boundary_not_interior b.2 (h.symm ▸ q.2))
        · have he : b.1 = q.1 := by
            have := congrArg reflectLink h
            simpa [indexJoin, reflectLink_boundary b.2] using this
          exact False.elim (boundary_not_interior b.2 (he ▸ q.2))
    · rcases p with p | p <;> rcases y with b | q
      · change p.1 = b.1 at h
        exact False.elim (boundary_not_interior b.2 (h ▸ p.2))
      · rcases q with q | q
        · exact congrArg (Sum.inr ∘ Sum.inl) (Subtype.ext h)
        · change p.1 = reflectLink q.1 at h
          exact False.elim (interior_reflect_disjoint q.2 (h ▸ p.2))
      · have he : p.1 = b.1 := by
          have := congrArg reflectLink h
          simpa [indexJoin, reflectLink_boundary b.2] using this
        exact False.elim (boundary_not_interior b.2 (he ▸ p.2))
      · rcases q with q | q
        · change reflectLink p.1 = q.1 at h
          exact False.elim (interior_reflect_disjoint p.2 (h.symm ▸ q.2))
        · apply congrArg (Sum.inr ∘ Sum.inr)
          apply Subtype.ext
          simpa [indexJoin] using congrArg reflectLink h
  · intro l
    rcases boundary_or_interior l with hb | hp | hn
    · exact ⟨.inl ⟨l, hb⟩, rfl⟩
    · exact ⟨.inr (.inl ⟨l, hp⟩), rfl⟩
    · exact ⟨.inr (.inr ⟨reflectLink l, hn⟩), reflectLink_involutive l⟩

def indexEquiv (d n : ℕ) : Boundary d n ⊕ (Interior d n ⊕ Interior d n) ≃ Link d n :=
  Equiv.ofBijective indexJoin (indexJoin_bijective d n)

section Configurations

variable {E : Type*} [Group E] {d n : ℕ}

/-- Site reflection on configurations, including reversal of temporal variables. -/
def theta (ω : Link d n → E) (l : Link d n) : E :=
  if l.2 = 0 then (ω (reflectLink l))⁻¹ else ω (reflectLink l)

@[simp] theorem theta_involutive (ω : Link d n → E) : theta (theta ω) = ω := by
  funext l
  by_cases h : l.2 = 0 <;> simp [theta, h]

/-- Reverse only the negative temporal variables when parametrizing the two halves. -/
def reverseNegative (ω : Link d n → E) (l : Link d n) : E :=
  if l.2 = 0 ∧ interior (reflectLink l) then (ω l)⁻¹ else ω l

variable [MeasurableSpace E] [MeasurableInv E]

theorem measurable_theta : Measurable (theta (E := E) (d := d) (n := n)) := by
  apply measurable_pi_lambda
  intro l
  dsimp [theta]
  split_ifs <;> fun_prop

/-- The product reference law is invariant under site reflection. -/
theorem measurePreserving_theta (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (hν : ν₀.map Inv.inv = ν₀) :
    MeasurePreserving (theta (d := d) (n := n))
      (Measure.pi fun _ : Link d n => ν₀) (Measure.pi fun _ : Link d n => ν₀) := by
  let e : Link d n ≃ Link d n :=
    ⟨reflectLink, reflectLink, reflectLink_involutive, reflectLink_involutive⟩
  have hi := measurePreserving_piCongrLeft (fun _ : Link d n => ν₀) e
  have hv : MeasurePreserving (fun (ω : Link d n → E) l => if l.2 = 0 then (ω l)⁻¹ else ω l)
      (Measure.pi fun _ : Link d n => ν₀) (Measure.pi fun _ : Link d n => ν₀) := by
    apply measurePreserving_pi _ _ (f := fun (l : Link d n) (g : E) => if l.2 = 0 then g⁻¹ else g)
    intro l
    split_ifs
    · exact ⟨measurable_inv, hν⟩
    · exact MeasurePreserving.id ν₀
  have he : (⇑(MeasurableEquiv.piCongrLeft (fun _ : Link d n => E) e)) =
      (fun ω l => ω (reflectLink l)) := by
    funext ω l
    have hh := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Link d n => E)
      e ω (reflectLink l)
    simpa only [e, Equiv.coe_fn_mk, reflectLink_involutive] using hh
  rw [he] at hi
  exact hv.comp hi

def sumConfiguration (x : (Boundary d n → E) × ((Interior d n → E) × (Interior d n → E))) :
    Boundary d n ⊕ (Interior d n ⊕ Interior d n) → E :=
  Sum.elim x.1 (Sum.elim x.2.1 x.2.2)

/-- Assemble boundary variables and two independent copies of the positive interior. -/
def join (x : (Boundary d n → E) × ((Interior d n → E) × (Interior d n → E))) :
    Link d n → E :=
  reverseNegative (MeasurableEquiv.piCongrLeft (fun _ : Link d n => E)
    (indexEquiv d n) (sumConfiguration x))

omit [MeasurableInv E] in
theorem join_boundary (x : (Boundary d n → E) × ((Interior d n → E) × (Interior d n → E)))
    (b : Boundary d n) : join x b.1 = x.1 b := by
  have hn : ¬ (b.1.2 = 0 ∧ interior (reflectLink b.1)) := fun h => b.2.1 h.1
  simp only [join, reverseNegative, hn, ↓reduceIte]
  change MeasurableEquiv.piCongrLeft (fun _ : Link d n => E) (indexEquiv d n)
    (sumConfiguration x) (indexEquiv d n (.inl b)) = _
  rw [MeasurableEquiv.piCongrLeft_apply_apply]
  rfl

omit [MeasurableInv E] in
theorem join_interior (x : (Boundary d n → E) × ((Interior d n → E) × (Interior d n → E)))
    (p : Interior d n) : join x p.1 = x.2.1 p := by
  have hn : ¬ (p.1.2 = 0 ∧ interior (reflectLink p.1)) :=
    fun h => interior_reflect_disjoint p.2 h.2
  simp only [join, reverseNegative, hn, ↓reduceIte]
  change MeasurableEquiv.piCongrLeft (fun _ : Link d n => E) (indexEquiv d n)
    (sumConfiguration x) (indexEquiv d n (.inr (.inl p))) = _
  rw [MeasurableEquiv.piCongrLeft_apply_apply]
  rfl

omit [MeasurableInv E] in
theorem join_reflected (x : (Boundary d n → E) × ((Interior d n → E) × (Interior d n → E)))
    (p : Interior d n) : join x (reflectLink p.1) =
      if p.1.2 = 0 then (x.2.2 p)⁻¹ else x.2.2 p := by
  simp only [join, reverseNegative, reflectLink_direction, reflectLink_involutive,
    p.2, and_true]
  have he := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Link d n => E) (indexEquiv d n)
    (sumConfiguration x) (.inr (.inr p))
  change MeasurableEquiv.piCongrLeft (fun _ : Link d n => E) (indexEquiv d n)
    (sumConfiguration x) (reflectLink p.1) = x.2.2 p at he
  rw [he]

theorem measurePreserving_join (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (hν : ν₀.map Inv.inv = ν₀) :
    MeasurePreserving (join (d := d) (n := n))
      ((Measure.pi fun _ : Boundary d n => ν₀).prod
        ((Measure.pi fun _ : Interior d n => ν₀).prod (Measure.pi fun _ : Interior d n => ν₀)))
      (Measure.pi fun _ : Link d n => ν₀) := by
  have hrev : MeasurePreserving (reverseNegative (d := d) (n := n))
      (Measure.pi fun _ : Link d n => ν₀) (Measure.pi fun _ : Link d n => ν₀) := by
    apply measurePreserving_pi _ _ (f := fun l g =>
      if l.2 = 0 ∧ interior (reflectLink l) then g⁻¹ else g)
    intro l
    split_ifs
    · exact ⟨measurable_inv, hν⟩
    · exact MeasurePreserving.id ν₀
  have hsum := measurePreserving_sumPiEquivProdPi_symm
    (fun _ : Interior d n ⊕ Interior d n => ν₀)
  have houter := measurePreserving_sumPiEquivProdPi_symm
    (fun _ : Boundary d n ⊕ (Interior d n ⊕ Interior d n) => ν₀)
  have hprod := (MeasurePreserving.id (Measure.pi fun _ : Boundary d n => ν₀)).prod hsum
  exact hrev.comp ((measurePreserving_piCongrLeft (fun _ : Link d n => ν₀)
    (indexEquiv d n)).comp (houter.comp hprod))

/-- Dependence only on links with both endpoints in the closed positive half. -/
def HalfLocal {A : Type*} (F : (Link d n → E) → A) : Prop :=
  ∀ ω ω', (∀ l, closedHalf l → ω l = ω' l) → F ω = F ω'

omit [MeasurableInv E] in
theorem halfLocal_join {A : Type*} {F : (Link d n → E) → A} (hF : HalfLocal F)
    (b : Boundary d n → E) (u v : Interior d n → E) :
    F (join (b, u, v)) = F (join (b, u, u)) := by
  apply hF
  intro l hl
  rcases (closedHalf_iff l).mp hl with hb | hp
  · simpa using (join_boundary (b, u, v) ⟨l, hb⟩).trans
      (join_boundary (b, u, u) ⟨l, hb⟩).symm
  · simpa using (join_interior (b, u, v) ⟨l, hp⟩).trans
      (join_interior (b, u, u) ⟨l, hp⟩).symm

omit [MeasurableInv E] in
theorem halfLocal_theta_join {A : Type*} {F : (Link d n → E) → A} (hF : HalfLocal F)
    (b : Boundary d n → E) (u v : Interior d n → E) :
    F (theta (join (b, u, v))) = F (join (b, v, v)) := by
  apply hF
  intro l hl
  rcases (closedHalf_iff l).mp hl with hb | hp
  · simp only [theta, hb.1, ↓reduceIte, reflectLink_boundary hb]
    exact (join_boundary (b, u, v) ⟨l, hb⟩).trans (join_boundary (b, v, v) ⟨l, hb⟩).symm
  · have h₁ := join_reflected (b, u, v) ⟨l, hp⟩
    have h₂ := join_interior (b, v, v) ⟨l, hp⟩
    dsimp [theta]
    rw [h₁, h₂]
    split_ifs <;> simp

theorem reflection_positive_factorized (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (hν : ν₀.map Inv.inv = ν₀) (F : (Link d n → E) → ℂ) (hF : HalfLocal F)
    (W : (Link d n → E) → ℝ) (hW : HalfLocal W) :
    ∃ r : ℝ, 0 ≤ r ∧
      (∫ ω, conj (F (theta ω)) * F ω * (W ω * W (theta ω) : ℝ)
        ∂Measure.pi (fun _ : Link d n => ν₀)) = (r : ℂ) := by
  apply reflection_positive_of_split (Measure.pi fun _ : Boundary d n => ν₀)
    (Measure.pi fun _ : Interior d n => ν₀) _ join (measurePreserving_join ν₀ hν)
    _ (fun b u => F (join (b, u, u)) * (W (join (b, u, u)) : ℂ))
  rintro ⟨b, u, v⟩
  simp only [halfLocal_join hF, halfLocal_theta_join hF,
    halfLocal_join hW, halfLocal_theta_join hW, map_mul, Complex.conj_ofReal]
  push_cast
  ring

end Configurations

/-- Reflection of an unoriented plaquette in its canonical positive orientation. -/
def reflectPlaquette {d n : ℕ} (p : Plaquette d n) : Plaquette d n :=
  ((reflectLink (p.1, p.2.1.1)).1, p.2)

@[simp] theorem reflectPlaquette_plane {d n : ℕ} (p : Plaquette d n) :
    (reflectPlaquette p).2 = p.2 := rfl

@[simp] theorem reflectPlaquette_involutive {d n : ℕ} (p : Plaquette d n) :
    reflectPlaquette (reflectPlaquette p) = p := by
  apply Prod.ext
  · exact congrArg (fun l : Link d n => l.1) (reflectLink_involutive (p.1, p.2.1.1))
  · rfl

def plaquetteEquiv (d n : ℕ) : Plaquette d n ≃ Plaquette d n :=
  ⟨reflectPlaquette, reflectPlaquette, reflectPlaquette_involutive, reflectPlaquette_involutive⟩

theorem plane_second_ne_zero {d : ℕ} (a : StrongCouplingCrossing.Plane (d + 1)) :
    a.1.2 ≠ 0 := by
  intro h
  have := a.2
  rw [h] at this
  exact (not_lt_of_ge (Fin.zero_le _)) this

theorem reflectLink_linkAt_spatial {d n : ℕ} (p : Plaquette d n) (hμ : p.2.1.1 ≠ 0)
    (i : Fin 4) : reflectLink (linkAt p i) = linkAt (reflectPlaquette p) i := by
  have hν := plane_second_ne_zero p.2
  fin_cases i <;>
    simp [linkAt, reflectPlaquette, reflectLink, reflectSite_add, reflectSite_step, hμ, hν]

theorem reflectLink_linkAt_temporal {d n : ℕ} (p : Plaquette d n) (hμ : p.2.1.1 = 0) :
    (reflectLink (linkAt p 0) = linkAt (reflectPlaquette p) 0) ∧
    (reflectLink (linkAt p 1) = linkAt (reflectPlaquette p) 3) ∧
    (reflectLink (linkAt p 2) = linkAt (reflectPlaquette p) 2) ∧
    (reflectLink (linkAt p 3) = linkAt (reflectPlaquette p) 1) := by
  have hν := plane_second_ne_zero p.2
  simp [linkAt, reflectPlaquette, reflectLink, reflectSite_add, reflectSite_step, hμ, hν]
  abel_nf
  trivial

section Action

open StrongCouplingTwist (holonomy)

variable {E : Type*} [Group E] {d n : ℕ}

def plaquetteValue (ψ : E → ℝ) (p : Plaquette d n) (ω : Link d n → E) : ℝ :=
  ψ (holonomy (fun i => ω (linkAt p i)))

/-- A class function even under inversion assigns the same action to a reflected
plaquette, including the temporal plaquettes whose boundary orientation reverses. -/
theorem plaquetteValue_theta (ψ : E → ℝ)
    (hclass : ∀ g h, ψ (g * h * g⁻¹) = ψ h) (hinv : ∀ g, ψ g⁻¹ = ψ g)
    (p : Plaquette d n) (ω : Link d n → E) :
    plaquetteValue ψ p (theta ω) = plaquetteValue ψ (reflectPlaquette p) ω := by
  have hν := plane_second_ne_zero p.2
  by_cases hμ : p.2.1.1 = 0
  · rcases reflectLink_linkAt_temporal p hμ with ⟨h₀, h₁, h₂, h₃⟩
    have he : holonomy (fun i => theta ω (linkAt p i)) =
        (ω (linkAt (reflectPlaquette p) 0))⁻¹ *
          (holonomy (fun i => ω (linkAt (reflectPlaquette p) i)))⁻¹ *
          ((ω (linkAt (reflectPlaquette p) 0))⁻¹)⁻¹ := by
      simp only [holonomy, theta]
      simp only [show (linkAt p 0).2 = p.2.1.1 from rfl,
        show (linkAt p 1).2 = p.2.1.2 from rfl,
        show (linkAt p 2).2 = p.2.1.1 from rfl,
        show (linkAt p 3).2 = p.2.1.2 from rfl, hμ, hν, ↓reduceIte,
        h₀, h₁, h₂, h₃]
      group
    exact (congrArg ψ he).trans ((hclass _ _).trans (hinv _))
  · unfold plaquetteValue
    congr 1
    unfold holonomy
    simp only [theta, show (linkAt p 0).2 = p.2.1.1 from rfl,
      show (linkAt p 1).2 = p.2.1.2 from rfl,
      show (linkAt p 2).2 = p.2.1.1 from rfl,
      show (linkAt p 3).2 = p.2.1.2 from rfl, hμ, hν, ↓reduceIte,
      reflectLink_linkAt_spatial p hμ]

/-- Coefficient of a plaquette in the positive half-action. Fixed-plane
plaquettes have coefficient one half. -/
def halfCoefficient (p : Plaquette d n) : ℝ :=
  if p.2.1.1 = 0 then
    if (p.1 0).val < n + 2 then 1 else 0
  else if (p.1 0).val = 0 ∨ (p.1 0).val = n + 2 then 1 / 2
  else if (p.1 0).val < n + 2 then 1 else 0

theorem halfCoefficient_reflect (p : Plaquette d n) :
    halfCoefficient p + halfCoefficient (reflectPlaquette p) = 1 := by
  have hx := ZMod.val_lt (p.1 0)
  have ht := reflectLink_time (p.1, p.2.1.1)
  change (((reflectPlaquette p).1 0).val) = _ at ht
  simp only [halfCoefficient, reflectPlaquette_plane, ht]
  split_ifs <;> norm_num <;> omega

theorem halfCoefficient_nonneg (p : Plaquette d n) : 0 ≤ halfCoefficient p := by
  unfold halfCoefficient
  split_ifs <;> norm_num

theorem halfCoefficient_le_one (p : Plaquette d n) : halfCoefficient p ≤ 1 := by
  unfold halfCoefficient
  split_ifs <;> norm_num

theorem closedHalf_temporal (x : Site d n) :
    closedHalf (x, 0) ↔ (x 0).val < n + 2 := by
  simp [closedHalf_iff, boundary, interior]

theorem closedHalf_spatial (x : Site d n) (μ : Fin (d + 1)) (hμ : μ ≠ 0) :
    closedHalf (x, μ) ↔ (x 0).val ≤ n + 2 := by
  rw [closedHalf_iff]
  simp only [boundary, interior, hμ, false_or]
  omega

theorem val_add_one_of_lt_half (x : ZMod (2 * n + 1 + 3)) (hx : x.val < n + 2) :
    (x + 1).val = x.val + 1 := by
  rw [ZMod.val_add, ZMod.val_one_eq_one_mod,
    Nat.mod_eq_of_lt (show 1 < 2 * n + 1 + 3 by omega), Nat.mod_eq_of_lt (by omega)]

/-- Every plaquette with nonzero positive-half weight uses only closed-half links. -/
theorem halfCoefficient_local (p : Plaquette d n) (hc : halfCoefficient p ≠ 0)
    (i : Fin 4) : closedHalf (linkAt p i) := by
  have hν := plane_second_ne_zero p.2
  by_cases hμ : p.2.1.1 = 0
  · have hx : (p.1 0).val < n + 2 := by
      by_contra hx
      simp [halfCoefficient, hμ, hx] at hc
    fin_cases i
    · simpa [linkAt, hμ, closedHalf_temporal] using hx
    · change closedHalf (p.1 + step (n := 2 * n + 1) p.2.1.1, p.2.1.2)
      rw [closedHalf_spatial _ _ hν]
      simpa [hμ, step, val_add_one_of_lt_half _ hx] using Nat.succ_le_of_lt hx
    · change closedHalf (p.1 + step (n := 2 * n + 1) p.2.1.2, p.2.1.1)
      rw [hμ, closedHalf_temporal]
      simpa [step, Ne.symm hν] using hx
    · change closedHalf (p.1, p.2.1.2)
      rw [closedHalf_spatial _ _ hν]
      omega
  · have hx : (p.1 0).val ≤ n + 2 := by
      by_contra hx
      have ha : ¬ ((p.1 0).val = 0 ∨ (p.1 0).val = n + 2) := by omega
      have hb : ¬ (p.1 0).val < n + 2 := by omega
      simp only [halfCoefficient, hμ, ha, hb, ↓reduceIte, ne_eq, not_true_eq_false] at hc
    fin_cases i <;>
      simpa [linkAt, closedHalf_spatial, hμ, hν, step, Ne.symm hμ, Ne.symm hν] using hx

def halfAction (ψ : E → ℝ) (ω : Link d n → E) : ℝ :=
  ∑ p : Plaquette d n, halfCoefficient p * plaquetteValue ψ p ω

def halfWeight (ψ : E → ℝ) (β : ℝ) (ω : Link d n → E) : ℝ :=
  Real.exp (-β * halfAction ψ ω)

/-- The real Wilson density on the even torus. -/
def density (ψ : E → ℝ) (β : ℝ) (ω : Link d n → E) : ℝ :=
  ∏ p : Plaquette d n, Real.exp (-β * plaquetteValue ψ p ω)

theorem halfAction_local (ψ : E → ℝ) : HalfLocal (halfAction (d := d) (n := n) ψ) := by
  intro ω ω' h
  apply sum_congr rfl
  intro p _
  by_cases hc : halfCoefficient p = 0
  · simp [hc]
  · congr 1
    apply congrArg ψ
    apply congrArg holonomy
    funext i
    exact h _ (halfCoefficient_local p hc i)

theorem halfWeight_local (ψ : E → ℝ) (β : ℝ) :
    HalfLocal (halfWeight (d := d) (n := n) ψ β) := by
  intro ω ω' h
  simp only [halfWeight, halfAction_local ψ ω ω' h]

theorem halfAction_add_reflection (ψ : E → ℝ)
    (hclass : ∀ g h, ψ (g * h * g⁻¹) = ψ h) (hinv : ∀ g, ψ g⁻¹ = ψ g)
    (ω : Link d n → E) :
    halfAction ψ ω + halfAction ψ (theta ω) = ∑ p : Plaquette d n, plaquetteValue ψ p ω := by
  have he := (plaquetteEquiv d n).sum_comp
    (fun p => halfCoefficient p * plaquetteValue ψ p (theta ω))
  simp only [plaquetteEquiv, Equiv.coe_fn_mk, plaquetteValue_theta ψ hclass hinv,
    reflectPlaquette_involutive] at he
  unfold halfAction
  simp only [plaquetteValue_theta ψ hclass hinv]
  rw [← he, ← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  rw [← add_mul, halfCoefficient_reflect, one_mul]

/-- Exact factorization including half of each fixed-plane plaquette action. -/
theorem density_factorization (ψ : E → ℝ) (β : ℝ)
    (hclass : ∀ g h, ψ (g * h * g⁻¹) = ψ h) (hinv : ∀ g, ψ g⁻¹ = ψ g)
    (ω : Link d n → E) : density ψ β ω = halfWeight ψ β ω * halfWeight ψ β (theta ω) := by
  simp only [density, halfWeight, ← Real.exp_sum, ← Real.exp_add, ← mul_add,
    halfAction_add_reflection ψ hclass hinv, mul_sum]

theorem density_eq_wilsonDensity (ψ : E → ℝ) (β : ℝ) (ω : Link d n → E) :
    (density ψ β ω : ℂ) = StrongCouplingCrossing.wilsonDensity (ψ ∘ holonomy) β ω := by
  simp [density, StrongCouplingCrossing.wilsonDensity, StrongCouplingCrossing.potential,
    plaquetteValue]

variable [MeasurableSpace E] [MeasurableInv E]

/-- Site reflection positivity at every real coupling, for the actual Wilson
plaquette product and every observable depending on the closed positive half. -/
theorem wilson_reflection_positive (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (hν : ν₀.map Inv.inv = ν₀) (ψ : E → ℝ) (β : ℝ)
    (hclass : ∀ g h, ψ (g * h * g⁻¹) = ψ h) (hinv : ∀ g, ψ g⁻¹ = ψ g)
    (F : (Link d n → E) → ℂ) (hF : HalfLocal F) :
    ∃ r : ℝ, 0 ≤ r ∧
      (∫ ω, conj (F (theta ω)) * F ω * (density ψ β ω : ℂ)
        ∂Measure.pi (fun _ : Link d n => ν₀)) = (r : ℂ) := by
  simp_rw [density_factorization ψ β hclass hinv]
  exact reflection_positive_factorized ν₀ hν F hF _ (halfWeight_local ψ β)

/-- The reflected integral equals a conditional square whenever it is integrable. -/
theorem wilson_conditional_square (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (hν : ν₀.map Inv.inv = ν₀) (ψ : E → ℝ) (β : ℝ)
    (hclass : ∀ g h, ψ (g * h * g⁻¹) = ψ h) (hinv : ∀ g, ψ g⁻¹ = ψ g)
    (F : (Link d n → E) → ℂ) (hF : HalfLocal F)
    (hi : Integrable (fun ω => conj (F (theta ω)) * F ω * (density ψ β ω : ℂ))
      (Measure.pi fun _ : Link d n => ν₀)) :
    (∫ ω, conj (F (theta ω)) * F ω * (density ψ β ω : ℂ)
      ∂Measure.pi (fun _ : Link d n => ν₀)) =
      (↑(∫ b : Boundary d n → E, Complex.normSq
        (∫ u : Interior d n → E, F (join (b, u, u)) *
          (halfWeight ψ β (join (b, u, u)) : ℂ) ∂Measure.pi (fun _ => ν₀))
        ∂Measure.pi (fun _ => ν₀) : ℝ) : ℂ) := by
  let H := fun ω => conj (F (theta ω)) * F ω * (density ψ β ω : ℂ)
  let g := fun (b : Boundary d n → E) (u : Interior d n → E) =>
    F (join (b, u, u)) * (halfWeight ψ β (join (b, u, u)) : ℂ)
  have he (x : (Boundary d n → E) × ((Interior d n → E) × (Interior d n → E))) :
      H (join x) = conj (g x.1 x.2.2) * g x.1 x.2.1 := by
    rcases x with ⟨b, u, v⟩
    dsimp [H, g]
    simp only [density_factorization ψ β hclass hinv,
      halfLocal_join hF, halfLocal_theta_join hF,
      halfLocal_join (halfWeight_local ψ β), halfLocal_theta_join (halfWeight_local ψ β),
      map_mul, Complex.conj_ofReal]
    push_cast
    ring
  have hj := measurePreserving_join (d := d) (n := n) ν₀ hν
  have hc := hj.integrable_comp_of_integrable hi
  have hm := integral_map hj.aemeasurable (hj.map_eq.symm ▸ hi.aestronglyMeasurable)
  rw [hj.map_eq] at hm
  change (∫ ω, H ω ∂Measure.pi (fun _ : Link d n => ν₀)) = _
  rw [hm]
  change Integrable (H ∘ join) _ at hc
  change (∫ x, H (join x) ∂_) = _
  simp only [Function.comp_def, he] at hc ⊢
  exact integral_conditional_square _ _ g hc

variable [MeasurableMul₂ E]

theorem measurable_plaquetteValue {ψ : E → ℝ} (hψ : Measurable ψ) (p : Plaquette d n) :
    Measurable (plaquetteValue ψ p) := by
  apply hψ.comp
  unfold holonomy
  fun_prop

theorem measurable_density {ψ : E → ℝ} (hψ : Measurable ψ) (β : ℝ) :
    Measurable (density (d := d) (n := n) ψ β) := by
  unfold density plaquetteValue holonomy
  fun_prop

omit [MeasurableSpace E] [MeasurableInv E] [MeasurableMul₂ E] in
theorem density_pos (ψ : E → ℝ) (β : ℝ) (ω : Link d n → E) :
    0 < density ψ β ω := by
  exact prod_pos (fun _ _ => Real.exp_pos _)

/-- A uniform finite-volume bound for arbitrary real coupling and bounded potential. -/
def densityBound (d n : ℕ) (β C : ℝ) : ℝ :=
  Real.exp (|β| * C) ^ Fintype.card (Plaquette d n)

omit [MeasurableSpace E] [MeasurableInv E] [MeasurableMul₂ E] in
theorem density_le {ψ : E → ℝ} {C : ℝ} (hψ : ∀ g, |ψ g| ≤ C) (β : ℝ)
    (ω : Link d n → E) : density ψ β ω ≤ densityBound d n β C := by
  unfold density densityBound
  rw [← card_univ, ← Finset.prod_const]
  apply prod_le_prod (fun _ _ => (Real.exp_pos _).le)
  intro p _
  apply Real.exp_le_exp.mpr
  calc
    -β * plaquetteValue ψ p ω ≤ |-β * plaquetteValue ψ p ω| := le_abs_self _
    _ = |β| * |plaquetteValue ψ p ω| := by rw [abs_mul, abs_neg]
    _ ≤ |β| * C := mul_le_mul_of_nonneg_left (hψ _) (abs_nonneg β)

theorem integrable_density (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    {ψ : E → ℝ} (hψ : Measurable ψ) {C : ℝ} (hbound : ∀ g, |ψ g| ≤ C) (β : ℝ) :
    Integrable (density (d := d) (n := n) ψ β) (Measure.pi fun _ : Link d n => ν₀) := by
  apply (integrable_const (densityBound d n β C)).mono' (measurable_density hψ β).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    simpa only [Real.norm_eq_abs, abs_of_pos (density_pos ψ β ω)] using density_le hbound β ω

theorem partition_pos (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    {ψ : E → ℝ} (hψ : Measurable ψ) {C : ℝ} (hbound : ∀ g, |ψ g| ≤ C) (β : ℝ) :
    0 < ∫ ω, density ψ β ω ∂Measure.pi (fun _ : Link d n => ν₀) := by
  have hi := integrable_density (d := d) (n := n) ν₀ hψ hbound β
  change Integrable (fun ω => density ψ β ω) _ at hi
  simp only [density, ← Real.exp_sum] at hi ⊢
  exact integral_exp_pos hi

/-- Bounded observables and bounded measurable potentials give genuine integrable
reflection forms, for every real value of the coupling. -/
theorem integrable_reflection_form (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    {ψ : E → ℝ} (hψ : Measurable ψ) {C : ℝ} (hbound : ∀ g, |ψ g| ≤ C) (β : ℝ)
    {F : (Link d n → E) → ℂ} (hF : Measurable F) {M : ℝ} (hFb : ∀ ω, ‖F ω‖ ≤ M) :
    Integrable (fun ω => conj (F (theta ω)) * F ω * (density ψ β ω : ℂ))
      (Measure.pi fun _ : Link d n => ν₀) := by
  have hM : 0 ≤ M := (norm_nonneg (F fun _ => 1)).trans (hFb _)
  have hm : Measurable (fun ω => conj (F (theta ω)) * F ω * (density ψ β ω : ℂ)) := by
    exact ((Complex.continuous_conj.measurable.comp (hF.comp measurable_theta)).mul hF).mul
      (Complex.measurable_ofReal.comp (measurable_density hψ β))
  apply (integrable_const (M * M * densityBound d n β C)).mono' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  simp only [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (density_pos ψ β ω)]
  exact mul_le_mul (mul_le_mul (hFb _) (hFb _) (norm_nonneg _) hM)
    (density_le hbound β ω) (density_pos ψ β ω).le (mul_nonneg hM hM)

/-- Reflection positivity of the normalized Wilson expectation. The normalization
is strictly positive under the bounded-potential hypotheses. -/
theorem normalized_reflection_positive (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (hν : ν₀.map Inv.inv = ν₀) {ψ : E → ℝ} (hψ : Measurable ψ)
    {C : ℝ} (hbound : ∀ g, |ψ g| ≤ C) (β : ℝ)
    (hclass : ∀ g h, ψ (g * h * g⁻¹) = ψ h) (hinv : ∀ g, ψ g⁻¹ = ψ g)
    (F : (Link d n → E) → ℂ) (hF : HalfLocal F) :
    ∃ r : ℝ, 0 ≤ r ∧
      ((∫ ω, conj (F (theta ω)) * F ω * (density ψ β ω : ℂ)
        ∂Measure.pi (fun _ : Link d n => ν₀)) /
        (↑(∫ ω, density ψ β ω ∂Measure.pi (fun _ : Link d n => ν₀) : ℝ) : ℂ)) = (r : ℂ) := by
  obtain ⟨r, hr, he⟩ := wilson_reflection_positive ν₀ hν ψ β hclass hinv F hF
  refine ⟨r / (∫ ω, density ψ β ω ∂Measure.pi (fun _ : Link d n => ν₀)),
    div_nonneg hr (partition_pos ν₀ hψ hbound β).le, ?_⟩
  rw [he, Complex.ofReal_div]

/-- The normalized positivity statement uses exactly the expectation from the
strong-coupling crossing and clustering construction. -/
theorem wilsonExpectation_reflection_positive (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (hν : ν₀.map Inv.inv = ν₀) {ψ : E → ℝ} (hψ : Measurable ψ)
    {C : ℝ} (hbound : ∀ g, |ψ g| ≤ C) (β : ℝ)
    (hclass : ∀ g h, ψ (g * h * g⁻¹) = ψ h) (hinv : ∀ g, ψ g⁻¹ = ψ g)
    (F : (Link d n → E) → ℂ) (hF : HalfLocal F) :
    ∃ r : ℝ, 0 ≤ r ∧ StrongCouplingCrossing.wilsonExpectation ν₀ (ψ ∘ holonomy) β
      (fun ω => conj (F (theta ω)) * F ω) = (r : ℂ) := by
  unfold StrongCouplingCrossing.wilsonExpectation
  simp_rw [← density_eq_wilsonDensity]
  rw [integral_complex_ofReal]
  exact normalized_reflection_positive ν₀ hν hψ hbound β hclass hinv F hF

/-- Reflection positivity for bounded measurable observables, together with
integrability of the reflected integrand. In particular the result does not
rely on assigning zero to a divergent Bochner integral. -/
theorem bounded_wilson_reflection_positive (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (hν : ν₀.map Inv.inv = ν₀) {ψ : E → ℝ} (hψ : Measurable ψ)
    {C : ℝ} (hbound : ∀ g, |ψ g| ≤ C) (β : ℝ)
    (hclass : ∀ g h, ψ (g * h * g⁻¹) = ψ h) (hinv : ∀ g, ψ g⁻¹ = ψ g)
    {F : (Link d n → E) → ℂ} (hF : Measurable F) {M : ℝ} (hFb : ∀ ω, ‖F ω‖ ≤ M)
    (hlocal : HalfLocal F) :
    Integrable (fun ω => conj (F (theta ω)) * F ω * (density ψ β ω : ℂ))
      (Measure.pi fun _ : Link d n => ν₀) ∧
    (∫ ω, conj (F (theta ω)) * F ω * (density ψ β ω : ℂ)
      ∂Measure.pi (fun _ : Link d n => ν₀)).im = 0 ∧
    0 ≤ (∫ ω, conj (F (theta ω)) * F ω * (density ψ β ω : ℂ)
      ∂Measure.pi (fun _ : Link d n => ν₀)).re := by
  obtain ⟨r, hr, he⟩ := wilson_reflection_positive ν₀ hν ψ β hclass hinv F hlocal
  exact ⟨integrable_reflection_form ν₀ hψ hbound β hF hFb,
    by rw [he]; rfl, by simpa only [he, Complex.ofReal_re] using hr⟩

end Action

end Lattice

#print axioms integral_conditional_square
#print axioms Lattice.closedHalf_iff
#print axioms Lattice.measurePreserving_theta
#print axioms Lattice.measurePreserving_join
#print axioms Lattice.plaquetteValue_theta
#print axioms Lattice.density_factorization
#print axioms Lattice.wilson_conditional_square
#print axioms Lattice.wilson_reflection_positive
#print axioms Lattice.partition_pos
#print axioms Lattice.bounded_wilson_reflection_positive
#print axioms Lattice.wilsonExpectation_reflection_positive

end Mettapedia.QuantumTheory.YangMills.WilsonReflectionPositivity
