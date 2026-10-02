import Mettapedia.Combinatorics.PolymerGas.Measure
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Regrouping activities by their support

A product of sums over fibres is a sum over sets choosing one element in each
fibre. This permits polymer activities with the same support to be added.
Finite-subset coefficients reconstruct activated functions exactly; products
convolve by union. Weighted coefficient domination passes through the full
convergent exponential and logarithm series.
-/

set_option autoImplicit false
noncomputable section

open Finset
open scoped Classical

namespace Mettapedia.Combinatorics.PolymerGas

variable {α β R : Type*} [DecidableEq α] [DecidableEq β] [CommSemiring R]

/-- Expanding fibre sums amounts to choosing an injective section over the
set of labels. -/
theorem prod_fiberSums (A : Finset α) (f : α → β) (w : α → R) (Γ : Finset β) :
    (∏ b ∈ Γ, ∑ a ∈ A.filter (fun a => f a = b), w a) =
      ∑ I ∈ A.powerset.filter (fun I : Finset α => Set.InjOn f (I : Set α) ∧ I.image f = Γ),
        ∏ a ∈ I, w a := by
  classical
  rw [← Finset.prod_attach Γ]
  change (∏ b : Γ, ∑ a ∈ A.filter (fun a => f a = b.1), w a) = _
  rw [Finset.prod_univ_sum]
  let choices := Fintype.piFinset (fun b : Γ => A.filter (fun a => f a = b.1))
  have hc_spec : ∀ c ∈ choices, ∀ b : Γ, c b ∈ A ∧ f (c b) = b.1 := by
    intro c hc b
    exact mem_filter.mp ((Fintype.mem_piFinset.mp hc) b)
  have hc_inj : ∀ c ∈ choices, Function.Injective c := by
    intro c hc b d h
    apply Subtype.ext
    exact ((hc_spec c hc b).2.symm.trans (congrArg f h)).trans (hc_spec c hc d).2
  apply Finset.sum_bij (fun c _ => univ.image c)
  · intro c hc
    refine mem_filter.mpr ⟨mem_powerset.mpr ?_, ?_, ?_⟩
    · intro a ha
      obtain ⟨b, _, rfl⟩ := mem_image.mp ha
      exact (hc_spec c hc b).1
    · intro a ha a' ha' heq
      obtain ⟨b, _, rfl⟩ := mem_image.mp ha
      obtain ⟨d, _, rfl⟩ := mem_image.mp ha'
      have : b = d := Subtype.ext
        (((hc_spec c hc b).2.symm.trans heq).trans (hc_spec c hc d).2)
      exact congrArg c this
    · ext b
      simp only [mem_image, mem_univ, true_and]
      constructor
      · rintro ⟨a, ⟨d, rfl⟩, rfl⟩
        exact (hc_spec c hc d).2.symm ▸ d.2
      · intro hb
        exact ⟨c ⟨b, hb⟩, ⟨⟨b, hb⟩, rfl⟩, (hc_spec c hc _).2⟩
  · intro c hc d hd heq
    funext b
    have : c b ∈ univ.image d := heq ▸ mem_image.mpr ⟨b, mem_univ _, rfl⟩
    obtain ⟨b', _, hbc⟩ := mem_image.mp this
    have hbb' : b' = b := Subtype.ext
      (((hc_spec d hd b').2.symm.trans (congrArg f hbc)).trans (hc_spec c hc b).2)
    simpa only [hbb'] using hbc.symm
  · intro I hI
    obtain ⟨hIA, hinj, himage⟩ := mem_filter.mp hI
    have hex : ∀ b : Γ, ∃ a ∈ I, f a = b.1 := by
      intro b
      exact mem_image.mp (himage.symm ▸ b.2)
    choose c hcI hcf using hex
    have hc : c ∈ choices := Fintype.mem_piFinset.mpr fun b =>
      mem_filter.mpr ⟨(mem_powerset.mp hIA) (hcI b), hcf b⟩
    refine ⟨c, hc, ?_⟩
    ext a
    constructor
    · intro ha
      obtain ⟨b, _, rfl⟩ := mem_image.mp ha
      exact hcI b
    · intro ha
      have hb : f a ∈ Γ := himage ▸ mem_image.mpr ⟨a, ha, rfl⟩
      exact mem_image.mpr ⟨⟨f a, hb⟩, mem_univ _, hinj (hcI _) ha (hcf _)⟩
  · intro c hc
    exact (prod_image (hc_inj c hc).injOn).symm

/-- Regroup a sum of fibre choices while imposing a condition on their labels. -/
theorem sum_prod_fiberSums [Fintype β] (A : Finset α) (f : α → β) (w : α → R)
    (P : Finset β → Prop) :
    (∑ Γ : Finset β, if P Γ then
      ∏ b ∈ Γ, ∑ a ∈ A.filter (fun a => f a = b), w a else 0) =
    ∑ I ∈ A.powerset, if Set.InjOn f (I : Set α) ∧ P (I.image f) then
      ∏ a ∈ I, w a else 0 := by
  classical
  calc
    _ = ∑ Γ : Finset β, ∑ I ∈ A.powerset,
        if I.image f = Γ then
          if Set.InjOn f (I : Set α) ∧ P Γ then ∏ a ∈ I, w a else 0
        else 0 := by
      apply sum_congr rfl
      intro Γ _
      rw [prod_fiberSums, sum_filter]
      by_cases hP : P Γ
      · simp only [hP, ↓reduceIte]
        apply sum_congr rfl
        intro I _
        split_ifs <;> simp_all
      · simp [hP]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro I _
      rw [sum_eq_single (I.image f)]
      · simp
      · intro Γ _ hΓ
        simp [Ne.symm hΓ]
      · simp

#print axioms prod_fiberSums
#print axioms sum_prod_fiberSums

end Mettapedia.Combinatorics.PolymerGas

/-! ## Finite-subset coefficients and analytic majorants -/

namespace Mettapedia.Combinatorics.PolymerGas.SubsetExpansion
variable {V A : Type*} [DecidableEq V]
section Additive
variable [AddCommGroup A]

def zeta (F : Finset V → A) (S : Finset V) : A := ∑ T ∈ S.powerset, F T

/-- Coefficients of a finite-subset expansion, defined by its triangular
reconstruction equation. This is finite Möbius inversion. -/
def coefficient (F : Finset V → A) (S : Finset V) : A :=
  F S - ∑ T : ↥(S.powerset.erase S), coefficient F T.val
termination_by S.card
decreasing_by
  exact Finset.card_lt_card ((ssubset_iff_subset_ne).mpr
    ⟨mem_powerset.mp (mem_erase.mp T.property).2, (mem_erase.mp T.property).1⟩)

theorem zeta_coefficient (F : Finset V → A) (S : Finset V) :
    zeta (coefficient F) S = F S := by
  unfold zeta
  rw [← sum_erase_add _ _ (mem_powerset_self S)]
  conv_lhs => rhs; rw [coefficient]
  rw [Finset.sum_coe_sort]
  abel

theorem zeta_injective : Function.Injective (zeta (V := V) (A := A)) := by
  intro F G h
  funext S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    have hh := congrFun h S
    change (∑ T ∈ S.powerset, F T) = ∑ T ∈ S.powerset, G T at hh
    rw [← sum_erase_add _ _ (mem_powerset_self S),
      ← sum_erase_add _ _ (mem_powerset_self S)] at hh
    have hs : ∑ T ∈ S.powerset.erase S, F T = ∑ T ∈ S.powerset.erase S, G T := by
      apply sum_congr rfl
      intro T hT
      exact ih T ((ssubset_iff_subset_ne).mpr
        ⟨mem_powerset.mp (mem_erase.mp hT).2, (mem_erase.mp hT).1⟩)
    rw [hs] at hh
    exact add_left_cancel hh

/-- Finite-subset coefficients commute with additive maps, including evaluation. -/
theorem coefficient_map {B : Type*} [AddCommGroup B] (f : A →+ B) (F : Finset V → A) :
    coefficient (fun S ↦ f (F S)) = fun S ↦ f (coefficient F S) := by
  apply zeta_injective
  funext S
  rw [zeta_coefficient]
  change f (F S) = ∑ T ∈ S.powerset, f (coefficient F T)
  rw [← map_sum]
  exact congrArg f (zeta_coefficient F S).symm
theorem coefficient_zeta (F : Finset V → A) : coefficient (zeta F) = F := by
  apply zeta_injective
  funext S
  exact zeta_coefficient (zeta F) S

theorem coefficient_injective : Function.Injective (coefficient (V := V) (A := A)) := by
  intro F G h
  funext S
  rw [← zeta_coefficient F S, ← zeta_coefficient G S, h]

@[simp] theorem zeta_add (F G : Finset V → A) : zeta (F + G) = zeta F + zeta G := by
  funext S
  exact Finset.sum_add_distrib

@[simp] theorem zeta_zero : zeta (0 : Finset V → A) = 0 := by
  funext S
  simp [zeta]

@[simp] theorem coefficient_add (F G : Finset V → A) :
    coefficient (F + G) = coefficient F + coefficient G := by
  apply zeta_injective
  rw [zeta_add]
  funext S
  simp only [zeta_coefficient, Pi.add_apply]

@[simp] theorem coefficient_zero : coefficient (0 : Finset V → A) = 0 := by
  apply zeta_injective
  rw [zeta_zero]
  funext S
  exact zeta_coefficient 0 S

@[simp] theorem coefficient_neg (F : Finset V → A) :
    coefficient (-F) = -coefficient F := by
  have h := coefficient_add F (-F)
  simp only [add_neg_cancel, coefficient_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

@[simp] theorem coefficient_sub (F G : Finset V → A) :
    coefficient (F - G) = coefficient F - coefficient G := by
  simp only [sub_eq_add_neg, coefficient_add, coefficient_neg]

/-- Disabling labels restricts the coefficient family to the remaining
subsets. This is exact and creates no new coefficients. -/
theorem coefficient_restrict (F : Finset V → A) (R : Finset V) :
    coefficient (fun S => F (S ∩ R)) =
      fun S => if S ⊆ R then coefficient F S else 0 := by
  apply zeta_injective
  funext S
  rw [zeta_coefficient]
  change F (S ∩ R) = ∑ T ∈ S.powerset, if T ⊆ R then coefficient F T else 0
  rw [← sum_filter]
  have he : S.powerset.filter (fun T => T ⊆ R) = (S ∩ R).powerset := by
    ext T
    simp only [mem_filter, mem_powerset, subset_inter_iff]
  rw [he]
  exact (zeta_coefficient F (S ∩ R)).symm

theorem coefficient_const (a : A) :
    coefficient (fun _ : Finset V => a) = fun S => if S = ∅ then a else 0 := by
  apply zeta_injective
  funext S
  rw [zeta_coefficient]
  simp [zeta]

theorem coefficient_indicator (p : V) (a : A) :
    coefficient (fun S : Finset V => if p ∈ S then a else 0) =
      fun S => if S = {p} then a else 0 := by
  apply zeta_injective
  funext S
  rw [zeta_coefficient]
  simp [zeta]

section Topology
variable [TopologicalSpace A] [IsTopologicalAddGroup A]

/-- Finite-subset coefficients commute with a convergent series; there is no
exchange of two infinite sums. -/
theorem coefficient_hasSum {f : ℕ → Finset V → A} {F : Finset V → A}
    (h : ∀ S, HasSum (fun n => f n S) (F S)) (S : Finset V) :
    HasSum (fun n => coefficient (f n) S) (coefficient F S) := by
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    have ht : ∀ T : ↥(S.powerset.erase S),
        HasSum (fun n => coefficient (f n) T.val) (coefficient F T.val) := by
      intro T
      exact ih T.val ((ssubset_iff_subset_ne).mpr
        ⟨mem_powerset.mp (mem_erase.mp T.property).2, (mem_erase.mp T.property).1⟩)
    have hs := (h S).sub (hasSum_sum (s := univ) (fun T _ => ht T))
    convert hs using 1
    · funext n
      rw [coefficient]
    · rw [coefficient]

end Topology

end Additive

section Multiplication
variable [Fintype V] [CommRing A]

def convolution (F G : Finset V → A) (S : Finset V) : A :=
  ∑ T, ∑ U, if T ∪ U = S then F T * G U else 0

theorem zeta_eq_sum_ite (F : Finset V → A) (S : Finset V) :
    zeta F S = ∑ T, if T ⊆ S then F T else 0 := by
  unfold zeta
  rw [← Finset.sum_filter]
  apply sum_congr
  · ext T
    simp
  · intros; rfl

theorem zeta_convolution (F G : Finset V → A) :
    zeta (convolution F G) = zeta F * zeta G := by
  funext S
  change zeta (convolution F G) S = zeta F S * zeta G S
  rw [zeta_eq_sum_ite F, zeta_eq_sum_ite G]
  unfold zeta convolution
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := S.powerset)]
  simp only [Finset.sum_ite_eq, mem_powerset, union_subset_iff]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  apply Finset.sum_congr rfl
  intro U _
  split_ifs <;> simp_all

theorem coefficient_mul (F G : Finset V → A) :
    coefficient (F * G) = convolution (coefficient F) (coefficient G) := by
  apply zeta_injective
  rw [zeta_convolution]
  funext S
  simp only [zeta_coefficient, Pi.mul_apply]

theorem coefficient_smul (c : A) (F : Finset V → A) :
    coefficient (fun S => c * F S) = fun S => c * coefficient F S := by
  apply zeta_injective
  funext S
  rw [zeta_coefficient]
  change c * F S = ∑ T ∈ S.powerset, c * coefficient F T
  rw [← mul_sum]
  congr 1
  exact (zeta_coefficient F S).symm

end Multiplication

section Majorants
variable [Fintype V]

/-- A weight that is submultiplicative under union, including overlap. -/
structure UnionWeight (V : Type*) [DecidableEq V] where
  toFun : Finset V → ℝ
  one_le : ∀ S, 1 ≤ toFun S
  empty : toFun ∅ = 1
  union_le : ∀ S T, toFun (S ∪ T) ≤ toFun S * toFun T

instance : CoeFun (UnionWeight V) (fun _ => Finset V → ℝ) := ⟨UnionWeight.toFun⟩

def Majorizes (w : UnionWeight V) (F G : Finset V → ℝ) : Prop :=
  ∀ S, w S * |coefficient F S| ≤ coefficient G S

variable {w : UnionWeight V} {F G H K : Finset V → ℝ}

theorem Majorizes.nonneg (h : Majorizes w F G) (S : Finset V) :
    0 ≤ coefficient G S :=
  (mul_nonneg ((w.one_le S).trans' (by norm_num)) (abs_nonneg _)).trans (h S)

theorem Majorizes.abs_eval_le (h : Majorizes w F G) (S : Finset V) : |F S| ≤ G S := by
  rw [← zeta_coefficient F S, ← zeta_coefficient G S]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro T hT
  exact (le_mul_of_one_le_left (abs_nonneg _) (w.one_le T)).trans (h T)

theorem Majorizes.eval_nonneg (h : Majorizes w F G) (S : Finset V) : 0 ≤ G S :=
  (abs_nonneg _).trans (h.abs_eval_le S)

theorem Majorizes.neg (h : Majorizes w F G) : Majorizes w (-F) G := by
  intro S
  simpa only [coefficient_neg, Pi.neg_apply, abs_neg] using h S

theorem Majorizes.add (h : Majorizes w F G) (h' : Majorizes w H K) :
    Majorizes w (F + H) (G + K) := by
  intro S
  simp only [coefficient_add, Pi.add_apply]
  calc
    _ ≤ w S * (|coefficient F S| + |coefficient H S|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) (by linarith [w.one_le S])
    _ ≤ _ := by nlinarith [h S, h' S]

theorem majorizes_const (w : UnionWeight V) {a b : ℝ} (h : |a| ≤ b) :
    Majorizes w (fun _ => a) (fun _ => b) := by
  intro S
  rw [coefficient_const, coefficient_const]
  by_cases hS : S = ∅
  · subst S
    simpa [w.empty] using h
  · simp [hS]

theorem majorizes_indicator (w : UnionWeight V) (p : V) {a b : ℝ}
    (h : w {p} * |a| ≤ b) :
    Majorizes w (fun S => if p ∈ S then a else 0)
      (fun S => if p ∈ S then b else 0) := by
  intro S
  rw [coefficient_indicator, coefficient_indicator]
  by_cases hS : S = {p}
  · subst S
    simpa using h
  · simp [hS]

theorem Majorizes.restrict (h : Majorizes w F G) (R : Finset V) :
    Majorizes w (fun S => F (S ∩ R)) (fun S => G (S ∩ R)) := by
  intro S
  rw [coefficient_restrict, coefficient_restrict]
  by_cases hS : S ⊆ R
  · simpa [hS] using h S
  · simp [hS]

theorem Majorizes.sub_restrict (h : Majorizes w F G) (R : Finset V) :
    Majorizes w (F - fun S => F (S ∩ R)) (G - fun S => G (S ∩ R)) := by
  intro S
  simp only [coefficient_sub, coefficient_restrict, Pi.sub_apply]
  by_cases hS : S ⊆ R
  · simp [hS]
  · simpa [hS] using h S

theorem Majorizes.mul (h : Majorizes w F G) (h' : Majorizes w H K) :
    Majorizes w (F * H) (G * K) := by
  intro S
  rw [coefficient_mul, coefficient_mul]
  unfold convolution
  calc
    _ ≤ w S * ∑ T, ∑ U,
        |if T ∪ U = S then coefficient F T * coefficient H U else 0| := by
      apply mul_le_mul_of_nonneg_left _ (by linarith [w.one_le S])
      exact (abs_sum_le_sum_abs _ _).trans
        (sum_le_sum fun T _ => abs_sum_le_sum_abs _ _)
    _ = ∑ T, ∑ U,
        if T ∪ U = S then w S * (|coefficient F T| * |coefficient H U|) else 0 := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro T _
      apply sum_congr rfl
      intro U _
      split_ifs <;> simp [abs_mul]
    _ ≤ _ := by
      apply sum_le_sum
      intro T _
      apply sum_le_sum
      intro U _
      by_cases hTU : T ∪ U = S
      · simp only [if_pos hTU]
        calc
          _ ≤ (w T * w U) * (|coefficient F T| * |coefficient H U|) :=
            mul_le_mul_of_nonneg_right (hTU ▸ w.union_le T U) (by positivity)
          _ = (w T * |coefficient F T|) * (w U * |coefficient H U|) := by ring
          _ ≤ _ := mul_le_mul (h T) (h' U) (by
            have := w.one_le U; positivity) (h.nonneg T)
      · simp [hTU]

theorem Majorizes.pow (h : Majorizes w F G) (n : ℕ) :
    Majorizes w (F ^ n) (G ^ n) := by
  induction n with
  | zero =>
    change Majorizes w (fun _ => 1) (fun _ => 1)
    exact majorizes_const w (show |(1 : ℝ)| ≤ 1 by norm_num)
  | succ n ih => simpa only [pow_succ] using ih.mul h

theorem Majorizes.scale (h : Majorizes w F G) {c : ℝ} (hc : 0 ≤ c) :
    Majorizes w (fun S => c * F S) (fun S => c * G S) := by
  intro S
  rw [coefficient_smul, coefficient_smul, abs_mul, abs_of_nonneg hc]
  nlinarith [h S]

/-- Coefficientwise domination passes to convergent series. The comparison
already contains every coefficient order. -/
theorem majorizes_series {f g : ℕ → Finset V → ℝ} {F G : Finset V → ℝ}
    (h : ∀ n, Majorizes w (f n) (g n))
    (hf : ∀ S, HasSum (fun n => f n S) (F S))
    (hg : ∀ S, HasSum (fun n => g n S) (G S)) : Majorizes w F G := by
  intro S
  have h' := ((coefficient_hasSum hf S).mul_left (w S)).norm_le_of_bounded
    (coefficient_hasSum hg S) (fun n => by
      simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (show 0 ≤ w S by
        linarith [w.one_le S])] using h n S)
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (show 0 ≤ w S by
    linarith [w.one_le S])] using h'

theorem Majorizes.exp (h : Majorizes w F G) :
    Majorizes w (fun S => Real.exp (F S)) (fun S => Real.exp (G S)) := by
  apply majorizes_series (f := fun n S => ((n.factorial : ℝ)⁻¹) * F S ^ n)
    (g := fun n S => ((n.factorial : ℝ)⁻¹) * G S ^ n)
  · intro n
    exact (h.pow n).scale (by positivity)
  · intro S
    simpa only [div_eq_mul_inv, mul_comm, Real.exp_eq_exp_ℝ] using
      NormedSpace.expSeries_div_hasSum_exp (F S)
  · intro S
    simpa only [div_eq_mul_inv, mul_comm, Real.exp_eq_exp_ℝ] using
      NormedSpace.expSeries_div_hasSum_exp (G S)

theorem Majorizes.neg_log_one_sub (h : Majorizes w F G) (hG : ∀ S, G S < 1) :
    Majorizes w (fun S => -Real.log (1 - F S)) (fun S => -Real.log (1 - G S)) := by
  apply majorizes_series (f := fun n S => ((n+1 : ℝ)⁻¹) * F S ^ (n+1))
    (g := fun n S => ((n+1 : ℝ)⁻¹) * G S ^ (n+1))
  · intro n
    exact (h.pow (n+1)).scale (by positivity)
  · intro S
    simpa only [div_eq_mul_inv, mul_comm] using
      Real.hasSum_pow_div_log_of_abs_lt_one ((h.abs_eval_le S).trans_lt (hG S))
  · intro S
    simpa only [div_eq_mul_inv, mul_comm] using
      Real.hasSum_pow_div_log_of_abs_lt_one (show |G S| < 1 by
        rw [abs_of_nonneg (h.eval_nonneg S)]
        exact hG S)

theorem Majorizes.log_one_add (h : Majorizes w F G) (hG : ∀ S, G S < 1) :
    Majorizes w (fun S => Real.log (1 + F S)) (fun S => -Real.log (1 - G S)) := by
  have he : (-fun S => -Real.log (1 - (-F) S)) = (fun S => Real.log (1 + F S)) := by
    funext S
    simp only [Pi.neg_apply, sub_neg_eq_add, neg_neg]
  rw [← he]
  exact (h.neg.neg_log_one_sub hG).neg

end Majorants

end Mettapedia.Combinatorics.PolymerGas.SubsetExpansion
