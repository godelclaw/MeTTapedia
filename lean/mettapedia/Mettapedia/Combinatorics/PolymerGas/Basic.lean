import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Polymer gases: the Dobrushin and Kotecký–Preiss criteria

A polymer gas is a set `V` of polymers with a reflexive, symmetric
incompatibility relation and complex activities `w`.  Incompatibility of
distinct polymers is a simple graph `G`, and a compatible family is a finite
independent set of `G`.  For a finite set `Λ` of polymers the partition function

`Z(Λ) = ∑_{I ⊆ Λ compatible} ∏_{γ ∈ I} w γ`

is the multivariate independence polynomial of `G` on `Λ`. Its definition
is shared over commutative semirings; the norm estimates use complex activities.
It satisfies
`Z(Λ ∪ {γ}) = Z(Λ) + w γ · Z(Λ ∖ N(γ))`, where `N(γ)` is the set of polymers
incompatible with `γ` (`partitionFunction_insert`).

Dobrushin's criterion asks for weights `c ≥ 0` with
`|w γ| ≤ (1 - e^{-c γ}) e^{-∑_{u ∈ S} c u}` for every finite set `S` of
polymers incompatible with `γ`.  Under it `Z(Λ) ≠ 0` for every finite `Λ`, and
removing a polymer `u` multiplies `|Z|` by at most `e^{c u}` and adding it by at
most `e^{c u}` as well (`removalBound_of_dobrushin`,
`norm_partitionFunction_le_exp_mul_erase`).  The proof is an induction on `|Λ|`.
The Kotecký–Preiss criterion `|w γ| e^{a γ} + ∑_{u ∈ S} |w u| e^{a u} ≤ a γ`
implies Dobrushin's criterion with `c = log (1 + |w| e^a)`
(`dobrushinCondition_of_koteckyPreiss`, `koteckyPreiss`).  No cluster expansion
is used.
-/

set_option autoImplicit false
noncomputable section

open Finset

namespace Mettapedia.Combinatorics.PolymerGas

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A finite family of polymers is compatible when no two of its members are
incompatible, i.e. adjacent in `G`. -/
def IsCompatible (I : Finset V) : Prop :=
  ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v

instance (I : Finset V) : Decidable (IsCompatible G I) := by
  unfold IsCompatible
  infer_instance

/-- The partition function of the polymers in `Λ` with activities `w`: the sum
over compatible subfamilies of the product of their activities. -/
def partitionFunction {R : Type*} [CommSemiring R] (w : V → R) (Λ : Finset V) : R :=
  ∑ I ∈ Λ.powerset, if IsCompatible G I then ∏ γ ∈ I, w γ else 0

/-- The independence polynomial commutes with semiring homomorphisms. -/
theorem partitionFunction_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (w : V → R) (Λ : Finset V) :
    f (partitionFunction G w Λ) = partitionFunction G (fun p => f (w p)) Λ := by
  unfold partitionFunction
  simp only [map_sum]
  apply sum_congr rfl
  intro I hI
  split_ifs <;> simp only [map_prod, map_zero]

/-- The real partition polynomial is the real-activity specialization of the
same complex polynomial used by the convergence estimates. -/
theorem ofReal_partitionFunction (a : V → ℝ) (Λ : Finset V) :
    ((partitionFunction G a Λ : ℝ) : ℂ) = partitionFunction G (fun p => (a p : ℂ)) Λ :=
  partitionFunction_map G Complex.ofRealHom a Λ

/-- The polymers of `S` compatible with `γ`. -/
def compatibleWith (S : Finset V) (γ : V) : Finset V :=
  S.filter fun u => ¬ G.Adj γ u

variable {G}

omit [DecidableEq V] in
@[simp] theorem partitionFunction_empty {R : Type*} [CommSemiring R] (w : V → R) :
    partitionFunction G w ∅ = 1 := by
  simp [partitionFunction, IsCompatible]

omit [DecidableEq V] in
/-- The partition function over `Λ` depends only on the weights of the polymers
of `Λ`. -/
theorem partitionFunction_congr {R : Type*} [CommSemiring R] {w w' : V → R} {Λ : Finset V}
    (h : ∀ γ ∈ Λ, w γ = w' γ) : partitionFunction G w Λ = partitionFunction G w' Λ := by
  unfold partitionFunction
  refine sum_congr rfl fun I hI => ?_
  have hsub : I ⊆ Λ := mem_powerset.mp hI
  split_ifs
  · exact prod_congr rfl fun γ hγ => h γ (hsub hγ)
  · rfl

omit [DecidableRel G.Adj] in
theorem isCompatible_insert {t : Finset V} {γ : V} :
    IsCompatible G (insert γ t) ↔ IsCompatible G t ∧ ∀ u ∈ t, ¬ G.Adj γ u := by
  constructor
  · intro h
    exact ⟨fun u hu v hv => h u (mem_insert_of_mem hu) v (mem_insert_of_mem hv),
      fun u hu => h γ (mem_insert_self γ t) u (mem_insert_of_mem hu)⟩
  · rintro ⟨ht, hγ⟩ u hu v hv
    rcases mem_insert.mp hu with hu | hu <;> rcases mem_insert.mp hv with hv | hv
    · rw [hu, hv]
      exact G.irrefl
    · rw [hu]
      exact hγ v hv
    · rw [hv]
      exact fun h => hγ u hu h.symm
    · exact ht u hu v hv

/-- The fundamental recursion: a compatible family either omits `γ` or contains
it together with a compatible family of polymers compatible with `γ`. -/
theorem partitionFunction_insert {R : Type*} [CommSemiring R] (w : V → R) {S : Finset V} {γ : V} (hγ : γ ∉ S) :
    partitionFunction G w (insert γ S) =
      partitionFunction G w S + w γ * partitionFunction G w (compatibleWith G S γ) := by
  unfold partitionFunction
  rw [sum_powerset_insert hγ, mul_sum]
  congr 1
  have hterm : ∀ t ∈ S.powerset,
      (if IsCompatible G (insert γ t) then ∏ x ∈ insert γ t, w x else 0) =
        if t ⊆ compatibleWith G S γ then
          w γ * (if IsCompatible G t then ∏ x ∈ t, w x else 0) else 0 := by
    intro t ht
    have htS : t ⊆ S := mem_powerset.mp ht
    have hγt : γ ∉ t := fun h => hγ (htS h)
    by_cases hsub : t ⊆ compatibleWith G S γ
    · have hadj : ∀ u ∈ t, ¬ G.Adj γ u := fun u hu => (mem_filter.mp (hsub hu)).2
      by_cases hc : IsCompatible G t
      · have hci : IsCompatible G (insert γ t) := isCompatible_insert.mpr ⟨hc, hadj⟩
        simp [hsub, hc, hci, prod_insert hγt]
      · have hci : ¬ IsCompatible G (insert γ t) := fun h => hc (isCompatible_insert.mp h).1
        simp [hsub, hc, hci]
    · have hci : ¬ IsCompatible G (insert γ t) := by
        intro h
        exact hsub fun u hu => mem_filter.mpr ⟨htS hu, (isCompatible_insert.mp h).2 u hu⟩
      simp [hsub, hci]
  rw [sum_congr rfl hterm, ← sum_filter]
  apply sum_congr _ fun _ _ => rfl
  ext t
  simp only [mem_filter, mem_powerset]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    exact ⟨h.trans (filter_subset _ _), h⟩

theorem compatibleWith_eq_sdiff (S : Finset V) (γ : V) :
    compatibleWith G S γ = S \ S.filter (G.Adj γ) := by
  ext u
  simp only [compatibleWith, mem_filter, mem_sdiff]
  tauto

/-! ## Dobrushin's criterion -/

variable (G) in
/-- Dobrushin's criterion with weights `c`: every activity is bounded by
`(1 - e^{-c γ}) e^{-∑_{u ∈ S} c u}` for every finite set `S` of polymers
incompatible with `γ`. -/
structure DobrushinCondition (w : V → ℂ) (c : V → ℝ) : Prop where
  nonneg : ∀ γ, 0 ≤ c γ
  bound : ∀ γ (S : Finset V), (∀ u ∈ S, G.Adj γ u) →
    ‖w γ‖ ≤ (1 - Real.exp (-c γ)) * Real.exp (-∑ u ∈ S, c u)

variable (G) in
/-- The partition function of `T` does not vanish, and removing one polymer
multiplies its modulus by at most `e^{c u}`. -/
def RemovalBound (w : V → ℂ) (c : V → ℝ) (T : Finset V) : Prop :=
  partitionFunction G w T ≠ 0 ∧
    ∀ u ∈ T, ‖partitionFunction G w (T.erase u)‖ ≤ Real.exp (c u) * ‖partitionFunction G w T‖

/-- Removing a set `B` of polymers multiplies the modulus by at most
`e^{∑_{u ∈ B} c u}`, once single removals are controlled below `S`. -/
theorem norm_partitionFunction_sdiff_le {w : V → ℂ} {c : V → ℝ} (hc : ∀ γ, 0 ≤ c γ)
    {S : Finset V} (hS : ∀ T ⊆ S, RemovalBound G w c T) (B : Finset V) :
    ‖partitionFunction G w (S \ B)‖ ≤
      Real.exp (∑ u ∈ B, c u) * ‖partitionFunction G w S‖ := by
  induction B using Finset.induction_on with
  | empty => simp
  | insert b B hb ih =>
    rw [sum_insert hb, Real.exp_add]
    have hsub : S \ insert b B = (S \ B).erase b := by
      ext u
      simp only [mem_sdiff, mem_insert, mem_erase]
      tauto
    rw [hsub]
    by_cases hbS : b ∈ S \ B
    · calc ‖partitionFunction G w ((S \ B).erase b)‖
          ≤ Real.exp (c b) * ‖partitionFunction G w (S \ B)‖ :=
            (hS (S \ B) sdiff_subset).2 b hbS
        _ ≤ Real.exp (c b) * (Real.exp (∑ u ∈ B, c u) * ‖partitionFunction G w S‖) := by
            gcongr
        _ = Real.exp (c b) * Real.exp (∑ u ∈ B, c u) * ‖partitionFunction G w S‖ := by
            ring
    · rw [erase_eq_of_notMem hbS]
      have hone : 1 ≤ Real.exp (c b) := Real.one_le_exp (hc b)
      calc ‖partitionFunction G w (S \ B)‖
          ≤ Real.exp (∑ u ∈ B, c u) * ‖partitionFunction G w S‖ := ih
        _ ≤ Real.exp (c b) * Real.exp (∑ u ∈ B, c u) * ‖partitionFunction G w S‖ := by
            have := mul_nonneg (Real.exp_pos (∑ u ∈ B, c u)).le
              (norm_nonneg (partitionFunction G w S))
            nlinarith

/-- **Dobrushin's theorem.**  Under Dobrushin's criterion the partition function
of every finite set of polymers is nonzero, and removing a polymer `u`
multiplies its modulus by at most `e^{c u}`. -/
theorem removalBound_of_dobrushin {w : V → ℂ} {c : V → ℝ}
    (hD : DobrushinCondition G w c) (Λ : Finset V) : RemovalBound G w c Λ := by
  induction Λ using Finset.strongInduction with
  | H Λ ih =>
    have key : ∀ γ ∈ Λ,
        Real.exp (-c γ) * ‖partitionFunction G w (Λ.erase γ)‖ ≤ ‖partitionFunction G w Λ‖ ∧
          partitionFunction G w (Λ.erase γ) ≠ 0 := by
      intro γ hγ
      set S := Λ.erase γ with hSdef
      have hSsub : ∀ T ⊆ S, RemovalBound G w c T := fun T hT =>
        ih T (_root_.ssubset_of_subset_of_ssubset hT (erase_ssubset hγ))
      have hZS : partitionFunction G w S ≠ 0 := (hSsub S subset_rfl).1
      have hA : ‖partitionFunction G w (compatibleWith G S γ)‖ ≤
          Real.exp (∑ u ∈ S.filter (G.Adj γ), c u) * ‖partitionFunction G w S‖ := by
        rw [compatibleWith_eq_sdiff]
        exact norm_partitionFunction_sdiff_le hD.nonneg hSsub _
      have hw := hD.bound γ (S.filter (G.Adj γ)) fun u hu => (mem_filter.mp hu).2
      have hfac : 0 ≤ 1 - Real.exp (-c γ) := by
        have : Real.exp (-c γ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hD.nonneg γ])
        linarith
      have hprod : ‖w γ * partitionFunction G w (compatibleWith G S γ)‖ ≤
          (1 - Real.exp (-c γ)) * ‖partitionFunction G w S‖ := by
        rw [norm_mul]
        calc ‖w γ‖ * ‖partitionFunction G w (compatibleWith G S γ)‖
            ≤ ((1 - Real.exp (-c γ)) * Real.exp (-∑ u ∈ S.filter (G.Adj γ), c u)) *
                (Real.exp (∑ u ∈ S.filter (G.Adj γ), c u) * ‖partitionFunction G w S‖) :=
              mul_le_mul hw hA (norm_nonneg _) (mul_nonneg hfac (Real.exp_pos _).le)
          _ = (1 - Real.exp (-c γ)) * ‖partitionFunction G w S‖ := by
              rw [show ∀ a b e f : ℝ, a * b * (e * f) = a * (b * e) * f by intros; ring,
                ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
      have hΛ : partitionFunction G w Λ =
          partitionFunction G w S + w γ * partitionFunction G w (compatibleWith G S γ) := by
        conv_lhs => rw [← insert_erase hγ]
        exact partitionFunction_insert w (notMem_erase γ Λ)
      refine ⟨?_, hZS⟩
      have htri := norm_sub_le (partitionFunction G w Λ)
        (w γ * partitionFunction G w (compatibleWith G S γ))
      rw [hΛ, add_sub_cancel_right] at htri
      rw [hΛ]
      have hsplit : Real.exp (-c γ) * ‖partitionFunction G w S‖ =
          ‖partitionFunction G w S‖ - (1 - Real.exp (-c γ)) * ‖partitionFunction G w S‖ := by
        ring
      linarith
    refine ⟨?_, fun u hu => ?_⟩
    · rcases Λ.eq_empty_or_nonempty with hΛ | ⟨γ, hγ⟩
      · simp [hΛ]
      · obtain ⟨hlow, hZ⟩ := key γ hγ
        intro hzero
        rw [hzero, norm_zero] at hlow
        have : 0 < Real.exp (-c γ) * ‖partitionFunction G w (Λ.erase γ)‖ :=
          mul_pos (Real.exp_pos _) (norm_pos_iff.mpr hZ)
        linarith
    · obtain ⟨hlow, _⟩ := key u hu
      calc ‖partitionFunction G w (Λ.erase u)‖
          = Real.exp (c u) * (Real.exp (-c u) * ‖partitionFunction G w (Λ.erase u)‖) := by
            rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
        _ ≤ Real.exp (c u) * ‖partitionFunction G w Λ‖ := by gcongr

/-- Under Dobrushin's criterion, removing any set `B` of polymers from `Λ`
multiplies the modulus of the partition function by at most `e^{∑_{u∈B} c u}`. -/
theorem norm_partitionFunction_sdiff_le_of_dobrushin {w : V → ℂ} {c : V → ℝ}
    (hD : DobrushinCondition G w c) (Λ B : Finset V) :
    ‖partitionFunction G w (Λ \ B)‖ ≤
      Real.exp (∑ u ∈ B, c u) * ‖partitionFunction G w Λ‖ :=
  norm_partitionFunction_sdiff_le hD.nonneg (fun T _ => removalBound_of_dobrushin hD T) B

/-! ## The Kotecký–Preiss criterion -/

variable (G) in
/-- The Kotecký–Preiss criterion with weights `a`: for every polymer `γ` and
every finite set `S` of polymers incompatible with it,
`|w γ| e^{a γ} + ∑_{u ∈ S} |w u| e^{a u} ≤ a γ`. -/
structure KoteckyPreissCondition (w : V → ℂ) (a : V → ℝ) : Prop where
  nonneg : ∀ γ, 0 ≤ a γ
  bound : ∀ γ (S : Finset V), (∀ u ∈ S, G.Adj γ u) →
    ‖w γ‖ * Real.exp (a γ) + ∑ u ∈ S, ‖w u‖ * Real.exp (a u) ≤ a γ

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The Kotecký–Preiss criterion implies Dobrushin's criterion with weights
`c γ = log (1 + |w γ| e^{a γ})`. -/
theorem dobrushinCondition_of_koteckyPreiss {w : V → ℂ} {a : V → ℝ}
    (h : KoteckyPreissCondition G w a) :
    DobrushinCondition G w fun γ => Real.log (1 + ‖w γ‖ * Real.exp (a γ)) where
  nonneg γ := Real.log_nonneg (by
    have := mul_nonneg (norm_nonneg (w γ)) (Real.exp_pos (a γ)).le
    linarith)
  bound γ S hS := by
    set x : V → ℝ := fun u => ‖w u‖ * Real.exp (a u) with hxdef
    have hx : ∀ u, 0 ≤ x u := fun u => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
    have hkp : x γ + ∑ u ∈ S, x u ≤ a γ := h.bound γ S hS
    show ‖w γ‖ ≤ (1 - Real.exp (-Real.log (1 + x γ))) * Real.exp (-∑ u ∈ S, Real.log (1 + x u))
    have hne : 1 + x γ ≠ 0 := by linarith [hx γ]
    have h1 : 1 - Real.exp (-Real.log (1 + x γ)) = x γ / (1 + x γ) := by
      rw [Real.exp_neg, Real.exp_log (by linarith [hx γ])]
      field_simp
      ring
    have h2 : Real.exp (-∑ u ∈ S, x u) ≤ Real.exp (-∑ u ∈ S, Real.log (1 + x u)) := by
      apply Real.exp_le_exp.mpr
      apply neg_le_neg
      apply sum_le_sum
      intro u _
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + x u by linarith [hx u])
      linarith
    have h3 : x γ * Real.exp (-x γ) ≤ x γ / (1 + x γ) := by
      rw [le_div_iff₀ (by linarith [hx γ])]
      have hexp := Real.add_one_le_exp (x γ)
      have hnn : 0 ≤ x γ * Real.exp (-x γ) := mul_nonneg (hx γ) (Real.exp_pos _).le
      calc x γ * Real.exp (-x γ) * (1 + x γ)
          ≤ x γ * Real.exp (-x γ) * Real.exp (x γ) := by
            apply mul_le_mul_of_nonneg_left _ hnn
            linarith
        _ = x γ := by rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    have h4 : ‖w γ‖ = x γ * Real.exp (-a γ) := by
      simp only [hxdef]
      rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    rw [h1, h4]
    calc x γ * Real.exp (-a γ)
        ≤ x γ * Real.exp (-(x γ + ∑ u ∈ S, x u)) := by
          apply mul_le_mul_of_nonneg_left _ (hx γ)
          exact Real.exp_le_exp.mpr (by linarith)
      _ = x γ * Real.exp (-x γ) * Real.exp (-∑ u ∈ S, x u) := by
          rw [neg_add, Real.exp_add]
          ring
      _ ≤ x γ / (1 + x γ) * Real.exp (-∑ u ∈ S, Real.log (1 + x u)) :=
          mul_le_mul h3 h2 (Real.exp_pos _).le (div_nonneg (hx γ) (by linarith [hx γ]))

/-- **Kotecký–Preiss.**  Under the Kotecký–Preiss criterion the partition
function of every finite set of polymers is nonzero, and removing a polymer
`γ` multiplies its modulus by at most `1 + |w γ| e^{a γ}`. -/
theorem koteckyPreiss {w : V → ℂ} {a : V → ℝ} (h : KoteckyPreissCondition G w a)
    (Λ : Finset V) :
    partitionFunction G w Λ ≠ 0 ∧
      ∀ γ ∈ Λ, ‖partitionFunction G w (Λ.erase γ)‖ ≤
        (1 + ‖w γ‖ * Real.exp (a γ)) * ‖partitionFunction G w Λ‖ := by
  obtain ⟨h0, h1⟩ := removalBound_of_dobrushin (dobrushinCondition_of_koteckyPreiss h) Λ
  refine ⟨h0, fun γ hγ => ?_⟩
  have hpos : 0 < 1 + ‖w γ‖ * Real.exp (a γ) := by
    have := mul_nonneg (norm_nonneg (w γ)) (Real.exp_pos (a γ)).le
    linarith
  simpa [Real.exp_log hpos] using h1 γ hγ


/-! ## Consequences of the removal bounds -/

/-- The polymers of `S` incompatible with `γ` are exactly those removed in
passing to `compatibleWith G S γ`. -/
theorem sdiff_filter_adj (S : Finset V) (γ : V) :
    S \ S.filter (G.Adj γ) = compatibleWith G S γ :=
  (compatibleWith_eq_sdiff S γ).symm

/-- Under Dobrushin's criterion, the polymer `a` contributes at most a fraction
`1 - e^{-c a}` of the partition function without it. -/
theorem norm_mul_partitionFunction_compatibleWith_le {w : V → ℂ} {c : V → ℝ}
    (hD : DobrushinCondition G w c) (S : Finset V) (a : V) :
    ‖w a * partitionFunction G w (compatibleWith G S a)‖ ≤
      (1 - Real.exp (-c a)) * ‖partitionFunction G w S‖ := by
  have hA : ‖partitionFunction G w (compatibleWith G S a)‖ ≤
      Real.exp (∑ u ∈ S.filter (G.Adj a), c u) * ‖partitionFunction G w S‖ := by
    rw [compatibleWith_eq_sdiff]
    exact norm_partitionFunction_sdiff_le_of_dobrushin hD S _
  have hw := hD.bound a (S.filter (G.Adj a)) fun u hu => (mem_filter.mp hu).2
  have hfac : 0 ≤ 1 - Real.exp (-c a) := by
    have : Real.exp (-c a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hD.nonneg a])
    linarith
  rw [norm_mul]
  calc ‖w a‖ * ‖partitionFunction G w (compatibleWith G S a)‖
      ≤ ((1 - Real.exp (-c a)) * Real.exp (-∑ u ∈ S.filter (G.Adj a), c u)) *
          (Real.exp (∑ u ∈ S.filter (G.Adj a), c u) * ‖partitionFunction G w S‖) :=
        mul_le_mul hw hA (norm_nonneg _) (mul_nonneg hfac (Real.exp_pos _).le)
    _ = (1 - Real.exp (-c a)) * ‖partitionFunction G w S‖ := by
        rw [show ∀ p q r s : ℝ, p * q * (r * s) = p * (q * r) * s by intros; ring,
          ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

theorem partitionFunction_eq_erase_add {R : Type*} [CommSemiring R] {w : V → R} {M : Finset V} {a : V} (ha : a ∈ M) :
    partitionFunction G w M =
      partitionFunction G w (M.erase a) +
        w a * partitionFunction G w (compatibleWith G (M.erase a) a) := by
  conv_lhs => rw [← insert_erase ha]
  exact partitionFunction_insert w (notMem_erase a M)

/-- Under Dobrushin's criterion, adding a polymer multiplies the modulus of the
partition function by at most `e^{c a}`. -/
theorem norm_partitionFunction_le_exp_mul_erase {w : V → ℂ} {c : V → ℝ}
    (hD : DobrushinCondition G w c) (M : Finset V) (a : V) :
    ‖partitionFunction G w M‖ ≤ Real.exp (c a) * ‖partitionFunction G w (M.erase a)‖ := by
  by_cases ha : a ∈ M
  · rw [partitionFunction_eq_erase_add ha]
    have h1 := norm_mul_partitionFunction_compatibleWith_le hD (M.erase a) a
    have h2 := norm_add_le (partitionFunction G w (M.erase a))
      (w a * partitionFunction G w (compatibleWith G (M.erase a) a))
    have hexp : 2 - Real.exp (-c a) ≤ Real.exp (c a) := by
      have h := Real.add_one_le_exp (c a)
      have h' := Real.add_one_le_exp (-c a)
      have hprod : Real.exp (c a) * Real.exp (-c a) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      nlinarith [Real.exp_pos (c a), Real.exp_pos (-c a)]
    have hnn := norm_nonneg (partitionFunction G w (M.erase a))
    nlinarith
  · rw [erase_eq_of_notMem ha]
    have := Real.one_le_exp (hD.nonneg a)
    nlinarith [norm_nonneg (partitionFunction G w M)]

/-- Under Dobrushin's criterion, removing a polymer changes the partition
function by at most `(e^{c a} - 1) |Z(M)|`. -/
theorem norm_partitionFunction_erase_sub_le {w : V → ℂ} {c : V → ℝ}
    (hD : DobrushinCondition G w c) (M : Finset V) (a : V) :
    ‖partitionFunction G w (M.erase a) - partitionFunction G w M‖ ≤
      (Real.exp (c a) - 1) * ‖partitionFunction G w M‖ := by
  by_cases ha : a ∈ M
  · have hsub : partitionFunction G w (M.erase a) - partitionFunction G w M =
        -(w a * partitionFunction G w (compatibleWith G (M.erase a) a)) := by
      rw [partitionFunction_eq_erase_add ha]
      ring
    rw [hsub, norm_neg]
    have h1 := norm_mul_partitionFunction_compatibleWith_le hD (M.erase a) a
    have h2 := (removalBound_of_dobrushin hD M).2 a ha
    have hfac : 0 ≤ 1 - Real.exp (-c a) := by
      have : Real.exp (-c a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hD.nonneg a])
      linarith
    calc ‖w a * partitionFunction G w (compatibleWith G (M.erase a) a)‖
        ≤ (1 - Real.exp (-c a)) * ‖partitionFunction G w (M.erase a)‖ := h1
      _ ≤ (1 - Real.exp (-c a)) * (Real.exp (c a) * ‖partitionFunction G w M‖) :=
          mul_le_mul_of_nonneg_left h2 hfac
      _ = (Real.exp (c a) - 1) * ‖partitionFunction G w M‖ := by
          rw [show ∀ p q r : ℝ, (1 - p) * (q * r) = (q - p * q) * r by intros; ring,
            ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  · rw [erase_eq_of_notMem ha, sub_self, norm_zero]
    have := Real.one_le_exp (hD.nonneg a)
    nlinarith [norm_nonneg (partitionFunction G w M)]

/-- Under Dobrushin's criterion, removing a set `B` of polymers from `M` divides
the modulus of the partition function by at most `e^{∑_{u∈B} c u}`. -/
theorem norm_partitionFunction_le_exp_mul_sdiff {w : V → ℂ} {c : V → ℝ}
    (hD : DobrushinCondition G w c) (M B : Finset V) :
    ‖partitionFunction G w M‖ ≤
      Real.exp (∑ u ∈ B, c u) * ‖partitionFunction G w (M \ B)‖ := by
  induction B using Finset.induction_on with
  | empty => simp
  | insert b B hb ih =>
    rw [sum_insert hb, Real.exp_add]
    have hsub : M \ insert b B = (M \ B).erase b := by
      ext u
      simp only [mem_sdiff, mem_insert, mem_erase]
      tauto
    rw [hsub]
    have h := norm_partitionFunction_le_exp_mul_erase hD (M \ B) b
    calc ‖partitionFunction G w M‖
        ≤ Real.exp (∑ u ∈ B, c u) * ‖partitionFunction G w (M \ B)‖ := ih
      _ ≤ Real.exp (∑ u ∈ B, c u) *
            (Real.exp (c b) * ‖partitionFunction G w ((M \ B).erase b)‖) := by gcongr
      _ = Real.exp (c b) * Real.exp (∑ u ∈ B, c u) *
            ‖partitionFunction G w ((M \ B).erase b)‖ := by ring


/-! ## Positive real partitions and logarithmic removal bounds -/

theorem DobrushinCondition.mono_activity {a b : V → ℂ} {c : V → ℝ}
    (hb : DobrushinCondition G b c) (hab : ∀ p, ‖a p‖ ≤ ‖b p‖) :
    DobrushinCondition G a c :=
  ⟨hb.nonneg, fun p S hS => (hab p).trans (hb.bound p S hS)⟩

theorem partitionFunction_pos_of_dobrushin {a : V → ℝ} {c : V → ℝ}
    (hD : DobrushinCondition G (fun p => (a p : ℂ)) c) (Λ : Finset V) :
    0 < partitionFunction G a Λ := by
  induction Λ using Finset.induction_on with
  | empty => simp
  | @insert p Λ hp ih =>
    rw [partitionFunction_insert (G := G) a hp]
    have hb := norm_mul_partitionFunction_compatibleWith_le hD Λ p
    rw [← ofReal_partitionFunction G a (compatibleWith G Λ p),
      ← ofReal_partitionFunction G a Λ, ← Complex.ofReal_mul] at hb
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ih] at hb
    have hh := neg_abs_le (a p * partitionFunction G a (compatibleWith G Λ p))
    have he := mul_pos (Real.exp_pos (-c p)) ih
    nlinarith

theorem partitionFunction_abs_insertion_ratio_le {a : V → ℝ} {c : V → ℝ}
    (hD : DobrushinCondition G (fun p => (a p : ℂ)) c) (Λ : Finset V) (p : V) :
    |a p * partitionFunction G a (compatibleWith G Λ p) / partitionFunction G a Λ| ≤
      1 - Real.exp (-c p) := by
  have hpos := partitionFunction_pos_of_dobrushin hD Λ
  have hb := norm_mul_partitionFunction_compatibleWith_le hD Λ p
  rw [← ofReal_partitionFunction G a (compatibleWith G Λ p),
    ← ofReal_partitionFunction G a Λ, ← Complex.ofReal_mul] at hb
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos] at hb
  rw [abs_div, abs_of_pos hpos]
  exact (div_le_iff₀ hpos).mpr hb

theorem log_partitionFunction_erase_le {a : V → ℝ} {c : V → ℝ}
    (hD : DobrushinCondition G (fun p => (a p : ℂ)) c) (Λ : Finset V) (p : V) :
    Real.log (partitionFunction G a (Λ.erase p)) - Real.log (partitionFunction G a Λ) ≤ c p := by
  by_cases hp : p ∈ Λ
  · have hp0 := partitionFunction_pos_of_dobrushin hD Λ
    have hp1 := partitionFunction_pos_of_dobrushin hD (Λ.erase p)
    have hb := (removalBound_of_dobrushin hD Λ).2 p hp
    rw [← ofReal_partitionFunction G a (Λ.erase p), ← ofReal_partitionFunction G a Λ] at hb
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp0, abs_of_pos hp1] at hb
    have hl := Real.log_le_log hp1 hb
    rw [Real.log_mul (Real.exp_ne_zero _) hp0.ne', Real.log_exp] at hl
    linarith
  · simp only [erase_eq_of_notMem hp, sub_self]
    exact hD.nonneg p

#print axioms removalBound_of_dobrushin
#print axioms koteckyPreiss

end Mettapedia.Combinatorics.PolymerGas

/-! ## Exact factorization across disconnected regions -/

namespace Mettapedia.Combinatorics.PolymerGas
open scoped Classical
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Regions with no common vertex or incompatibility edge have factorized partitions. -/
theorem partitionFunction_union_of_no_edges {R : Type*} [CommSemiring R] (w : V → R)
    (A B : Finset V) (hd : Disjoint A B)
    (hn : ∀ a ∈ A, ∀ b ∈ B, ¬G.Adj a b) :
    partitionFunction G w (A ∪ B) = partitionFunction G w A * partitionFunction G w B := by
  revert B
  refine Finset.strongInductionOn A ?_
  intro A ih B hd hn
  by_cases hA : A.Nonempty
  · obtain ⟨v, hv⟩ := hA
    let A' := A.erase v
    have hs : A' ⊂ A := erase_ssubset hv
    have hvB : v ∉ B := fun h => disjoint_left.mp hd hv h
    have hAB : Disjoint A' B := hd.mono_left (erase_subset _ _)
    have hno : ∀ a ∈ A', ∀ b ∈ B, ¬G.Adj a b := fun a ha => hn a (erase_subset _ _ ha)
    have hcompat : compatibleWith G (A' ∪ B) v = compatibleWith G A' v ∪ B := by
      simp only [compatibleWith, filter_union]
      rw [filter_eq_self.mpr (fun b hb => hn v hv b hb)]
    have hZ := ih A' hs B hAB hno
    have hZ' := ih (compatibleWith G A' v)
      (Finset.ssubset_of_subset_of_ssubset (filter_subset _ _) hs) B
      (hAB.mono_left (filter_subset _ _))
      (fun a ha => hno a (filter_subset _ _ ha))
    have hve : v ∉ A' := by simp [A']
    calc
      partitionFunction G w (A ∪ B) = partitionFunction G w (insert v (A' ∪ B)) := by
        congr 1
        rw [← insert_union, show insert v A' = A from insert_erase hv]
      _ = partitionFunction G w (A' ∪ B) + w v * partitionFunction G w (compatibleWith G (A' ∪ B) v) :=
        partitionFunction_insert w (by simp [hve, hvB])
      _ = (partitionFunction G w A' + w v * partitionFunction G w (compatibleWith G A' v)) * partitionFunction G w B := by
        rw [hcompat, hZ, hZ']
        ring
      _ = partitionFunction G w A * partitionFunction G w B := by
        rw [← partitionFunction_insert w hve, insert_erase hv]
  · simp [not_nonempty_iff_eq_empty.mp hA]


end Mettapedia.Combinatorics.PolymerGas
