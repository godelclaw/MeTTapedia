import Mathlib
import OfficialPfaffian
import FourVertices
import UniformRigidity

/-!
# The two scenarios

What follows if the Krenn–Gu conjecture is true, and what any counterexample would have to
look like if it is false.  Every statement is proved; none assumes either scenario beyond its
stated hypothesis.

**If true** (`OfficialKrennGu`):
- a three-colour GHZ system exists on exactly `0`, `2` and `4` sites
  (`official_iff_classification`);
- no solution exists in any dimension `D ≥ 3` (`krennGu_all_dimensions`);
- bosons can do exactly what fermions can (`official_iff_bosons_match_fermions`).

**If false**, a `Counterexample` exists, and every counterexample:
- is a task bosons perform and fermions provably cannot (`false_iff_bosonic_advantage`);
- has weights that generate `1/2` (`half_mem_weightRing`), so they are never all algebraic
  integers (`not_all_integral`): no design using only integer amplitudes and root-of-unity
  phases works;
- has a live graph with no Pfaffian signs (`no_pfaffian_signs`), hence, by Kasteleyn's theorem
  (not formalized), a non-planar one;
- gives every site at least three partners single-coloured at the partner
  (`three_mono_partners`);
- heralds a GHZ state on an odd number of sites (`herald`);
- and, taken smallest, is a non-Pfaffian brick or brace (`exists_minimal_counterexample`).
-/

namespace KrennScenarios

open Amplitude MatchingSum MatchingPfaffian MonochromaticQuantumGraph GeneralOfficialBridge
  KrennCharTwo KrennFermi

/-! ## Small solutions -/

/-- **No sites**: the empty system is vacuously a GHZ system. -/
theorem solvable_zero : KrennGu.Solvable 0 := by
  refine ⟨fun _ => 0, fun k => ?_, fun c hc => ?_⟩
  · rw [← pmSum_univ]
    have : (Finset.univ : Finset (Fin (2 * 0))) = ∅ :=
      Finset.eq_empty_of_forall_notMem fun v _ => absurd v.2 (by simp)
    rw [this, pmSum_empty]
    exact one_ne_zero
  · exact absurd ⟨0, fun v => absurd v.2 (by simp)⟩ hc

/-- The two-site weights: one pair, with all three diagonal entries. -/
def bellW : Sym2 (Fin (2 * 1) × Fin 3) → ℂ :=
  Sym2.lift ⟨fun x y => if x.2 = y.2 then 1 else 0, fun x y => by
    dsimp only
    by_cases h : x.2 = y.2
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]⟩

theorem amplitude_bellW (c : Fin (2 * 1) → Fin 3) :
    amplitude bellW c = if c 0 = c 1 then 1 else 0 := by
  rw [← pmSum_univ]
  have huniv : (Finset.univ : Finset (Fin (2 * 1))) = {0, 1} := by decide
  rw [huniv, pmSum_pair bellW c (by decide : (1 : Fin (2 * 1)) ≠ 0)]
  rfl

/-- **Two sites**: a Bell pair in three colours. -/
theorem solvable_one : KrennGu.Solvable 1 := by
  refine ⟨bellW, fun k => ?_, fun c hc => ?_⟩
  · rw [amplitude_bellW]
    simp [Amplitude.const]
  · rw [amplitude_bellW, if_neg]
    intro h
    apply hc
    refine ⟨c 0, fun v => ?_⟩
    have hv : v = 0 ∨ v = 1 := by
      have := v.2
      rcases v with ⟨_ | _ | m, hm⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · omega
    rcases hv with rfl | rfl
    · rfl
    · exact h.symm

/-! ## Scenario: the conjecture is true -/

/-- **If true, the classification is complete.**  Three-colour GHZ systems exist on exactly
`0`, `2` and `4` sites. -/
theorem classification_of_official (h : OfficialKrennGu) (n : ℕ) :
    KrennGu.Solvable n ↔ n ≤ 2 := by
  constructor
  · intro hs
    by_contra hn
    exact notSolvable_of_official h n (by omega) hs
  · intro hn
    interval_cases n
    · exact solvable_zero
    · exact solvable_one
    · exact FourVertices.solvable_two

/-- **The conjecture is exactly this classification.** -/
theorem official_iff_classification :
    OfficialKrennGu ↔ ∀ n : ℕ, KrennGu.Solvable n ↔ n ≤ 2 := by
  constructor
  · exact classification_of_official
  · intro h n hn hex
    have := (h n).mp (solvable_of_eqSystemN hex)
    omega

/-- **If true, every dimension from three on is excluded.**  Restricting to three colours turns
a solution in dimension `D ≥ 3` into a three-colour one. -/
theorem krennGu_all_dimensions (h : OfficialKrennGu) {D : ℕ} (hD : 3 ≤ D) :
    ∀ n : ℕ, 3 ≤ n → ¬ ∃ W : WeightsN (2 * n) D ℂ, EqSystemN (2 * n) D W := by
  rintro n hn ⟨W, hW⟩
  rw [eqSystemN_iff_amplitude_const] at hW
  refine notSolvable_of_official h n hn ⟨restrict (Fin.castLE hD) (symWeight W), fun k => ?_,
    fun c hc => ?_⟩
  · rw [amplitude_restrict, hW]
    simp [Amplitude.const]
  · rw [amplitude_restrict, hW, if_neg]
    intro hconst
    exact hc ⟨c ⟨0, by omega⟩, fun v => Fin.castLE_injective hD (hconst v _)⟩

/-- No fermionic GHZ system on `2n ≥ 6` sites, read on `Fin (2n)`. -/
theorem no_fermi (n : ℕ) (hn : 3 ≤ n) :
    ¬ ∃ W' : Sym2 (Fin (2 * n) × Fin 3) → ℂ, IsFermiGHZ W' :=
  fun ⟨W', hW'⟩ => krennGu_fermi n hn (Fin (2 * n)) (Fintype.card_fin _) W' hW'

/-- **The conjecture says bosons can do exactly what fermions can**, site count by site
count: a bosonic solution exists exactly when a fermionic one does. -/
theorem official_iff_bosons_match_fermions :
    OfficialKrennGu ↔ ∀ n : ℕ, 3 ≤ n →
      ((∃ W : WeightsN (2 * n) 3 ℂ, EqSystemN (2 * n) 3 W) ↔
        ∃ W' : Sym2 (Fin (2 * n) × Fin 3) → ℂ, IsFermiGHZ W') := by
  constructor
  · intro h n hn
    exact ⟨fun hb => absurd hb (h n hn), fun hf => absurd hf (no_fermi n hn)⟩
  · intro h n hn hb
    exact no_fermi n hn ((h n hn).mp hb)

/-! ## Scenario: the conjecture is false -/

/-- **A counterexample**: an official solution on `2n ≥ 6` sites in three colours. -/
structure Counterexample where
  n : ℕ
  three_le : 3 ≤ n
  W : WeightsN (2 * n) 3 ℂ
  solves : EqSystemN (2 * n) 3 W

theorem official_iff_isEmpty : OfficialKrennGu ↔ IsEmpty Counterexample := by
  constructor
  · intro h
    exact ⟨fun X => h X.n X.three_le ⟨X.W, X.solves⟩⟩
  · intro h n hn ⟨W, hW⟩
    exact h.false ⟨n, hn, W, hW⟩

/-- **Falsity is a strict bosonic advantage.**  The conjecture fails exactly when, at some site
count, bosons produce the state and fermions provably cannot. -/
theorem false_iff_bosonic_advantage :
    ¬ OfficialKrennGu ↔ ∃ n : ℕ, 3 ≤ n ∧
      (∃ W : WeightsN (2 * n) 3 ℂ, EqSystemN (2 * n) 3 W) ∧
      ¬ ∃ W' : Sym2 (Fin (2 * n) × Fin 3) → ℂ, IsFermiGHZ W' := by
  constructor
  · intro h
    by_contra hno
    apply h
    intro n hn hb
    exact hno ⟨n, hn, hb, no_fermi n hn⟩
  · rintro ⟨n, hn, hb, -⟩ h
    exact h n hn hb

section Anatomy

variable (X : Counterexample)

/-- The three-colour GHZ system of a counterexample. -/
theorem isGHZOver : IsGHZOver (symWeight X.W) :=
  isGHZOver_of_eqSystemN (by have := X.three_le; omega) X.solves

theorem symWeight_map {N D : ℕ} {α β : Type} [Semiring α] [Semiring β] (f : α →+* β)
    (W : WeightsN N D α) (z : Sym2 (Fin N × Fin D)) :
    symWeight (fun e => f (W e)) z = f (symWeight W z) := by
  induction z using Sym2.ind with
  | h p q =>
    simp only [symWeight, Sym2.lift_mk]
    split_ifs <;> rfl

/-- An official solution survives an injective ring homomorphism read backwards: if the images
of the weights solve the system, so do the weights. -/
theorem eqSystemN_of_map {N D : ℕ} {α β : Type} [CommRing α] [CommRing β] (f : α →+* β)
    (hf : Function.Injective f) (W : WeightsN N D α) (h : EqSystemN N D (fun e => f (W e))) :
    EqSystemN N D W := by
  rw [eqSystemN_iff_amplitude_const] at h ⊢
  intro ι
  apply hf
  have h1 := h ι
  have hmap : (fun z => symWeight (fun e => f (W e)) z) = fun z => f (symWeight W z) :=
    funext (symWeight_map f W)
  rw [show symWeight (fun e => f (W e)) = fun z => f (symWeight W z) from hmap,
    amplitude_map_ringHom] at h1
  rw [h1]
  split_ifs <;> simp

/-- **The weights of a counterexample generate `1/2`.**  If `2` were not a unit in the ring they
generate, reducing modulo a maximal ideal containing `2` would give a solution in
characteristic two, which cannot exist. -/
theorem half_mem_weightRing : (1 / 2 : ℂ) ∈ Subring.closure (Set.range X.W) := by
  set R := Subring.closure (Set.range X.W) with hR
  by_contra hhalf
  have hu : ¬ IsUnit (2 : R) := by
    intro hu2
    obtain ⟨b, hb⟩ := hu2.exists_right_inv
    apply hhalf
    have h2b := congrArg R.subtype hb
    rw [map_mul, map_ofNat, map_one] at h2b
    change (2 : ℂ) * (b : ℂ) = 1 at h2b
    have hval : (b : ℂ) = 1 / 2 := by
      field_simp
      linear_combination h2b
    rw [← hval]
    exact b.2
  let W' : WeightsN (2 * X.n) 3 R := fun e => ⟨X.W e, Subring.subset_closure ⟨e, rfl⟩⟩
  exact krennGu_of_not_isUnit_two R hu X.n X.three_le
    ⟨W', eqSystemN_of_map R.subtype Subtype.val_injective W' X.solves⟩

/-- **A counterexample's weights never all lie in a ring of complex numbers without `1/2`.**
For instance the Gaussian integers, the cyclotomic integers, `ℤ[1/3]`, or `ℤ[√2]`. -/
theorem not_all_mem (S : Subring ℂ) (hS : (1 / 2 : ℂ) ∉ S) : ¬ ∀ e, X.W e ∈ S := by
  intro h
  apply hS
  exact (Subring.closure_le.mpr (by rintro _ ⟨e, rfl⟩; exact h e)) (half_mem_weightRing X)

/-- `1/2` is not an algebraic integer. -/
theorem half_not_integral : ¬ IsIntegral ℤ (1 / 2 : ℂ) := by
  intro h
  have h' : IsIntegral ℤ (algebraMap ℚ ℂ (1 / 2)) := by simpa using h
  rw [isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective] at h'
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h'
  have : (2 * y : ℚ) = 1 := by
    rw [show ((2 : ℚ) * (y : ℚ)) = 2 * algebraMap ℤ ℚ y from rfl, hy]
    norm_num
  have : 2 * y = 1 := by exact_mod_cast this
  omega

/-- **The weights of a counterexample are not all algebraic integers.**  No design with integer
amplitudes and root-of-unity phases — sums of roots of unity with integer coefficients — can be
a counterexample. -/
theorem not_all_integral : ¬ ∀ e, IsIntegral ℤ (X.W e) := by
  intro h
  exact not_all_mem X (integralClosure ℤ ℂ).toSubring
    (fun hmem => half_not_integral hmem) h

/-- **The live graph of a counterexample carries no Pfaffian signs.**  By Kasteleyn's theorem
(not formalized here) it is therefore not planar. -/
theorem no_pfaffian_signs (sg : Sym2 (Fin (2 * X.n)) → ℂ) (ε : ℂ) :
    ¬ PfaffianSigns (symWeight X.W) sg ε :=
  krennGu_pfaffian_complex X.n X.three_le X.W X.solves sg ε

open Classical in
/-- **Every site has at least three partners single-coloured at the partner.** -/
theorem three_mono_partners (w : Fin (2 * X.n)) :
    3 ≤ ((Finset.univ.erase w).filter fun b => KrennUniform.MonoAt (symWeight X.W) w b).card :=
  KrennUniform.three_monoAt (isGHZOver X) w (by rw [Fintype.card_fin]; have := X.three_le; omega)

/-- **Heralding.**  Summing the amplitude over the colours of one site — detecting that site in
the balanced superposition — leaves a GHZ state on the other `2n - 1` sites. -/
theorem herald (u : Fin (2 * X.n)) (c : Fin (2 * X.n) → Fin 3) :
    ∑ a : Fin 3, amplitude (symWeight X.W) (Function.update c u a)
      = if ∀ v w, v ≠ u → w ≠ u → c v = c w then 1 else 0 := by
  classical
  have hW := (eqSystemN_iff_amplitude_const X.W).mp X.solves
  simp_rw [hW]
  have hn := X.three_le
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : Fin (2 * X.n), v₀ ≠ u := by
    by_cases hu : u = ⟨0, by omega⟩
    · exact ⟨⟨1, by omega⟩, by rw [hu]; simp⟩
    · exact ⟨⟨0, by omega⟩, Ne.symm hu⟩
  have hupd : ∀ a x, x ≠ u → Function.update c u a x = c x := fun a x hx =>
    Function.update_of_ne hx a c
  split_ifs with hc
  · -- constant off `u`: exactly the colour of the other sites completes a constant colouring
    have key : ∀ a : Fin 3, (∀ x y, Function.update c u a x = Function.update c u a y) ↔
        a = c v₀ := by
      intro a
      constructor
      · intro h
        have := h u v₀
        rwa [Function.update_self, hupd a v₀ hv₀] at this
      · rintro rfl x y
        have ex : Function.update c u (c v₀) x = c v₀ := by
          by_cases hx : x = u
          · rw [hx, Function.update_self]
          · rw [hupd _ x hx]; exact hc x v₀ hx hv₀
        have ey : Function.update c u (c v₀) y = c v₀ := by
          by_cases hy : y = u
          · rw [hy, Function.update_self]
          · rw [hupd _ y hy]; exact hc y v₀ hy hv₀
        rw [ex, ey]
    simp_rw [key]
    rw [Finset.sum_ite_eq' Finset.univ (c v₀), if_pos (Finset.mem_univ _)]
  · -- not constant off `u`: no choice at `u` makes the colouring constant
    push Not at hc
    obtain ⟨v, w, hvu, hwu, hvw⟩ := hc
    refine Finset.sum_eq_zero fun a _ => if_neg fun h => hvw ?_
    have := h v w
    rwa [hupd a v hvu, hupd a w hwu] at this

end Anatomy

/-- **A smallest counterexample is a non-Pfaffian brick or brace.**  If the conjecture fails,
there is a support-minimal GHZ system above four sites with no GHZ system on fewer sites, no
shore-tight cut keeping five or more sites, and no Pfaffian signs on its live graph for any
order of its sites. -/
theorem exists_minimal_counterexample (h : ¬ OfficialKrennGu) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (_ : LinearOrder V)
      (W : Sym2 (V × Fin 3) → ℂ),
      4 < Fintype.card V ∧ MinimalSupport.IsSupportMinimal W ∧
      (∀ n : ℕ, 3 ≤ n → 2 * n < Fintype.card V → ¬ KrennGu.Solvable n) ∧
      (∀ S : Finset V, 5 ≤ S.card → 3 ≤ (Finset.univ \ S).card →
        ¬ KrennTightCut.ShoreTight W S) ∧
      (∀ (sg : Sym2 V → ℂ) (ε : ℂ), ¬ PfaffianSigns W sg ε) := by
  by_contra hne
  apply h
  apply official_of_nonPfaffianHeart
  intro V _ _ _ W hcard hmin hsmall htight hP
  exact hne ⟨V, _, _, _, W, hcard, hmin, hsmall, htight, hP⟩

end KrennScenarios

#print axioms KrennScenarios.official_iff_classification
#print axioms KrennScenarios.krennGu_all_dimensions
#print axioms KrennScenarios.official_iff_bosons_match_fermions
#print axioms KrennScenarios.false_iff_bosonic_advantage
#print axioms KrennScenarios.half_mem_weightRing
#print axioms KrennScenarios.not_all_integral
#print axioms KrennScenarios.no_pfaffian_signs
#print axioms KrennScenarios.three_mono_partners
#print axioms KrennScenarios.herald
#print axioms KrennScenarios.exists_minimal_counterexample
