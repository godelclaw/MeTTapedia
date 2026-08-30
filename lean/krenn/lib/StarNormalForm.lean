import NoCancellation
import Mettapedia.Combinatorics.Matching.Crossing

/-!
# The star-circuit normal form

Fix a site and freeze every weight off its star.  Every perfect matching covers that site exactly
once, so every amplitude is *linear* in the star: it is the sum, over the site's partners, of the
block entry the colouring selects times the matching sum on what is left.

This file turns that observation into one interface.  A variation of a block contributes through the
same linear map; support minimality says the actual contribution of a live block is not reachable
from the others' variations; evaluation on the three constant colourings is the only thing the
degree argument consumes; and a site with four or more live partners carries an explicit circuit --
coefficients on at most four of them, cancelling on all three constant colourings, yet surviving on
one exhibited mixed colouring.

Everything here is a property of *support-minimal GHZ systems above four sites*.  The conjecture
implies there are none, so each such property is implied back by it: these are equivalent structural
targets, not weaker hypotheses.  See `allDegenerate_iff_official` for that argument written out.
-/

namespace StarNormalForm

open Amplitude MatchingSum MatchingCrossing LiveDegree MinimalSupport

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The star term through `v`: the block entry the colouring selects, times the matching sum on the
complement of the pair. -/
noncomputable def starTerm (W : Sym2 (V × Fin 3) → ℂ) (u v : V) (c : V → Fin 3) : ℂ :=
  W s((u, c u), (v, c v)) * pmSum W c ((Finset.univ.erase u).erase v)

/-- The contribution of an arbitrary `3 × 3` variation of the block at `{u, v}`, through the same
linear map.  `starTerm` is the value at the block the system actually carries. -/
noncomputable def blockTerm (W : Sym2 (V × Fin 3) → ℂ) (u v : V) (A : Fin 3 → Fin 3 → ℂ)
    (c : V → Fin 3) : ℂ :=
  A (c u) (c v) * pmSum W c ((Finset.univ.erase u).erase v)

theorem starTerm_eq_blockTerm (W : Sym2 (V × Fin 3) → ℂ) (u v : V) (c : V → Fin 3) :
    starTerm W u v c = blockTerm W u v (fun a b => W s((u, a), (v, b))) c := rfl

/-- The symmetric correction adding `A w` to the block at `{u, w}` for every `w ≠ u`. -/
noncomputable def starCorr (u : V) (A : V → Fin 3 → Fin 3 → ℂ) : Sym2 (V × Fin 3) → ℂ :=
  Sym2.lift ⟨fun p q => if p.1 = u then (if q.1 = u then 0 else A q.1 p.2 q.2)
                        else (if q.1 = u then A p.1 q.2 p.2 else 0), by
    intro p q
    by_cases hp : p.1 = u <;> by_cases hq : q.1 = u <;> simp [hp, hq]⟩

@[simp] theorem starCorr_apply (u : V) (A : V → Fin 3 → Fin 3 → ℂ) (p q : V × Fin 3) :
    starCorr u A s(p, q)
      = if p.1 = u then (if q.1 = u then 0 else A q.1 p.2 q.2)
        else (if q.1 = u then A p.1 q.2 p.2 else 0) := rfl

/-- The star at `u` with the block at `{u, v}` erased and every other block varied by `A`. -/
noncomputable def starPerturb (W : Sym2 (V × Fin 3) → ℂ) (u v : V)
    (A : V → Fin 3 → Fin 3 → ℂ) : Sym2 (V × Fin 3) → ℂ :=
  fun e => if Sym2.map Prod.fst e = s(u, v) then 0 else W e + starCorr u A e

theorem starPerturb_erased (W : Sym2 (V × Fin 3) → ℂ) (u v : V) (A : V → Fin 3 → Fin 3 → ℂ)
    (a b : Fin 3) : starPerturb W u v A s((u, a), (v, b)) = 0 := by
  simp [starPerturb]

theorem starPerturb_star (W : Sym2 (V × Fin 3) → ℂ) {u v : V} (hvu : v ≠ u)
    (A : V → Fin 3 → Fin 3 → ℂ) {w : V} (hwu : w ≠ u) (hwv : w ≠ v) (a b : Fin 3) :
    starPerturb W u v A s((u, a), (w, b)) = W s((u, a), (w, b)) + A w a b := by
  have hne : Sym2.map Prod.fst (s((u, a), (w, b))) ≠ s(u, v) := by
    simp only [Sym2.map_pair_eq]
    intro h
    rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact hwv h2
    · exact hvu h1.symm
  unfold starPerturb
  rw [if_neg hne]
  simp [hwu]

theorem starPerturb_off (W : Sym2 (V × Fin 3) → ℂ) (u v : V) (A : V → Fin 3 → Fin 3 → ℂ)
    {x y : V} (hxu : x ≠ u) (hyu : y ≠ u) (a b : Fin 3) :
    starPerturb W u v A s((x, a), (y, b)) = W s((x, a), (y, b)) := by
  have hne : Sym2.map Prod.fst (s((x, a), (y, b))) ≠ s(u, v) := by
    simp only [Sym2.map_pair_eq]
    intro h
    rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact hxu h1
    · exact hyu h2
  unfold starPerturb
  rw [if_neg hne]
  simp [hxu, hyu]

theorem starPerturb_loop (W : Sym2 (V × Fin 3) → ℂ) {u v : V} (hvu : v ≠ u)
    (A : V → Fin 3 → Fin 3 → ℂ) (a b : Fin 3) :
    starPerturb W u v A s((u, a), (u, b)) = W s((u, a), (u, b)) := by
  have hne : Sym2.map Prod.fst (s((u, a), (u, b))) ≠ s(u, v) := by
    simp only [Sym2.map_pair_eq]
    intro h
    rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨h2, -⟩ <;> exact hvu h2.symm
  unfold starPerturb
  rw [if_neg hne]
  simp

/-! ### Blockwise irredundance

The perturbation that proves it: erase the block at `{u, v}` and redistribute its contribution
through arbitrary variations of blocks that are *already live*.  Every amplitude is unchanged,
because each matching meets `u` exactly once and the sums on the complements never see the star.  No
new neighbour appears, because the variations are supported on live blocks.  And the pair `{u, v}`
is gone, so the support strictly drops -- which minimal support forbids. -/

theorem live_symm {W : Sym2 (V × Fin 3) → ℂ} {u x : V} (h : x ∈ liveNbrs W u) :
    u ∈ liveNbrs W x := by
  obtain ⟨hxu, a, b, hab⟩ := mem_liveNbrs.mp h
  exact mem_liveNbrs.mpr ⟨Ne.symm hxu, b, a, by rw [Sym2.eq_swap]; exact hab⟩

/-- **Blockwise star irredundance.**  On a support-minimal system the contribution of a live block
is not reachable from arbitrary variations of the site's other live blocks. -/
theorem blockwise_star_irredundant (W : Sym2 (V × Fin 3) → ℂ) (hmin : IsSupportMinimal W)
    {u v : V} (hv : v ∈ liveNbrs W u) (A : V → Fin 3 → Fin 3 → ℂ)
    (hAsupp : ∀ w : V, w ∉ liveNbrs W u → ∀ a b : Fin 3, A w a b = 0)
    (hAv : ∀ a b : Fin 3, A v a b = 0)
    (hdep : ∀ c : V → Fin 3,
      starTerm W u v c = ∑ w ∈ (liveNbrs W u).erase v, blockTerm W u w (A w) c) :
    False := by
  classical
  have hvu : v ≠ u := (mem_liveNbrs.mp hv).1
  have hvmem : v ∈ (Finset.univ : Finset V).erase u := Finset.mem_erase.mpr ⟨hvu, Finset.mem_univ v⟩
  have hpm : ∀ (c : V → Fin 3) (y : V),
      pmSum (starPerturb W u v A) c ((Finset.univ.erase u).erase y)
        = pmSum W c ((Finset.univ.erase u).erase y) := by
    intro c y
    refine pmSum_congr _ W c (fun x hx z hz => ?_)
    have hxu : x ≠ u := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hx)).1
    have hzu : z ≠ u := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hz)).1
    exact starPerturb_off W u v A hxu hzu _ _
  have hexp : ∀ (X : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3), amplitude X c
      = ∑ y ∈ Finset.univ.erase u,
          X s((u, c u), (y, c y)) * pmSum X c ((Finset.univ.erase u).erase y) := by
    intro X c
    rw [← pmSum_univ, pmSum_expand X c (Finset.mem_univ u)]
    rfl
  have hamp : ∀ c : V → Fin 3, amplitude (starPerturb W u v A) c = amplitude W c := by
    intro c
    rw [hexp (starPerturb W u v A) c, hexp W c]
    simp only [hpm c]
    rw [← Finset.add_sum_erase _ _ hvmem, ← Finset.add_sum_erase _ _ hvmem,
      starPerturb_erased W u v A, zero_mul, zero_add]
    have hterm : ∀ y ∈ ((Finset.univ : Finset V).erase u).erase v,
        starPerturb W u v A s((u, c u), (y, c y)) * pmSum W c ((Finset.univ.erase u).erase y)
          = W s((u, c u), (y, c y)) * pmSum W c ((Finset.univ.erase u).erase y)
            + blockTerm W u y (A y) c := by
      intro y hy
      have hyv : y ≠ v := (Finset.mem_erase.mp hy).1
      have hyu : y ≠ u := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hy)).1
      rw [starPerturb_star W hvu A hyu hyv, blockTerm, add_mul]
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
    have hsub : (liveNbrs W u).erase v ⊆ ((Finset.univ : Finset V).erase u).erase v := by
      intro y hy
      have hyv : y ≠ v := (Finset.mem_erase.mp hy).1
      have hyl : y ∈ liveNbrs W u := Finset.mem_of_mem_erase hy
      exact Finset.mem_erase.mpr ⟨hyv,
        Finset.mem_erase.mpr ⟨(mem_liveNbrs.mp hyl).1, Finset.mem_univ y⟩⟩
    have hrest : ∑ y ∈ ((Finset.univ : Finset V).erase u).erase v, blockTerm W u y (A y) c
        = ∑ y ∈ (liveNbrs W u).erase v, blockTerm W u y (A y) c := by
      refine (Finset.sum_subset hsub ?_).symm
      intro y hy hyn
      have hyv : y ≠ v := (Finset.mem_erase.mp hy).1
      have hyl : y ∉ liveNbrs W u := fun hc => hyn (Finset.mem_erase.mpr ⟨hyv, hc⟩)
      rw [blockTerm, hAsupp y hyl, zero_mul]
    rw [hrest, ← hdep c, starTerm]
    ring
  have hW' : KrennGu.IsGHZ (starPerturb W u v A) := by
    refine ⟨fun k => ?_, fun c hc => ?_⟩
    · rw [hamp]; exact hmin.1.1 k
    · rw [hamp]; exact hmin.1.2 c hc
  have hsub : ∀ x : V, liveNbrs (starPerturb W u v A) x ⊆ liveNbrs W x := by
    intro x y hy
    obtain ⟨hyx, a, b, hab⟩ := mem_liveNbrs.mp hy
    refine mem_liveNbrs.mpr ⟨hyx, ?_⟩
    by_cases hxu : x = u
    · have hyu : y ≠ u := hxu ▸ hyx
      rw [hxu] at hab ⊢
      by_cases hyv : y = v
      · rw [hyv] at hab
        exact absurd (starPerturb_erased W u v A a b) hab
      · rw [starPerturb_star W hvu A hyu hyv] at hab
        by_cases hyl : y ∈ liveNbrs W u
        · exact (mem_liveNbrs.mp hyl).2
        · rw [hAsupp y hyl, add_zero] at hab
          exact ⟨a, b, hab⟩
    · by_cases hyu : y = u
      · rw [hyu] at hab ⊢
        rw [Sym2.eq_swap] at hab
        by_cases hxv : x = v
        · rw [hxv] at hab
          exact absurd (starPerturb_erased W u v A b a) hab
        · rw [starPerturb_star W hvu A hxu hxv] at hab
          by_cases hxl : x ∈ liveNbrs W u
          · exact (mem_liveNbrs.mp (live_symm hxl)).2
          · rw [hAsupp x hxl, add_zero] at hab
            exact ⟨a, b, by rw [Sym2.eq_swap]; exact hab⟩
      · rw [starPerturb_off W u v A hxu hyu] at hab
        exact ⟨a, b, hab⟩
  have hvnew : v ∉ liveNbrs (starPerturb W u v A) u := by
    intro hmem
    obtain ⟨-, a, b, hab⟩ := mem_liveNbrs.mp hmem
    exact hab (starPerturb_erased W u v A a b)
  have hlt : supportMass (starPerturb W u v A) < supportMass W := by
    rw [supportMass, supportMass]
    refine Finset.sum_lt_sum (fun x _ => Finset.card_le_card (hsub x)) ⟨u, Finset.mem_univ u, ?_⟩
    refine Finset.card_lt_card ?_
    rw [Finset.ssubset_iff_subset_ne]
    exact ⟨hsub u, fun heq => hvnew (heq ▸ hv)⟩
  exact (Nat.not_lt_of_ge (hmin.2 _ hW')) hlt

/-- **Scalar independence, as a regression theorem.**  The special case of blockwise irredundance in
which each variation is a multiple of the block it varies. -/
theorem star_scalar_independent (W : Sym2 (V × Fin 3) → ℂ) (hmin : IsSupportMinimal W) (u : V)
    (μ : V → ℂ) (hrel : ∀ c : V → Fin 3, ∑ w ∈ liveNbrs W u, μ w * starTerm W u w c = 0) :
    ∀ w ∈ liveNbrs W u, μ w = 0 := by
  classical
  intro v hv
  by_contra hne
  refine blockwise_star_irredundant W hmin hv
    (fun w a b => if w ∈ liveNbrs W u ∧ w ≠ v then -(μ v)⁻¹ * (μ w * W s((u, a), (w, b))) else 0)
    (fun w hw a b => if_neg (fun hc => hw hc.1)) (fun a b => by simp) (fun c => ?_)
  have hsplit := hrel c
  rw [← Finset.add_sum_erase _ _ hv] at hsplit
  have hterm : ∀ w ∈ (liveNbrs W u).erase v,
      blockTerm W u w
        (fun a b => if w ∈ liveNbrs W u ∧ w ≠ v then -(μ v)⁻¹ * (μ w * W s((u, a), (w, b)))
          else 0) c
        = -(μ v)⁻¹ * (μ w * starTerm W u w c) := by
    intro w hw
    have h1 : w ∈ liveNbrs W u := Finset.mem_of_mem_erase hw
    have h2 : w ≠ v := (Finset.mem_erase.mp hw).1
    simp only [blockTerm, starTerm]
    rw [if_pos (⟨h1, h2⟩ : w ∈ liveNbrs W u ∧ w ≠ v)]
    ring
  have hsum : ∑ w ∈ (liveNbrs W u).erase v, μ w * starTerm W u w c
      = -(μ v * starTerm W u v c) := by linear_combination hsplit
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hsum]
  field_simp

/-! ### Star observability

The degree argument consumes exactly one thing: that the values on the three constant colourings
determine the coefficients.  Forcing each star term to vanish on every mixed colouring is one way to
have that, and strictly more than is needed; the converse is neither assumed nor used. -/

/-- The value of the star term through `v` on the constant colouring of colour `k`. -/
noncomputable def starRow (W : Sym2 (V × Fin 3) → ℂ) (u v : V) (k : Fin 3) : ℂ :=
  starTerm W u v (Amplitude.const (V := V) k)

/-- **Star observability at a site.**  A combination of the live star terms that cancels on all three
constant colourings has every coefficient zero. -/
def StarObservable (W : Sym2 (V × Fin 3) → ℂ) (u : V) : Prop :=
  ∀ μ : V → ℂ, (∀ k : Fin 3, ∑ w ∈ liveNbrs W u, μ w * starRow W u w k = 0) →
    ∀ w ∈ liveNbrs W u, μ w = 0

/-- **The degree bound, from observability alone.**  Three constant colourings, three dimensions. -/
theorem liveNbrs_card_le_three_of_observable (W : Sym2 (V × Fin 3) → ℂ) (u : V)
    (h : StarObservable W u) : (liveNbrs W u).card ≤ 3 := by
  classical
  by_contra hgt
  push_neg at hgt
  have hcard : 3 < Fintype.card ↥(liveNbrs W u) := by
    rw [Fintype.card_coe]; exact hgt
  have hdep : ¬ LinearIndependent ℂ (fun w : ↥(liveNbrs W u) => fun k : Fin 3 => starRow W u w k) := by
    intro hLI
    have := hLI.fintype_card_le_finrank
    have h3 : Module.finrank ℂ (Fin 3 → ℂ) = 3 := by
      simp [Module.finrank_fintype_fun_eq_card]
    omega
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨g, hg, i, hi⟩ := hdep
  refine hi ?_
  have := h (fun w => if hw : w ∈ liveNbrs W u then g ⟨w, hw⟩ else 0) ?_ i.1 i.2
  · simpa using this
  · intro k
    have : ∑ w : ↥(liveNbrs W u), g w * starRow W u (w : V) k = 0 := by
      have := congrFun hg k
      simpa using this
    rw [← Finset.sum_coe_sort (liveNbrs W u)]
    refine this ▸ Finset.sum_congr rfl fun w _ => ?_
    simp [w.2]

/-- Star terms that vanish pointwise on every mixed colouring give observability.  This is the
sufficient condition full degeneracy supplies; the converse is not assumed and is not needed. -/
theorem starObservable_of_mixed_zero (W : Sym2 (V × Fin 3) → ℂ) (hmin : IsSupportMinimal W) (u : V)
    (hmix : ∀ v ∈ liveNbrs W u, ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c →
      starTerm W u v c = 0) :
    StarObservable W u := by
  classical
  intro μ hconst
  refine star_scalar_independent W hmin u μ (fun c => ?_)
  by_cases hc : Amplitude.Monochromatic c
  · obtain ⟨k, hk⟩ := hc
    have hck : c = Amplitude.const (V := V) k := funext hk
    subst hck
    exact hconst k
  · refine Finset.sum_eq_zero fun w hw => ?_
    rw [hmix w hw c hc, mul_zero]

/-! ### The circuit witness

Four or more live neighbours give four vectors in a three-dimensional space, hence a relation among
their constant-colouring rows.  The full star terms are independent, so the same relation does *not*
hold as an identity of functions: some colouring sees it, and that colouring cannot be constant.
What comes out is a finite, explicit object. -/

/-- A **star circuit** at `u`: coefficients carried by at most four live neighbours, cancelling on
all three constant colourings, together with one exhibited mixed colouring on which the combined
star defect survives. -/
structure StarCircuitWitness (W : Sym2 (V × Fin 3) → ℂ) (u : V) where
  /-- the neighbours carrying the circuit -/
  supp : Finset V
  supp_subset : supp ⊆ liveNbrs W u
  supp_nonempty : supp.Nonempty
  supp_card_le : supp.card ≤ 4
  /-- the coefficients, non-zero exactly on the support -/
  coeff : V → ℂ
  coeff_ne_zero : ∀ w ∈ supp, coeff w ≠ 0
  coeff_eq_zero : ∀ w ∉ supp, coeff w = 0
  /-- cancellation on each of the three constant colourings -/
  const_null : ∀ k : Fin 3, ∑ w ∈ supp, coeff w * starRow W u w k = 0
  /-- the colouring on which the defect survives -/
  mixed : V → Fin 3
  mixed_not_mono : ¬ Amplitude.Monochromatic mixed
  defect_ne_zero : ∑ w ∈ supp, coeff w * starTerm W u w mixed ≠ 0

/-- **Every site of degree four or more carries a circuit.** -/
theorem exists_starCircuitWitness (W : Sym2 (V × Fin 3) → ℂ) (hmin : IsSupportMinimal W) (u : V)
    (hdeg : 4 ≤ (liveNbrs W u).card) : Nonempty (StarCircuitWitness W u) := by
  classical
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hdeg
  have hcard : 3 < Fintype.card ↥t := by rw [Fintype.card_coe, htc]; omega
  have hdep : ¬ LinearIndependent ℂ (fun w : ↥t => fun k : Fin 3 => starRow W u w k) := by
    intro hLI
    have h1 := hLI.fintype_card_le_finrank
    have h3 : Module.finrank ℂ (Fin 3 → ℂ) = 3 := by simp [Module.finrank_fintype_fun_eq_card]
    omega
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨g, hg, i, hi⟩ := hdep
  set μ : V → ℂ := fun w => if hw : w ∈ t then g ⟨w, hw⟩ else 0 with hμ
  have hμt : ∀ w : ↥t, μ (w : V) = g w := by
    intro w; simp [hμ, w.2]
  have hμoff : ∀ w, w ∉ t → μ w = 0 := by intro w hw; simp [hμ, hw]
  set supp : Finset V := t.filter (fun w => μ w ≠ 0) with hsupp
  have hsuppt : supp ⊆ t := Finset.filter_subset _ _
  have hmemsupp : ∀ w, w ∈ supp ↔ w ∈ t ∧ μ w ≠ 0 := by
    intro w; simp [hsupp]
  have hoff : ∀ w, w ∉ supp → μ w = 0 := by
    intro w hw
    by_cases hwt : w ∈ t
    · by_contra hne
      exact hw ((hmemsupp w).mpr ⟨hwt, hne⟩)
    · exact hμoff w hwt
  have hsum_supp : ∀ f : V → ℂ, ∑ w ∈ supp, μ w * f w = ∑ w ∈ t, μ w * f w := by
    intro f
    refine Finset.sum_subset hsuppt ?_
    intro w _ hw
    rw [hoff w hw, zero_mul]
  have hconst : ∀ k : Fin 3, ∑ w ∈ supp, μ w * starRow W u w k = 0 := by
    intro k
    rw [hsum_supp, ← Finset.sum_coe_sort t (fun w => μ w * starRow W u w k)]
    have := congrFun hg k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [Finset.sum_congr rfl (fun w _ => by rw [hμt w])]
    simpa using this
  have hinonzero : μ (i : V) ≠ 0 := by rw [hμt i]; exact hi
  have hisupp : (i : V) ∈ supp := (hmemsupp _).mpr ⟨i.2, hinonzero⟩
  have hexists : ∃ c : V → Fin 3, ∑ w ∈ supp, μ w * starTerm W u w c ≠ 0 := by
    by_contra hall
    push_neg at hall
    refine hinonzero (star_scalar_independent W hmin u μ (fun c => ?_) _ (hts i.2))
    have hlive : ∑ w ∈ liveNbrs W u, μ w * starTerm W u w c
        = ∑ w ∈ supp, μ w * starTerm W u w c := by
      refine (Finset.sum_subset (hsuppt.trans hts) ?_).symm
      intro w _ hw
      rw [hoff w hw, zero_mul]
    rw [hlive, hall c]
  obtain ⟨c, hc⟩ := hexists
  refine ⟨{ supp := supp, supp_subset := hsuppt.trans hts,
            supp_nonempty := ⟨(i : V), hisupp⟩,
            supp_card_le := le_trans (Finset.card_le_card hsuppt) (le_of_eq htc),
            coeff := μ, coeff_ne_zero := fun w hw => ((hmemsupp w).mp hw).2,
            coeff_eq_zero := hoff, const_null := hconst,
            mixed := c, mixed_not_mono := ?_, defect_ne_zero := hc }⟩
  rintro ⟨k, hk⟩
  have hck : c = Amplitude.const (V := V) k := funext hk
  rw [hck] at hc
  exact hc (hconst k)

/-! ### The interface

`NoStarCircuit` is the statement that no such witness exists anywhere.  It gives the degree bound,
hence the conjecture.  It is also *implied by* the conjecture, for the reason every statement in
this file is: it is a universal property of support-minimal GHZ systems above four sites, and the
conjecture says there are none.  See `noStarCircuit_iff_official`.  It is an equivalent structural
target, not a weaker theorem. -/

/-- **No star circuits anywhere.** -/
def NoStarCircuit : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (W : Sym2 (V × Fin 3) → ℂ),
    4 < Fintype.card V → IsSupportMinimal W → ∀ u : V, IsEmpty (StarCircuitWitness W u)

/-- **No circuits gives the degree bound.** -/
theorem minimalLiveDegreeThree_of_noStarCircuit (h : NoStarCircuit) :
    MinimalSupport.MinimalLiveDegreeThree := by
  classical
  intro V _ _ W hcard hmin u
  by_contra hgt
  push_neg at hgt
  exact (h V W hcard hmin u).false (exists_starCircuitWitness W hmin u hgt).some

/-! ### The cofactor calculus

Write the star term as a block entry times the matching sum on the rest.  That second factor is
blind to the colouring at either end of its own pair, which is what makes recolouring the centre a
usable move: it changes the block entries and nothing else.  Everything in this section is uniform
in the site set and consumes no hypothesis beyond the definitions; the GHZ equations enter only in
the last statement, which is the relation the vanishing of a mixed amplitude supplies. -/

/-- The matching sum on the complement of the pair `{u, v}`. -/
noncomputable def cofactor (W : Sym2 (V × Fin 3) → ℂ) (u v : V) (c : V → Fin 3) : ℂ :=
  pmSum W c ((Finset.univ.erase u).erase v)

theorem starTerm_eq_mul (W : Sym2 (V × Fin 3) → ℂ) (u v : V) (c : V → Fin 3) :
    starTerm W u v c = W s((u, c u), (v, c v)) * cofactor W u v c := rfl

/-- **The cofactor is blind at its own pair.** -/
theorem cofactor_congr (W : Sym2 (V × Fin 3) → ℂ) (u v : V) {c c' : V → Fin 3}
    (h : ∀ x, x ≠ u → x ≠ v → c x = c' x) : cofactor W u v c = cofactor W u v c' := by
  refine pmSum_congr_colour W (fun x hx => ?_)
  have hxv : x ≠ v := (Finset.mem_erase.mp hx).1
  have hxu : x ≠ u := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hx)).1
  exact h x hxu hxv

@[simp] theorem cofactor_update_left (W : Sym2 (V × Fin 3) → ℂ) (u v : V) (c : V → Fin 3)
    (a : Fin 3) : cofactor W u v (Function.update c u a) = cofactor W u v c :=
  cofactor_congr W u v (fun x hxu _ => Function.update_of_ne hxu _ _)

@[simp] theorem cofactor_update_right (W : Sym2 (V × Fin 3) → ℂ) (u v : V) (c : V → Fin 3)
    (b : Fin 3) : cofactor W u v (Function.update c v b) = cofactor W u v c :=
  cofactor_congr W u v (fun x _ hxv => Function.update_of_ne hxv _ _)

/-- **One-pivot expansion.**  Recolouring the centre leaves every cofactor alone. -/
theorem amplitude_update_expand (W : Sym2 (V × Fin 3) → ℂ) (u : V) (c : V → Fin 3) (a : Fin 3) :
    amplitude W (Function.update c u a)
      = ∑ y ∈ Finset.univ.erase u, W s((u, a), (y, c y)) * cofactor W u y c := by
  rw [← pmSum_univ, pmSum_expand W _ (Finset.mem_univ u)]
  refine Finset.sum_congr rfl fun y hy => ?_
  have hyu : y ≠ u := (Finset.mem_erase.mp hy).1
  have h1 : (Function.update c u a) u = a := Function.update_self _ _ _
  have h2 : (Function.update c u a) y = c y := Function.update_of_ne hyu _ _
  show W s((u, (Function.update c u a) u), (y, (Function.update c u a) y)) *
      pmSum W (Function.update c u a) ((Finset.univ.erase u).erase y) = _
  rw [h1, h2]
  exact congrArg (fun t => W s((u, a), (y, c y)) * t) (cofactor_update_left W u y c a)

/-- **The star relation.**  A vanishing mixed amplitude, read at the centre. -/
theorem star_relation (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (u : V) (c : V → Fin 3) (a : Fin 3)
    (h : ¬ Amplitude.Monochromatic (Function.update c u a)) :
    ∑ y ∈ Finset.univ.erase u, W s((u, a), (y, c y)) * cofactor W u y c = 0 := by
  rw [← amplitude_update_expand]
  exact hzero _ h

/-- **Two-pivot expansion.**  A cofactor expands at any site outside its own pair. -/
theorem cofactor_expand (W : Sym2 (V × Fin 3) → ℂ) (u v : V) (c : V → Fin 3) {z : V}
    (hzu : z ≠ u) (hzv : z ≠ v) :
    cofactor W u v c = ∑ y ∈ ((Finset.univ.erase u).erase v).erase z,
      W s((z, c z), (y, c y)) * pmSum W c ((((Finset.univ.erase u).erase v).erase z).erase y) := by
  rw [cofactor, pmSum_expand W c (Finset.mem_erase.mpr ⟨hzv,
    Finset.mem_erase.mpr ⟨hzu, Finset.mem_univ z⟩⟩)]
  rfl

/-! ### Minimal circuits

A relation among the constant rows carried by at most four live neighbours is already a circuit: the
surviving mixed colouring comes free from independence, since a non-trivial combination of the full
star terms cannot vanish identically and cannot survive on a constant colouring.  Choosing a circuit
of least support then makes every proper non-empty subset independent, which is the matroid-circuit
property in the form the case analysis uses. -/

/-- **Any constant-row relation is a circuit.** -/
theorem witness_of_const_null (W : Sym2 (V × Fin 3) → ℂ) (hmin : IsSupportMinimal W) (u : V)
    {S : Finset V} (hS : S ⊆ liveNbrs W u) (hSne : S.Nonempty) (hS4 : S.card ≤ 4)
    (μ : V → ℂ) (hne : ∀ w ∈ S, μ w ≠ 0) (hz : ∀ w ∉ S, μ w = 0)
    (hconst : ∀ k : Fin 3, ∑ w ∈ S, μ w * starRow W u w k = 0) :
    ∃ ω : StarCircuitWitness W u, ω.supp = S := by
  classical
  obtain ⟨w₀, hw₀⟩ := hSne
  have hexists : ∃ c : V → Fin 3, ∑ w ∈ S, μ w * starTerm W u w c ≠ 0 := by
    by_contra hall
    push_neg at hall
    refine hne w₀ hw₀ (star_scalar_independent W hmin u μ (fun c => ?_) w₀ (hS hw₀))
    have hlive : ∑ w ∈ liveNbrs W u, μ w * starTerm W u w c
        = ∑ w ∈ S, μ w * starTerm W u w c := by
      refine (Finset.sum_subset hS ?_).symm
      intro w _ hw
      rw [hz w hw, zero_mul]
    rw [hlive, hall c]
  obtain ⟨c, hc⟩ := hexists
  have hmixed : ¬ Amplitude.Monochromatic c := by
    rintro ⟨k, hk⟩
    have hck : c = Amplitude.const (V := V) k := funext hk
    rw [hck] at hc
    exact hc (hconst k)
  exact ⟨{ supp := S, supp_subset := hS, supp_nonempty := ⟨w₀, hw₀⟩, supp_card_le := hS4,
           coeff := μ, coeff_ne_zero := hne, coeff_eq_zero := hz, const_null := hconst,
           mixed := c, mixed_not_mono := hmixed, defect_ne_zero := hc }, rfl⟩

/-- **A circuit of least support.** -/
theorem exists_minimal_starCircuitWitness (W : Sym2 (V × Fin 3) → ℂ) (hmin : IsSupportMinimal W)
    (u : V) (hdeg : 4 ≤ (liveNbrs W u).card) :
    ∃ ω : StarCircuitWitness W u, ∀ ω' : StarCircuitWitness W u, ω.supp.card ≤ ω'.supp.card := by
  classical
  obtain ⟨ω₀⟩ := exists_starCircuitWitness W hmin u hdeg
  have hex : ∃ n, ∃ ω : StarCircuitWitness W u, ω.supp.card = n := ⟨ω₀.supp.card, ω₀, rfl⟩
  obtain ⟨ω, hω⟩ := Nat.find_spec hex
  exact ⟨ω, fun ω' => by rw [hω]; exact Nat.find_le ⟨ω', rfl⟩⟩

/-- **The matroid-circuit property.**  No proper non-empty part of a least circuit carries a
constant-row relation of its own; equivalently the rows on the support have rank one less than its
size. -/
theorem no_proper_subcircuit (W : Sym2 (V × Fin 3) → ℂ) (hmin : IsSupportMinimal W) (u : V)
    (ω : StarCircuitWitness W u)
    (hleast : ∀ ω' : StarCircuitWitness W u, ω.supp.card ≤ ω'.supp.card)
    {T : Finset V} (hT : T ⊂ ω.supp) (hTne : T.Nonempty) (ν : V → ℂ)
    (hne : ∀ w ∈ T, ν w ≠ 0) (hz : ∀ w ∉ T, ν w = 0)
    (hconst : ∀ k : Fin 3, ∑ w ∈ T, ν w * starRow W u w k = 0) : False := by
  have hcardlt : T.card < ω.supp.card := Finset.card_lt_card hT
  obtain ⟨ω', hω'⟩ :=
    witness_of_const_null W hmin u (hT.subset.trans ω.supp_subset) hTne
      (le_trans (le_of_lt hcardlt) ω.supp_card_le) ν hne hz hconst
  have := hleast ω'
  rw [hω'] at this
  omega

/-- The support of a circuit has between one and four sites. -/
theorem circuit_card_range (W : Sym2 (V × Fin 3) → ℂ) (u : V) (ω : StarCircuitWitness W u) :
    1 ≤ ω.supp.card ∧ ω.supp.card ≤ 4 :=
  ⟨Finset.card_pos.mpr ω.supp_nonempty, ω.supp_card_le⟩

/-! ### What a circuit is, exactly

Circuits are neither more nor less than failures of observability.  One direction is immediate: a
circuit's coefficients cancel on the constant colourings and are non-zero at a live site.  The other
uses only that four vectors in three dimensions are dependent, so a relation on a large support can
always be traded for one on at most four sites.

The consequence is worth stating plainly, because it says what the circuit normal form does and does
not buy.  It repackages the degree question exactly: at a site of degree four or more the constant
rows are dependent, so a circuit exists, and no local identity can prevent that.  Eliminating
circuits is therefore not a matter of finding identities the cofactors satisfy; it is the degree
bound again, wearing different clothes. -/

theorem not_starObservable_of_witness (W : Sym2 (V × Fin 3) → ℂ) (u : V)
    (ω : StarCircuitWitness W u) : ¬ StarObservable W u := by
  classical
  intro hobs
  obtain ⟨w₀, hw₀⟩ := ω.supp_nonempty
  refine ω.coeff_ne_zero w₀ hw₀ (hobs ω.coeff (fun k => ?_) w₀ (ω.supp_subset hw₀))
  have : ∑ w ∈ liveNbrs W u, ω.coeff w * starRow W u w k
      = ∑ w ∈ ω.supp, ω.coeff w * starRow W u w k := by
    refine (Finset.sum_subset ω.supp_subset ?_).symm
    intro w _ hw
    rw [ω.coeff_eq_zero w hw, zero_mul]
  rw [this, ω.const_null k]

theorem witness_of_not_starObservable (W : Sym2 (V × Fin 3) → ℂ) (hmin : IsSupportMinimal W)
    (u : V) (h : ¬ StarObservable W u) : Nonempty (StarCircuitWitness W u) := by
  classical
  rw [StarObservable] at h
  push_neg at h
  obtain ⟨μ, hμ, w₀, hw₀live, hw₀⟩ := h
  set ν : V → ℂ := fun w => if w ∈ liveNbrs W u then μ w else 0 with hνdef
  have hνlive : ∀ w ∈ liveNbrs W u, ν w = μ w := by intro w hw; simp [hνdef, hw]
  set S : Finset V := (liveNbrs W u).filter (fun w => ν w ≠ 0) with hSdef
  have hSsub : S ⊆ liveNbrs W u := Finset.filter_subset _ _
  have hmemS : ∀ w, w ∈ S ↔ w ∈ liveNbrs W u ∧ ν w ≠ 0 := by intro w; simp [hSdef]
  have hw₀ν : ν w₀ ≠ 0 := by rw [hνlive w₀ hw₀live]; exact hw₀
  have hSne : S.Nonempty := ⟨w₀, (hmemS w₀).mpr ⟨hw₀live, hw₀ν⟩⟩
  have hoff : ∀ w, w ∉ S → ν w = 0 := by
    intro w hw
    by_cases hwl : w ∈ liveNbrs W u
    · by_contra hne; exact hw ((hmemS w).mpr ⟨hwl, hne⟩)
    · simp [hνdef, hwl]
  have hconstS : ∀ k : Fin 3, ∑ w ∈ S, ν w * starRow W u w k = 0 := by
    intro k
    have h1 : ∑ w ∈ liveNbrs W u, ν w * starRow W u w k
        = ∑ w ∈ liveNbrs W u, μ w * starRow W u w k :=
      Finset.sum_congr rfl (fun w hw => by rw [hνlive w hw])
    have h2 : ∑ w ∈ liveNbrs W u, ν w * starRow W u w k = ∑ w ∈ S, ν w * starRow W u w k := by
      refine (Finset.sum_subset hSsub ?_).symm
      intro w _ hw
      rw [hoff w hw, zero_mul]
    rw [← h2, h1]; exact hμ k
  by_cases hcard : S.card ≤ 4
  · obtain ⟨ω, -⟩ := witness_of_const_null W hmin u hSsub hSne hcard ν
      (fun w hw => ((hmemS w).mp hw).2) hoff hconstS
    exact ⟨ω⟩
  · push_neg at hcard
    exact exists_starCircuitWitness W hmin u
      (le_trans (by omega) (Finset.card_le_card hSsub))

/-- **Circuits are exactly the failures of observability.** -/
theorem nonempty_starCircuitWitness_iff (W : Sym2 (V × Fin 3) → ℂ) (hmin : IsSupportMinimal W)
    (u : V) : Nonempty (StarCircuitWitness W u) ↔ ¬ StarObservable W u :=
  ⟨fun ⟨ω⟩ => not_starObservable_of_witness W u ω, witness_of_not_starObservable W hmin u⟩

/-! ### Transport

Two consequences of the calculus that are uniform in the site set.  The first says a live arm is
never invisible: some colouring sees it.  The second is the transport the elimination programme
wants -- one arm's term, moved onto the others by the vanishing of a mixed amplitude, with the
recolouring at the far end of the arm made explicit. -/

/-- **A live arm is seen by some colouring.** -/
theorem exists_starTerm_ne_zero (W : Sym2 (V × Fin 3) → ℂ) (hmin : IsSupportMinimal W) (u : V)
    {v : V} (hv : v ∈ liveNbrs W u) : ∃ c : V → Fin 3, starTerm W u v c ≠ 0 := by
  classical
  by_contra hall
  push_neg at hall
  have hz := star_scalar_independent W hmin u (fun w => if w = v then (1 : ℂ) else 0)
    (fun c => ?_) v hv
  · simp at hz
  · rw [Finset.sum_eq_single v]
    · simp [hall c]
    · intro w _ hwv; simp [hwv]
    · intro hvn; exact absurd hv hvn

/-- **Arm transport.**  Recolour the centre to `a` and the far end of the arm to `b`; if the result
is not monochromatic, the arm's own term is exactly minus the other arms' terms, read at the
recoloured far end. -/
theorem arm_transport (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u v : V} (hvu : v ≠ u) (c : V → Fin 3) (a b : Fin 3)
    (hmix : ¬ Amplitude.Monochromatic (Function.update (Function.update c v b) u a)) :
    W s((u, a), (v, b)) * cofactor W u v c
      = - ∑ y ∈ (Finset.univ.erase u).erase v,
          W s((u, a), (y, c y)) * cofactor W u y (Function.update c v b) := by
  classical
  have hrel := star_relation W hzero u (Function.update c v b) a hmix
  have hvmem : v ∈ (Finset.univ : Finset V).erase u :=
    Finset.mem_erase.mpr ⟨hvu, Finset.mem_univ v⟩
  rw [← Finset.add_sum_erase _ _ hvmem] at hrel
  have hv1 : (Function.update c v b) v = b := Function.update_self _ _ _
  have hv2 : cofactor W u v (Function.update c v b) = cofactor W u v c :=
    cofactor_update_right W u v c b
  rw [hv1, hv2] at hrel
  have hrest : ∀ y ∈ ((Finset.univ : Finset V).erase u).erase v,
      W s((u, a), (y, (Function.update c v b) y)) * cofactor W u y (Function.update c v b)
        = W s((u, a), (y, c y)) * cofactor W u y (Function.update c v b) := by
    intro y hy
    rw [Function.update_of_ne (Finset.mem_erase.mp hy).1]
  rw [Finset.sum_congr rfl hrest] at hrel
  linear_combination hrel

/-! ### Locating size one exactly

A circuit of support one is a live arm that all three constant colourings miss.  Both directions are
immediate, and stating them fixes precisely what eliminating that size would require: every live arm
carries a non-zero constant row.  (Under full degeneracy that already holds -- a live pair is
certified in its own colour -- which is another way of seeing that the size cases are instances of
the conjecture rather than steps towards it.) -/

theorem size_one_circuit_of_row_zero (W : Sym2 (V × Fin 3) → ℂ) (hmin : IsSupportMinimal W) (u : V)
    {v : V} (hv : v ∈ liveNbrs W u) (hrow : ∀ k : Fin 3, starRow W u v k = 0) :
    ∃ ω : StarCircuitWitness W u, ω.supp = ({v} : Finset V) := by
  classical
  refine witness_of_const_null W hmin u (by simpa using hv) ⟨v, by simp⟩ (by simp)
    (fun w => if w = v then (1 : ℂ) else 0) (fun w hw => by simp at hw; simp [hw])
    (fun w hw => by simp at hw; simp [hw]) (fun k => ?_)
  simp [hrow k]

theorem row_zero_of_size_one_circuit (W : Sym2 (V × Fin 3) → ℂ) (u : V)
    (ω : StarCircuitWitness W u) {v : V} (hsupp : ω.supp = ({v} : Finset V)) :
    ∀ k : Fin 3, starRow W u v k = 0 := by
  intro k
  have h := ω.const_null k
  rw [hsupp, Finset.sum_singleton] at h
  have hne : ω.coeff v ≠ 0 := ω.coeff_ne_zero v (by rw [hsupp]; simp)
  exact (mul_eq_zero.mp h).resolve_left hne

/-! ### Pure arms

The one unconditional scarcity-free structure the star carries.  It comes from the master relation:
choose, at every arm, a covector annihilating that arm's row in a fixed colour; the relation then
says the product of their components in that colour vanishes, so some arm's row admits no such
covector -- which happens exactly when the row is a multiple of its own basis vector.

Stated here in the star vocabulary so that later work has it in the right form.  Note what it does
*not* give: it produces an arm with a pure row, not a bound on how many arms there are.  Adding arms
only makes the product easier to kill, so the master relation cannot bound the degree from above. -/

theorem exists_pure_arm (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const (V := V) k) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (u : V) (α : Fin 3) :
    ∃ v ∈ liveNbrs W u, (∀ b : Fin 3, b ≠ α → W s((u, α), (v, b)) = 0) ∧
      W s((u, α), (v, α)) ≠ 0 := by
  obtain ⟨v, hv, hpure, hne⟩ := PurePartner.exists_pure_partner W hone hzero u α
  exact ⟨v, mem_liveNbrs.mpr ⟨(Finset.mem_erase.mp hv).1, α, α, hne⟩, hpure, hne⟩

/-! ### The constant rows in total

The row expansion at the centre, read on a constant colouring, says the star rows of a fixed colour
add up to that colour's amplitude.  Since that amplitude does not vanish, no colour's row is
identically zero: the three-by-degree matrix of constant rows has no zero row.  This is a necessary
condition for observability, and it rules out the degenerate shape in which a colour sees nothing at
a site. -/

theorem sum_starRow (W : Sym2 (V × Fin 3) → ℂ) (u : V) (k : Fin 3) :
    ∑ v ∈ Finset.univ.erase u, starRow W u v k = amplitude W (Amplitude.const (V := V) k) := by
  rw [← pmSum_univ, pmSum_expand W _ (Finset.mem_univ u)]
  rfl

/-- **No colour is blind at a site.** -/
theorem exists_starRow_ne_zero (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const (V := V) k) ≠ 0) (u : V) (k : Fin 3) :
    ∃ v ∈ liveNbrs W u, starRow W u v k ≠ 0 := by
  classical
  by_contra hall
  push_neg at hall
  refine hone k ?_
  rw [← sum_starRow W u k]
  refine Finset.sum_eq_zero fun v hv => ?_
  by_cases hlive : v ∈ liveNbrs W u
  · exact hall v hlive
  · have hvu : v ≠ u := (Finset.mem_erase.mp hv).1
    have : W s((u, k), (v, k)) = 0 := by
      by_contra hne
      exact hlive (mem_liveNbrs.mpr ⟨hvu, k, k, hne⟩)
    simp only [starRow, starTerm, Amplitude.const]
    rw [this, zero_mul]

/-! ### The nine rows

A colouring at distance one from a constant — the centre recoloured — produces a row of the star
that the constant colourings do not supply.  Writing `starRowAt W u v a k` for the arm's term when
the centre wears `a` and everything else wears `k`, the three constant rows are the diagonal cases
`a = k`, and the six off-diagonal cases are genuinely new data.

Their totals are known exactly: the diagonal rows add to their colour's amplitude, the off-diagonal
rows add to zero.  So the all-ones vector annihilates every off-diagonal row.

This is worth isolating because it turns the first step of observability into a finite question: do
the six off-diagonal rows lie in the span of the three diagonal ones?  Nothing above forces it, and
nothing above forbids it. -/

/-- The arm's term with the centre recoloured to `a` and every other site wearing `k`. -/
noncomputable def starRowAt (W : Sym2 (V × Fin 3) → ℂ) (u v : V) (a k : Fin 3) : ℂ :=
  W s((u, a), (v, k)) * cofactor W u v (Amplitude.const (V := V) k)

theorem starRowAt_diag (W : Sym2 (V × Fin 3) → ℂ) (u v : V) (k : Fin 3) :
    starRowAt W u v k k = starRow W u v k := rfl

/-- **The totals of the nine rows.** -/
theorem sum_starRowAt (W : Sym2 (V × Fin 3) → ℂ) (u : V) (a k : Fin 3) :
    ∑ v ∈ Finset.univ.erase u, starRowAt W u v a k
      = amplitude W (Function.update (Amplitude.const (V := V) k) u a) := by
  rw [amplitude_update_expand]
  rfl

/-- **The off-diagonal rows sum to zero**, so the all-ones vector annihilates each of them. -/
theorem sum_starRowAt_off (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hcard : 1 < Fintype.card V) (u : V) {a k : Fin 3} (hak : a ≠ k) :
    ∑ v ∈ Finset.univ.erase u, starRowAt W u v a k = 0 := by
  classical
  rw [sum_starRowAt]
  refine hzero _ ?_
  rintro ⟨m, hm⟩
  obtain ⟨x, hx⟩ : ∃ x : V, x ≠ u := by
    by_contra hall
    push_neg at hall
    have : Fintype.card V ≤ 1 := by
      rw [Fintype.card_le_one_iff_subsingleton]
      exact ⟨fun p q => by rw [hall p, hall q]⟩
    omega
  have h1 : (Function.update (Amplitude.const (V := V) k) u a) u = a := Function.update_self _ _ _
  have h2 : (Function.update (Amplitude.const (V := V) k) u a) x = k :=
    Function.update_of_ne hx _ _
  exact hak (by rw [← h1, hm u, ← hm x, h2])

/-- **The diagonal rows sum to their colour's amplitude.** -/
theorem sum_starRowAt_diag (W : Sym2 (V × Fin 3) → ℂ) (u : V) (k : Fin 3) :
    ∑ v ∈ Finset.univ.erase u, starRowAt W u v k k
      = amplitude W (Amplitude.const (V := V) k) := by
  rw [sum_starRowAt]
  congr 1
  exact Function.update_eq_self u (Amplitude.const (V := V) k)

/-- **The pure arm is invisible to its colour's off-diagonal rows.**  Together with the totals, this
is what is known about the nine rows without further input: the diagonal ones add to a non-zero
amplitude, the off-diagonal ones add to zero, and each off-diagonal row of a colour vanishes at that
colour's pure arm. -/
theorem exists_arm_off_diagonal_zero (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const (V := V) k) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (u : V) (α : Fin 3) :
    ∃ v ∈ liveNbrs W u, ∀ k : Fin 3, k ≠ α → starRowAt W u v α k = 0 := by
  obtain ⟨v, hv, hpure, -⟩ := exists_pure_arm W hone hzero u α
  exact ⟨v, hv, fun k hk => by rw [starRowAt, hpure k hk, zero_mul]⟩

/-! ### The edge functions, globally

Everything above works inside one star.  The terms themselves, however, belong to *edges*, not to
stars: the term through the pair `{u,v}` is symmetric in its two ends, so a single family of
functions indexed by unordered pairs is being read from many centres at once.

The vertex-sum identity below is that reading.  At **every** site, the terms of the edges meeting it
add to the amplitude -- as an identity of functions, not merely at one colouring.  On a mixed
colouring the amplitude vanishes, so the vector of edge values lies in the kernel of the graph's
unsigned incidence matrix, at every mixed colouring at once.

That is a global constraint, and it is the first one in this development that is not local to a
single star. -/

/-- The term carried by the pair `{u, v}`, symmetric in its two ends. -/
theorem starTerm_symm (W : Sym2 (V × Fin 3) → ℂ) (u v : V) (c : V → Fin 3) :
    starTerm W u v c = starTerm W v u c := by
  rw [starTerm, starTerm, Sym2.eq_swap, Finset.erase_right_comm]

/-- **The vertex-sum identity**, for every colouring: the terms of the edges at a site add to the
amplitude. -/
theorem sum_starTerm_eq_amplitude (W : Sym2 (V × Fin 3) → ℂ) (u : V) (c : V → Fin 3) :
    ∑ v ∈ Finset.univ.erase u, starTerm W u v c = amplitude W c := by
  rw [← pmSum_univ, pmSum_expand W c (Finset.mem_univ u)]
  rfl

/-- **On a mixed colouring the edge values form a circulation**: they sum to zero at every site. -/
theorem sum_starTerm_eq_zero (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (u : V) (c : V → Fin 3) (hc : ¬ Amplitude.Monochromatic c) :
    ∑ v ∈ Finset.univ.erase u, starTerm W u v c = 0 := by
  rw [sum_starTerm_eq_amplitude]
  exact hzero c hc

/-- **Every site has a live neighbour.**  Needed by the global bound: it makes every component of
the live graph have at least two sites. -/
theorem liveNbrs_nonempty (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const (V := V) k) ≠ 0) (u : V) :
    (liveNbrs W u).Nonempty := by
  obtain ⟨v, hv, -⟩ := exists_starRow_ne_zero W hone u 0
  exact ⟨v, hv⟩

/-! ### Gauge relations

Weighting the vertex-sum identity by a site function and adding gives a relation among the edge
functions: the edge `{u,v}` is counted with `σ u + σ v`, and the total is the sum of `σ` times the
amplitude.  When `σ` sums to zero the right-hand side vanishes, so every such `σ` produces a
genuine relation.

These are the first-order gauge transformations.  Scaling the block at `{u,v}` by `ν u * ν v`
multiplies every perfect matching's contribution by the same factor `∏ ν`, because a matching meets
each site exactly once; differentiating at the identity gives the relation below.  So gauge symmetry
is a *source* of relations among the edge functions, and it accounts for the slack in the global
bound exactly. -/

/-- **The weighted vertex-sum identity**, which is the gauge relation in ordered form. -/
theorem sum_weighted_starTerm (W : Sym2 (V × Fin 3) → ℂ) (σ : V → ℂ) (c : V → Fin 3) :
    ∑ u : V, σ u * (∑ v ∈ Finset.univ.erase u, starTerm W u v c)
      = (∑ u : V, σ u) * amplitude W c := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun u _ => by rw [sum_starTerm_eq_amplitude]

/-- **A site function summing to zero gives a relation among the edge functions.** -/
theorem gauge_relation (W : Sym2 (V × Fin 3) → ℂ) (σ : V → ℂ) (hσ : ∑ u : V, σ u = 0)
    (c : V → Fin 3) :
    ∑ u : V, σ u * (∑ v ∈ Finset.univ.erase u, starTerm W u v c) = 0 := by
  rw [sum_weighted_starTerm, hσ, zero_mul]

/-! ### Two edges at once

Every argument so far has been first order: linear in one star, or the first variation of a global
scaling.  A second-order argument needs the term carried by *two* disjoint pairs at once, and the
expansion of a single star term into those.  Both are recorded here as the natural next primitive. -/

/-- The term carried by the two disjoint pairs `{u,v}` and `{x,y}`. -/
noncomputable def pairTerm (W : Sym2 (V × Fin 3) → ℂ) (u v x y : V) (c : V → Fin 3) : ℂ :=
  W s((u, c u), (v, c v)) * (W s((x, c x), (y, c y)) *
    pmSum W c (((((Finset.univ.erase u).erase v).erase x).erase y)))

/-- **A star term expands into two-pair terms** at any site outside its own pair. -/
theorem starTerm_expand_pair (W : Sym2 (V × Fin 3) → ℂ) (u v : V) (c : V → Fin 3) {x : V}
    (hxu : x ≠ u) (hxv : x ≠ v) :
    starTerm W u v c
      = ∑ y ∈ ((Finset.univ.erase u).erase v).erase x, pairTerm W u v x y c := by
  rw [starTerm_eq_mul, cofactor_expand W u v c hxu hxv, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => rfl

/-- **An arm live only off the diagonal has all three constant rows zero.**  Without the fact that no
live edge mixes colours, an arm can be live purely through an entry whose two colours differ; every
constant colouring then misses it entirely.  With `size_one_circuit_of_row_zero`, such an arm yields a
circuit of support one directly, so circuits of that size are not exotic. -/
theorem starRow_zero_of_offdiag (W : Sym2 (V × Fin 3) → ℂ) (u v : V)
    (h : ∀ k : Fin 3, W s((u, k), (v, k)) = 0) : ∀ k : Fin 3, starRow W u v k = 0 := by
  intro k
  simp only [starRow, starTerm, Amplitude.const]
  rw [h k, zero_mul]

/-! ### Moving along the variety, not along the fibre

Every deformation used so far preserved each amplitude exactly.  Minimality forbids more than
that: it forbids any GHZ system of smaller support, so a deformation only needs to keep the mixed
amplitudes at zero and the constant ones away from zero.  Zeroing a whole live block shifts every
amplitude by exactly that arm's own star term -- the expansion below, unconditional.  If the arm is
dead on every mixed colouring, the mixed amplitudes do not move at all, and minimality can only be
rescued by a constant amplitude landing on zero.

Hence the dichotomy: **a live arm is either alive on some mixed colouring, or it carries a
colour** -- some constant amplitude equals the arm's own constant row, the matchings avoiding the
pair cancelling exactly.  The four-site solution realises the carrying branch at every edge: each
colour class is a single perfect matching, so the colour-`k` matchings avoiding one of its own
edges sum to zero on the nose. -/

/-- **Zeroing a block shifts each amplitude by the arm's star term.** -/
theorem amplitude_zeroPair_expand (W : Sym2 (V × Fin 3) → ℂ) {u v : V} (hvu : v ≠ u)
    (c : V → Fin 3) :
    amplitude (MinimalSupport.zeroPair W u v) c = amplitude W c - starTerm W u v c := by
  classical
  have hexp : ∀ (X : Sym2 (V × Fin 3) → ℂ), amplitude X c
      = ∑ y ∈ Finset.univ.erase u,
          X s((u, c u), (y, c y)) * pmSum X c ((Finset.univ.erase u).erase y) := by
    intro X
    rw [← pmSum_univ, pmSum_expand X c (Finset.mem_univ u)]
    first
      | rfl
      | (refine Finset.sum_congr rfl fun y _ => ?_; congr 1)
  have hvmem : v ∈ (Finset.univ : Finset V).erase u :=
    Finset.mem_erase.mpr ⟨hvu, Finset.mem_univ v⟩
  have hpm : ∀ y : V, pmSum (MinimalSupport.zeroPair W u v) c ((Finset.univ.erase u).erase y)
      = pmSum W c ((Finset.univ.erase u).erase y) := by
    intro y
    refine pmSum_congr _ W c (fun x hx z hz => ?_)
    have hxu : x ≠ u := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hx)).1
    have hzu : z ≠ u := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hz)).1
    exact MinimalSupport.zeroPair_agree W u v x z _ _ (fun h => hxu h.1) (fun h => hzu h.2)
  rw [hexp (MinimalSupport.zeroPair W u v), hexp W]
  simp only [hpm]
  rw [← Finset.add_sum_erase _ _ hvmem, ← Finset.add_sum_erase _ _ hvmem,
    MinimalSupport.zeroPair_target, zero_mul, zero_add]
  have hrest : ∀ y ∈ ((Finset.univ : Finset V).erase u).erase v,
      MinimalSupport.zeroPair W u v s((u, c u), (y, c y))
          * pmSum W c ((Finset.univ.erase u).erase y)
        = W s((u, c u), (y, c y)) * pmSum W c ((Finset.univ.erase u).erase y) := by
    intro y hy
    have hyv : y ≠ v := (Finset.mem_erase.mp hy).1
    rw [MinimalSupport.zeroPair_agree W u v u y _ _ (fun h => hyv h.2) (fun h => hvu h.1.symm)]
  rw [Finset.sum_congr rfl hrest]
  simp only [starTerm]
  ring

/-- **A mixed-dead live arm carries a colour.**  If every non-constant colouring is blind through
the pair -- dead entry or vanishing cofactor -- then some constant amplitude equals the arm's own
constant row. -/
theorem mixed_dead_arm_carries_colour (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : IsSupportMinimal W) {u v : V} (hvu : v ≠ u)
    (hlive : ∃ a b : Fin 3, W s((u, a), (v, b)) ≠ 0)
    (hdead : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → starTerm W u v c = 0) :
    ∃ k : Fin 3, amplitude W (Amplitude.const (V := V) k) = starRow W u v k := by
  classical
  by_contra hcon
  push_neg at hcon
  have hghz : KrennGu.IsGHZ (MinimalSupport.zeroPair W u v) := by
    constructor
    · intro k
      rw [amplitude_zeroPair_expand W hvu]
      exact sub_ne_zero.mpr (hcon k)
    · intro c hc
      rw [amplitude_zeroPair_expand W hvu, hmin.1.2 c hc, hdead c hc, sub_zero]
  exact (Nat.not_lt_of_ge (hmin.2 _ hghz))
    (MinimalSupport.supportMass_zeroPair_lt W hvu hlive)

/-- The carried colour is live on the arm's diagonal: a dead entry would make the carried
amplitude zero. -/
theorem carried_colour_live_diag (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : IsSupportMinimal W) {u v : V} (hvu : v ≠ u)
    (hlive : ∃ a b : Fin 3, W s((u, a), (v, b)) ≠ 0)
    (hdead : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → starTerm W u v c = 0) :
    ∃ k : Fin 3, W s((u, k), (v, k)) ≠ 0 ∧
      amplitude W (Amplitude.const (V := V) k) = starRow W u v k := by
  obtain ⟨k, hk⟩ := mixed_dead_arm_carries_colour W hmin hvu hlive hdead
  refine ⟨k, fun h0 => hmin.1.1 k ?_, hk⟩
  rw [hk]
  simp only [starRow, starTerm, Amplitude.const]
  rw [h0, zero_mul]

/-- **Carrying arms are scarce.**  The constant rows at a site add to the amplitude, and a carrying
arm's row *is* the amplitude, so a site whose live arms all carry the same colour has exactly one of
them.  This is the counting bite of the dichotomy: wherever the mixed colourings are blind, the
carrying branch caps the degree by colour. -/
theorem liveNbrs_card_eq_one_of_all_carrying (W : Sym2 (V × Fin 3) → ℂ) (u : V) (k : Fin 3)
    (hone : amplitude W (Amplitude.const (V := V) k) ≠ 0)
    (hcarry : ∀ y ∈ liveNbrs W u, amplitude W (Amplitude.const (V := V) k) = starRow W u y k) :
    (liveNbrs W u).card = 1 := by
  classical
  have hsub : liveNbrs W u ⊆ (Finset.univ : Finset V).erase u := fun y hy =>
    Finset.mem_erase.mpr ⟨(mem_liveNbrs.mp hy).1, Finset.mem_univ y⟩
  have hsum := sum_starRow W u k
  rw [← Finset.sum_subset hsub (fun y hy hyn => ?_)] at hsum
  · rw [Finset.sum_congr rfl (fun y hy => (hcarry y hy).symm), Finset.sum_const,
      nsmul_eq_mul] at hsum
    have hzero : (((liveNbrs W u).card : ℂ) - 1)
        * amplitude W (Amplitude.const (V := V) k) = 0 := by
      rw [sub_mul, one_mul, hsum, sub_self]
    rcases mul_eq_zero.mp hzero with h1 | h1
    · exact_mod_cast sub_eq_zero.mp h1
    · exact absurd h1 hone
  · have hyu : y ≠ u := (Finset.mem_erase.mp hy).1
    have hdead : W s((u, k), (y, k)) = 0 := by
      by_contra hne
      exact hyn (mem_liveNbrs.mpr ⟨hyu, k, k, hne⟩)
    simp only [starRow, starTerm, Amplitude.const]
    rw [hdead, zero_mul]

/-! ### The dichotomy, sharpened at a monochromatic-block site

When no live edge mixes colours, a mixed-alive certificate cannot hide in the pair's own values:
the selected entry forces both ends to wear one colour `b`, and a complement wearing a single
constant is either `b` -- making the whole colouring constant -- or a different colour, which the
live pair kills.  So the surviving cofactor belongs to a colouring **non-constant on the
complement**: a direct witness against degeneracy at the site, in its exact form.

Hence at a degenerate site every live arm carries a colour.  This is the bridge between the
carrying dichotomy and the degeneracy frontier, per site rather than global. -/

theorem arm_carries_or_not_degenerate (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : IsSupportMinimal W)
    (hmono : ∀ (x y : V), y ≠ x → ∀ p q : Fin 3, p ≠ q → W s((x, p), (y, q)) = 0)
    (hcard : 4 < Fintype.card V)
    {u v : V} (hvu : v ≠ u) (hlive : ∃ a b : Fin 3, W s((u, a), (v, b)) ≠ 0) :
    (∃ k : Fin 3, amplitude W (Amplitude.const (V := V) k) = starRow W u v k) ∨
      ¬ FanStructure.Degenerate W u := by
  classical
  by_cases hdead : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → starTerm W u v c = 0
  · exact Or.inl (mixed_dead_arm_carries_colour W hmin hvu hlive hdead)
  · push_neg at hdead
    obtain ⟨c, hcmix, hcne⟩ := hdead
    have hW : W s((u, c u), (v, c v)) ≠ 0 := fun h => hcne (by
      simp only [starTerm]
      rw [h, zero_mul])
    have hH : pmSum W c ((Finset.univ.erase u).erase v) ≠ 0 := fun h => hcne (by
      simp only [starTerm]
      rw [h, mul_zero])
    have hcuv : c u = c v := by
      by_contra hne
      exact hW (hmono u v hvu (c u) (c v) hne)
    have hSne : (((Finset.univ : Finset V).erase u).erase v).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem
        (Finset.mem_erase.mpr ⟨hvu, Finset.mem_univ v⟩), Finset.card_erase_of_mem
        (Finset.mem_univ u), Finset.card_univ]
      omega
    by_cases hconst : ∀ x ∈ ((Finset.univ : Finset V).erase u).erase v,
        ∀ y ∈ ((Finset.univ : Finset V).erase u).erase v, c x = c y
    · exfalso
      obtain ⟨w, hw⟩ := id hSne
      by_cases hmb : c w = c u
      · refine hcmix ⟨c u, fun z => ?_⟩
        by_cases hzu : z = u
        · rw [hzu]
        · by_cases hzv : z = v
          · rw [hzv, hcuv]
          · rw [hconst z (Finset.mem_erase.mpr ⟨hzv, Finset.mem_erase.mpr
              ⟨hzu, Finset.mem_univ z⟩⟩) w hw, hmb]
      · have hnem : Nonempty V := Fintype.card_pos_iff.mp (by omega)
        have hghz : MatchingSum.IsGHZOn W (Finset.univ : Finset V) :=
          (MatchingSum.isGHZOn_univ_iff W).mpr hmin.1
        have hset : ((Finset.univ : Finset V).erase u).erase v
            = (Finset.univ : Finset V) \ ({u, v} : Finset V) := by
          ext z
          simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
            Finset.mem_singleton, true_and, not_or]
          tauto
        have hrest : ((Finset.univ : Finset V) \ ({u, v} : Finset V)).Nonempty := by
          rw [← hset]; exact hSne
        have hbb : W s((u, c v), (v, c v)) ≠ 0 := by
          rw [show s((u, c v), (v, c v)) = s((u, c u), (v, c v)) from by rw [hcuv]]
          exact hW
        have hwv : c w ≠ c v := fun h => hmb (h.trans hcuv.symm)
        have hkill := NoCancellation.pmSum_delete_live_pair_zero W hmono hghz hwv hvu
          (Finset.mem_univ u) (Finset.mem_univ v) hrest hbb
        rw [← hset] at hkill
        refine hH ?_
        rw [pmSum_congr_colour W (c' := Amplitude.const (V := V) (c w))
          (fun x hx => hconst x hx w hw)]
        exact hkill
    · push_neg at hconst
      obtain ⟨x, hx, y, hy, hxy⟩ := hconst
      exact Or.inr (fun hdeg => hH (hdeg v (Finset.mem_erase.mpr ⟨hvu, Finset.mem_univ v⟩)
        c x hx y hy hxy))

/-- **At a degenerate site every live arm carries a colour.** -/
theorem degenerate_site_arms_carry (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : IsSupportMinimal W)
    (hmono : ∀ (x y : V), y ≠ x → ∀ p q : Fin 3, p ≠ q → W s((x, p), (y, q)) = 0)
    (hcard : 4 < Fintype.card V) {u : V} (hdeg : FanStructure.Degenerate W u)
    {v : V} (hv : v ∈ liveNbrs W u) :
    ∃ k : Fin 3, amplitude W (Amplitude.const (V := V) k) = starRow W u v k := by
  obtain ⟨hvu, hlive⟩ := mem_liveNbrs.mp hv
  exact (arm_carries_or_not_degenerate W hmin hmono hcard hvu hlive).resolve_right
    (fun h => h hdeg)

/-- **A carried star is exactly three-regular.**  If every live arm at a site has a single diagonal
colour and carries some colour, it can only carry its own; the colour-`k` rows then vanish except at
the colour-`k` arms, each contributing the whole amplitude, and the rows sum to the amplitude -- so
every colour is represented exactly once.  Not merely at most three arms: exactly three, one per
colour.  The four-site solution is the model case. -/
theorem liveNbrs_card_eq_three_of_carrying (W : Sym2 (V × Fin 3) → ℂ) (u : V)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const (V := V) k) ≠ 0)
    (col : V → Fin 3)
    (hdiag : ∀ v ∈ liveNbrs W u, ∀ k : Fin 3, k ≠ col v → W s((u, k), (v, k)) = 0)
    (hcarry : ∀ v ∈ liveNbrs W u, ∃ k : Fin 3,
      amplitude W (Amplitude.const (V := V) k) = starRow W u v k) :
    (liveNbrs W u).card = 3 := by
  classical
  have hsub : liveNbrs W u ⊆ (Finset.univ : Finset V).erase u := fun y hy =>
    Finset.mem_erase.mpr ⟨(mem_liveNbrs.mp hy).1, Finset.mem_univ y⟩
  -- a carrying arm carries its own colour
  have hcol : ∀ v ∈ liveNbrs W u,
      amplitude W (Amplitude.const (V := V) (col v)) = starRow W u v (col v) := by
    intro v hv
    obtain ⟨k, hk⟩ := hcarry v hv
    by_cases hkc : k = col v
    · rw [← hkc]; exact hk
    · exfalso
      refine hone k ?_
      rw [hk]
      simp only [starRow, starTerm, Amplitude.const]
      rw [hdiag v hv k hkc, zero_mul]
  -- each colour class has exactly one arm
  have hfib : ∀ k : Fin 3, ((liveNbrs W u).filter (fun v => col v = k)).card = 1 := by
    intro k
    have h1 := sum_starRow W u k
    have h2 : ∑ y ∈ (Finset.univ : Finset V).erase u, starRow W u y k
        = ∑ y ∈ liveNbrs W u, starRow W u y k := by
      refine (Finset.sum_subset hsub (fun y hy hyn => ?_)).symm
      have hyu : y ≠ u := (Finset.mem_erase.mp hy).1
      have hdead : W s((u, k), (y, k)) = 0 := by
        by_contra hne
        exact hyn (mem_liveNbrs.mpr ⟨hyu, k, k, hne⟩)
      simp only [starRow, starTerm, Amplitude.const]
      rw [hdead, zero_mul]
    have h3 : ∑ y ∈ liveNbrs W u, starRow W u y k
        = ∑ y ∈ (liveNbrs W u).filter (fun v => col v = k), starRow W u y k := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) (fun y hy hyn => ?_)).symm
      have hne : col y ≠ k := fun h => hyn (Finset.mem_filter.mpr ⟨hy, h⟩)
      simp only [starRow, starTerm, Amplitude.const]
      rw [hdiag y hy k (fun h => hne h.symm), zero_mul]
    have h4 : ∑ y ∈ (liveNbrs W u).filter (fun v => col v = k), starRow W u y k
        = (((liveNbrs W u).filter (fun v => col v = k)).card : ℕ)
            • amplitude W (Amplitude.const (V := V) k) := by
      rw [← Finset.sum_const]
      refine Finset.sum_congr rfl (fun y hy => ?_)
      have hyl : y ∈ liveNbrs W u := Finset.mem_of_mem_filter y hy
      have hyk : col y = k := (Finset.mem_filter.mp hy).2
      rw [← hyk]
      exact (hcol y hyl).symm
    rw [h2, h3, h4, nsmul_eq_mul] at h1
    have hzero : ((((liveNbrs W u).filter (fun v => col v = k)).card : ℂ) - 1)
        * amplitude W (Amplitude.const (V := V) k) = 0 := by
      rw [sub_mul, one_mul, h1, sub_self]
    rcases mul_eq_zero.mp hzero with h5 | h5
    · exact_mod_cast sub_eq_zero.mp h5
    · exact absurd h5 (hone k)
  rw [Finset.card_eq_sum_card_fiberwise (f := col) (t := (Finset.univ : Finset (Fin 3)))
    (fun x _ => Finset.mem_univ (col x))]
  simp [hfib]

/-- **A tame star is exactly three-regular.**  Call an arm *tame* when its live diagonal colours
agree pairwise -- at most one diagonal colour -- and it is dead on every mixed colouring.  If every
live arm at a site is tame, the site has exactly three arms: tameness forces each arm to carry its
own single colour, and carried arms come one per colour.

Contrapositive, which is the excess-site defect disjunction: at any site whose degree is *not*
three -- in particular wherever a circuit lives -- some live arm is **bi-diagonal** (two live
diagonal colours) or **mixed-alive** (a non-constant colouring with live entry and surviving
cofactor).  Excess produces a concrete object, rather than merely resisting analysis. -/
theorem liveNbrs_card_eq_three_of_tame (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : IsSupportMinimal W) (u : V)
    (htame : ∀ v ∈ liveNbrs W u,
      (∀ k k' : Fin 3, W s((u, k), (v, k)) ≠ 0 → W s((u, k'), (v, k')) ≠ 0 → k = k') ∧
      (∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → starTerm W u v c = 0)) :
    (liveNbrs W u).card = 3 := by
  classical
  have hcarryall : ∀ v ∈ liveNbrs W u, ∃ k : Fin 3, W s((u, k), (v, k)) ≠ 0 ∧
      amplitude W (Amplitude.const (V := V) k) = starRow W u v k := by
    intro v hv
    obtain ⟨hvu, hlive⟩ := mem_liveNbrs.mp hv
    exact carried_colour_live_diag W hmin hvu hlive (htame v hv).2
  choose! col hcold hcolc using hcarryall
  refine liveNbrs_card_eq_three_of_carrying W u hmin.1.1 col (fun v hv k hk => ?_)
    (fun v hv => ⟨col v, hcolc v hv⟩)
  by_contra hne
  exact hk ((htame v hv).1 k (col v) hne (hcold v hv))

/-! ### The bi-diagonal branch collapses

A bi-diagonal arm is live in two colours, so the delete-live-pair theorem fires twice: the
`a`-liveness kills every constant cofactor except `a`'s, the `b`-liveness kills every one except
`b`'s, and together they kill all three.  All constant rows are then zero, so the arm cannot carry;
by the dichotomy it is mixed-alive, and with zero rows it is *precisely a size-one circuit*.

So under monochromatic blocks the trichotomy is a dichotomy -- degree three, or a mixed-alive
arm -- and bi-diagonal arms are not a separate difficulty: they are the size-one circuits.
Eliminating that size is exactly per-pair single-colouredness, previously reachable only through
full degeneracy. -/

theorem bidiagonal_const_cofactors_zero (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : IsSupportMinimal W)
    (hmono : ∀ (x y : V), y ≠ x → ∀ p q : Fin 3, p ≠ q → W s((x, p), (y, q)) = 0)
    (hcard : 4 < Fintype.card V)
    {u v : V} (hvu : v ≠ u) {a b : Fin 3} (hab : a ≠ b)
    (ha : W s((u, a), (v, a)) ≠ 0) (hb : W s((u, b), (v, b)) ≠ 0) :
    ∀ k : Fin 3, pmSum W (Amplitude.const (V := V) k) ((Finset.univ.erase u).erase v) = 0 := by
  classical
  intro k
  have hnem : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hghz : MatchingSum.IsGHZOn W (Finset.univ : Finset V) :=
    (MatchingSum.isGHZOn_univ_iff W).mpr hmin.1
  have hSne : (((Finset.univ : Finset V).erase u).erase v).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem
      (Finset.mem_erase.mpr ⟨hvu, Finset.mem_univ v⟩), Finset.card_erase_of_mem
      (Finset.mem_univ u), Finset.card_univ]
    omega
  have hset : ((Finset.univ : Finset V).erase u).erase v
      = (Finset.univ : Finset V) \ ({u, v} : Finset V) := by
    ext z
    simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
      Finset.mem_singleton, true_and, not_or]
    tauto
  have hrest : ((Finset.univ : Finset V) \ ({u, v} : Finset V)).Nonempty := by
    rw [← hset]; exact hSne
  by_cases hka : k = a
  · subst hka
    have := NoCancellation.pmSum_delete_live_pair_zero W hmono hghz hab hvu
      (Finset.mem_univ u) (Finset.mem_univ v) hrest hb
    rw [← hset] at this
    exact this
  · have := NoCancellation.pmSum_delete_live_pair_zero W hmono hghz hka hvu
      (Finset.mem_univ u) (Finset.mem_univ v) hrest ha
    rw [← hset] at this
    exact this

/-- **A bi-diagonal arm is a size-one circuit.** -/
theorem bidiagonal_size_one_circuit (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : IsSupportMinimal W)
    (hmono : ∀ (x y : V), y ≠ x → ∀ p q : Fin 3, p ≠ q → W s((x, p), (y, q)) = 0)
    (hcard : 4 < Fintype.card V)
    {u v : V} (hvu : v ≠ u) {a b : Fin 3} (hab : a ≠ b)
    (ha : W s((u, a), (v, a)) ≠ 0) (hb : W s((u, b), (v, b)) ≠ 0) :
    ∃ ω : StarCircuitWitness W u, ω.supp = ({v} : Finset V) := by
  have hcof := bidiagonal_const_cofactors_zero W hmin hmono hcard hvu hab ha hb
  refine size_one_circuit_of_row_zero W hmin u
    (mem_liveNbrs.mpr ⟨hvu, a, a, ha⟩) (fun k => ?_)
  simp only [starRow, starTerm]
  rw [hcof k, mul_zero]

/-- **Degree three, or a mixed-alive arm.**  Under monochromatic blocks the trichotomy is a
dichotomy: every site of a support-minimal system is exactly three-regular or hands over a
non-constant colouring with a live entry and a surviving cofactor. -/
theorem three_regular_or_mixed_alive (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : IsSupportMinimal W)
    (hmono : ∀ (x y : V), y ≠ x → ∀ p q : Fin 3, p ≠ q → W s((x, p), (y, q)) = 0)
    (hcard : 4 < Fintype.card V) (u : V) :
    (liveNbrs W u).card = 3 ∨
      ∃ v ∈ liveNbrs W u, ∃ c : V → Fin 3,
        ¬ Amplitude.Monochromatic c ∧ starTerm W u v c ≠ 0 := by
  classical
  by_cases hmx : ∃ v ∈ liveNbrs W u, ∃ c : V → Fin 3,
      ¬ Amplitude.Monochromatic c ∧ starTerm W u v c ≠ 0
  · exact Or.inr hmx
  · push_neg at hmx
    refine Or.inl (liveNbrs_card_eq_three_of_tame W hmin u (fun v hv =>
      ⟨fun k k' hk hk' => ?_, fun c hc => hmx v hv c hc⟩))
    by_contra hne
    have hvu : v ≠ u := (mem_liveNbrs.mp hv).1
    have hcof := bidiagonal_const_cofactors_zero W hmin hmono hcard hvu hne hk hk'
    obtain ⟨m, hm⟩ := mixed_dead_arm_carries_colour W hmin hvu ⟨k, k, hk⟩
      (fun c hc => hmx v hv c hc)
    refine hmin.1.1 m ?_
    rw [hm]
    simp only [starRow, starTerm]
    rw [hcof m, mul_zero]

/-! ### What a mixed-alive certificate is made of

Under monochromatic blocks a surviving mixed cofactor factors over its colour fibres, so each fibre
of the certificate's colouring is certified in its own colour: the certificate *is* a certified
partition of the doubly-punctured set.  And the pair-and-split closer then eliminates outright every
certificate whose colouring avoids the pair's own colour -- the first sub-case of the mixed-alive
branch to die.  Every surviving certificate must colour part of the complement with the pair's own
colour, giving the pair a certified same-colour crowd. -/

theorem mixed_alive_fibre_certificates (W : Sym2 (V × Fin 3) → ℂ)
    (hmono : ∀ (x y : V), y ≠ x → ∀ p q : Fin 3, p ≠ q → W s((x, p), (y, q)) = 0)
    (u v : V) {c : V → Fin 3}
    (hH : pmSum W c ((Finset.univ.erase u).erase v) ≠ 0) :
    ∀ k : Fin 3, pmSum W (Amplitude.const (V := V) k)
      (((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c k) ≠ 0 := by
  classical
  have hcut : ∀ x y : V, c x ≠ c y → W s((x, c x), (y, c y)) = 0 := by
    intro x y hne
    exact hmono x y (fun h => hne (by rw [h])) _ _ hne
  rw [NoCancellation.pmSum_product_on W c hcut] at hH
  have h0 := left_ne_zero_of_mul (left_ne_zero_of_mul hH)
  have h1 := right_ne_zero_of_mul (left_ne_zero_of_mul hH)
  have h2 := right_ne_zero_of_mul hH
  intro k
  have hcongr : ∀ m : Fin 3,
      pmSum W c (((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c m)
        = pmSum W (Amplitude.const (V := V) m)
            (((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c m) :=
    fun m => pmSum_congr_colour W
      (fun x hx => NoCancellation.mem_fiber.mp (Finset.mem_inter.mp hx).2)
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by revert k; decide
  rcases hk with rfl | rfl | rfl
  · rw [← hcongr 0]; exact h0
  · rw [← hcongr 1]; exact h1
  · rw [← hcongr 2]; exact h2

/-- **A certificate cannot avoid its own colour.**  A mixed-alive certificate whose colouring keeps
the pair's colour off the complement splits the complement into the two other colours' certified
fibres, and the pair-and-split closer forbids exactly that.  So some complement site wears the
pair's colour. -/
theorem mixed_alive_uses_own_colour (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ cc : V → Fin 3, ¬ Amplitude.Monochromatic cc → amplitude W cc = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ p q : Fin 3, p ≠ q → W s((x, p), (y, q)) = 0)
    (hcard : 4 < Fintype.card V)
    {u v : V} (hvu : v ≠ u) {c : V → Fin 3}
    (hlive : W s((u, c u), (v, c v)) ≠ 0)
    (hH : pmSum W c ((Finset.univ.erase u).erase v) ≠ 0) :
    ∃ z ∈ (Finset.univ.erase u).erase v, c z = c u := by
  classical
  by_contra hcon
  push_neg at hcon
  have hcv : c v = c u := by
    by_contra hne
    exact hlive (hmono u v hvu _ _ (fun h => hne h.symm))
  have hothers : ∀ b₀ : Fin 3, ∃ p q : Fin 3, b₀ ≠ p ∧ b₀ ≠ q ∧ p ≠ q ∧
      ∀ k : Fin 3, k = b₀ ∨ k = p ∨ k = q := by decide
  obtain ⟨p, q, hp, hq, hpq, hcover⟩ := hothers (c u)
  have hcert := mixed_alive_fibre_certificates W hmono u v hH
  have hset : ((Finset.univ : Finset V).erase u).erase v
      = (Finset.univ : Finset V) \ ({u, v} : Finset V) := by
    ext z
    simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
      Finset.mem_singleton, true_and, not_or]
    tauto
  have hSne : (((Finset.univ : Finset V).erase u).erase v).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem
      (Finset.mem_erase.mpr ⟨hvu, Finset.mem_univ v⟩), Finset.card_erase_of_mem
      (Finset.mem_univ u), Finset.card_univ]
    omega
  have hunion : (((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c p)
      ∪ (((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c q)
      = (Finset.univ.erase u).erase v := by
    ext z
    simp only [Finset.mem_union, Finset.mem_inter, NoCancellation.mem_fiber]
    constructor
    · rintro (⟨hz, -⟩ | ⟨hz, -⟩) <;> exact hz
    · intro hz
      rcases hcover (c z) with h | h | h
      · exact absurd h (hcon z hz)
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨hz, h⟩
  refine NoCancellation.false_of_pair_and_split W hzero hmono hp hq hpq hvu
    (by rw [show s((u, c u), (v, c u)) = s((u, c u), (v, c v)) from by rw [hcv]]; exact hlive)
    _ _ (Finset.disjoint_left.mpr (fun z hz hz' => hpq ?_))
    (by rw [hunion, hset]) (by rw [hunion]; exact hSne)
    (hcert p) (hcert q)
  rw [← NoCancellation.mem_fiber.mp (Finset.mem_inter.mp hz).2,
    NoCancellation.mem_fiber.mp (Finset.mem_inter.mp hz').2]

/-- **The excess-site normal form.**  At any site of a support-minimal system with monochromatic
blocks whose degree is not three, there is a live arm and a colouring in which:
the arm's two ends wear one colour and its entry there is live; every colour fibre of the punctured
complement is certified in its own colour; the arm's own colour appears on the complement; and so
does some other colour.  This is everything the carrying lane extracts from excess, in one
statement: a live pair with a certified same-colour crowd, inside a fully certified partition. -/
theorem excess_site_normal_form (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : IsSupportMinimal W)
    (hmono : ∀ (x y : V), y ≠ x → ∀ p q : Fin 3, p ≠ q → W s((x, p), (y, q)) = 0)
    (hcard : 4 < Fintype.card V)
    {u : V} (hdeg : (liveNbrs W u).card ≠ 3) :
    ∃ v ∈ liveNbrs W u, ∃ c : V → Fin 3,
      c v = c u ∧
      W s((u, c u), (v, c u)) ≠ 0 ∧
      (∀ k : Fin 3, pmSum W (Amplitude.const (V := V) k)
        (((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c k) ≠ 0) ∧
      (∃ z ∈ (Finset.univ.erase u).erase v, c z = c u) ∧
      (∃ z ∈ (Finset.univ.erase u).erase v, c z ≠ c u) := by
  classical
  rcases three_regular_or_mixed_alive W hmin hmono hcard u with h3 | ⟨v, hv, c, hcmix, hterm⟩
  · exact absurd h3 hdeg
  · have hvu : v ≠ u := (mem_liveNbrs.mp hv).1
    have hW : W s((u, c u), (v, c v)) ≠ 0 := fun h => hterm (by
      simp only [starTerm]
      rw [h, zero_mul])
    have hH : pmSum W c ((Finset.univ.erase u).erase v) ≠ 0 := fun h => hterm (by
      simp only [starTerm]
      rw [h, mul_zero])
    have hcv : c v = c u := by
      by_contra hne
      exact hW (hmono u v hvu _ _ (fun h => hne h.symm))
    have hentry : W s((u, c u), (v, c u)) ≠ 0 := by
      rw [show s((u, c u), (v, c u)) = s((u, c u), (v, c v)) from by rw [hcv]]
      exact hW
    have hnonb : ∃ z ∈ (Finset.univ.erase u).erase v, c z ≠ c u := by
      by_contra hall
      push_neg at hall
      refine hcmix ⟨c u, fun z => ?_⟩
      by_cases hzu : z = u
      · rw [hzu]
      · by_cases hzv : z = v
        · rw [hzv, hcv]
        · exact hall z (Finset.mem_erase.mpr ⟨hzv, Finset.mem_erase.mpr
            ⟨hzu, Finset.mem_univ z⟩⟩)
    exact ⟨v, hv, c, hcv, hentry,
      mixed_alive_fibre_certificates W hmono u v hH,
      mixed_alive_uses_own_colour W hmin.1.2 hmono hcard hvu hW hH, hnonb⟩

/-! The generic two-pivot expansion and forced-crossing calculus lives in
`Mettapedia.Combinatorics.Matching.Crossing`. -/

/-! ### The crossing certificate at an excess site

The excess normal form hands over a live same-coloured pair together with a certified crowd of its
own colour and two certified fibres in the other colours.  The colouring is not constant, so its
amplitude vanishes; the amplitude factors over the three fibres; the other two factors are non-zero;
so the pair's own fibre -- the crowd *with the pair adjoined* -- has vanishing sum.  The direct term
of that sum is the pair's live entry times the crowd's non-zero sum, so the crossing lemma applies.

The crowd must therefore reach back: two of its sites take live edges from the two ends of the pair,
and what is left of the crowd is still certified.  This strictly strengthens the normal form -- every
field of it is retained -- and it depends on monochromatic blocks exactly as the normal form does. -/
theorem excess_site_crossing_certificate (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : IsSupportMinimal W)
    (hmono : ∀ (x y : V), y ≠ x → ∀ p q : Fin 3, p ≠ q → W s((x, p), (y, q)) = 0)
    (hcard : 4 < Fintype.card V)
    {u : V} (hdeg : (liveNbrs W u).card ≠ 3) :
    ∃ v ∈ liveNbrs W u, ∃ c : V → Fin 3,
      c v = c u ∧
      W s((u, c u), (v, c u)) ≠ 0 ∧
      (∀ k : Fin 3, pmSum W (Amplitude.const (V := V) k)
        (((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c k) ≠ 0) ∧
      (∃ z ∈ (Finset.univ.erase u).erase v, c z = c u) ∧
      (∃ z ∈ (Finset.univ.erase u).erase v, c z ≠ c u) ∧
      ∃ x ∈ ((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c (c u),
        ∃ y ∈ (((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c (c u)).erase x,
          W s((u, c u), (x, c u)) ≠ 0 ∧ W s((v, c u), (y, c u)) ≠ 0 ∧
            pmSum W (Amplitude.const (V := V) (c u))
              (((((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c (c u)).erase x).erase y)
              ≠ 0 := by
  classical
  obtain ⟨v, hv, c, hcv, hentry, hfib, hown, hother⟩ :=
    excess_site_normal_form W hmin hmono hcard hdeg
  refine ⟨v, hv, c, hcv, hentry, hfib, hown, hother, ?_⟩
  have hvu : v ≠ u := (mem_liveNbrs.mp hv).1
  set A : Finset V := ((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c (c u) with hAdef
  have hcmix : ¬ Amplitude.Monochromatic c := by
    obtain ⟨z, hz, hzne⟩ := hother
    rintro ⟨k, hk⟩
    exact hzne (by rw [hk z, hk u])
  have hfibre : NoCancellation.fiber c (c u) = insert u (insert v A) := by
    ext z
    simp only [NoCancellation.mem_fiber, Finset.mem_insert, hAdef, Finset.mem_inter,
      Finset.mem_erase, Finset.mem_univ, and_true, true_and]
    constructor
    · intro hz
      by_cases hzu : z = u
      · exact Or.inl hzu
      · by_cases hzv : z = v
        · exact Or.inr (Or.inl hzv)
        · exact Or.inr (Or.inr ⟨⟨hzv, hzu⟩, hz⟩)
    · rintro (rfl | rfl | ⟨-, hz⟩)
      · rfl
      · exact hcv
      · exact hz
  have huA : u ∉ A := by
    intro h
    exact (Finset.mem_erase.mp
      (Finset.mem_of_mem_erase (Finset.mem_inter.mp h).1)).1 rfl
  have hvA : v ∉ A := by
    intro h
    exact (Finset.mem_erase.mp (Finset.mem_inter.mp h).1).1 rfl
  have hcut : ∀ x y : V, c x ≠ c y → W s((x, c x), (y, c y)) = 0 := fun x y hne =>
    hmono x y (fun h => hne (by rw [h])) _ _ hne
  have hprod := NoCancellation.pmSum_product_on W c hcut (Finset.univ : Finset V)
  rw [pmSum_univ, hmin.1.2 c hcmix] at hprod
  have hinter : ∀ k : Fin 3, (Finset.univ : Finset V) ∩ NoCancellation.fiber c k
      = NoCancellation.fiber c k := fun k => Finset.univ_inter _
  simp only [hinter] at hprod
  have hother_fib : ∀ k : Fin 3, k ≠ c u → pmSum W c (NoCancellation.fiber c k) ≠ 0 := by
    intro k hk
    have hEq : NoCancellation.fiber c k
        = ((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c k := by
      ext z
      simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_univ, and_true,
        NoCancellation.mem_fiber, true_and]
      constructor
      · intro hz
        refine ⟨⟨fun h => hk ?_, fun h => hk ?_⟩, hz⟩
        · rw [← hcv, ← h]; exact hz.symm
        · rw [← h]; exact hz.symm
      · exact fun h => h.2
    rw [hEq, pmSum_congr_colour W (c' := Amplitude.const (V := V) k)
      (fun z hz => NoCancellation.mem_fiber.mp (Finset.mem_inter.mp hz).2)]
    exact hfib k
  have hzeroA : pmSum W (Amplitude.const (V := V) (c u)) (insert u (insert v A)) = 0 := by
    have hfa : pmSum W c (NoCancellation.fiber c (c u)) = 0 := by
      rcases mul_eq_zero.mp hprod.symm with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · by_cases h0 : (0 : Fin 3) = c u
          · rw [← h0]; exact h'
          · exact absurd h' (hother_fib 0 h0)
        · by_cases h1 : (1 : Fin 3) = c u
          · rw [← h1]; exact h'
          · exact absurd h' (hother_fib 1 h1)
      · by_cases h2 : (2 : Fin 3) = c u
        · rw [← h2]; exact h
        · exact absurd h (hother_fib 2 h2)
    rw [← hfibre, ← pmSum_congr_colour W (c := c) (c' := Amplitude.const (V := V) (c u))
      (fun z hz => NoCancellation.mem_fiber.mp hz)]
    exact hfa
  have hdirect : W (Sym2.map (Amplitude.paint (Amplitude.const (V := V) (c u))) s(u, v)) ≠ 0 :=
    hentry
  obtain ⟨x, hx, y, hy, hux, hvy, hrem⟩ :=
    exists_crossing W (Amplitude.const (V := V) (c u)) huA hvA (Ne.symm hvu) hdirect
      (hfib (c u)) hzeroA
  exact ⟨x, hx, y, hy, hux, hvy, hrem⟩

/-! ## The enriched state and the transport law

The obstruction says a transition must see more than the crossing fields.  The extra data is exactly
the ambient three-fibre partition: a vanishing matching sum in this setting is never an accident, it
is one factor of a vanishing amplitude whose other two factors are certified.  So the enriched state
is a *sharp partition* -- a colouring, a live pair inside one fibre, and non-vanishing certificates
for all three fibres off that pair -- and the moves available are recolourings of pairs, single-site
moves being free for parity reasons.

Recolouring the crossing pair `{x,y}` out of its fibre into any other colour `k` produces a
non-constant colouring, hence a vanishing amplitude, hence a vanishing product of three fibre sums.
The third fibre is untouched and certified.  What is left is a dichotomy: either the shrunk crowd
carries a vanishing extension by the *same* pair -- which is precisely a crossing state two sites
smaller -- or the receiving fibre is annihilated by the pair it absorbed. -/

section Recolour

variable {c : V → Fin 3} {x y : V} {k : Fin 3}

/-- Recolouring `x` and `y` to `k` leaves every other site alone. -/
theorem recolour_of_ne {z : V} (hzx : z ≠ x) (hzy : z ≠ y) :
    Function.update (Function.update c x k) y k z = c z := by
  rw [Function.update_of_ne hzy, Function.update_of_ne hzx]

theorem recolour_left (hxy : x ≠ y) : Function.update (Function.update c x k) y k x = k := by
  rw [Function.update_of_ne hxy, Function.update_self]

theorem recolour_right : Function.update (Function.update c x k) y k y = k :=
  Function.update_self _ _ _

/-- The receiving fibre gains the pair. -/
theorem fiber_recolour_self (hxy : x ≠ y) :
    NoCancellation.fiber (Function.update (Function.update c x k) y k) k
      = insert x (insert y (NoCancellation.fiber c k)) := by
  ext z
  simp only [NoCancellation.mem_fiber, Finset.mem_insert]
  by_cases hzy : z = y
  · rw [hzy, recolour_right]; simp
  · by_cases hzx : z = x
    · rw [hzx, recolour_left (hzx ▸ hzy)]; simp
    · rw [recolour_of_ne hzx hzy]
      simp only [hzx, hzy, false_or]

/-- Every other fibre loses the pair. -/
theorem fiber_recolour_other {m : Fin 3} (hm : m ≠ k) :
    NoCancellation.fiber (Function.update (Function.update c x k) y k) m
      = ((NoCancellation.fiber c m).erase x).erase y := by
  ext z
  simp only [NoCancellation.mem_fiber, Finset.mem_erase]
  by_cases hzy : z = y
  · rw [hzy, recolour_right]; simp [Ne.symm hm]
  · by_cases hzx : z = x
    · rw [hzx, recolour_left (hzx ▸ hzy)]; simp [Ne.symm hm]
    · rw [recolour_of_ne hzx hzy]
      simp only [hzy, hzx, ne_eq, not_false_eq_true, true_and]

end Recolour

/-- On its own fibre a colouring is the constant colouring. -/
theorem pmSum_fiber_const (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3) (k : Fin 3) :
    pmSum W c (NoCancellation.fiber c k)
      = pmSum W (Amplitude.const (V := V) k) (NoCancellation.fiber c k) :=
  pmSum_congr_colour W (fun _ hz => NoCancellation.mem_fiber.mp hz)

/-- A non-constant colouring has a vanishing amplitude, and under monochromatic blocks the amplitude
is the product of its three fibre sums.  So the three fibres cannot all be certified. -/
theorem fibres_product_eq_zero (W : Sym2 (V × Fin 3) → ℂ) (hmin : IsSupportMinimal W)
    (hmono : ∀ (p q : V), q ≠ p → ∀ a b : Fin 3, a ≠ b → W s((p, a), (q, b)) = 0)
    {c : V → Fin 3} (hnc : ¬ Amplitude.Monochromatic c) :
    pmSum W (Amplitude.const (V := V) 0) (NoCancellation.fiber c 0)
        * pmSum W (Amplitude.const (V := V) 1) (NoCancellation.fiber c 1)
        * pmSum W (Amplitude.const (V := V) 2) (NoCancellation.fiber c 2) = 0 := by
  have hcut : ∀ p q : V, c p ≠ c q → W s((p, c p), (q, c q)) = 0 := fun p q hne =>
    hmono p q (fun h => hne (by rw [h])) _ _ hne
  have hprod := NoCancellation.pmSum_product_on W c hcut (Finset.univ : Finset V)
  rw [pmSum_univ, hmin.1.2 c hnc] at hprod
  have hinter : ∀ m : Fin 3, (Finset.univ : Finset V) ∩ NoCancellation.fiber c m
      = NoCancellation.fiber c m := fun m => Finset.univ_inter _
  simp only [hinter, pmSum_fiber_const W c] at hprod
  exact hprod.symm

/-- If two fibres of a non-constant colouring are certified, the third vanishes. -/
theorem fibre_zero_of_others (W : Sym2 (V × Fin 3) → ℂ) (hmin : IsSupportMinimal W)
    (hmono : ∀ (p q : V), q ≠ p → ∀ a b : Fin 3, a ≠ b → W s((p, a), (q, b)) = 0)
    {c : V → Fin 3} (hnc : ¬ Amplitude.Monochromatic c)
    (hall : ∀ m : Fin 3, pmSum W (Amplitude.const (V := V) m) (NoCancellation.fiber c m) ≠ 0) :
    False := by
  have h := fibres_product_eq_zero W hmin hmono hnc
  rcases mul_eq_zero.mp h with h' | h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · exact hall 0 h''
    · exact hall 1 h''
  · exact hall 2 h'

/-- **The transport law.**  Take a sharp partition: a colouring `c`, a live pair `u, v` inside the
fibre of its own colour, all three fibres certified off the pair.  Take the crossing pair `x, y`
inside the crowd and any other colour `k`.  Recolouring `x, y` into `k` is again non-constant, so its
amplitude vanishes and its three fibres cannot all be certified.  The third fibre is untouched, so
one of the two that moved must vanish: either the crowd shrunk by the crossing pair carries a
vanishing extension by the *same* live pair -- a crossing state two sites smaller -- or the receiving
fibre is annihilated by the pair it absorbed. -/
theorem crossing_transport_dichotomy (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : IsSupportMinimal W)
    (hmono : ∀ (p q : V), q ≠ p → ∀ a b : Fin 3, a ≠ b → W s((p, a), (q, b)) = 0)
    {c : V → Fin 3} {u v : V} (hcv : c v = c u)
    (hfib : ∀ m : Fin 3, pmSum W (Amplitude.const (V := V) m)
      (((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c m) ≠ 0)
    {x y : V} (hx : x ∈ ((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c (c u))
    (hy : y ∈ (((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c (c u)).erase x)
    {k : Fin 3} (hk : k ≠ c u) :
    pmSum W (Amplitude.const (V := V) (c u))
        (insert u (insert v (((((Finset.univ.erase u).erase v) ∩
          NoCancellation.fiber c (c u)).erase x).erase y))) = 0
      ∨ pmSum W (Amplitude.const (V := V) k)
        (insert x (insert y (NoCancellation.fiber c k))) = 0 := by
  classical
  have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
  have hyA := Finset.mem_of_mem_erase hy
  have hxv : x ≠ v := (Finset.mem_erase.mp (Finset.mem_inter.mp hx).1).1
  have hxu : x ≠ u :=
    (Finset.mem_erase.mp (Finset.mem_of_mem_erase (Finset.mem_inter.mp hx).1)).1
  have hyv : y ≠ v := (Finset.mem_erase.mp (Finset.mem_inter.mp hyA).1).1
  have hyu : y ≠ u :=
    (Finset.mem_erase.mp (Finset.mem_of_mem_erase (Finset.mem_inter.mp hyA).1)).1
  have hcx : c x = c u := NoCancellation.mem_fiber.mp (Finset.mem_inter.mp hx).2
  have hcy : c y = c u := NoCancellation.mem_fiber.mp (Finset.mem_inter.mp hyA).2
  by_contra hcon
  push_neg at hcon
  obtain ⟨hane, hkne⟩ := hcon
  have hnc : ¬ Amplitude.Monochromatic (Function.update (Function.update c x k) y k) := by
    rintro ⟨m, hm⟩
    have h1 : Function.update (Function.update c x k) y k x = k := recolour_left (Ne.symm hyx)
    have h2 : Function.update (Function.update c x k) y k u = c u :=
      recolour_of_ne (Ne.symm hxu) (Ne.symm hyu)
    exact hk (by rw [← h1, hm x, ← hm u, h2])
  refine fibre_zero_of_others W hmin hmono hnc ?_
  intro m
  by_cases hmk : m = k
  · subst hmk
    rw [fiber_recolour_self (Ne.symm hyx)]
    exact hkne
  · rw [fiber_recolour_other hmk]
    by_cases hma : m = c u
    · subst hma
      have hset : ((NoCancellation.fiber c (c u)).erase x).erase y
          = insert u (insert v (((((Finset.univ.erase u).erase v) ∩
              NoCancellation.fiber c (c u)).erase x).erase y)) := by
        ext z
        simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_inter, NoCancellation.mem_fiber,
          Finset.mem_univ, and_true]
        constructor
        · rintro ⟨hzy, hzx, hcz⟩
          by_cases hzu : z = u
          · exact Or.inl hzu
          · by_cases hzv : z = v
            · exact Or.inr (Or.inl hzv)
            · exact Or.inr (Or.inr ⟨hzy, hzx, ⟨hzv, hzu⟩, hcz⟩)
        · rintro (rfl | rfl | ⟨hzy, hzx, -, hcz⟩)
          · exact ⟨Ne.symm hyu, Ne.symm hxu, rfl⟩
          · exact ⟨Ne.symm hyv, Ne.symm hxv, hcv⟩
          · exact ⟨hzy, hzx, hcz⟩
      rw [hset]
      exact hane
    · have hxm : x ∉ NoCancellation.fiber c m := fun h =>
        hma (by rw [← NoCancellation.mem_fiber.mp h, hcx])
      have hym : y ∉ NoCancellation.fiber c m := fun h =>
        hma (by rw [← NoCancellation.mem_fiber.mp h, hcy])
      rw [Finset.erase_eq_of_notMem hxm, Finset.erase_eq_of_notMem hym]
      have hum : u ∉ NoCancellation.fiber c m := fun h =>
        hma (NoCancellation.mem_fiber.mp h).symm
      have hvm : v ∉ NoCancellation.fiber c m := fun h =>
        hma (by rw [← NoCancellation.mem_fiber.mp h, hcv])
      have hset : ((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c m
          = NoCancellation.fiber c m := by
        ext z
        simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_univ, and_true, and_iff_right_iff_imp]
        intro hz
        exact ⟨fun h => hvm (h ▸ hz), fun h => hum (h ▸ hz)⟩
      rw [← hset]
      exact hfib m

/-- **Base behaviour at crowd size two.**  The descent branch would leave an empty crowd carrying a
vanishing extension by a live pair, which is impossible.  So at a two-site crowd the dichotomy
collapses: *both* other fibres are annihilated by the crossing pair. -/
theorem crossing_pair_annihilates_of_card_two (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : IsSupportMinimal W)
    (hmono : ∀ (p q : V), q ≠ p → ∀ a b : Fin 3, a ≠ b → W s((p, a), (q, b)) = 0)
    {c : V → Fin 3} {u v : V} (huv : u ≠ v) (hcv : c v = c u)
    (hlive : W s((u, c u), (v, c u)) ≠ 0)
    (hfib : ∀ m : Fin 3, pmSum W (Amplitude.const (V := V) m)
      (((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c m) ≠ 0)
    {x y : V} (hx : x ∈ ((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c (c u))
    (hy : y ∈ (((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c (c u)).erase x)
    (hcard : (((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c (c u)).card = 2)
    {k : Fin 3} (hk : k ≠ c u) :
    pmSum W (Amplitude.const (V := V) k) (insert x (insert y (NoCancellation.fiber c k))) = 0 := by
  have hemp : (((((Finset.univ.erase u).erase v) ∩
      NoCancellation.fiber c (c u)).erase x).erase y) = ∅ := by
    have h1 := Finset.card_erase_of_mem hx
    have h2 := Finset.card_erase_of_mem hy
    exact Finset.card_eq_zero.mp (by omega)
  rcases crossing_transport_dichotomy W hmin hmono hcv hfib hx hy hk with hdesc | hann
  · rw [hemp] at hdesc
    exact absurd hdesc (pmSum_live_pair_ne_zero W (Amplitude.const (V := V) (c u)) huv hlive)
  · exact hann

/-- **Initialization.**  An excess site supplies the enriched state, so the transport law applies
there: for each of the two other colours, either the crowd descends by two against the same live
pair, or that colour's fibre is annihilated by the crossing pair. -/
theorem excess_site_transport (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : IsSupportMinimal W)
    (hmono : ∀ (p q : V), q ≠ p → ∀ a b : Fin 3, a ≠ b → W s((p, a), (q, b)) = 0)
    (hcard : 4 < Fintype.card V)
    {u : V} (hdeg : (liveNbrs W u).card ≠ 3) :
    ∃ v ∈ liveNbrs W u, ∃ c : V → Fin 3,
      c v = c u ∧ W s((u, c u), (v, c u)) ≠ 0 ∧
      ∃ x ∈ ((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c (c u),
        ∃ y ∈ (((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c (c u)).erase x,
          W s((u, c u), (x, c u)) ≠ 0 ∧ W s((v, c u), (y, c u)) ≠ 0 ∧
          pmSum W (Amplitude.const (V := V) (c u))
            (((((Finset.univ.erase u).erase v) ∩
              NoCancellation.fiber c (c u)).erase x).erase y) ≠ 0 ∧
          ∀ k : Fin 3, k ≠ c u →
            pmSum W (Amplitude.const (V := V) (c u))
                (insert u (insert v (((((Finset.univ.erase u).erase v) ∩
                  NoCancellation.fiber c (c u)).erase x).erase y))) = 0
              ∨ pmSum W (Amplitude.const (V := V) k)
                (insert x (insert y (NoCancellation.fiber c k))) = 0 := by
  obtain ⟨v, hv, c, hcv, hentry, hfib, hown, hother, x, hx, y, hy, hux, hvy, hrem⟩ :=
    excess_site_crossing_certificate W hmin hmono hcard hdeg
  exact ⟨v, hv, c, hcv, hentry, x, hx, y, hy, hux, hvy, hrem,
    fun k hk => crossing_transport_dichotomy W hmin hmono hcv hfib hx hy hk⟩

/-! ## The transport law in uniform form

Nothing in the recolouring argument cares that two sites move.  Recolouring an arbitrary subset `S`
of the crowd into another colour gives the same dichotomy, with `S` in place of the crossing pair.
Taking `S` to be the whole crowd makes the first disjunct impossible -- it would leave the live pair
alone against an empty crowd -- and the law becomes an outright conclusion. -/

section RecolourSet

variable {c : V → Fin 3} {S : Finset V} {k : Fin 3}

theorem fiber_recolourSet_self :
    NoCancellation.fiber (fun z => if z ∈ S then k else c z) k = S ∪ NoCancellation.fiber c k := by
  ext z
  simp only [NoCancellation.mem_fiber, Finset.mem_union]
  by_cases hz : z ∈ S <;> simp [hz]

theorem fiber_recolourSet_other {m : Fin 3} (hm : m ≠ k) :
    NoCancellation.fiber (fun z => if z ∈ S then k else c z) m = NoCancellation.fiber c m \ S := by
  ext z
  simp only [NoCancellation.mem_fiber, Finset.mem_sdiff]
  by_cases hz : z ∈ S <;> simp [hz, Ne.symm hm]

end RecolourSet

/-- **The transport law, uniform in the moved set.**  Recolouring any subset `S` of the crowd into
another colour `k`: either the crowd with `S` removed still carries a vanishing extension by the live
pair, or the receiving fibre is annihilated by what it absorbed. -/
theorem crossing_transport_dichotomy_set (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : IsSupportMinimal W)
    (hmono : ∀ (p q : V), q ≠ p → ∀ a b : Fin 3, a ≠ b → W s((p, a), (q, b)) = 0)
    {c : V → Fin 3} {u v : V} (hcv : c v = c u)
    (hfib : ∀ m : Fin 3, pmSum W (Amplitude.const (V := V) m)
      (((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c m) ≠ 0)
    {S : Finset V} (hS : S ⊆ ((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c (c u))
    (hSne : S.Nonempty) {k : Fin 3} (hk : k ≠ c u) :
    pmSum W (Amplitude.const (V := V) (c u))
        (insert u (insert v ((((Finset.univ.erase u).erase v) ∩
          NoCancellation.fiber c (c u)) \ S))) = 0
      ∨ pmSum W (Amplitude.const (V := V) k) (S ∪ NoCancellation.fiber c k) = 0 := by
  classical
  have hmemS : ∀ z ∈ S, z ≠ u ∧ z ≠ v ∧ c z = c u := by
    intro z hz
    have h := hS hz
    exact ⟨(Finset.mem_erase.mp (Finset.mem_of_mem_erase (Finset.mem_inter.mp h).1)).1,
      (Finset.mem_erase.mp (Finset.mem_inter.mp h).1).1,
      NoCancellation.mem_fiber.mp (Finset.mem_inter.mp h).2⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨hane, hkne⟩ := hcon
  obtain ⟨z₀, hz₀⟩ := hSne
  have huS : u ∉ S := fun h => (hmemS u h).1 rfl
  have hnc : ¬ Amplitude.Monochromatic (fun z => if z ∈ S then k else c z) := by
    rintro ⟨m, hm⟩
    have h1 : k = m := by simpa [hz₀] using hm z₀
    have h2 : c u = m := by simpa [huS] using hm u
    exact hk (h1.trans h2.symm)
  refine fibre_zero_of_others W hmin hmono hnc ?_
  intro m
  by_cases hmk : m = k
  · subst hmk
    rw [fiber_recolourSet_self]
    exact hkne
  · rw [fiber_recolourSet_other hmk]
    by_cases hma : m = c u
    · subst hma
      have hset : NoCancellation.fiber c (c u) \ S
          = insert u (insert v ((((Finset.univ.erase u).erase v) ∩
              NoCancellation.fiber c (c u)) \ S)) := by
        ext z
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_inter, Finset.mem_erase,
          NoCancellation.mem_fiber, Finset.mem_univ, and_true]
        constructor
        · rintro ⟨hcz, hzS⟩
          by_cases hzu : z = u
          · exact Or.inl hzu
          · by_cases hzv : z = v
            · exact Or.inr (Or.inl hzv)
            · exact Or.inr (Or.inr ⟨⟨⟨hzv, hzu⟩, hcz⟩, hzS⟩)
        · rintro (rfl | rfl | ⟨⟨-, hcz⟩, hzS⟩)
          · exact ⟨rfl, fun h => (hmemS _ h).1 rfl⟩
          · exact ⟨hcv, fun h => (hmemS _ h).2.1 rfl⟩
          · exact ⟨hcz, hzS⟩
      rw [hset]
      exact hane
    · have hdisj : NoCancellation.fiber c m \ S = NoCancellation.fiber c m := by
        rw [Finset.sdiff_eq_self_iff_disjoint]
        refine Finset.disjoint_left.mpr fun z hz hzS => hma ?_
        rw [← NoCancellation.mem_fiber.mp hz, (hmemS z hzS).2.2]
      rw [hdisj]
      have hum : u ∉ NoCancellation.fiber c m := fun h =>
        hma (NoCancellation.mem_fiber.mp h).symm
      have hvm : v ∉ NoCancellation.fiber c m := fun h =>
        hma (by rw [← NoCancellation.mem_fiber.mp h, hcv])
      have hset : ((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c m
          = NoCancellation.fiber c m := by
        ext z
        simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_univ, and_true,
          and_iff_right_iff_imp]
        intro hz
        exact ⟨fun h => hvm (h ▸ hz), fun h => hum (h ▸ hz)⟩
      rw [← hset]
      exact hfib m

/-- **The crowd annihilates both other fibres.**  Move the whole crowd into either other colour: the
`a`-fibre is left as the live pair alone, whose matching sum is the live entry, so the receiving
fibre must carry the zero.  No crossing is consumed -- the enriched state alone forces this. -/
theorem crowd_annihilates_other_fibres (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : IsSupportMinimal W)
    (hmono : ∀ (p q : V), q ≠ p → ∀ a b : Fin 3, a ≠ b → W s((p, a), (q, b)) = 0)
    {c : V → Fin 3} {u v : V} (hvu : v ≠ u) (hcv : c v = c u)
    (hlive : W s((u, c u), (v, c u)) ≠ 0)
    (hfib : ∀ m : Fin 3, pmSum W (Amplitude.const (V := V) m)
      (((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c m) ≠ 0)
    (hAne : (((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c (c u)).Nonempty)
    {k : Fin 3} (hk : k ≠ c u) :
    pmSum W (Amplitude.const (V := V) k)
      ((((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c (c u)) ∪
        NoCancellation.fiber c k) = 0 := by
  rcases crossing_transport_dichotomy_set W hmin hmono hcv hfib (Finset.Subset.refl _) hAne hk with
    hdesc | hann
  · rw [Finset.sdiff_self] at hdesc
    exact absurd hdesc (pmSum_live_pair_ne_zero W (Amplitude.const (V := V) (c u))
      (Ne.symm hvu) hlive)
  · exact hann

/-- At an excess site the crowd annihilates both other fibres. -/
theorem excess_site_crowd_annihilates (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : IsSupportMinimal W)
    (hmono : ∀ (p q : V), q ≠ p → ∀ a b : Fin 3, a ≠ b → W s((p, a), (q, b)) = 0)
    (hcard : 4 < Fintype.card V)
    {u : V} (hdeg : (liveNbrs W u).card ≠ 3) :
    ∃ v ∈ liveNbrs W u, ∃ c : V → Fin 3, c v = c u ∧
      W s((u, c u), (v, c u)) ≠ 0 ∧
      ∀ k : Fin 3, k ≠ c u →
        pmSum W (Amplitude.const (V := V) k)
          ((((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c (c u)) ∪
            NoCancellation.fiber c k) = 0 := by
  obtain ⟨v, hv, c, hcv, hentry, hfib, hown, hother⟩ :=
    excess_site_normal_form W hmin hmono hcard hdeg
  obtain ⟨z, hz, hcz⟩ := hown
  refine ⟨v, hv, c, hcv, hentry, fun k hk =>
    crowd_annihilates_other_fibres W hmin hmono (mem_liveNbrs.mp hv).1 hcv hentry hfib
      ⟨z, Finset.mem_inter.mpr ⟨hz, NoCancellation.mem_fiber.mpr hcz⟩⟩ hk⟩

/-- **The live pair annihilates both other fibres.**  Move the pair itself instead of the crowd: the
`a`-fibre is left as the certified crowd, the third fibre is untouched, so the receiving fibre must
carry the zero.  Together with its own certificate this is a zero-extension state in colour `k` with
crowd `fiber c k` and the same pair -- everything the crossing lemma needs except one entry, the
liveness of the pair in the receiving colour. -/
theorem pair_annihilates_other_fibres (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : IsSupportMinimal W)
    (hmono : ∀ (p q : V), q ≠ p → ∀ a b : Fin 3, a ≠ b → W s((p, a), (q, b)) = 0)
    {c : V → Fin 3} {u v : V} (hvu : v ≠ u) (hcv : c v = c u)
    (hfib : ∀ m : Fin 3, pmSum W (Amplitude.const (V := V) m)
      (((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c m) ≠ 0)
    (hAne : (((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c (c u)).Nonempty)
    {k : Fin 3} (hk : k ≠ c u) :
    pmSum W (Amplitude.const (V := V) k)
      (({u, v} : Finset V) ∪ NoCancellation.fiber c k) = 0 := by
  classical
  obtain ⟨z₀, hz₀⟩ := hAne
  have hz₀v : z₀ ≠ v := (Finset.mem_erase.mp (Finset.mem_inter.mp hz₀).1).1
  have hz₀u : z₀ ≠ u :=
    (Finset.mem_erase.mp (Finset.mem_of_mem_erase (Finset.mem_inter.mp hz₀).1)).1
  have hcz₀ : c z₀ = c u := NoCancellation.mem_fiber.mp (Finset.mem_inter.mp hz₀).2
  by_contra hkne
  have hnc : ¬ Amplitude.Monochromatic
      (fun z => if z ∈ ({u, v} : Finset V) then k else c z) := by
    rintro ⟨m, hm⟩
    have h1 : k = m := by simpa using hm u
    have h2 : c u = m := by simpa [hz₀u, hz₀v, hcz₀] using hm z₀
    exact hk (h1.trans h2.symm)
  refine fibre_zero_of_others W hmin hmono hnc ?_
  intro m
  by_cases hmk : m = k
  · subst hmk; rw [fiber_recolourSet_self]; exact hkne
  · rw [fiber_recolourSet_other hmk]
    by_cases hma : m = c u
    · subst hma
      have hset : NoCancellation.fiber c (c u) \ ({u, v} : Finset V)
          = ((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c (c u) := by
        ext z
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, Finset.mem_inter,
          Finset.mem_erase, NoCancellation.mem_fiber, Finset.mem_univ, and_true]
        constructor
        · rintro ⟨hcz, hzS⟩
          exact ⟨⟨fun h => hzS (Or.inr h), fun h => hzS (Or.inl h)⟩, hcz⟩
        · rintro ⟨⟨hzv, hzu⟩, hcz⟩
          exact ⟨hcz, fun h => h.elim hzu hzv⟩
      rw [hset]; exact hfib (c u)
    · have hum : u ∉ NoCancellation.fiber c m := fun h =>
        hma (NoCancellation.mem_fiber.mp h).symm
      have hvm : v ∉ NoCancellation.fiber c m := fun h =>
        hma (by rw [← NoCancellation.mem_fiber.mp h, hcv])
      have hset : NoCancellation.fiber c m \ ({u, v} : Finset V)
          = ((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c m := by
        ext z
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, Finset.mem_inter,
          Finset.mem_erase, NoCancellation.mem_fiber, Finset.mem_univ, and_true]
        constructor
        · rintro ⟨hcz, hzS⟩
          exact ⟨⟨fun h => hzS (Or.inr h), fun h => hzS (Or.inl h)⟩, hcz⟩
        · rintro ⟨⟨hzv, hzu⟩, hcz⟩
          exact ⟨hcz, fun h => h.elim hzu hzv⟩
      rw [hset]; exact hfib m

/-- **What is missing, exactly.**  In the receiving colour the state is complete except for one
entry: the crowd `fiber c k` is certified, the pair extends it to zero, so the crossing fires there
as soon as the pair is live in colour `k`. -/
theorem transported_crossing_of_live (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : IsSupportMinimal W)
    (hmono : ∀ (p q : V), q ≠ p → ∀ a b : Fin 3, a ≠ b → W s((p, a), (q, b)) = 0)
    {c : V → Fin 3} {u v : V} (hvu : v ≠ u) (hcv : c v = c u)
    (hfib : ∀ m : Fin 3, pmSum W (Amplitude.const (V := V) m)
      (((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c m) ≠ 0)
    (hAne : (((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c (c u)).Nonempty)
    {k : Fin 3} (hk : k ≠ c u) (hlive : W s((u, k), (v, k)) ≠ 0) :
    ∃ x ∈ NoCancellation.fiber c k, ∃ y ∈ (NoCancellation.fiber c k).erase x,
      W s((u, k), (x, k)) ≠ 0 ∧ W s((v, k), (y, k)) ≠ 0 ∧
        pmSum W (Amplitude.const (V := V) k)
          (((NoCancellation.fiber c k).erase x).erase y) ≠ 0 := by
  classical
  have hum : u ∉ NoCancellation.fiber c k := fun h =>
    hk (NoCancellation.mem_fiber.mp h).symm
  have hvm : v ∉ NoCancellation.fiber c k := fun h =>
    hk (by rw [← NoCancellation.mem_fiber.mp h, hcv])
  have hcrowd : pmSum W (Amplitude.const (V := V) k) (NoCancellation.fiber c k) ≠ 0 := by
    have hset : ((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c k
        = NoCancellation.fiber c k := by
      ext z
      simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_univ, and_true,
        and_iff_right_iff_imp]
      intro hz
      exact ⟨fun h => hvm (h ▸ hz), fun h => hum (h ▸ hz)⟩
    rw [← hset]; exact hfib k
  have hzero : pmSum W (Amplitude.const (V := V) k)
      (insert u (insert v (NoCancellation.fiber c k))) = 0 := by
    have hset : insert u (insert v (NoCancellation.fiber c k))
        = ({u, v} : Finset V) ∪ NoCancellation.fiber c k := by
      ext z; simp [Finset.mem_insert, Finset.mem_union, or_assoc]
    rw [hset]
    exact pair_annihilates_other_fibres W hmin hmono hvu hcv hfib hAne hk
  exact exists_crossing W (Amplitude.const (V := V) k) hum hvm (Ne.symm hvu) hlive hcrowd hzero

/-! ## The receiving-colour fork

Transport hands the pair to another colour, and there the crossing needs one entry: the pair being
live in the colour it moved into.  That entry is not forced -- but its failure is not free either.
A dead pair still has to be covered by the non-vanishing monochromatic amplitude of that colour, and
covering it takes two edges to two other sites, leaving a certified complement.  So both sides of the
fork produce structure, and the dead side produces more: its two detour sites cannot be joined in the
third colour, or the split criterion closes the configuration outright. -/

/-- **The dead-pair detour.**  A pair dead in colour `k` is still covered by that colour's
non-vanishing amplitude, through two distinct other sites, with a certified remainder.  Two certified
deletions; no GHZ system, no monochromatic blocks, no cardinality hypothesis. -/
theorem exists_dead_pair_detour (W : Sym2 (V × Fin 3) → ℂ) {k : Fin 3}
    (hone : amplitude W (Amplitude.const (V := V) k) ≠ 0)
    {u v : V} (huv : u ≠ v) (hdead : W s((u, k), (v, k)) = 0) :
    ∃ p q : V, p ≠ u ∧ p ≠ v ∧ q ≠ u ∧ q ≠ v ∧ p ≠ q ∧
      W s((u, k), (p, k)) ≠ 0 ∧ W s((v, k), (q, k)) ≠ 0 ∧
      pmSum W (Amplitude.const (V := V) k)
        ((Finset.univ : Finset V) \ ({u, p, v, q} : Finset V)) ≠ 0 := by
  classical
  have hU : pmSum W (Amplitude.const (V := V) k) (Finset.univ : Finset V) ≠ 0 := by
    rw [pmSum_univ]; exact hone
  obtain ⟨p, hp, hup, hrest⟩ :=
    MatchingSum.exists_partner_ne_zero W (Amplitude.const (V := V) k) (Finset.mem_univ u) hU
  have hpu : p ≠ u := Finset.ne_of_mem_erase hp
  have hpv : p ≠ v := by
    intro h; exact hup (by rw [h]; exact hdead)
  have hvmem : v ∈ ((Finset.univ : Finset V).erase u).erase p :=
    Finset.mem_erase.mpr ⟨Ne.symm hpv, Finset.mem_erase.mpr ⟨Ne.symm huv, Finset.mem_univ v⟩⟩
  obtain ⟨q, hq, hvq, hrest'⟩ :=
    MatchingSum.exists_partner_ne_zero W (Amplitude.const (V := V) k) hvmem hrest
  have hqv : q ≠ v := Finset.ne_of_mem_erase hq
  have hqp : q ≠ p := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hq)
  have hqu : q ≠ u :=
    Finset.ne_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hq))
  refine ⟨p, q, hpu, hpv, hqu, hqv, Ne.symm hqp, hup, hvq, ?_⟩
  have hset : (Finset.univ : Finset V) \ ({u, p, v, q} : Finset V)
      = ((((Finset.univ : Finset V).erase u).erase p).erase v).erase q := by
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Finset.mem_erase, not_or]
    tauto
  rw [hset]
  exact hrest'

/-- The colour that is neither of two given ones. -/
def thirdColour (a k : Fin 3) : Fin 3 := -a - k

theorem thirdColour_ne_left {a k : Fin 3} (h : a ≠ k) : thirdColour a k ≠ a := by
  revert h; revert a k; decide

theorem thirdColour_ne_right {a k : Fin 3} (h : a ≠ k) : thirdColour a k ≠ k := by
  revert h; revert a k; decide

/-- **The forbidden chord.**  If the two detour sites were joined in the third colour, the
configuration would be a live pair of one colour, a live pair of another, and a certified remainder
in the third -- which the split criterion refutes.  So the chord is dead. -/
theorem exists_dead_pair_detour_chord (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ cc : V → Fin 3, ¬ Amplitude.Monochromatic cc → amplitude W cc = 0)
    (hmono : ∀ (p q : V), q ≠ p → ∀ i j : Fin 3, i ≠ j → W s((p, i), (q, j)) = 0)
    (hcard : 4 < Fintype.card V)
    {a k : Fin 3} (hak : a ≠ k)
    (hone : amplitude W (Amplitude.const (V := V) k) ≠ 0)
    {u v : V} (huv : u ≠ v)
    (hlive : W s((u, a), (v, a)) ≠ 0) (hdead : W s((u, k), (v, k)) = 0) :
    ∃ p q : V, p ≠ u ∧ p ≠ v ∧ q ≠ u ∧ q ≠ v ∧ p ≠ q ∧
      W s((u, k), (p, k)) ≠ 0 ∧ W s((v, k), (q, k)) ≠ 0 ∧
      pmSum W (Amplitude.const (V := V) k)
        ((Finset.univ : Finset V) \ ({u, p, v, q} : Finset V)) ≠ 0 ∧
      W s((p, thirdColour a k), (q, thirdColour a k)) = 0 := by
  classical
  obtain ⟨p, q, hpu, hpv, hqu, hqv, hpq, hup, hvq, hcert⟩ :=
    exists_dead_pair_detour W hone huv hdead
  refine ⟨p, q, hpu, hpv, hqu, hqv, hpq, hup, hvq, hcert, ?_⟩
  by_contra hchord
  have hdisj : Disjoint ({u, v} : Finset V) ({p, q} : Finset V) := by
    simp only [Finset.disjoint_insert_left, Finset.disjoint_singleton_left,
      Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨⟨Ne.symm hpu, Ne.symm hqu⟩, ⟨Ne.symm hpv, Ne.symm hqv⟩⟩
  have hset : ((((Finset.univ : Finset V).erase u).erase p).erase v).erase q
      = (Finset.univ : Finset V) \ ({u, p, v, q} : Finset V) := by
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Finset.mem_erase, not_or]
    tauto
  have hcompl : ((Finset.univ : Finset V) \ (({u, v} : Finset V) ∪ ({p, q} : Finset V))).Nonempty := by
    refine Finset.card_pos.mp ?_
    have hle : (({u, v} : Finset V) ∪ ({p, q} : Finset V)).card ≤ 4 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      have h1 : ({u, v} : Finset V).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
      have h2 : ({p, q} : Finset V).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
      omega
    have hcd : ((Finset.univ : Finset V) \ (({u, v} : Finset V) ∪ ({p, q} : Finset V))).card
        = (Finset.univ : Finset V).card
          - ((({u, v} : Finset V) ∪ ({p, q} : Finset V)) ∩ (Finset.univ : Finset V)).card :=
      Finset.card_sdiff
    rw [hcd, Finset.inter_univ, Finset.card_univ]
    omega
  exact NoCancellation.false_of_certified_quad_split W hzero hmono
    (Ne.symm hak) (Ne.symm (thirdColour_ne_right hak))
    (Ne.symm (thirdColour_ne_left hak))
    (Ne.symm huv) (Ne.symm hpq) hdisj (by rw [hset]; exact hcert) hlive hchord hcompl

/-- The transported crossing in a receiving colour: the pair is live there and the crossing lemma
fires through that colour's fibre. -/
def TransportedCrossing (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3) (u v : V) (k : Fin 3) : Prop :=
  W s((u, k), (v, k)) ≠ 0 ∧
    ∃ x ∈ NoCancellation.fiber c k, ∃ y ∈ (NoCancellation.fiber c k).erase x,
      W s((u, k), (x, k)) ≠ 0 ∧ W s((v, k), (y, k)) ≠ 0 ∧
        pmSum W (Amplitude.const (V := V) k)
          (((NoCancellation.fiber c k).erase x).erase y) ≠ 0

/-- The certified detour in a receiving colour: the pair is dead there, so that colour's amplitude
routes its two sites through two others, with a certified remainder and a dead third-colour chord. -/
def CertifiedDetour (W : Sym2 (V × Fin 3) → ℂ) (u v : V) (a k : Fin 3) : Prop :=
  W s((u, k), (v, k)) = 0 ∧
    ∃ p q : V, p ≠ u ∧ p ≠ v ∧ q ≠ u ∧ q ≠ v ∧ p ≠ q ∧
      W s((u, k), (p, k)) ≠ 0 ∧ W s((v, k), (q, k)) ≠ 0 ∧
      pmSum W (Amplitude.const (V := V) k)
        ((Finset.univ : Finset V) \ ({u, p, v, q} : Finset V)) ≠ 0 ∧
      W s((p, thirdColour a k), (q, thirdColour a k)) = 0

/-- **The receiving-colour dichotomy.**  Take the sharp partition.  In each of the two other colours
the pair is either live -- and the transported crossing fires through that colour's fibre -- or dead,
and then that colour's amplitude must route the pair through two other sites, whose joining edge is
dead in the remaining colour.  Neither alternative is excluded here. -/
theorem receiving_colour_dichotomy (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : IsSupportMinimal W)
    (hmono : ∀ (p q : V), q ≠ p → ∀ i j : Fin 3, i ≠ j → W s((p, i), (q, j)) = 0)
    (hcard : 4 < Fintype.card V)
    {c : V → Fin 3} {u v : V} (hvu : v ≠ u) (hcv : c v = c u)
    (hlive : W s((u, c u), (v, c u)) ≠ 0)
    (hfib : ∀ m : Fin 3, pmSum W (Amplitude.const (V := V) m)
      (((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c m) ≠ 0)
    (hAne : (((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c (c u)).Nonempty)
    {k : Fin 3} (hk : k ≠ c u) :
    TransportedCrossing W c u v k ∨ CertifiedDetour W u v (c u) k := by
  classical
  by_cases hpair : W s((u, k), (v, k)) = 0
  · refine Or.inr ⟨hpair, ?_⟩
    obtain ⟨p, q, hpu, hpv, hqu, hqv, hpq, hup, hvq, hcert, hchord⟩ :=
      exists_dead_pair_detour_chord W hmin.1.2 hmono hcard (Ne.symm hk) (hmin.1.1 k)
        (Ne.symm hvu) hlive hpair
    exact ⟨p, q, hpu, hpv, hqu, hqv, hpq, hup, hvq, hcert, hchord⟩
  · exact Or.inl ⟨hpair, transported_crossing_of_live W hmin hmono hvu hcv hfib hAne hk hpair⟩

/-- **The excess-site corollary.**  Everything the excess normal form gives, together with the
receiving-colour alternative in each of the two other colours. -/
theorem excess_site_receiving_dichotomy (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : IsSupportMinimal W)
    (hmono : ∀ (p q : V), q ≠ p → ∀ i j : Fin 3, i ≠ j → W s((p, i), (q, j)) = 0)
    (hcard : 4 < Fintype.card V)
    {u : V} (hdeg : (liveNbrs W u).card ≠ 3) :
    ∃ v ∈ liveNbrs W u, ∃ c : V → Fin 3,
      c v = c u ∧
      W s((u, c u), (v, c u)) ≠ 0 ∧
      (∀ k : Fin 3, pmSum W (Amplitude.const (V := V) k)
        (((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c k) ≠ 0) ∧
      (∃ z ∈ (Finset.univ.erase u).erase v, c z = c u) ∧
      (∃ z ∈ (Finset.univ.erase u).erase v, c z ≠ c u) ∧
      (∃ x ∈ ((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c (c u),
        ∃ y ∈ (((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c (c u)).erase x,
          W s((u, c u), (x, c u)) ≠ 0 ∧ W s((v, c u), (y, c u)) ≠ 0 ∧
            pmSum W (Amplitude.const (V := V) (c u))
              (((((Finset.univ.erase u).erase v) ∩
                NoCancellation.fiber c (c u)).erase x).erase y) ≠ 0) ∧
      ∀ k : Fin 3, k ≠ c u →
        TransportedCrossing W c u v k ∨ CertifiedDetour W u v (c u) k := by
  obtain ⟨v, hv, c, hcv, hentry, hfib, hown, hother, x, hx, y, hy, hux, hvy, hrem⟩ :=
    excess_site_crossing_certificate W hmin hmono hcard hdeg
  obtain ⟨z, hz, hcz⟩ := hown
  refine ⟨v, hv, c, hcv, hentry, hfib, ⟨z, hz, hcz⟩, hother,
    ⟨x, hx, y, hy, hux, hvy, hrem⟩, fun k hk =>
      receiving_colour_dichotomy W hmin hmono hcard (mem_liveNbrs.mp hv).1 hcv hentry hfib
        ⟨z, Finset.mem_inter.mpr ⟨hz, NoCancellation.mem_fiber.mpr hcz⟩⟩ hk⟩

/-! ## Compatibility of two receiving-colour detours

A dead detour contains more than its two route edges.  Its certified complement forces the
four-site matching sum to vanish in the third colour, while its forbidden chord deletes one of the
three pairings.  The two possible routings in the third colour therefore satisfy an exact
two-product relation.

This relation settles the first overlap case for the two receiving colours.  If the second detour
reuses both ports of the first, in either orientation, one routing product is non-zero.  The relation
forces the other product non-zero as well.  In particular the first detour's two route arms are live
in both receiving colours, and each is a size-one star circuit.  Thus the unresolved double-detour
network may be reduced to the port-separated case or to the already isolated size-one circuit case.
It is not eliminated here. -/

/-- **The cross relation carried by a certified detour.** -/
theorem certified_detour_cross_relation (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : IsSupportMinimal W)
    (hmono : ∀ (x y : V), y ≠ x → ∀ i j : Fin 3, i ≠ j → W s((x, i), (y, j)) = 0)
    (hcard : 4 < Fintype.card V)
    {a k : Fin 3} (hak : a ≠ k)
    {u v p q : V} (huv : u ≠ v) (hpu : p ≠ u) (hpv : p ≠ v)
    (hqu : q ≠ u) (hqv : q ≠ v) (hpq : p ≠ q)
    (hcert : pmSum W (Amplitude.const (V := V) k)
      ((Finset.univ : Finset V) \ ({u, p, v, q} : Finset V)) ≠ 0)
    (hchord : W s((p, thirdColour a k), (q, thirdColour a k)) = 0) :
    W s((p, thirdColour a k), (u, thirdColour a k))
        * W s((q, thirdColour a k), (v, thirdColour a k))
      + W s((p, thirdColour a k), (v, thirdColour a k))
        * W s((q, thirdColour a k), (u, thirdColour a k)) = 0 := by
  classical
  have hset : ({p, q, u, v} : Finset V) = ({u, p, v, q} : Finset V) := by
    ext z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  apply NoCancellation.certified_quad_cross_relation W hmin.1.2 hmono hcard
    (thirdColour_ne_right hak) hpq hpu hpv hqu hqv huv
  · rw [hset]
    exact hcert
  · exact hchord

/-- **Reusing both detour ports forces size-one circuits at both ends.**

The second receiving colour may traverse the first detour's two ports in parallel or crossed
orientation.  Either routing product is enough: the detour cross relation forces the other product,
so the original two route arms are bi-diagonal. -/
theorem detour_port_reuse_forces_size_one_circuits (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : IsSupportMinimal W)
    (hmono : ∀ (x y : V), y ≠ x → ∀ i j : Fin 3, i ≠ j → W s((x, i), (y, j)) = 0)
    (hcard : 4 < Fintype.card V)
    {a k : Fin 3} (hak : a ≠ k)
    {u v p q : V} (huv : u ≠ v) (hpu : p ≠ u) (hpv : p ≠ v)
    (hqu : q ≠ u) (hqv : q ≠ v) (hpq : p ≠ q)
    (hkup : W s((u, k), (p, k)) ≠ 0) (hkvq : W s((v, k), (q, k)) ≠ 0)
    (hcert : pmSum W (Amplitude.const (V := V) k)
      ((Finset.univ : Finset V) \ ({u, p, v, q} : Finset V)) ≠ 0)
    (hchord : W s((p, thirdColour a k), (q, thirdColour a k)) = 0)
    (hreuse :
      (W s((p, thirdColour a k), (u, thirdColour a k)) ≠ 0 ∧
        W s((q, thirdColour a k), (v, thirdColour a k)) ≠ 0) ∨
      (W s((p, thirdColour a k), (v, thirdColour a k)) ≠ 0 ∧
        W s((q, thirdColour a k), (u, thirdColour a k)) ≠ 0)) :
    (∃ ω : StarCircuitWitness W u, ω.supp = ({p} : Finset V)) ∧
      ∃ ω : StarCircuitWitness W v, ω.supp = ({q} : Finset V) := by
  have hrel := certified_detour_cross_relation W hmin hmono hcard hak huv hpu hpv hqu hqv hpq
    hcert hchord
  have hparallel :
      W s((p, thirdColour a k), (u, thirdColour a k)) ≠ 0 ∧
        W s((q, thirdColour a k), (v, thirdColour a k)) ≠ 0 := by
    rcases hreuse with h | h
    · exact h
    · have hcross : W s((p, thirdColour a k), (v, thirdColour a k))
          * W s((q, thirdColour a k), (u, thirdColour a k)) ≠ 0 :=
        mul_ne_zero h.1 h.2
      have hprod : W s((p, thirdColour a k), (u, thirdColour a k))
          * W s((q, thirdColour a k), (v, thirdColour a k)) ≠ 0 := by
        intro hz
        rw [hz, zero_add] at hrel
        exact hcross hrel
      exact ⟨fun hp => hprod (by rw [hp, zero_mul]),
        fun hq => hprod (by rw [hq, mul_zero])⟩
  have hlup : W s((u, thirdColour a k), (p, thirdColour a k)) ≠ 0 := by
    rw [Sym2.eq_swap]
    exact hparallel.1
  have hlvq : W s((v, thirdColour a k), (q, thirdColour a k)) ≠ 0 := by
    rw [Sym2.eq_swap]
    exact hparallel.2
  exact ⟨bidiagonal_size_one_circuit W hmin hmono hcard hpu
      (Ne.symm (thirdColour_ne_right hak)) hkup hlup,
    bidiagonal_size_one_circuit W hmin hmono hcard hqv
      (Ne.symm (thirdColour_ne_right hak)) hkvq hlvq⟩

/-! ## Two receiving-colour detours at one site

Both receiving colours can fail the live-entry test at once, and then the site carries two
certified detours: one through colour `k` with ports `p, q`, one through the third colour with
ports `r, s`.  Full reuse of both ports is already known to force size-one circuits.  What is
settled here is the single-port case, `card ({p,q} ∩ {r,s}) = 1`.

Reuse on the same side of the pair puts one route arm in two colours at once, which is a size-one
circuit.  Crossed reuse does not: it is answered by a rigid cap in which every remaining
cross-colour entry at the shared port vanishes. -/

theorem thirdColour_thirdColour (a k : Fin 3) : thirdColour a (thirdColour a k) = k := by
  revert a k; decide

/-- The ports of a certified detour, exposed as data. -/
structure DetourPorts (W : Sym2 (V × Fin 3) → ℂ) (u v : V) (a k : Fin 3) where
  /-- the port carrying `u` -/
  fst : V
  /-- the port carrying `v` -/
  snd : V
  fst_ne_u : fst ≠ u
  fst_ne_v : fst ≠ v
  snd_ne_u : snd ≠ u
  snd_ne_v : snd ≠ v
  fst_ne_snd : fst ≠ snd
  live_fst : W s((u, k), (fst, k)) ≠ 0
  live_snd : W s((v, k), (snd, k)) ≠ 0
  cert : pmSum W (Amplitude.const (V := V) k)
    ((Finset.univ : Finset V) \ ({u, fst, v, snd} : Finset V)) ≠ 0
  chord : W s((fst, thirdColour a k), (snd, thirdColour a k)) = 0
  dead_pair : W s((u, k), (v, k)) = 0

theorem exists_detourPorts {W : Sym2 (V × Fin 3) → ℂ} {u v : V} {a k : Fin 3}
    (h : CertifiedDetour W u v a k) : Nonempty (DetourPorts W u v a k) := by
  obtain ⟨hdead, p, q, hpu, hpv, hqu, hqv, hpq, hup, hvq, hcert, hchord⟩ := h
  exact ⟨⟨p, q, hpu, hpv, hqu, hqv, hpq, hup, hvq, hcert, hchord, hdead⟩⟩

/-- **Same-side reuse is a size-one circuit.**  If the two detours share the port carrying `u`,
that arm is live in both receiving colours; likewise for the port carrying `v`. -/
theorem same_side_reuse_size_one_circuit (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : IsSupportMinimal W)
    (hmono : ∀ (x y : V), y ≠ x → ∀ i j : Fin 3, i ≠ j → W s((x, i), (y, j)) = 0)
    (hcard : 4 < Fintype.card V)
    {a k : Fin 3} (hak : a ≠ k) {u v : V}
    (D : DetourPorts W u v a k) (E : DetourPorts W u v a (thirdColour a k)) :
    (D.fst = E.fst → ∃ ω : StarCircuitWitness W u, ω.supp = ({D.fst} : Finset V)) ∧
      (D.snd = E.snd → ∃ ω : StarCircuitWitness W v, ω.supp = ({D.snd} : Finset V)) := by
  have hkl : k ≠ thirdColour a k := Ne.symm (thirdColour_ne_right hak)
  constructor
  · intro hfst
    refine bidiagonal_size_one_circuit W hmin hmono hcard D.fst_ne_u hkl D.live_fst ?_
    rw [hfst]; exact E.live_fst
  · intro hsnd
    refine bidiagonal_size_one_circuit W hmin hmono hcard D.snd_ne_v hkl D.live_snd ?_
    rw [hsnd]; exact E.live_snd

/-- A size-one circuit at one of the two sites of the pair. -/
def SomeSizeOneCircuit (W : Sym2 (V × Fin 3) → ℂ) (u v : V) : Prop :=
  (∃ w : V, ∃ ω : StarCircuitWitness W u, ω.supp = ({w} : Finset V)) ∨
    ∃ w : V, ∃ ω : StarCircuitWitness W v, ω.supp = ({w} : Finset V)

/-- **The crossed one-port cap.**  `p` is shared: it is the `u`-port of the `k`-detour and the
`v`-port of the third-colour detour.  `q` is the other `k`-port, `r` the other third-colour port.
Every field is derived, never assumed. -/
structure CrossedOnePortCap (W : Sym2 (V × Fin 3) → ℂ) (u v : V) (a k : Fin 3) (p q r : V) :
    Prop where
  /-- the shared port and the two free ports avoid the pair -/
  p_ne_u : p ≠ u
  p_ne_v : p ≠ v
  q_ne_u : q ≠ u
  q_ne_v : q ≠ v
  r_ne_u : r ≠ u
  r_ne_v : r ≠ v
  p_ne_q : p ≠ q
  r_ne_p : r ≠ p
  /-- the four route arms that are live -/
  live_k_up : W s((u, k), (p, k)) ≠ 0
  live_k_vq : W s((v, k), (q, k)) ≠ 0
  live_l_ur : W s((u, thirdColour a k), (r, thirdColour a k)) ≠ 0
  live_l_vp : W s((v, thirdColour a k), (p, thirdColour a k)) ≠ 0
  /-- both forbidden chords -/
  chord_l_pq : W s((p, thirdColour a k), (q, thirdColour a k)) = 0
  chord_k_rp : W s((r, k), (p, k)) = 0
  /-- both certified complements -/
  cert_k : pmSum W (Amplitude.const (V := V) k)
    ((Finset.univ : Finset V) \ ({u, p, v, q} : Finset V)) ≠ 0
  cert_l : pmSum W (Amplitude.const (V := V) (thirdColour a k))
    ((Finset.univ : Finset V) \ ({u, r, v, p} : Finset V)) ≠ 0
  /-- the cap: every remaining cross-colour entry at the ports vanishes -/
  dead_l_up : W s((u, thirdColour a k), (p, thirdColour a k)) = 0
  dead_l_vq : W s((v, thirdColour a k), (q, thirdColour a k)) = 0
  dead_l_uq : W s((u, thirdColour a k), (q, thirdColour a k)) = 0
  dead_k_ur : W s((u, k), (r, k)) = 0
  dead_k_vp : W s((v, k), (p, k)) = 0
  dead_k_vr : W s((v, k), (r, k)) = 0

/-- **Crossed one-port reuse: a circuit, or the cap.**  The shared port is the `u`-port of the
`k`-detour and the `v`-port of the third-colour detour.  Either some route arm is live in two
colours -- a size-one circuit -- or every remaining cross entry at the ports is dead. -/
theorem crossed_one_port_dichotomy (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : IsSupportMinimal W)
    (hmono : ∀ (x y : V), y ≠ x → ∀ i j : Fin 3, i ≠ j → W s((x, i), (y, j)) = 0)
    (hcard : 4 < Fintype.card V)
    {a k : Fin 3} (hak : a ≠ k) {u v : V} (huv : u ≠ v)
    (D : DetourPorts W u v a k) (E : DetourPorts W u v a (thirdColour a k))
    (hshare : D.fst = E.snd) :
    SomeSizeOneCircuit W u v ∨ CrossedOnePortCap W u v a k D.fst D.snd E.fst := by
  classical
  have hal : a ≠ thirdColour a k := Ne.symm (thirdColour_ne_left hak)
  have hkl : k ≠ thirdColour a k := Ne.symm (thirdColour_ne_right hak)
  have hlvp : W s((v, thirdColour a k), (D.fst, thirdColour a k)) ≠ 0 := by
    rw [hshare]; exact E.live_snd
  have hchord2 : W s((E.fst, k), (E.snd, k)) = 0 := by
    have h := E.chord; rw [thirdColour_thirdColour] at h; exact h
  have hrel1 := certified_detour_cross_relation W hmin hmono hcard hak huv
    D.fst_ne_u D.fst_ne_v D.snd_ne_u D.snd_ne_v D.fst_ne_snd D.cert D.chord
  have hrel2 := certified_detour_cross_relation W hmin hmono hcard hal huv
    E.fst_ne_u E.fst_ne_v E.snd_ne_u E.snd_ne_v E.fst_ne_snd E.cert E.chord
  rw [thirdColour_thirdColour] at hrel2
  by_cases h1 : W s((u, thirdColour a k), (D.fst, thirdColour a k)) ≠ 0
  · exact Or.inl (Or.inl ⟨D.fst,
      bidiagonal_size_one_circuit W hmin hmono hcard D.fst_ne_u hkl D.live_fst h1⟩)
  by_cases h2 : W s((v, k), (D.fst, k)) ≠ 0
  · exact Or.inl (Or.inr ⟨D.fst, bidiagonal_size_one_circuit W hmin hmono hcard
      D.fst_ne_v (Ne.symm hkl) hlvp h2⟩)
  by_cases h3 : W s((v, thirdColour a k), (D.snd, thirdColour a k)) ≠ 0
  · exact Or.inl (Or.inr ⟨D.snd,
      bidiagonal_size_one_circuit W hmin hmono hcard D.snd_ne_v hkl D.live_snd h3⟩)
  by_cases h4 : W s((u, k), (E.fst, k)) ≠ 0
  · exact Or.inl (Or.inl ⟨E.fst, bidiagonal_size_one_circuit W hmin hmono hcard
      E.fst_ne_u (Ne.symm hkl) E.live_fst h4⟩)
  push_neg at h1 h2 h3 h4
  have hdead_l_uq : W s((u, thirdColour a k), (D.snd, thirdColour a k)) = 0 := by
    have hz : W s((D.fst, thirdColour a k), (u, thirdColour a k)) = 0 := by
      rw [Sym2.eq_swap]; exact h1
    rw [hz, zero_mul, zero_add] at hrel1
    have hne : W s((D.fst, thirdColour a k), (v, thirdColour a k)) ≠ 0 := by
      rw [Sym2.eq_swap]; exact hlvp
    have hq := (mul_eq_zero.mp hrel1).resolve_left hne
    rw [Sym2.eq_swap]; exact hq
  have hdead_k_vr : W s((v, k), (E.fst, k)) = 0 := by
    have hz : W s((E.fst, k), (u, k)) = 0 := by rw [Sym2.eq_swap]; exact h4
    rw [hz, zero_mul, zero_add] at hrel2
    have hne : W s((E.snd, k), (u, k)) ≠ 0 := by
      rw [Sym2.eq_swap, ← hshare]; exact D.live_fst
    have hr := (mul_eq_zero.mp hrel2).resolve_right hne
    rw [Sym2.eq_swap]; exact hr
  refine Or.inr ⟨D.fst_ne_u, D.fst_ne_v, D.snd_ne_u, D.snd_ne_v, E.fst_ne_u, E.fst_ne_v,
    D.fst_ne_snd, ?_, D.live_fst, D.live_snd, E.live_fst, hlvp, D.chord, ?_,
    D.cert, ?_, h1, h3, hdead_l_uq, h4, h2, hdead_k_vr⟩
  · rw [hshare]; exact E.fst_ne_snd
  · rw [hshare]; exact hchord2
  · rw [hshare]; exact E.cert

/-- Reading the same detour from the other end of the pair. -/
def DetourPorts.swap {W : Sym2 (V × Fin 3) → ℂ} {u v : V} {a k : Fin 3}
    (D : DetourPorts W u v a k) : DetourPorts W v u a k where
  fst := D.snd
  snd := D.fst
  fst_ne_u := D.snd_ne_v
  fst_ne_v := D.snd_ne_u
  snd_ne_u := D.fst_ne_v
  snd_ne_v := D.fst_ne_u
  fst_ne_snd := Ne.symm D.fst_ne_snd
  live_fst := D.live_snd
  live_snd := D.live_fst
  cert := by
    have hset : ({v, D.snd, u, D.fst} : Finset V) = ({u, D.fst, v, D.snd} : Finset V) := by
      ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [hset]; exact D.cert
  chord := by rw [Sym2.eq_swap]; exact D.chord
  dead_pair := by rw [Sym2.eq_swap]; exact D.dead_pair

/-- **The overlap normal form for two receiving-colour detours.**  Either some route arm is live in
two colours, or the two detours use disjoint ports, or they share exactly the crossed port and the
rigid cap holds in one of its two orientations. -/
theorem double_certified_detour_overlap_normal_form (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : IsSupportMinimal W)
    (hmono : ∀ (x y : V), y ≠ x → ∀ i j : Fin 3, i ≠ j → W s((x, i), (y, j)) = 0)
    (hcard : 4 < Fintype.card V)
    {a k : Fin 3} (hak : a ≠ k) {u v : V} (huv : u ≠ v)
    (D : DetourPorts W u v a k) (E : DetourPorts W u v a (thirdColour a k)) :
    SomeSizeOneCircuit W u v
      ∨ Disjoint ({D.fst, D.snd} : Finset V) ({E.fst, E.snd} : Finset V)
      ∨ CrossedOnePortCap W u v a k D.fst D.snd E.fst
      ∨ CrossedOnePortCap W v u a k D.snd D.fst E.snd := by
  classical
  by_cases hff : D.fst = E.fst
  · exact Or.inl (Or.inl ⟨D.fst, (same_side_reuse_size_one_circuit W hmin hmono hcard hak D E).1 hff⟩)
  by_cases hss : D.snd = E.snd
  · exact Or.inl (Or.inr ⟨D.snd, (same_side_reuse_size_one_circuit W hmin hmono hcard hak D E).2 hss⟩)
  by_cases hfs : D.fst = E.snd
  · rcases crossed_one_port_dichotomy W hmin hmono hcard hak huv D E hfs with hc | hcap
    · exact Or.inl hc
    · exact Or.inr (Or.inr (Or.inl hcap))
  by_cases hsf : D.snd = E.fst
  · have hshare : D.swap.fst = E.swap.snd := hsf
    rcases crossed_one_port_dichotomy W hmin hmono hcard hak (Ne.symm huv) D.swap E.swap hshare
      with hc | hcap
    · exact Or.inl (Or.symm hc)
    · exact Or.inr (Or.inr (Or.inr hcap))
  · refine Or.inr (Or.inl ?_)
    simp only [Finset.disjoint_insert_left, Finset.disjoint_singleton_left,
      Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨⟨hff, hfs⟩, ⟨hsf, hss⟩⟩

/-- **The receiving pair, classified.**  At a site with a certified sharp partition, in each of the
two receiving colours the pair is either live -- giving a transported crossing -- or dead, giving a
certified detour.  When both are dead the two detours meet the overlap normal form. -/
theorem receiving_pair_normal_form (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : IsSupportMinimal W)
    (hmono : ∀ (p q : V), q ≠ p → ∀ i j : Fin 3, i ≠ j → W s((p, i), (q, j)) = 0)
    (hcard : 4 < Fintype.card V)
    {c : V → Fin 3} {u v : V} (hvu : v ≠ u) (hcv : c v = c u)
    (hlive : W s((u, c u), (v, c u)) ≠ 0)
    (hfib : ∀ m : Fin 3, pmSum W (Amplitude.const (V := V) m)
      (((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c m) ≠ 0)
    (hAne : (((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c (c u)).Nonempty)
    {k : Fin 3} (hk : k ≠ c u) :
    TransportedCrossing W c u v k
      ∨ TransportedCrossing W c u v (thirdColour (c u) k)
      ∨ SomeSizeOneCircuit W u v
      ∨ ∃ D : DetourPorts W u v (c u) k,
          ∃ E : DetourPorts W u v (c u) (thirdColour (c u) k),
            Disjoint ({D.fst, D.snd} : Finset V) ({E.fst, E.snd} : Finset V)
              ∨ CrossedOnePortCap W u v (c u) k D.fst D.snd E.fst
              ∨ CrossedOnePortCap W v u (c u) k D.snd D.fst E.snd := by
  classical
  have hcuk : c u ≠ k := Ne.symm hk
  have hlne : thirdColour (c u) k ≠ c u := thirdColour_ne_left hcuk
  rcases receiving_colour_dichotomy W hmin hmono hcard hvu hcv hlive hfib hAne hk with hx | hdk
  · exact Or.inl hx
  rcases receiving_colour_dichotomy W hmin hmono hcard hvu hcv hlive hfib hAne hlne with hy | hdl
  · exact Or.inr (Or.inl hy)
  obtain ⟨D⟩ := exists_detourPorts hdk
  obtain ⟨E⟩ := exists_detourPorts hdl
  rcases double_certified_detour_overlap_normal_form W hmin hmono hcard hcuk (Ne.symm hvu) D E with
    hc | hrest
  · exact Or.inr (Or.inr (Or.inl hc))
  · exact Or.inr (Or.inr (Or.inr ⟨D, E, hrest⟩))

/-- **Initialization at an excess site.**  A site whose live degree is not three supplies the sharp
partition, hence the receiving-pair classification in both receiving colours. -/
theorem excess_site_receiving_pair_normal_form (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : IsSupportMinimal W)
    (hmono : ∀ (p q : V), q ≠ p → ∀ i j : Fin 3, i ≠ j → W s((p, i), (q, j)) = 0)
    (hcard : 4 < Fintype.card V)
    {u : V} (hdeg : (liveNbrs W u).card ≠ 3) :
    ∃ v ∈ liveNbrs W u, ∃ c : V → Fin 3, c v = c u ∧
      W s((u, c u), (v, c u)) ≠ 0 ∧
      ∀ k : Fin 3, k ≠ c u →
        TransportedCrossing W c u v k
          ∨ TransportedCrossing W c u v (thirdColour (c u) k)
          ∨ SomeSizeOneCircuit W u v
          ∨ ∃ D : DetourPorts W u v (c u) k,
              ∃ E : DetourPorts W u v (c u) (thirdColour (c u) k),
                Disjoint ({D.fst, D.snd} : Finset V) ({E.fst, E.snd} : Finset V)
                  ∨ CrossedOnePortCap W u v (c u) k D.fst D.snd E.fst
                  ∨ CrossedOnePortCap W v u (c u) k D.snd D.fst E.snd := by
  obtain ⟨v, hv, c, hcv, hentry, hfib, hown, -, -, -⟩ :=
    excess_site_receiving_dichotomy W hmin hmono hcard hdeg
  obtain ⟨z, hz, hcz⟩ := hown
  exact ⟨v, hv, c, hcv, hentry, fun k hk =>
    receiving_pair_normal_form W hmin hmono hcard (mem_liveNbrs.mp hv).1 hcv hentry hfib
      ⟨z, Finset.mem_inter.mpr ⟨hz, NoCancellation.mem_fiber.mpr hcz⟩⟩ hk⟩

/-! ## Disjoint detours route outward

When the two receiving-colour detours share no port, each pair of ports sits inside the *other*
colour's certified complement, joined by an edge that colour has killed.  A non-vanishing sum cannot
cover such a pair by joining it to itself, so it routes both sites outward, to two sites outside all
six.  This consumes only the detour data: no minimality, no monochromatic blocks, no size bound. -/

/-- Both outward routes: each colour's certified complement routes the *other* colour's
ports to two sites outside all six. -/
def OutwardRoutes {W : Sym2 (V × Fin 3) → ℂ} {a k : Fin 3} {u v : V}
    (D : DetourPorts W u v a k) (E : DetourPorts W u v a (thirdColour a k)) : Prop :=
    (∃ x y : V, x ≠ u ∧ x ≠ v ∧ x ≠ D.fst ∧ x ≠ D.snd ∧ x ≠ E.fst ∧ x ≠ E.snd ∧
      y ≠ u ∧ y ≠ v ∧ y ≠ D.fst ∧ y ≠ D.snd ∧ y ≠ E.fst ∧ y ≠ E.snd ∧ x ≠ y ∧
      W s((E.fst, k), (x, k)) ≠ 0 ∧ W s((E.snd, k), (y, k)) ≠ 0 ∧
      pmSum W (Amplitude.const (V := V) k)
        ((Finset.univ : Finset V) \
          ({u, D.fst, v, D.snd, E.fst, x, E.snd, y} : Finset V)) ≠ 0) ∧
    (∃ x y : V, x ≠ u ∧ x ≠ v ∧ x ≠ D.fst ∧ x ≠ D.snd ∧ x ≠ E.fst ∧ x ≠ E.snd ∧
      y ≠ u ∧ y ≠ v ∧ y ≠ D.fst ∧ y ≠ D.snd ∧ y ≠ E.fst ∧ y ≠ E.snd ∧ x ≠ y ∧
      W s((D.fst, thirdColour a k), (x, thirdColour a k)) ≠ 0 ∧
      W s((D.snd, thirdColour a k), (y, thirdColour a k)) ≠ 0 ∧
      pmSum W (Amplitude.const (V := V) (thirdColour a k))
        ((Finset.univ : Finset V) \
          ({u, E.fst, v, E.snd, D.fst, x, D.snd, y} : Finset V)) ≠ 0)

theorem disjoint_detours_force_outward_routes {W : Sym2 (V × Fin 3) → ℂ}
    {a k : Fin 3} {u v : V}
    (D : DetourPorts W u v a k) (E : DetourPorts W u v a (thirdColour a k))
    (hdisj : Disjoint ({D.fst, D.snd} : Finset V) ({E.fst, E.snd} : Finset V)) :
    OutwardRoutes D E := by
  classical
  have hd := Finset.disjoint_left.mp hdisj
  have hm1 : D.fst ∈ ({D.fst, D.snd} : Finset V) := Finset.mem_insert_self _ _
  have hm2 : D.snd ∈ ({D.fst, D.snd} : Finset V) :=
    Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hpr : D.fst ≠ E.fst := fun h => hd hm1 (by rw [h]; exact Finset.mem_insert_self _ _)
  have hps : D.fst ≠ E.snd := fun h => hd hm1 (by
    rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hqr : D.snd ≠ E.fst := fun h => hd hm2 (by rw [h]; exact Finset.mem_insert_self _ _)
  have hqs : D.snd ≠ E.snd := fun h => hd hm2 (by
    rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hchordE : W s((E.fst, k), (E.snd, k)) = 0 := by
    have h := E.chord; rw [thirdColour_thirdColour] at h; exact h
  constructor
  · -- route the third-colour ports outward inside the `k`-certified complement
    have hmemr : E.fst ∈ (Finset.univ : Finset V) \ ({u, D.fst, v, D.snd} : Finset V) := by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, not_or]
      exact ⟨E.fst_ne_u, Ne.symm hpr, E.fst_ne_v, Ne.symm hqr⟩
    have hmems : E.snd ∈ (Finset.univ : Finset V) \ ({u, D.fst, v, D.snd} : Finset V) := by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, not_or]
      exact ⟨E.snd_ne_u, Ne.symm hps, E.snd_ne_v, Ne.symm hqs⟩
    obtain ⟨x, y, hxS, hyS, hxr, hxs, hyr, hys, hxy, hrx, hsy, hrem⟩ :=
      MatchingCrossing.exists_dead_pair_detour_on W (Amplitude.const (V := V) k)
        hmemr hmems E.fst_ne_snd D.cert hchordE
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or] at hxS hyS
    refine ⟨x, y, hxS.1, hxS.2.2.1, hxS.2.1, hxS.2.2.2, hxr, hxs,
      hyS.1, hyS.2.2.1, hyS.2.1, hyS.2.2.2, hyr, hys, hxy, hrx, hsy, ?_⟩
    have hset : ((Finset.univ : Finset V) \ ({u, D.fst, v, D.snd} : Finset V))
        \ ({E.fst, x, E.snd, y} : Finset V)
        = (Finset.univ : Finset V) \ ({u, D.fst, v, D.snd, E.fst, x, E.snd, y} : Finset V) := by
      ext z
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, not_or]
      tauto
    rw [← hset]; exact hrem
  · -- and symmetrically inside the third colour's certified complement
    have hmemp : D.fst ∈ (Finset.univ : Finset V) \ ({u, E.fst, v, E.snd} : Finset V) := by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, not_or]
      exact ⟨D.fst_ne_u, hpr, D.fst_ne_v, hps⟩
    have hmemq : D.snd ∈ (Finset.univ : Finset V) \ ({u, E.fst, v, E.snd} : Finset V) := by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, not_or]
      exact ⟨D.snd_ne_u, hqr, D.snd_ne_v, hqs⟩
    obtain ⟨x, y, hxS, hyS, hxp, hxq, hyp, hyq, hxy, hpx, hqy, hrem⟩ :=
      MatchingCrossing.exists_dead_pair_detour_on W
        (Amplitude.const (V := V) (thirdColour a k)) hmemp hmemq D.fst_ne_snd E.cert D.chord
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or] at hxS hyS
    refine ⟨x, y, hxS.1, hxS.2.2.1, hxp, hxq, hxS.2.1, hxS.2.2.2,
      hyS.1, hyS.2.2.1, hyp, hyq, hyS.2.1, hyS.2.2.2, hxy, hpx, hqy, ?_⟩
    have hset : ((Finset.univ : Finset V) \ ({u, E.fst, v, E.snd} : Finset V))
        \ ({D.fst, x, D.snd, y} : Finset V)
        = (Finset.univ : Finset V) \ ({u, E.fst, v, E.snd, D.fst, x, D.snd, y} : Finset V) := by
      ext z
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, not_or]
      tauto
    rw [← hset]; exact hrem

/-- Eight pairwise-distinct sites span a set of size eight. -/
theorem card_eight_of_pairwise_ne {u p v q r x s y : V}
    (h1 : u ≠ p) (h2 : u ≠ v) (h3 : u ≠ q) (h4 : u ≠ r) (h5 : u ≠ x) (h6 : u ≠ s) (h7 : u ≠ y)
    (h8 : p ≠ v) (h9 : p ≠ q) (h10 : p ≠ r) (h11 : p ≠ x) (h12 : p ≠ s) (h13 : p ≠ y)
    (h14 : v ≠ q) (h15 : v ≠ r) (h16 : v ≠ x) (h17 : v ≠ s) (h18 : v ≠ y)
    (h19 : q ≠ r) (h20 : q ≠ x) (h21 : q ≠ s) (h22 : q ≠ y)
    (h23 : r ≠ x) (h24 : r ≠ s) (h25 : r ≠ y)
    (h26 : x ≠ s) (h27 : x ≠ y) (h28 : s ≠ y) :
    ({u, p, v, q, r, x, s, y} : Finset V).card = 8 := by
  classical
  rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨h1, h2, h3, h4, h5, h6, h7⟩),
    Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨h8, h9, h10, h11, h12, h13⟩),
    Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨h14, h15, h16, h17, h18⟩),
    Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨h19, h20, h21, h22⟩),
    Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨h23, h24, h25⟩),
    Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨h26, h27⟩),
    Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; exact h28),
    Finset.card_singleton]

/-- The `k`-route's eight sites, with their size and the live product. -/
theorem exists_disjoint_detour_octet {W : Sym2 (V × Fin 3) → ℂ}
    {a k : Fin 3} {u v : V} (huv : u ≠ v)
    (D : DetourPorts W u v a k) (E : DetourPorts W u v a (thirdColour a k))
    (hdisj : Disjoint ({D.fst, D.snd} : Finset V) ({E.fst, E.snd} : Finset V)) :
    ∃ x y : V, x ≠ y ∧
      ({u, D.fst, v, D.snd, E.fst, x, E.snd, y} : Finset V).card = 8 ∧
      W s((E.fst, k), (x, k)) * W s((E.snd, k), (y, k)) ≠ 0 := by
  classical
  obtain ⟨⟨x, y, hxu, hxv, hxp, hxq, hxr, hxs, hyu, hyv, hyp, hyq, hyr, hys, hxy, hrx, hsy, -⟩, -⟩ :=
    disjoint_detours_force_outward_routes D E hdisj
  have hd := Finset.disjoint_left.mp hdisj
  have hm1 : D.fst ∈ ({D.fst, D.snd} : Finset V) := Finset.mem_insert_self _ _
  have hm2 : D.snd ∈ ({D.fst, D.snd} : Finset V) :=
    Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hpr : D.fst ≠ E.fst := fun h => hd hm1 (by rw [h]; exact Finset.mem_insert_self _ _)
  have hps : D.fst ≠ E.snd := fun h => hd hm1 (by
    rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hqr : D.snd ≠ E.fst := fun h => hd hm2 (by rw [h]; exact Finset.mem_insert_self _ _)
  have hqs : D.snd ≠ E.snd := fun h => hd hm2 (by
    rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  refine ⟨x, y, hxy, card_eight_of_pairwise_ne
    (Ne.symm D.fst_ne_u) huv (Ne.symm D.snd_ne_u) (Ne.symm E.fst_ne_u) (Ne.symm hxu)
      (Ne.symm E.snd_ne_u) (Ne.symm hyu)
    D.fst_ne_v D.fst_ne_snd hpr (Ne.symm hxp) hps (Ne.symm hyp)
    (Ne.symm D.snd_ne_v) (Ne.symm E.fst_ne_v) (Ne.symm hxv) (Ne.symm E.snd_ne_v) (Ne.symm hyv)
    hqr (Ne.symm hxq) hqs (Ne.symm hyq)
    (Ne.symm hxr) E.fst_ne_snd (Ne.symm hyr)
    hxs hxy (Ne.symm hys), mul_ne_zero hrx hsy⟩

/-- The eight sites the `k`-route exhibits are distinct, so disjoint detours need at least eight
sites. -/
theorem eight_le_card_of_disjoint_detours {W : Sym2 (V × Fin 3) → ℂ}
    {a k : Fin 3} {u v : V} (huv : u ≠ v)
    (D : DetourPorts W u v a k) (E : DetourPorts W u v a (thirdColour a k))
    (hdisj : Disjoint ({D.fst, D.snd} : Finset V) ({E.fst, E.snd} : Finset V)) :
    8 ≤ Fintype.card V := by
  classical
  obtain ⟨x, y, hx8, hcard8, -⟩ := exists_disjoint_detour_octet huv D E hdisj
  calc 8 = ({u, D.fst, v, D.snd, E.fst, x, E.snd, y} : Finset V).card := hcard8.symm
    _ ≤ Fintype.card V := Finset.card_le_univ _

/-- **Sharp exhaustion at eight sites.**  With exactly eight sites the `k`-route uses precisely the
two sites outside the six, the eight fill the vertex type, and the certified remainder is the
matching sum on the empty set.  Both route edges are live, so their product does not vanish. -/
theorem disjoint_detours_card_eight_exhaustion {W : Sym2 (V × Fin 3) → ℂ}
    {a k : Fin 3} {u v : V} (huv : u ≠ v)
    (D : DetourPorts W u v a k) (E : DetourPorts W u v a (thirdColour a k))
    (hdisj : Disjoint ({D.fst, D.snd} : Finset V) ({E.fst, E.snd} : Finset V))
    (hcard : Fintype.card V = 8) :
    ∃ x y : V, x ≠ y ∧
      W s((E.fst, k), (x, k)) * W s((E.snd, k), (y, k)) ≠ 0 ∧
      ({u, D.fst, v, D.snd, E.fst, x, E.snd, y} : Finset V) = (Finset.univ : Finset V) ∧
      (Finset.univ : Finset V) \ ({u, D.fst, v, D.snd, E.fst, x, E.snd, y} : Finset V)
        = (∅ : Finset V) := by
  classical
  obtain ⟨x, y, hxy, hcard8, hlive⟩ := exists_disjoint_detour_octet huv D E hdisj
  have huniv : ({u, D.fst, v, D.snd, E.fst, x, E.snd, y} : Finset V) = Finset.univ :=
    Finset.eq_univ_of_card _ (by omega)
  exact ⟨x, y, hxy, hlive, huniv, by rw [huniv, Finset.sdiff_self]⟩

/-- **The refined receiving fork.**  In a receiving colour the pair is live, giving a transported
crossing; or a route arm is bicoloured, giving a size-one circuit; or the two detours share their
crossed port, giving the rigid cap; or they share no port, and then each colour routes the other's
ports outward to two further sites -- which needs at least eight sites in all. -/
theorem receiving_pair_routed_normal_form (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : IsSupportMinimal W)
    (hmono : ∀ (p q : V), q ≠ p → ∀ i j : Fin 3, i ≠ j → W s((p, i), (q, j)) = 0)
    (hcard : 4 < Fintype.card V)
    {c : V → Fin 3} {u v : V} (hvu : v ≠ u) (hcv : c v = c u)
    (hlive : W s((u, c u), (v, c u)) ≠ 0)
    (hfib : ∀ m : Fin 3, pmSum W (Amplitude.const (V := V) m)
      (((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c m) ≠ 0)
    (hAne : (((Finset.univ.erase u).erase v) ∩ NoCancellation.fiber c (c u)).Nonempty)
    {k : Fin 3} (hk : k ≠ c u) :
    TransportedCrossing W c u v k
      ∨ TransportedCrossing W c u v (thirdColour (c u) k)
      ∨ SomeSizeOneCircuit W u v
      ∨ (∃ D : DetourPorts W u v (c u) k,
          ∃ E : DetourPorts W u v (c u) (thirdColour (c u) k),
            CrossedOnePortCap W u v (c u) k D.fst D.snd E.fst
              ∨ CrossedOnePortCap W v u (c u) k D.snd D.fst E.snd)
      ∨ (∃ D : DetourPorts W u v (c u) k,
          ∃ E : DetourPorts W u v (c u) (thirdColour (c u) k),
            Disjoint ({D.fst, D.snd} : Finset V) ({E.fst, E.snd} : Finset V)
              ∧ OutwardRoutes D E
              ∧ 8 ≤ Fintype.card V) := by
  rcases receiving_pair_normal_form W hmin hmono hcard hvu hcv hlive hfib hAne hk with
    h | h | h | ⟨D, E, hrest⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  rcases hrest with hdisj | hcap
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨D, E, hdisj,
      disjoint_detours_force_outward_routes D E hdisj,
      eight_le_card_of_disjoint_detours (Ne.symm hvu) D E hdisj⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨D, E, hcap⟩)))

/-- **Initialization at an excess site.**  A site whose live degree is not three supplies the sharp
partition, hence the refined fork in both receiving colours. -/
theorem excess_site_receiving_pair_routed (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : IsSupportMinimal W)
    (hmono : ∀ (p q : V), q ≠ p → ∀ i j : Fin 3, i ≠ j → W s((p, i), (q, j)) = 0)
    (hcard : 4 < Fintype.card V)
    {u : V} (hdeg : (liveNbrs W u).card ≠ 3) :
    ∃ v ∈ liveNbrs W u, ∃ c : V → Fin 3, c v = c u ∧
      W s((u, c u), (v, c u)) ≠ 0 ∧
      ∀ k : Fin 3, k ≠ c u →
        TransportedCrossing W c u v k
          ∨ TransportedCrossing W c u v (thirdColour (c u) k)
          ∨ SomeSizeOneCircuit W u v
          ∨ (∃ D : DetourPorts W u v (c u) k,
              ∃ E : DetourPorts W u v (c u) (thirdColour (c u) k),
                CrossedOnePortCap W u v (c u) k D.fst D.snd E.fst
                  ∨ CrossedOnePortCap W v u (c u) k D.snd D.fst E.snd)
          ∨ (∃ D : DetourPorts W u v (c u) k,
              ∃ E : DetourPorts W u v (c u) (thirdColour (c u) k),
                Disjoint ({D.fst, D.snd} : Finset V) ({E.fst, E.snd} : Finset V)
                  ∧ OutwardRoutes D E
                  ∧ 8 ≤ Fintype.card V) := by
  obtain ⟨v, hv, c, hcv, hentry, hfib, hown, -, -, -⟩ :=
    excess_site_receiving_dichotomy W hmin hmono hcard hdeg
  obtain ⟨z, hz, hcz⟩ := hown
  exact ⟨v, hv, c, hcv, hentry, fun k hk =>
    receiving_pair_routed_normal_form W hmin hmono hcard (mem_liveNbrs.mp hv).1 hcv hentry hfib
      ⟨z, Finset.mem_inter.mpr ⟨hz, NoCancellation.mem_fiber.mpr hcz⟩⟩ hk⟩

/-! ## Tails of the crossed cap

The cap's two certified complements each contain one of its free ports: the `k`-complement
contains `r`, the third-colour complement contains `q`.  Neither can be a matching sum's dead end,
so each has a live partner outside the cap, with a remainder that still does not vanish. -/

/-- The cap forces its two free ports apart: `r = q` would make one edge both live and dead. -/
theorem CrossedOnePortCap.r_ne_q {W : Sym2 (V × Fin 3) → ℂ} {u v : V} {a k : Fin 3} {p q r : V}
    (H : CrossedOnePortCap W u v a k p q r) : r ≠ q := fun h =>
  H.live_k_vq (h ▸ H.dead_k_vr)

/-- Six pairwise-distinct sites span a set of size six. -/
theorem card_six_of_pairwise_ne {u p v q r t : V}
    (h1 : u ≠ p) (h2 : u ≠ v) (h3 : u ≠ q) (h4 : u ≠ r) (h5 : u ≠ t)
    (h6 : p ≠ v) (h7 : p ≠ q) (h8 : p ≠ r) (h9 : p ≠ t)
    (h10 : v ≠ q) (h11 : v ≠ r) (h12 : v ≠ t)
    (h13 : q ≠ r) (h14 : q ≠ t) (h15 : r ≠ t) :
    ({u, p, v, q, r, t} : Finset V).card = 6 := by
  classical
  rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨h1, h2, h3, h4, h5⟩),
    Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨h6, h7, h8, h9⟩),
    Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨h10, h11, h12⟩),
    Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨h13, h14⟩),
    Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; exact h15),
    Finset.card_singleton]

/-- The two tails of a crossed cap, with their live edges and certified remainders. -/
structure CrossedCapTails (W : Sym2 (V × Fin 3) → ℂ) (u v : V) (a k : Fin 3) (p q r : V) where
  /-- the `k`-tail of the free port `r` -/
  kt : V
  /-- the third-colour tail of the free port `q` -/
  lt : V
  kt_ne_u : kt ≠ u
  kt_ne_p : kt ≠ p
  kt_ne_v : kt ≠ v
  kt_ne_q : kt ≠ q
  kt_ne_r : kt ≠ r
  lt_ne_u : lt ≠ u
  lt_ne_r : lt ≠ r
  lt_ne_v : lt ≠ v
  lt_ne_p : lt ≠ p
  lt_ne_q : lt ≠ q
  live_k : W s((r, k), (kt, k)) ≠ 0
  live_l : W s((q, thirdColour a k), (lt, thirdColour a k)) ≠ 0
  rem_k : pmSum W (Amplitude.const (V := V) k)
    ((Finset.univ : Finset V) \ ({u, p, v, q, r, kt} : Finset V)) ≠ 0
  rem_l : pmSum W (Amplitude.const (V := V) (thirdColour a k))
    ((Finset.univ : Finset V) \ ({u, r, v, p, q, lt} : Finset V)) ≠ 0

theorem exists_crossedCapTails {W : Sym2 (V × Fin 3) → ℂ} {u v : V} {a k : Fin 3} {p q r : V}
    (H : CrossedOnePortCap W u v a k p q r) : Nonempty (CrossedCapTails W u v a k p q r) := by
  classical
  have hrq := H.r_ne_q
  have hmemr : r ∈ (Finset.univ : Finset V) \ ({u, p, v, q} : Finset V) := by
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    exact ⟨H.r_ne_u, H.r_ne_p, H.r_ne_v, hrq⟩
  obtain ⟨t, ht, hlt, hremt⟩ :=
    MatchingSum.exists_partner_ne_zero W (Amplitude.const (V := V) k) hmemr H.cert_k
  have htr : t ≠ r := Finset.ne_of_mem_erase ht
  have htS := Finset.mem_of_mem_erase ht
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, not_or] at htS
  have hmemq : q ∈ (Finset.univ : Finset V) \ ({u, r, v, p} : Finset V) := by
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    exact ⟨H.q_ne_u, Ne.symm hrq, H.q_ne_v, Ne.symm H.p_ne_q⟩
  obtain ⟨w, hw, hlw, hremw⟩ :=
    MatchingSum.exists_partner_ne_zero W (Amplitude.const (V := V) (thirdColour a k)) hmemq H.cert_l
  have hwq : w ≠ q := Finset.ne_of_mem_erase hw
  have hwS := Finset.mem_of_mem_erase hw
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, not_or] at hwS
  have hsetk : (((Finset.univ : Finset V) \ ({u, p, v, q} : Finset V)).erase r).erase t
      = (Finset.univ : Finset V) \ ({u, p, v, q, r, t} : Finset V) := by
    ext z
    simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton, not_or]
    tauto
  have hsetl : (((Finset.univ : Finset V) \ ({u, r, v, p} : Finset V)).erase q).erase w
      = (Finset.univ : Finset V) \ ({u, r, v, p, q, w} : Finset V) := by
    ext z
    simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton, not_or]
    tauto
  exact ⟨⟨t, w, htS.1, htS.2.1, htS.2.2.1, htS.2.2.2, htr,
    hwS.1, hwS.2.1, hwS.2.2.1, hwS.2.2.2, hwq,
    hlt, hlw, by rw [← hsetk]; exact hremt, by rw [← hsetl]; exact hremw⟩⟩

/-- Six distinct sites, so a crossed cap with tails needs at least six sites. -/
theorem six_le_card_of_crossedCapTails {W : Sym2 (V × Fin 3) → ℂ} {u v : V} {a k : Fin 3}
    {p q r : V} (huv : u ≠ v) (H : CrossedOnePortCap W u v a k p q r)
    (T : CrossedCapTails W u v a k p q r) : 6 ≤ Fintype.card V := by
  classical
  calc 6 = ({u, p, v, q, r, T.kt} : Finset V).card :=
        (card_six_of_pairwise_ne (Ne.symm H.p_ne_u) huv (Ne.symm H.q_ne_u) (Ne.symm H.r_ne_u)
          (Ne.symm T.kt_ne_u) H.p_ne_v H.p_ne_q (Ne.symm H.r_ne_p) (Ne.symm T.kt_ne_p)
          (Ne.symm H.q_ne_v) (Ne.symm H.r_ne_v) (Ne.symm T.kt_ne_v)
          (Ne.symm H.r_ne_q) (Ne.symm T.kt_ne_q) (Ne.symm T.kt_ne_r)).symm
    _ ≤ Fintype.card V := Finset.card_le_univ _

/-- **Sharp behaviour at six sites.**  The cap and its `k`-tail already fill the vertex type, the
third-colour tail must coincide with the `k`-tail, and both remainders are empty. -/
theorem crossedCapTails_card_six {W : Sym2 (V × Fin 3) → ℂ} {u v : V} {a k : Fin 3}
    {p q r : V} (huv : u ≠ v) (H : CrossedOnePortCap W u v a k p q r)
    (T : CrossedCapTails W u v a k p q r) (hcard : Fintype.card V = 6) :
    ({u, p, v, q, r, T.kt} : Finset V) = (Finset.univ : Finset V) ∧ T.lt = T.kt ∧
      (Finset.univ : Finset V) \ ({u, p, v, q, r, T.kt} : Finset V) = (∅ : Finset V) := by
  classical
  have hc6 : ({u, p, v, q, r, T.kt} : Finset V).card = 6 :=
    card_six_of_pairwise_ne (Ne.symm H.p_ne_u) huv (Ne.symm H.q_ne_u) (Ne.symm H.r_ne_u)
      (Ne.symm T.kt_ne_u) H.p_ne_v H.p_ne_q (Ne.symm H.r_ne_p) (Ne.symm T.kt_ne_p)
      (Ne.symm H.q_ne_v) (Ne.symm H.r_ne_v) (Ne.symm T.kt_ne_v)
      (Ne.symm H.r_ne_q) (Ne.symm T.kt_ne_q) (Ne.symm T.kt_ne_r)
  have huniv : ({u, p, v, q, r, T.kt} : Finset V) = Finset.univ :=
    Finset.eq_univ_of_card _ (by omega)
  refine ⟨huniv, ?_, by rw [huniv, Finset.sdiff_self]⟩
  have hmem : T.lt ∈ ({u, p, v, q, r, T.kt} : Finset V) := huniv ▸ Finset.mem_univ T.lt
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h | h
  · exact absurd h T.lt_ne_u
  · exact absurd h T.lt_ne_p
  · exact absurd h T.lt_ne_v
  · exact absurd h T.lt_ne_q
  · exact absurd h T.lt_ne_r
  · exact h

/-- Distinct tails give a seventh site. -/
theorem seven_le_card_of_distinct_tails {W : Sym2 (V × Fin 3) → ℂ} {u v : V} {a k : Fin 3}
    {p q r : V} (huv : u ≠ v) (H : CrossedOnePortCap W u v a k p q r)
    (T : CrossedCapTails W u v a k p q r) (hne : T.lt ≠ T.kt) : 7 ≤ Fintype.card V := by
  classical
  have hc6 : ({u, p, v, q, r, T.kt} : Finset V).card = 6 :=
    card_six_of_pairwise_ne (Ne.symm H.p_ne_u) huv (Ne.symm H.q_ne_u) (Ne.symm H.r_ne_u)
      (Ne.symm T.kt_ne_u) H.p_ne_v H.p_ne_q (Ne.symm H.r_ne_p) (Ne.symm T.kt_ne_p)
      (Ne.symm H.q_ne_v) (Ne.symm H.r_ne_v) (Ne.symm T.kt_ne_v)
      (Ne.symm H.r_ne_q) (Ne.symm T.kt_ne_q) (Ne.symm T.kt_ne_r)
  have hnot : T.lt ∉ ({u, p, v, q, r, T.kt} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨T.lt_ne_u, T.lt_ne_p, T.lt_ne_v, T.lt_ne_q, T.lt_ne_r, hne⟩
  have hc7 : (insert T.lt ({u, p, v, q, r, T.kt} : Finset V)).card = 7 := by
    rw [Finset.card_insert_of_notMem hnot, hc6]
  calc 7 = (insert T.lt ({u, p, v, q, r, T.kt} : Finset V)).card := hc7.symm
    _ ≤ Fintype.card V := Finset.card_le_univ _

/-- **Sharp behaviour at eight sites.**  Each certified remainder is a two-element set whose edge
in that colour is live -- the matching sum on a pair is that pair's own weight. -/
theorem crossedCapTails_card_eight {W : Sym2 (V × Fin 3) → ℂ} {u v : V} {a k : Fin 3}
    {p q r : V} (huv : u ≠ v) (H : CrossedOnePortCap W u v a k p q r)
    (T : CrossedCapTails W u v a k p q r) (hcard : Fintype.card V = 8) :
    ∃ e f : V, e ≠ f ∧
      (Finset.univ : Finset V) \ ({u, p, v, q, r, T.kt} : Finset V) = ({e, f} : Finset V) ∧
      W s((e, k), (f, k)) ≠ 0 := by
  classical
  have hc6 : ({u, p, v, q, r, T.kt} : Finset V).card = 6 :=
    card_six_of_pairwise_ne (Ne.symm H.p_ne_u) huv (Ne.symm H.q_ne_u) (Ne.symm H.r_ne_u)
      (Ne.symm T.kt_ne_u) H.p_ne_v H.p_ne_q (Ne.symm H.r_ne_p) (Ne.symm T.kt_ne_p)
      (Ne.symm H.q_ne_v) (Ne.symm H.r_ne_v) (Ne.symm T.kt_ne_v)
      (Ne.symm H.r_ne_q) (Ne.symm T.kt_ne_q) (Ne.symm T.kt_ne_r)
  have hcs : ((Finset.univ : Finset V) \ ({u, p, v, q, r, T.kt} : Finset V)).card = 2 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hc6, hcard]
  obtain ⟨e, f, hef, hset⟩ := Finset.card_eq_two.mp hcs
  refine ⟨e, f, hef, hset, ?_⟩
  have hrem := T.rem_k
  rw [hset, MatchingSum.pmSum_pair W (Amplitude.const (V := V) k) (Ne.symm hef)] at hrem
  exact hrem

/-! ## Synchronization of the two routes at eight sites

With exactly eight sites the six named ones plus the `k`-route's two exhaust the vertex type, so
the third colour's route has nowhere else to go: it uses the same two sites, in one of two
orientations. -/

theorem disjoint_detours_octet_synchronized {W : Sym2 (V × Fin 3) → ℂ}
    {a k : Fin 3} {u v : V} (huv : u ≠ v)
    (D : DetourPorts W u v a k) (E : DetourPorts W u v a (thirdColour a k))
    (hdisj : Disjoint ({D.fst, D.snd} : Finset V) ({E.fst, E.snd} : Finset V))
    (hcard : Fintype.card V = 8) :
    ∃ x y : V, x ≠ y ∧
      ({u, D.fst, v, D.snd, E.fst, x, E.snd, y} : Finset V) = (Finset.univ : Finset V) ∧
      W s((E.fst, k), (x, k)) ≠ 0 ∧ W s((E.snd, k), (y, k)) ≠ 0 ∧
      ((W s((D.fst, thirdColour a k), (x, thirdColour a k)) ≠ 0 ∧
          W s((D.snd, thirdColour a k), (y, thirdColour a k)) ≠ 0) ∨
        (W s((D.fst, thirdColour a k), (y, thirdColour a k)) ≠ 0 ∧
          W s((D.snd, thirdColour a k), (x, thirdColour a k)) ≠ 0)) := by
  classical
  obtain ⟨⟨x, y, hxu, hxv, hxp, hxq, hxr, hxs, hyu, hyv, hyp, hyq, hyr, hys, hxy, hrx, hsy, -⟩,
    ⟨x', y', hx'u, hx'v, hx'p, hx'q, hx'r, hx's, hy'u, hy'v, hy'p, hy'q, hy'r, hy's, hx'y',
      hpx', hqy', -⟩⟩ := disjoint_detours_force_outward_routes D E hdisj
  have hd := Finset.disjoint_left.mp hdisj
  have hm1 : D.fst ∈ ({D.fst, D.snd} : Finset V) := Finset.mem_insert_self _ _
  have hm2 : D.snd ∈ ({D.fst, D.snd} : Finset V) :=
    Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hpr : D.fst ≠ E.fst := fun h => hd hm1 (by rw [h]; exact Finset.mem_insert_self _ _)
  have hps : D.fst ≠ E.snd := fun h => hd hm1 (by
    rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hqr : D.snd ≠ E.fst := fun h => hd hm2 (by rw [h]; exact Finset.mem_insert_self _ _)
  have hqs : D.snd ≠ E.snd := fun h => hd hm2 (by
    rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hc8 : ({u, D.fst, v, D.snd, E.fst, x, E.snd, y} : Finset V).card = 8 :=
    card_eight_of_pairwise_ne
      (Ne.symm D.fst_ne_u) huv (Ne.symm D.snd_ne_u) (Ne.symm E.fst_ne_u) (Ne.symm hxu)
        (Ne.symm E.snd_ne_u) (Ne.symm hyu)
      D.fst_ne_v D.fst_ne_snd hpr (Ne.symm hxp) hps (Ne.symm hyp)
      (Ne.symm D.snd_ne_v) (Ne.symm E.fst_ne_v) (Ne.symm hxv) (Ne.symm E.snd_ne_v) (Ne.symm hyv)
      hqr (Ne.symm hxq) hqs (Ne.symm hyq)
      (Ne.symm hxr) E.fst_ne_snd (Ne.symm hyr)
      hxs hxy (Ne.symm hys)
  have huniv : ({u, D.fst, v, D.snd, E.fst, x, E.snd, y} : Finset V) = Finset.univ :=
    Finset.eq_univ_of_card _ (by omega)
  -- the third colour's route sites lie in the same octet, hence in `{x, y}`
  have hin : ∀ z : V, z ≠ u → z ≠ v → z ≠ D.fst → z ≠ D.snd → z ≠ E.fst → z ≠ E.snd →
      z = x ∨ z = y := by
    intro z h1 h2 h3 h4 h5 h6
    have hz : z ∈ ({u, D.fst, v, D.snd, E.fst, x, E.snd, y} : Finset V) :=
      huniv ▸ Finset.mem_univ z
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with h | h | h | h | h | h | h | h
    · exact absurd h h1
    · exact absurd h h3
    · exact absurd h h2
    · exact absurd h h4
    · exact absurd h h5
    · exact Or.inl h
    · exact absurd h h6
    · exact Or.inr h
  refine ⟨x, y, hxy, huniv, hrx, hsy, ?_⟩
  rcases hin x' hx'u hx'v hx'p hx'q hx'r hx's with hxx | hxy'
  · left
    refine ⟨by rw [← hxx]; exact hpx', ?_⟩
    rcases hin y' hy'u hy'v hy'p hy'q hy'r hy's with h | h
    · exact absurd (hxx.trans h.symm) hx'y'
    · rw [← h]; exact hqy'
  · right
    refine ⟨by rw [← hxy']; exact hpx', ?_⟩
    rcases hin y' hy'u hy'v hy'p hy'q hy'r hy's with h | h
    · rw [← h]; exact hqy'
    · exact absurd (hxy'.trans h.symm) hx'y'

/-- **The synchronized octet.**  Everything two disjoint receiving-colour detours force at exactly
eight sites: which sites there are, which edges are live, which are dead, and which of the two
orientations the third colour's route takes.  No field is assumed. -/
structure DisjointDetourOctet (W : Sym2 (V × Fin 3) → ℂ) (u v : V) (a k : Fin 3)
    (p q r s x y : V) : Prop where
  /-- the eight sites are the whole vertex type -/
  fills : ({u, p, v, q, r, x, s, y} : Finset V) = (Finset.univ : Finset V)
  x_ne_y : x ≠ y
  /-- the pair is dead in both receiving colours -/
  dead_k_uv : W s((u, k), (v, k)) = 0
  dead_l_uv : W s((u, thirdColour a k), (v, thirdColour a k)) = 0
  /-- both forbidden chords -/
  dead_l_pq : W s((p, thirdColour a k), (q, thirdColour a k)) = 0
  dead_k_rs : W s((r, k), (s, k)) = 0
  /-- the four `k`-live edges: the detour's two arms and its outward route -/
  live_k_up : W s((u, k), (p, k)) ≠ 0
  live_k_vq : W s((v, k), (q, k)) ≠ 0
  live_k_rx : W s((r, k), (x, k)) ≠ 0
  live_k_sy : W s((s, k), (y, k)) ≠ 0
  /-- the third colour's two detour arms -/
  live_l_ur : W s((u, thirdColour a k), (r, thirdColour a k)) ≠ 0
  live_l_vs : W s((v, thirdColour a k), (s, thirdColour a k)) ≠ 0
  /-- and its outward route, in one of the two orientations on the same two sites -/
  orientation :
    (W s((p, thirdColour a k), (x, thirdColour a k)) ≠ 0 ∧
      W s((q, thirdColour a k), (y, thirdColour a k)) ≠ 0) ∨
    (W s((p, thirdColour a k), (y, thirdColour a k)) ≠ 0 ∧
      W s((q, thirdColour a k), (x, thirdColour a k)) ≠ 0)

theorem exists_disjointDetourOctet {W : Sym2 (V × Fin 3) → ℂ}
    {a k : Fin 3} {u v : V} (huv : u ≠ v)
    (D : DetourPorts W u v a k) (E : DetourPorts W u v a (thirdColour a k))
    (hdisj : Disjoint ({D.fst, D.snd} : Finset V) ({E.fst, E.snd} : Finset V))
    (hcard : Fintype.card V = 8) :
    ∃ x y : V, DisjointDetourOctet W u v a k D.fst D.snd E.fst E.snd x y := by
  classical
  obtain ⟨x, y, hxy, huniv, hrx, hsy, horient⟩ :=
    disjoint_detours_octet_synchronized huv D E hdisj hcard
  have hchordE : W s((E.fst, k), (E.snd, k)) = 0 := by
    have h := E.chord; rw [thirdColour_thirdColour] at h; exact h
  have hdeadl : W s((u, thirdColour a k), (v, thirdColour a k)) = 0 := E.dead_pair
  exact ⟨x, y, ⟨huniv, hxy, D.dead_pair, hdeadl, D.chord, hchordE,
    D.live_fst, D.live_snd, hrx, hsy, E.live_fst, E.live_snd, horient⟩⟩

/-! ## The route-overlap calculus

At arbitrary size the two outward routes need not land on the same sites.  Their two-site
destinations meet in two sites, one, or none, and in the last case four genuinely new sites appear. -/

/-- Two unordered pairs meet in both, one, or neither site. -/
theorem pair_overlap_trichotomy {x y x' y' : V} (hxy : x ≠ y) (hx'y' : x' ≠ y') :
    ({x, y} : Finset V) = ({x', y'} : Finset V)
      ∨ (∃ z : V, ({x, y} : Finset V) ∩ ({x', y'} : Finset V) = ({z} : Finset V))
      ∨ Disjoint ({x, y} : Finset V) ({x', y'} : Finset V) := by
  classical
  by_cases hx' : x' ∈ ({x, y} : Finset V)
  · by_cases hy' : y' ∈ ({x, y} : Finset V)
    · refine Or.inl ?_
      have hsub : ({x', y'} : Finset V) ⊆ ({x, y} : Finset V) := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> assumption
      have hc : ({x, y} : Finset V).card = 2 := Finset.card_pair hxy
      have hc' : ({x', y'} : Finset V).card = 2 := Finset.card_pair hx'y'
      exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
    · refine Or.inr (Or.inl ⟨x', ?_⟩)
      have hx'm : x' = x ∨ x' = y := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hx'
      have hy'm : ¬(y' = x ∨ y' = y) := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hy'
      ext z
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hz, hz' | rfl⟩
        · exact hz'
        · exact absurd hz hy'm
      · rintro rfl
        exact ⟨hx'm, Or.inl rfl⟩
  · by_cases hy' : y' ∈ ({x, y} : Finset V)
    · refine Or.inr (Or.inl ⟨y', ?_⟩)
      have hy'm : y' = x ∨ y' = y := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hy'
      have hx'm : ¬(x' = x ∨ x' = y) := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hx'
      ext z
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hz, rfl | hz'⟩
        · exact absurd hz hx'm
        · exact hz'
      · rintro rfl
        exact ⟨hy'm, Or.inr rfl⟩
    · refine Or.inr (Or.inr ?_)
      refine Finset.disjoint_right.mpr ?_
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption

/-- **Both routes exposed, with their destinations classified.**  For any size: the `k`-route, the
third colour's route, all four destinations outside the six named sites, and the trichotomy on how
the two destination pairs meet. -/
theorem outward_route_overlap {W : Sym2 (V × Fin 3) → ℂ}
    {a k : Fin 3} {u v : V}
    (D : DetourPorts W u v a k) (E : DetourPorts W u v a (thirdColour a k))
    (hdisj : Disjoint ({D.fst, D.snd} : Finset V) ({E.fst, E.snd} : Finset V)) :
    ∃ x y x' y' : V, x ≠ y ∧ x' ≠ y' ∧
      W s((E.fst, k), (x, k)) ≠ 0 ∧ W s((E.snd, k), (y, k)) ≠ 0 ∧
      pmSum W (Amplitude.const (V := V) k)
        ((Finset.univ : Finset V) \
          ({u, D.fst, v, D.snd, E.fst, x, E.snd, y} : Finset V)) ≠ 0 ∧
      W s((D.fst, thirdColour a k), (x', thirdColour a k)) ≠ 0 ∧
      W s((D.snd, thirdColour a k), (y', thirdColour a k)) ≠ 0 ∧
      pmSum W (Amplitude.const (V := V) (thirdColour a k))
        ((Finset.univ : Finset V) \
          ({u, E.fst, v, E.snd, D.fst, x', D.snd, y'} : Finset V)) ≠ 0 ∧
      (∀ z ∈ ({x, y, x', y'} : Finset V),
        z ≠ u ∧ z ≠ v ∧ z ≠ D.fst ∧ z ≠ D.snd ∧ z ≠ E.fst ∧ z ≠ E.snd) ∧
      (({x, y} : Finset V) = ({x', y'} : Finset V)
        ∨ (∃ z : V, ({x, y} : Finset V) ∩ ({x', y'} : Finset V) = ({z} : Finset V))
        ∨ Disjoint ({x, y} : Finset V) ({x', y'} : Finset V)) := by
  classical
  obtain ⟨⟨x, y, hxu, hxv, hxp, hxq, hxr, hxs, hyu, hyv, hyp, hyq, hyr, hys, hxy, hrx, hsy, hkr⟩,
    ⟨x', y', hx'u, hx'v, hx'p, hx'q, hx'r, hx's, hy'u, hy'v, hy'p, hy'q, hy'r, hy's, hx'y',
      hpx', hqy', hlr⟩⟩ := disjoint_detours_force_outward_routes D E hdisj
  refine ⟨x, y, x', y', hxy, hx'y', hrx, hsy, hkr, hpx', hqy', hlr, ?_,
    pair_overlap_trichotomy hxy hx'y'⟩
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact ⟨hxu, hxv, hxp, hxq, hxr, hxs⟩
  · exact ⟨hyu, hyv, hyp, hyq, hyr, hys⟩
  · exact ⟨hx'u, hx'v, hx'p, hx'q, hx'r, hx's⟩
  · exact ⟨hy'u, hy'v, hy'p, hy'q, hy'r, hy's⟩

/-- Two further sites beyond an octet give ten. -/
theorem ten_le_card_of_two_beyond_octet {u p v q r x s y x' y' : V}
    (hc8 : ({u, p, v, q, r, x, s, y} : Finset V).card = 8)
    (hx' : x' ∉ ({u, p, v, q, r, x, s, y} : Finset V))
    (hy' : y' ∉ insert x' ({u, p, v, q, r, x, s, y} : Finset V)) :
    10 ≤ Fintype.card V := by
  classical
  have h9 : (insert x' ({u, p, v, q, r, x, s, y} : Finset V)).card = 9 := by
    rw [Finset.card_insert_of_notMem hx', hc8]
  have h10 : (insert y' (insert x' ({u, p, v, q, r, x, s, y} : Finset V))).card = 10 := by
    rw [Finset.card_insert_of_notMem hy', h9]
  calc 10 = (insert y' (insert x' ({u, p, v, q, r, x, s, y} : Finset V))).card := h10.symm
    _ ≤ Fintype.card V := Finset.card_le_univ _

/-- **The route-overlap calculus with its size consequence.**  The two destination pairs coincide,
meet in one site, or are disjoint -- and disjoint destinations mean four genuinely new sites, hence
at least ten in all. -/
theorem outward_route_overlap_sized {W : Sym2 (V × Fin 3) → ℂ}
    {a k : Fin 3} {u v : V} (huv : u ≠ v)
    (D : DetourPorts W u v a k) (E : DetourPorts W u v a (thirdColour a k))
    (hdisj : Disjoint ({D.fst, D.snd} : Finset V) ({E.fst, E.snd} : Finset V)) :
    ∃ x y x' y' : V, x ≠ y ∧ x' ≠ y' ∧
      W s((E.fst, k), (x, k)) ≠ 0 ∧ W s((E.snd, k), (y, k)) ≠ 0 ∧
      W s((D.fst, thirdColour a k), (x', thirdColour a k)) ≠ 0 ∧
      W s((D.snd, thirdColour a k), (y', thirdColour a k)) ≠ 0 ∧
      (({x, y} : Finset V) = ({x', y'} : Finset V)
        ∨ (∃ z : V, ({x, y} : Finset V) ∩ ({x', y'} : Finset V) = ({z} : Finset V))
        ∨ (Disjoint ({x, y} : Finset V) ({x', y'} : Finset V) ∧ 10 ≤ Fintype.card V)) := by
  classical
  obtain ⟨x, y, x', y', hxy, hx'y', hrx, hsy, hkr, hpx', hqy', hlr, hout, htri⟩ :=
    outward_route_overlap D E hdisj
  have hmemx : x ∈ ({x, y, x', y'} : Finset V) := Finset.mem_insert_self _ _
  have hmemy : y ∈ ({x, y, x', y'} : Finset V) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hmemx' : x' ∈ ({x, y, x', y'} : Finset V) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hmemy' : y' ∈ ({x, y, x', y'} : Finset V) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
  obtain ⟨hxu, hxv, hxp, hxq, hxr, hxs⟩ := hout x hmemx
  obtain ⟨hyu, hyv, hyp, hyq, hyr, hys⟩ := hout y hmemy
  obtain ⟨hx'u, hx'v, hx'p, hx'q, hx'r, hx's⟩ := hout x' hmemx'
  obtain ⟨hy'u, hy'v, hy'p, hy'q, hy'r, hy's⟩ := hout y' hmemy'
  refine ⟨x, y, x', y', hxy, hx'y', hrx, hsy, hpx', hqy', ?_⟩
  rcases htri with h | h | hdd
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  refine Or.inr (Or.inr ⟨hdd, ?_⟩)
  have hd := Finset.disjoint_left.mp hdisj
  have hm1 : D.fst ∈ ({D.fst, D.snd} : Finset V) := Finset.mem_insert_self _ _
  have hm2 : D.snd ∈ ({D.fst, D.snd} : Finset V) :=
    Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hpr : D.fst ≠ E.fst := fun h => hd hm1 (by rw [h]; exact Finset.mem_insert_self _ _)
  have hps : D.fst ≠ E.snd := fun h => hd hm1 (by
    rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hqr : D.snd ≠ E.fst := fun h => hd hm2 (by rw [h]; exact Finset.mem_insert_self _ _)
  have hqs : D.snd ≠ E.snd := fun h => hd hm2 (by
    rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hc8 : ({u, D.fst, v, D.snd, E.fst, x, E.snd, y} : Finset V).card = 8 :=
    card_eight_of_pairwise_ne
      (Ne.symm D.fst_ne_u) huv (Ne.symm D.snd_ne_u) (Ne.symm E.fst_ne_u) (Ne.symm hxu)
        (Ne.symm E.snd_ne_u) (Ne.symm hyu)
      D.fst_ne_v D.fst_ne_snd hpr (Ne.symm hxp) hps (Ne.symm hyp)
      (Ne.symm D.snd_ne_v) (Ne.symm E.fst_ne_v) (Ne.symm hxv) (Ne.symm E.snd_ne_v) (Ne.symm hyv)
      hqr (Ne.symm hxq) hqs (Ne.symm hyq)
      (Ne.symm hxr) E.fst_ne_snd (Ne.symm hyr)
      hxs hxy (Ne.symm hys)
  have hddl := Finset.disjoint_right.mp hdd
  have hmx' : x' ∈ ({x', y'} : Finset V) := Finset.mem_insert_self _ _
  have hmy' : y' ∈ ({x', y'} : Finset V) :=
    Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hx'nx : x' ≠ x := fun h => hddl hmx' (by rw [h]; exact Finset.mem_insert_self _ _)
  have hx'ny : x' ≠ y := fun h => hddl hmx' (by
    rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hy'nx : y' ≠ x := fun h => hddl hmy' (by rw [h]; exact Finset.mem_insert_self _ _)
  have hy'ny : y' ≠ y := fun h => hddl hmy' (by
    rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  refine ten_le_card_of_two_beyond_octet (x' := x') (y' := y') hc8 ?_ ?_
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hx'u, hx'p, hx'v, hx'q, hx'r, hx'nx, hx's, hx'ny⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hx'y', hy'u, hy'p, hy'v, hy'q, hy'r, hy'nx, hy's, hy'ny⟩

/-! ## Why the route is not yet a detour

A `DetourPorts` at a pair needs five things: the pair dead in its colour, two live arms to its
ports, a certificate on the complement of those four sites, and a dead chord between the ports in
the third colour.  The outward route supplies the first three and neither of the last two.  The
certificate it does supply is on a strictly smaller set, and a matching sum on a subset says
nothing about one on a superset. -/

/-- **Three of the five detour fields, supplied.**  At the routed pair the pair is dead in its own
colour and both arms to the route's destinations are live. -/
theorem routed_pair_dead_with_live_arms {W : Sym2 (V × Fin 3) → ℂ}
    {a k : Fin 3} {u v : V}
    (D : DetourPorts W u v a k) (E : DetourPorts W u v a (thirdColour a k))
    (hdisj : Disjoint ({D.fst, D.snd} : Finset V) ({E.fst, E.snd} : Finset V)) :
    ∃ x y : V, x ≠ y ∧
      W s((E.fst, k), (E.snd, k)) = 0 ∧
      W s((E.fst, k), (x, k)) ≠ 0 ∧
      W s((E.snd, k), (y, k)) ≠ 0 ∧
      pmSum W (Amplitude.const (V := V) k)
        ((Finset.univ : Finset V) \
          ({u, D.fst, v, D.snd, E.fst, x, E.snd, y} : Finset V)) ≠ 0 := by
  classical
  obtain ⟨⟨x, y, -, -, -, -, -, -, -, -, -, -, -, -, hxy, hrx, hsy, hrem⟩, -⟩ :=
    disjoint_detours_force_outward_routes D E hdisj
  have hchordE : W s((E.fst, k), (E.snd, k)) = 0 := by
    have h := E.chord; rw [thirdColour_thirdColour] at h; exact h
  exact ⟨x, y, hxy, hchordE, hrx, hsy, hrem⟩

/-- **The certificate does not transfer upward.**  A non-vanishing matching sum on a subset is
compatible with a vanishing one on a superset, so the route's certificate on the eight-site
complement is not the certificate a detour at the routed pair would need. -/
theorem certificate_does_not_transfer_upward :
    ∃ (W : Sym2 (Fin 2 × Fin 3) → ℂ) (c : Fin 2 → Fin 3) (S T : Finset (Fin 2)),
      S ⊆ T ∧ pmSum W c S ≠ 0 ∧ pmSum W c T = 0 := by
  refine ⟨fun _ => 0, fun _ => 0, ∅, ({0, 1} : Finset (Fin 2)), Finset.empty_subset _, ?_, ?_⟩
  · rw [MatchingSum.pmSum_empty]; exact one_ne_zero
  · rw [MatchingSum.pmSum_pair _ _ (by decide : (1 : Fin 2) ≠ 0)]

/-- **The iteration obstruction.**  Everything the route gives toward a detour at its own pair,
together with the fact that its certificate cannot be lifted.  The two fields a detour still needs
-- a certificate on the four-site complement, and a third-colour chord between the destinations --
are not among them, and no field of the route constrains the chord's edge at all. -/
theorem routing_iteration_obstruction {W : Sym2 (V × Fin 3) → ℂ}
    {a k : Fin 3} {u v : V}
    (D : DetourPorts W u v a k) (E : DetourPorts W u v a (thirdColour a k))
    (hdisj : Disjoint ({D.fst, D.snd} : Finset V) ({E.fst, E.snd} : Finset V)) :
    (∃ x y : V, x ≠ y ∧
      W s((E.fst, k), (E.snd, k)) = 0 ∧
      W s((E.fst, k), (x, k)) ≠ 0 ∧
      W s((E.snd, k), (y, k)) ≠ 0 ∧
      pmSum W (Amplitude.const (V := V) k)
        ((Finset.univ : Finset V) \
          ({u, D.fst, v, D.snd, E.fst, x, E.snd, y} : Finset V)) ≠ 0) ∧
    (∃ (W' : Sym2 (Fin 2 × Fin 3) → ℂ) (c : Fin 2 → Fin 3) (S T : Finset (Fin 2)),
      S ⊆ T ∧ pmSum W' c S ≠ 0 ∧ pmSum W' c T = 0) :=
  ⟨routed_pair_dead_with_live_arms D E hdisj, certificate_does_not_transfer_upward⟩

/-! ## The routing network at an excess site

Everything the monochromatic-block branch forces at a site whose live degree is not three,
assembled.  Each branch is a normal form, not a contradiction: none of them is excluded here. -/

theorem excess_site_routing_network (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : IsSupportMinimal W)
    (hmono : ∀ (p q : V), q ≠ p → ∀ i j : Fin 3, i ≠ j → W s((p, i), (q, j)) = 0)
    (hcard : 4 < Fintype.card V)
    {u : V} (hdeg : (liveNbrs W u).card ≠ 3) :
    ∃ v ∈ liveNbrs W u, ∃ c : V → Fin 3, c v = c u ∧
      W s((u, c u), (v, c u)) ≠ 0 ∧
      ∀ k : Fin 3, k ≠ c u →
        TransportedCrossing W c u v k
          ∨ TransportedCrossing W c u v (thirdColour (c u) k)
          ∨ SomeSizeOneCircuit W u v
          ∨ (∃ D : DetourPorts W u v (c u) k,
              ∃ E : DetourPorts W u v (c u) (thirdColour (c u) k),
                (CrossedOnePortCap W u v (c u) k D.fst D.snd E.fst ∧
                    Nonempty (CrossedCapTails W u v (c u) k D.fst D.snd E.fst))
                  ∨ (CrossedOnePortCap W v u (c u) k D.snd D.fst E.snd ∧
                      Nonempty (CrossedCapTails W v u (c u) k D.snd D.fst E.snd)))
          ∨ (∃ D : DetourPorts W u v (c u) k,
              ∃ E : DetourPorts W u v (c u) (thirdColour (c u) k),
                Disjoint ({D.fst, D.snd} : Finset V) ({E.fst, E.snd} : Finset V)
                  ∧ OutwardRoutes D E
                  ∧ 8 ≤ Fintype.card V) := by
  obtain ⟨v, hv, c, hcv, hentry, hfork⟩ :=
    excess_site_receiving_pair_routed W hmin hmono hcard hdeg
  refine ⟨v, hv, c, hcv, hentry, fun k hk => ?_⟩
  rcases hfork k hk with h | h | h | ⟨D, E, hcap⟩ | hroute
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨D, E, ?_⟩)))
    rcases hcap with hc | hc
    · exact Or.inl ⟨hc, exists_crossedCapTails hc⟩
    · exact Or.inr ⟨hc, exists_crossedCapTails hc⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr hroute)))

/-! ## Recolouring relations at a live pair

Colour a live pair in its own colour and everything else in one other colour.  The colouring is
non-constant, so its amplitude vanishes; under monochromatic blocks that amplitude is the product of
three fibre sums, of which the pair's is its own live weight and the third colour's is the empty
sum.  The remaining factor must therefore vanish: **a live pair kills every other colour on its
complement.**  This needs no detour, no cap and no route -- only the live pair. -/

theorem live_pair_annihilates_complement (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : IsSupportMinimal W)
    (hmono : ∀ (x y : V), y ≠ x → ∀ i j : Fin 3, i ≠ j → W s((x, i), (y, j)) = 0)
    {a k : Fin 3} (hak : a ≠ k) {u v : V} (huv : u ≠ v)
    (hlive : W s((u, a), (v, a)) ≠ 0)
    (hout : ∃ z : V, z ∉ ({u, v} : Finset V)) :
    pmSum W (Amplitude.const (V := V) k)
      ((Finset.univ : Finset V) \ ({u, v} : Finset V)) = 0 := by
  classical
  obtain ⟨z₀, hz₀⟩ := hout
  set c : V → Fin 3 := fun z => if z ∈ ({u, v} : Finset V) then a else k with hc
  have hcu : c u = a := by simp [hc]
  have hcv : c v = a := by simp [hc]
  have hcz : c z₀ = k := by simp only [hc]; exact if_neg hz₀
  have hnc : ¬ Amplitude.Monochromatic c := by
    rintro ⟨m, hm⟩
    exact hak (by rw [← hcu, hm u, ← hm z₀, hcz])
  have hfa : NoCancellation.fiber c a = ({u, v} : Finset V) := by
    ext w
    simp only [NoCancellation.mem_fiber, hc]
    by_cases hw : w ∈ ({u, v} : Finset V) <;> simp [hw, Ne.symm hak]
  have hfk : NoCancellation.fiber c k = (Finset.univ : Finset V) \ ({u, v} : Finset V) := by
    ext w
    simp only [NoCancellation.mem_fiber, Finset.mem_sdiff, Finset.mem_univ, true_and, hc]
    by_cases hw : w ∈ ({u, v} : Finset V) <;> simp [hw, hak]
  have hfo : ∀ m : Fin 3, m ≠ a → m ≠ k → NoCancellation.fiber c m = (∅ : Finset V) := by
    intro m hma hmk
    ext w
    simp only [NoCancellation.mem_fiber, Finset.notMem_empty, iff_false, hc]
    by_cases hw : w ∈ ({u, v} : Finset V) <;> simp [hw, Ne.symm hma, Ne.symm hmk]
  by_contra hne
  refine fibre_zero_of_others W hmin hmono hnc ?_
  intro m
  by_cases hma : m = a
  · subst hma; rw [hfa, MatchingSum.pmSum_pair W _ (Ne.symm huv)]; exact hlive
  by_cases hmk : m = k
  · subst hmk; rw [hfk]; exact hne
  · rw [hfo m hma hmk, MatchingSum.pmSum_empty]; exact one_ne_zero

/-- **The octet's recolouring relations.**  At the synchronized octet the live pair in its own
colour kills both receiving colours on the six remaining sites. -/
theorem octet_ghz_relations (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : IsSupportMinimal W)
    (hmono : ∀ (x y : V), y ≠ x → ∀ i j : Fin 3, i ≠ j → W s((x, i), (y, j)) = 0)
    (hcard : 4 < Fintype.card V)
    {a k : Fin 3} (hak : a ≠ k) {u v : V} (huv : u ≠ v)
    (hlive : W s((u, a), (v, a)) ≠ 0) :
    pmSum W (Amplitude.const (V := V) k)
        ((Finset.univ : Finset V) \ ({u, v} : Finset V)) = 0 ∧
      pmSum W (Amplitude.const (V := V) (thirdColour a k))
        ((Finset.univ : Finset V) \ ({u, v} : Finset V)) = 0 := by
  classical
  have hout : ∃ z : V, z ∉ ({u, v} : Finset V) := by
    by_contra hcon
    push_neg at hcon
    have hsub : (Finset.univ : Finset V) ⊆ ({u, v} : Finset V) := fun z _ => hcon z
    have : Fintype.card V ≤ 2 := by
      calc Fintype.card V = (Finset.univ : Finset V).card := (Finset.card_univ).symm
        _ ≤ ({u, v} : Finset V).card := Finset.card_le_card hsub
        _ ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
    omega
  exact ⟨live_pair_annihilates_complement W hmin hmono hak huv hlive hout,
    live_pair_annihilates_complement W hmin hmono
      (Ne.symm (thirdColour_ne_left hak)) huv hlive hout⟩

end StarNormalForm
