import Mathlib
import FermiSix

/-!
# Krenn–Gu for fermionic systems, and for Pfaffian live graphs

**Fermionic Krenn–Gu** (`krennGu_fermi`): over every infinite field, no ordered set of `2n ≥ 6`
sites carries a fermionic GHZ system.  Descent to six sites is exact for signed matching sums in
every characteristic (`descent`), and six sites are impossible (`no_isFermiGHZ_six`).

**Pfaffian live graphs** (`not_isGHZOver_of_pfaffian`): give each pair of sites a sign.  If every
perfect matching of the live pairs gets the same total sign (its matching sign times the signs of
its pairs), the unsigned matching sum is, up to that sign, the signed matching sum of the signed
weights.  A GHZ system with such a live graph therefore yields a fermionic one, which cannot
exist.

The signed matching sum here is the Pfaffian of the skew matrix read from the smaller site to the
larger one: its recursion is the Pfaffian's expansion along the first row, and `msgn` is the sign
of a matching in that expansion.  By Kasteleyn's theorem, not formalized here, every planar graph
admits such signs.  So Krenn–Gu holds for every GHZ system with a planar live graph, over ℂ, for
every even number of sites from six on, including bicoloured entries and several entries per
pair.

**Class-coherent signs** (`not_isGHZOver_of_coherentSigns`): the same argument needs far less.
Put the signs on the entries, and ask only that all perfect matchings live in one colouring share
their total sign; different colourings may have different signs.
-/

namespace KrennFermi

open Amplitude MatchingSum MatchingPfaffian MatchingBlockRank KrennCharTwo

variable {F : Type*} [Field F]

/-- **Fermionic Krenn–Gu.**  Over an infinite field, no fermionic GHZ system exists on `2n` sites
for any `n ≥ 3`, whatever the order of the sites. -/
theorem krennGu_fermi [Infinite F] :
    ∀ n : ℕ, 3 ≤ n → ∀ (V : Type) [Fintype V] [DecidableEq V] [LinearOrder V],
      Fintype.card V = 2 * n → ∀ W : Sym2 (V × Fin 3) → F, ¬ IsFermiGHZ W :=
  no_isFermiGHZ_of_six no_isFermiGHZ_six

section Signs

variable {V C R : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] [CommRing R]

/-- **The sign of a matching**, read off the same recursion as the signed matching sum: the
smallest site `m` of `S` is matched to `σ m`, contributing `(-1) ^ (pos S (σ m) + 1)`. -/
noncomputable def msgn (σ : Equiv.Perm V) (S : Finset V) : R :=
  if h : S.Nonempty then
    (-1) ^ (pos S (σ (S.min' h)) + 1) * msgn σ ((S.erase (S.min' h)).erase (σ (S.min' h)))
  else 1
termination_by S.card
decreasing_by
  exact lt_of_le_of_lt Finset.card_erase_le (Finset.card_erase_lt_of_mem (S.min'_mem h))

omit [Fintype V] in
theorem msgn_min (σ : Equiv.Perm V) {S : Finset V} {u : V} (hu : u ∈ S)
    (hmin : ∀ w ∈ S, u ≤ w) :
    (msgn σ S : R) = (-1) ^ (pos S (σ u) + 1) * msgn σ ((S.erase u).erase (σ u)) := by
  have h : S.Nonempty := ⟨u, hu⟩
  have hm : S.min' h = u := le_antisymm (Finset.min'_le S u hu) (hmin _ (S.min'_mem h))
  rw [msgn, dif_pos h, hm]

omit [Fintype V] in
/-- The sign of a matching of `S` depends only on the matching inside `S`. -/
theorem msgn_congr {σ τ : Equiv.Perm V} {S : Finset V} (h : ∀ x ∈ S, σ x = τ x) :
    (msgn σ S : R) = msgn τ S := by
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | _ n ih =>
  rcases S.eq_empty_or_nonempty with hS | hne
  · subst hS; simp [msgn]
  have hm := S.min'_mem hne
  have hmin : ∀ w ∈ S, S.min' hne ≤ w := fun w hw => Finset.min'_le S w hw
  rw [msgn_min σ hm hmin, msgn_min τ hm hmin, h _ hm]
  have hlt : ((S.erase (S.min' hne)).erase (τ (S.min' hne))).card < n := by
    rw [← hn]
    exact lt_of_le_of_lt Finset.card_erase_le (Finset.card_erase_lt_of_mem hm)
  rw [ih _ hlt (fun x hx => h x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))) rfl]

/-- **The signed matching sum is the sum over matchings, each with its sign.** -/
theorem pfSum_eq_sum_msgn (W : Sym2 (V × C) → R) (c : V → C) (S : Finset V) :
    pfSum W c S = ∑ σ ∈ pairingsOn S, msgn σ S *
      ∏ e ∈ S.image (fun x => s(x, σ x)), W (Sym2.map (paint c) e) := by
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | _ n ih =>
  rcases S.eq_empty_or_nonempty with hS | hne
  · subst hS
    rw [pfSum_empty, pairingsOn_empty, Finset.sum_singleton]
    simp [msgn]
  set m := S.min' hne with hmdef
  have hm : m ∈ S := S.min'_mem hne
  have hmin : ∀ w ∈ S, m ≤ w := fun w hw => Finset.min'_le S w hw
  rw [pfSum_min W c hm hmin]
  have hmaps : ∀ σ ∈ pairingsOn S, σ m ∈ S.erase m := by
    intro σ hσ
    obtain ⟨-, hne', -⟩ := mem_pairingsOn.mp hσ
    exact Finset.mem_erase.mpr ⟨hne' m hm, pairingsOn_closed hσ m hm⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun v hv => ?_
  obtain ⟨hvm, hvS⟩ := Finset.mem_erase.mp hv
  have hlt : ((S.erase m).erase v).card < n := by
    rw [← hn]
    exact lt_of_le_of_lt Finset.card_erase_le (Finset.card_erase_lt_of_mem hm)
  rw [ih _ hlt _ rfl, filter_eq_image_mul_swap hm hvS (Ne.symm hvm),
    Finset.sum_image (fun _ _ _ _ h => mul_right_cancel h), Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ hτ => ?_
  have hσm : (τ * Equiv.swap m v) m = v := (mul_swap_mem_of_erase hτ hm hvS (Ne.symm hvm)).2
  rw [prod_mul_swap W c hτ hm hvS, msgn_min _ hm hmin, hσm,
    msgn_congr (σ := τ * Equiv.swap m v) (τ := τ) (fun x hx => by
      have hxv : x ≠ v := (Finset.mem_erase.mp hx).1
      have hxm : x ≠ m := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hx)).1
      exact mul_swap_apply_other hxm hxv)]
  ring

end Signs

section Pfaffian

variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- The weights with each pair of sites multiplied by its sign. -/
def signW (sg : Sym2 V → F) (W : Sym2 (V × Fin 3) → F) : Sym2 (V × Fin 3) → F :=
  fun z => sg (Sym2.map Prod.fst z) * W z

/-- **A Pfaffian orientation of the live graph**: signs on the pairs, and a nonzero `ε`, such
that every perfect matching whose pairs are all live has total sign `ε`, where the total sign is
the matching sign times the signs of its pairs. -/
def PfaffianSigns (W : Sym2 (V × Fin 3) → F) (sg : Sym2 V → F) (ε : F) : Prop :=
  ε ≠ 0 ∧ ∀ σ ∈ pairingsOn (Finset.univ : Finset V),
    (∀ x, ∃ a b : Fin 3, W s((x, a), (σ x, b)) ≠ 0) →
      msgn σ Finset.univ * ∏ e ∈ (Finset.univ : Finset V).image (fun x => s(x, σ x)), sg e = ε

/-- **With Pfaffian signs, the signed sum of the signed weights is `ε` times the amplitude.** -/
theorem pfSum_signW (W : Sym2 (V × Fin 3) → F) {sg : Sym2 V → F} {ε : F}
    (h : PfaffianSigns W sg ε) (c : V → Fin 3) :
    pfSum (signW sg W) c Finset.univ = ε * amplitude W c := by
  classical
  rw [pfSum_eq_sum_msgn, ← pmSum_univ, pmSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  have hsplit : ∏ e ∈ (Finset.univ : Finset V).image (fun x => s(x, σ x)),
      signW sg W (Sym2.map (paint c) e)
        = (∏ e ∈ (Finset.univ : Finset V).image (fun x => s(x, σ x)), sg e) *
          ∏ e ∈ (Finset.univ : Finset V).image (fun x => s(x, σ x)), W (Sym2.map (paint c) e) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun e _ => ?_
    unfold signW
    congr 2
    induction e using Sym2.ind with
    | h x y => simp [paint]
  rw [hsplit]
  by_cases hz : ∏ e ∈ (Finset.univ : Finset V).image (fun x => s(x, σ x)),
      W (Sym2.map (paint c) e) = 0
  · rw [hz]; ring
  · have hlive : ∀ x, ∃ a b : Fin 3, W s((x, a), (σ x, b)) ≠ 0 := by
      intro x
      refine ⟨c x, c (σ x), fun h0 => hz (Finset.prod_eq_zero
        (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩) ?_)⟩
      exact h0
    rw [← mul_assoc, h.2 σ hσ hlive]

/-- **Krenn–Gu for Pfaffian live graphs.**  Over an infinite field, a GHZ system on `2n ≥ 6`
sites whose live graph carries Pfaffian signs does not exist.  No assumption on the
characteristic, on bicoloured entries, or on the number of entries per pair. -/
theorem not_isGHZOver_of_pfaffian [Infinite F] {n : ℕ} (hn : 3 ≤ n)
    (hV : Fintype.card V = 2 * n) {W : Sym2 (V × Fin 3) → F} (hW : IsGHZOver W)
    {sg : Sym2 V → F} {ε : F} (hP : PfaffianSigns W sg ε) : False := by
  refine krennGu_fermi n hn V hV (signW sg W) ⟨fun k => ?_, fun c hc => ?_⟩
  · rw [pfSum_signW W hP]
    exact mul_ne_zero hP.1 (hW.1 k)
  · rw [pfSum_signW W hP, hW.2 c hc, mul_zero]

/-- The weights with each entry multiplied by its sign. -/
def entrySignW (sg : Sym2 (V × Fin 3) → F) (W : Sym2 (V × Fin 3) → F) :
    Sym2 (V × Fin 3) → F :=
  fun z => sg z * W z

/-- **Class-coherent signs**: signs on the entries and, for every colouring `c`, a nonzero
`ε c`, such that every perfect matching live in the colouring `c` has total sign `ε c` (its
matching sign times the signs of the entries it uses in `c`).  Pfaffian signs are the special
case of signs depending only on the pair and one `ε` for all colourings. -/
def CoherentSigns (W : Sym2 (V × Fin 3) → F) (sg : Sym2 (V × Fin 3) → F)
    (ε : (V → Fin 3) → F) : Prop :=
  (∀ c, ε c ≠ 0) ∧ ∀ c : V → Fin 3, ∀ σ ∈ pairingsOn (Finset.univ : Finset V),
    (∀ x, W s((x, c x), (σ x, c (σ x))) ≠ 0) →
      msgn σ Finset.univ * ∏ e ∈ (Finset.univ : Finset V).image (fun x => s(x, σ x)),
        sg (Sym2.map (paint c) e) = ε c

/-- **With class-coherent signs, each signed matching sum is `ε c` times the amplitude.** -/
theorem pfSum_entrySignW (W : Sym2 (V × Fin 3) → F) {sg : Sym2 (V × Fin 3) → F}
    {ε : (V → Fin 3) → F} (h : CoherentSigns W sg ε) (c : V → Fin 3) :
    pfSum (entrySignW sg W) c Finset.univ = ε c * amplitude W c := by
  classical
  rw [pfSum_eq_sum_msgn, ← pmSum_univ, pmSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  have hsplit : ∏ e ∈ (Finset.univ : Finset V).image (fun x => s(x, σ x)),
      entrySignW sg W (Sym2.map (paint c) e)
        = (∏ e ∈ (Finset.univ : Finset V).image (fun x => s(x, σ x)),
            sg (Sym2.map (paint c) e)) *
          ∏ e ∈ (Finset.univ : Finset V).image (fun x => s(x, σ x)),
            W (Sym2.map (paint c) e) := by
    rw [← Finset.prod_mul_distrib]
    rfl
  rw [hsplit]
  by_cases hz : ∏ e ∈ (Finset.univ : Finset V).image (fun x => s(x, σ x)),
      W (Sym2.map (paint c) e) = 0
  · rw [hz]; ring
  · have hlive : ∀ x, W s((x, c x), (σ x, c (σ x))) ≠ 0 := by
      intro x h0
      exact hz (Finset.prod_eq_zero (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩) h0)
    rw [← mul_assoc, h.2 c σ hσ hlive]

/-- **Krenn–Gu for class-coherent signs.**  Over an infinite field, a GHZ system on `2n ≥ 6`
sites admitting class-coherent signs does not exist: the signed weights would form a fermionic
GHZ system.  This contains `not_isGHZOver_of_pfaffian`, and only asks for one common sign inside
each colouring class. -/
theorem not_isGHZOver_of_coherentSigns [Infinite F] {n : ℕ} (hn : 3 ≤ n)
    (hV : Fintype.card V = 2 * n) {W : Sym2 (V × Fin 3) → F} (hW : IsGHZOver W)
    {sg : Sym2 (V × Fin 3) → F} {ε : (V → Fin 3) → F} (hC : CoherentSigns W sg ε) : False := by
  refine krennGu_fermi n hn V hV (entrySignW sg W) ⟨fun k => ?_, fun c hc => ?_⟩
  · rw [pfSum_entrySignW W hC]
    exact mul_ne_zero (hC.1 _) (hW.1 k)
  · rw [pfSum_entrySignW W hC, hW.2 c hc, mul_zero]

end Pfaffian

end KrennFermi
