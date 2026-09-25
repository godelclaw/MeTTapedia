import Mathlib
import Mettapedia.Combinatorics.Matching.TightCut
import CharTwoRigidity

/-!
# Collapsing a shore of a GHZ system

Call the cut around a set `S` of sites *shore-tight* when, at every colouring that is constant
off `S`, the matchings crossing it more than once contribute nothing.  This happens whenever the
cut is tight, crossed exactly once by every perfect matching of the pairs that carry weight.  Then
collapsing the complement of `S` to one site (`MatchingTightCut.shoreContract`) turns a GHZ system
into a GHZ system on `|S| + 1` sites with the same constant amplitudes (`isGHZOver_shoreContract`).

The collapse is exact in every characteristic.  Removing a pair of sites instead, and folding its
edges into the rest, is exact only when `2 = 0`: over other fields it fails by the matchings that
use the removed pair twice.  A tight cut rules those matchings out by itself.

Two consequences for a smallest counterexample:
- a shore-tight cut with at least five sites on the kept side produces a smaller one;
- at six sites, two shore-tight triangles are impossible outright (`false_of_shoreTight_six`).
  Both collapses are four-site systems, hence rigid, and that rigidity leaves a colouring with a
  single contributing matching.
-/

namespace KrennTightCut

open Amplitude MatchingSum MatchingTightCut KrennCharTwo

variable {F : Type*} [Field F]

/-- The cut around `S` is **shore-tight** when, at every colouring that is constant off `S`, the
whole amplitude is carried by the matchings crossing the cut exactly once. -/
def ShoreTight {V : Type} [Fintype V] [DecidableEq V] (W : Sym2 (V × Fin 3) → F)
    (S : Finset V) : Prop :=
  ∀ (cS : ↥S → Fin 3) (k : Fin 3), amplitude W (glue S cS k) = crossOne W S (glue S cS k)

section Collapse

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Collapsing a shore-tight complement keeps a GHZ system.**  The collapsed system lives on the
sites of `S` plus one, and its amplitudes are those of the original at the colourings constant off
`S`. -/
theorem isGHZOver_shoreContract {W : Sym2 (V × Fin 3) → F} (hW : IsGHZOver W) {S : Finset V}
    (hS : (Finset.univ \ S).Nonempty) (ht : ShoreTight W S) :
    IsGHZOver (shoreContract W S) := by
  have key : ∀ c' : Option ↥S → Fin 3, amplitude (shoreContract W S) c'
      = amplitude W (glue S (fun s => c' (some s)) (c' none)) := by
    intro c'
    have h1 := amplitude_shoreContract W S (fun s => c' (some s)) (c' none)
    have hc' : (fun o : Option ↥S => o.elim (c' none) (fun s => c' (some s))) = c' := by
      funext o
      cases o <;> rfl
    rw [hc'] at h1
    rw [h1, ht]
  obtain ⟨t, htS⟩ := hS
  have htS' : t ∉ S := (Finset.mem_sdiff.mp htS).2
  refine ⟨fun k => ?_, fun c' hc' => ?_⟩
  · rw [key]
    have hconst : glue S (fun s => (Amplitude.const k : Option ↥S → Fin 3) (some s))
        ((Amplitude.const k : Option ↥S → Fin 3) none) = Amplitude.const (V := V) k := by
      funext v
      by_cases hv : v ∈ S
      · rw [glue_of_mem _ _ hv]
        rfl
      · rw [glue_of_not_mem _ _ hv]
        rfl
    rw [hconst]
    exact hW.1 k
  · rw [key]
    refine hW.2 _ (fun ⟨m, hm⟩ => hc' ⟨m, fun o => ?_⟩)
    have hk : c' none = m := by
      have := hm t
      rwa [glue_of_not_mem _ _ htS'] at this
    cases o with
    | none => exact hk
    | some s =>
      have := hm s
      rwa [glue_of_mem _ _ s.2] at this

end Collapse

section Four

/-- **A four-site GHZ system seen from one site.**  Over an infinite field the three colours at a
site `p` go to three different partners, each along a single diagonal entry, every nonzero weight
at `p` is one of those three, and the partner of colour `k` carries no weight of colour `k` to
the two remaining sites. -/
theorem four_star [Infinite F] {U : Type} [Fintype U] [DecidableEq U] (hU : Fintype.card U = 4)
    {W : Sym2 (U × Fin 3) → F} (hW : IsGHZOver W) (p : U) :
    ∃ σ : Fin 3 → U, Function.Injective σ ∧ (∀ k, σ k ≠ p) ∧
      (∀ k, W s((p, k), (σ k, k)) ≠ 0) ∧
      (∀ q a b, q ≠ p → W s((p, a), (q, b)) ≠ 0 → a = b ∧ q = σ a) ∧
      (∀ k v, v ≠ p → v ≠ σ k → W s((σ k, k), (v, k)) = 0) := by
  classical
  have hrig : FourRigid F := fourRigid
  obtain ⟨hdiag, hone⟩ := hrig U hU W hW
  have hsw : ∀ (u v : U) (a b : Fin 3), W s((u, a), (v, b)) = W s((v, b), (u, a)) :=
    fun _ _ _ _ => congrArg W Sym2.eq_swap
  have h3 : ((Finset.univ : Finset U).erase p).card = 3 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, hU]
  obtain ⟨b, x, y, hbx, hby, hxy, hbxy⟩ := Finset.card_eq_three.mp h3
  have hin : ∀ z, z ∈ ({b, x, y} : Finset U) → z ≠ p := by
    intro z hz
    rw [← hbxy] at hz
    exact (Finset.mem_erase.mp hz).1
  have hbp : b ≠ p := hin b (by simp)
  have hxp : x ≠ p := hin x (by simp)
  have hyp : y ≠ p := hin y (by simp)
  have hmem : ∀ z, z ≠ p → z = b ∨ z = x ∨ z = y := by
    intro z hz
    have : z ∈ (Finset.univ : Finset U).erase p := Finset.mem_erase.mpr ⟨hz, Finset.mem_univ z⟩
    rw [hbxy] at this
    simpa using this
  have huniv : (Finset.univ : Finset U) = {p, b, x, y} := by
    rw [← hbxy, Finset.insert_erase (Finset.mem_univ p)]
  obtain ⟨π, ⟨h0a, h0b⟩, ⟨h1a, h1b⟩, ⟨h2a, h2b⟩⟩ :=
    k4_shape hrig hU hW (Ne.symm hbp) (Ne.symm hxp) (Ne.symm hyp) hbx hby hxy huniv
  have hπ01 : π 0 ≠ π 1 := π.injective.ne (by decide)
  have hπ02 : π 0 ≠ π 2 := π.injective.ne (by decide)
  have hπ12 : π 1 ≠ π 2 := π.injective.ne (by decide)
  let σ : Fin 3 → U := fun k => if k = π 0 then b else if k = π 1 then x else y
  have hσ0 : σ (π 0) = b := if_pos rfl
  have hσ1 : σ (π 1) = x := by
    show (if π 1 = π 0 then b else if π 1 = π 1 then x else y) = x
    rw [if_neg hπ01.symm, if_pos rfl]
  have hσ2 : σ (π 2) = y := by
    show (if π 2 = π 0 then b else if π 2 = π 1 then x else y) = y
    rw [if_neg hπ02.symm, if_neg hπ12.symm]
  have hcases : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  refine ⟨σ, ?_, ?_, ?_, ?_, ?_⟩
  · intro k₁ k₂ h
    obtain ⟨i, rfl⟩ := π.surjective k₁
    obtain ⟨j, rfl⟩ := π.surjective k₂
    rcases hcases i with rfl | rfl | rfl <;> rcases hcases j with rfl | rfl | rfl <;>
      first
        | rfl
        | (rw [hσ0, hσ1] at h; exact absurd h hbx)
        | (rw [hσ0, hσ2] at h; exact absurd h hby)
        | (rw [hσ1, hσ0] at h; exact absurd h.symm hbx)
        | (rw [hσ1, hσ2] at h; exact absurd h hxy)
        | (rw [hσ2, hσ0] at h; exact absurd h.symm hby)
        | (rw [hσ2, hσ1] at h; exact absurd h.symm hxy)
  · intro k
    obtain ⟨i, rfl⟩ := π.surjective k
    rcases hcases i with rfl | rfl | rfl
    · rw [hσ0]; exact hbp
    · rw [hσ1]; exact hxp
    · rw [hσ2]; exact hyp
  · intro k
    obtain ⟨i, rfl⟩ := π.surjective k
    rcases hcases i with rfl | rfl | rfl
    · rw [hσ0]; exact h0a
    · rw [hσ1]; exact h1a
    · rw [hσ2]; exact h2a
  · intro q a a' hq hw
    have haa : a = a' := by
      by_contra hne
      exact hw (hdiag p q (Ne.symm hq) a a' hne)
    subst haa
    refine ⟨rfl, ?_⟩
    rcases hmem q hq with hqb | hqx | hqy
    · rw [hqb] at hw ⊢
      have : a = π 0 := by
        by_contra hne
        rcases hone p b (Ne.symm hbp) a (π 0) hne with h | h
        · exact hw h
        · exact h0a h
      rw [this, hσ0]
    · rw [hqx] at hw ⊢
      have : a = π 1 := by
        by_contra hne
        rcases hone p x (Ne.symm hxp) a (π 1) hne with h | h
        · exact hw h
        · exact h1a h
      rw [this, hσ1]
    · rw [hqy] at hw ⊢
      have : a = π 2 := by
        by_contra hne
        rcases hone p y (Ne.symm hyp) a (π 2) hne with h | h
        · exact hw h
        · exact h2a h
      rw [this, hσ2]
  · intro k v hvp hvk
    obtain ⟨i, rfl⟩ := π.surjective k
    rcases hcases i with rfl | rfl | rfl
    · rw [hσ0] at hvk ⊢
      rcases hmem v hvp with hv | hv | hv
      · exact absurd hv hvk
      · rw [hv]
        rcases hone b x hbx (π 0) (π 2) hπ02 with h | h
        · exact h
        · exact absurd h h2b
      · rw [hv]
        rcases hone b y hby (π 0) (π 1) hπ01 with h | h
        · exact h
        · exact absurd h h1b
    · rw [hσ1] at hvk ⊢
      rcases hmem v hvp with hv | hv | hv
      · rw [hv]
        rcases hone x b (Ne.symm hbx) (π 1) (π 2) hπ12 with h | h
        · exact h
        · exact absurd (by rw [hsw]; exact h) h2b
      · exact absurd hv hvk
      · rw [hv]
        rcases hone x y hxy (π 1) (π 0) hπ01.symm with h | h
        · exact h
        · exact absurd h h0b
    · rw [hσ2] at hvk ⊢
      rcases hmem v hvp with hv | hv | hv
      · rw [hv]
        rcases hone y b (Ne.symm hby) (π 2) (π 1) hπ12.symm with h | h
        · exact h
        · exact absurd (by rw [hsw]; exact h) h1b
      · rw [hv]
        rcases hone y x (Ne.symm hxy) (π 2) (π 0) hπ02.symm with h | h
        · exact h
        · exact absurd (by rw [hsw]; exact h) h0b
      · exact absurd hv hvk

end Four

section Six

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Six sites: two shore-tight triangles are impossible.**  Collapsing the complement of either
triangle gives a four-site GHZ system, which is rigid (`fourRigid`).
- The collapse keeping `S` makes that triangle's entries diagonal, and sends colour `k` at the
  collapsed site to a single site `s k`.
- The other collapse sends colour `k` at its collapsed site to a single site `t k`, and no pair of
  that triangle through `t k` carries colour `k`.

Hence the weight from `s i` coloured `i` to `t j` coloured `j` vanishes unless `i = j`, while each
rung `s k t k` in colour `k` does not.  Colour each `s k` and `t k` with `k`: that colouring is
mixed, and its only contributing matching is the three rungs. -/
theorem false_of_shoreTight_six [Infinite F] {W : Sym2 (V × Fin 3) → F} (hW : IsGHZOver W)
    (hV : Fintype.card V = 6) {S : Finset V} (hS : S.card = 3)
    (htS : ShoreTight W S) (htT : ShoreTight W (Finset.univ \ S)) : False := by
  classical
  have hT : (Finset.univ \ S).card = 3 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, hV, hS]
  have hTS : Finset.univ \ (Finset.univ \ S) = S := Finset.sdiff_sdiff_eq_self (Finset.subset_univ S)
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hTne : (Finset.univ \ S).Nonempty := Finset.card_pos.mp (by omega)
  have hW₁ : IsGHZOver (shoreContract W S) := isGHZOver_shoreContract hW hTne htS
  have hW₂ : IsGHZOver (shoreContract W (Finset.univ \ S)) :=
    isGHZOver_shoreContract hW (by rw [hTS]; exact hSne) htT
  have hc₁ : Fintype.card (Option ↥S) = 4 := by simp [hS]
  have hc₂ : Fintype.card (Option ↥(Finset.univ \ S)) = 4 := by
    rw [Fintype.card_option, Fintype.card_coe, hT]
  obtain ⟨σ, hσinj, hσne, hσlive, hσstar, -⟩ := four_star hc₁ hW₁ none
  obtain ⟨τ, hτinj, hτne, -, -, hτopp⟩ := four_star hc₂ hW₂ none
  obtain ⟨hdiag₁, -⟩ := (fourRigid : FourRigid F) (Option ↥S) hc₁ _ hW₁
  choose s hs using fun k => Option.ne_none_iff_exists'.mp (hσne k)
  choose t ht using fun k => Option.ne_none_iff_exists'.mp (hτne k)
  -- facts about the named sites
  have hsinj : Function.Injective s := fun i j h => hσinj (by rw [hs i, hs j, h])
  have hsbij : Function.Bijective s :=
    (Fintype.bijective_iff_injective_and_card s).mpr
      ⟨hsinj, by rw [Fintype.card_fin, Fintype.card_coe, hS]⟩
  have htS : ∀ k, ((t k : V)) ∉ S := fun k => (Finset.mem_sdiff.mp (t k).2).2
  have hst : ∀ i j, ((s i : V)) ≠ (t j : V) := fun i j h => htS j (h ▸ (s i).2)
  have hss : ∀ i j, i ≠ j → ((s i : V)) ≠ (s j : V) :=
    fun i j hij h => hij (hsinj (Subtype.ext h))
  -- the colour-`k` pair of the far triangle avoids `t k`
  have hfar : ∀ (k : Fin 3) (v : V), v ∈ Finset.univ \ S → v ≠ (t k : V) →
      W s(((t k : V), k), (v, k)) = 0 := by
    intro k v hv hvk
    have h := hτopp k (some ⟨v, hv⟩) (Option.some_ne_none _)
      (by rw [ht k]; exact fun h => hvk (congrArg Subtype.val (Option.some_injective _ h)))
    rw [ht k, shoreContract_some_some] at h
    exact h
  -- a kept site reaches the collapsed site through `t k` alone
  have hsum : ∀ (u : V) (a k : Fin 3), shoreWeight W S u a k
      = W s((u, a), ((t k : V), k)) * pmSum W (fun _ => k) ((Finset.univ \ S).erase (t k)) := by
    intro u a k
    rw [shoreWeight]
    refine Finset.sum_eq_single_of_mem ((t k : V)) (t k).2 (fun t' ht' hne => ?_)
    rw [pmSum_eq_zero_of_isolated W (fun _ => k) (u := (t k : V))
      (Finset.mem_erase.mpr ⟨fun h => hne h.symm, (t k).2⟩) ?_, mul_zero]
    intro v hv
    exact hfar k v (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hv))
      (Finset.mem_erase.mp hv).1
  -- the rungs are live, and they are the only cross weights at `t k` in colour `k`
  have hrung : ∀ k, W s(((s k : V), k), ((t k : V), k)) ≠ 0 := by
    intro k h
    have hl := hσlive k
    rw [hs k, shoreContract_none_some, hsum, h, zero_mul] at hl
    exact hl rfl
  have hcross : ∀ (i j : Fin 3), W s(((s i : V), i), ((t j : V), j)) ≠ 0 → i = j := by
    intro i j hw
    have hP : pmSum W (fun _ => j) ((Finset.univ \ S).erase (t j)) ≠ 0 := by
      intro h
      have hl := hσlive j
      rw [hs j, shoreContract_none_some, hsum, h, mul_zero] at hl
      exact hl rfl
    have hsw : shoreWeight W S (s i) i j ≠ 0 := by
      rw [hsum]
      exact mul_ne_zero hw hP
    have := hσstar (some (s i)) j i (Option.some_ne_none _)
      (by rw [shoreContract_none_some]; exact hsw)
    exact this.1.symm
  -- the rung colouring
  have htinj : Function.Injective t := fun i j h => hτinj (by rw [ht i, ht j, h])
  have htbij : Function.Bijective t :=
    (Fintype.bijective_iff_injective_and_card t).mpr
      ⟨htinj, by rw [Fintype.card_fin, Fintype.card_coe, hT]⟩
  have htt : ∀ i j, i ≠ j → ((t i : V)) ≠ (t j : V) :=
    fun i j hij h => hij (htinj (Subtype.ext h))
  let es := Equiv.ofBijective s hsbij
  let et := Equiv.ofBijective t htbij
  let c : V → Fin 3 := fun v =>
    if h : v ∈ S then es.symm ⟨v, h⟩ else et.symm ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, h⟩⟩
  have hcs : ∀ k, c (s k) = k := by
    intro k
    show (if h : ((s k : V)) ∈ S then es.symm ⟨_, h⟩ else _) = k
    rw [dif_pos (s k).2]
    exact es.symm_apply_apply k
  have hct : ∀ k, c (t k) = k := by
    intro k
    show (if h : ((t k : V)) ∈ S then es.symm ⟨_, h⟩ else _) = k
    rw [dif_neg (htS k)]
    exact et.symm_apply_apply k
  have henum : ∀ w : V, (∃ j, (s j : V) = w) ∨ (∃ j, (t j : V) = w) := by
    intro w
    by_cases hw : w ∈ S
    · obtain ⟨j, hj⟩ := hsbij.2 ⟨w, hw⟩
      exact Or.inl ⟨j, congrArg Subtype.val hj⟩
    · obtain ⟨j, hj⟩ := htbij.2 ⟨w, Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hw⟩⟩
      exact Or.inr ⟨j, congrArg Subtype.val hj⟩
  -- at the rung colouring each `s i` has `t i` as its only partner
  have hforced : ∀ (i : Fin 3) (R : Finset V), (s i : V) ∈ R → (t i : V) ∈ R.erase (s i) →
      pmSum W c R
        = W s(((s i : V), i), ((t i : V), i)) * pmSum W c ((R.erase (s i)).erase (t i)) := by
    intro i R hsR htR
    rw [pmSum_of_forced W c hsR htR]
    · show W s(((s i : V), c (s i)), ((t i : V), c (t i))) * _ = _
      rw [hcs, hct]
    · intro w hw hne
      show W s(((s i : V), c (s i)), (w, c w)) = 0
      rw [hcs]
      rcases henum w with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rw [hcs]
        have hij : i ≠ j := fun hij => (Finset.mem_erase.mp hw).1 (by rw [hij])
        have := hdiag₁ (some (s i)) (some (s j))
          (fun h => hij (hsinj (Option.some_injective _ h))) i j hij
        rwa [shoreContract_some_some] at this
      · rw [hct]
        by_contra hnz
        have hij := hcross i j hnz
        exact hne (by rw [hij])
  -- the three rungs are the whole matching
  have m1 : (s 1 : V) ∈ (Finset.univ.erase (s 0 : V)).erase (t 0 : V) :=
    Finset.mem_erase.mpr ⟨hst 1 0,
      Finset.mem_erase.mpr ⟨hss 1 0 (by decide), Finset.mem_univ _⟩⟩
  have m2 : (t 1 : V) ∈ ((Finset.univ.erase (s 0 : V)).erase (t 0 : V)).erase (s 1 : V) :=
    Finset.mem_erase.mpr ⟨(hst 1 1).symm, Finset.mem_erase.mpr ⟨htt 1 0 (by decide),
      Finset.mem_erase.mpr ⟨(hst 0 1).symm, Finset.mem_univ _⟩⟩⟩
  have m3 : (s 2 : V) ∈
      (((Finset.univ.erase (s 0 : V)).erase (t 0 : V)).erase (s 1 : V)).erase (t 1 : V) :=
    Finset.mem_erase.mpr ⟨hst 2 1, Finset.mem_erase.mpr ⟨hss 2 1 (by decide),
      Finset.mem_erase.mpr ⟨hst 2 0, Finset.mem_erase.mpr ⟨hss 2 0 (by decide),
        Finset.mem_univ _⟩⟩⟩⟩
  have m4 : (t 2 : V) ∈
      ((((Finset.univ.erase (s 0 : V)).erase (t 0 : V)).erase (s 1 : V)).erase
        (t 1 : V)).erase (s 2 : V) :=
    Finset.mem_erase.mpr ⟨(hst 2 2).symm, Finset.mem_erase.mpr ⟨htt 2 1 (by decide),
      Finset.mem_erase.mpr ⟨(hst 1 2).symm, Finset.mem_erase.mpr ⟨htt 2 0 (by decide),
        Finset.mem_erase.mpr ⟨(hst 0 2).symm, Finset.mem_univ _⟩⟩⟩⟩⟩
  have hcases : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  have hempty : ((((((Finset.univ.erase (s 0 : V)).erase (t 0 : V)).erase (s 1 : V)).erase
      (t 1 : V)).erase (s 2 : V)).erase (t 2 : V)) = ∅ := by
    refine Finset.eq_empty_of_forall_notMem (fun w hw => ?_)
    simp only [Finset.mem_erase] at hw
    obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := hw
    rcases henum w with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;> rcases hcases j with rfl | rfl | rfl
    · exact h6 rfl
    · exact h4 rfl
    · exact h2 rfl
    · exact h5 rfl
    · exact h3 rfl
    · exact h1 rfl
  have hamp : amplitude W c = W s(((s 0 : V), 0), ((t 0 : V), 0)) *
      (W s(((s 1 : V), 1), ((t 1 : V), 1)) * (W s(((s 2 : V), 2), ((t 2 : V), 2)) * 1)) := by
    rw [← pmSum_univ, hforced 0 Finset.univ (Finset.mem_univ _)
      (Finset.mem_erase.mpr ⟨(hst 0 0).symm, Finset.mem_univ _⟩), hforced 1 _ m1 m2,
      hforced 2 _ m3 m4, hempty, pmSum_empty]
  have hmixed : ¬ Monochromatic c := by
    rintro ⟨m, hm⟩
    have h0 := hm (s 0)
    have h1 := hm (s 1)
    rw [hcs] at h0 h1
    exact absurd (h0.trans h1.symm) (by decide)
  have hzero := hW.2 c hmixed
  rw [hamp] at hzero
  exact mul_ne_zero (hrung 0) (mul_ne_zero (hrung 1) (mul_ne_zero (hrung 2) one_ne_zero)) hzero

end Six

section ThreeSite

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem triple_rotate {a b d : V} : ({b, a, d} : Finset V) = {a, b, d} := Finset.insert_comm b a {d}

omit [Fintype V] in
theorem triple_rotate' {a b d : V} : ({d, a, b} : Finset V) = {a, b, d} := by
  ext v; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

/-- **Export criterion.**  If for every colour `k` one of three sites has no weight of colour `k`,
at its own end, to the sites outside the three, then the sites outside are shore-tight: at a
colouring constant on the three, that site cannot cross, so no matching crosses three times. -/
theorem shoreTight_of_export_dead {W : Sym2 (V × Fin 3) → F} {a b d : V}
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (h : ∀ k : Fin 3, ∃ t ∈ ({a, b, d} : Finset V),
      ∀ v, v ≠ a → v ≠ b → v ≠ d → ∀ j, W s((t, k), (v, j)) = 0) :
    ShoreTight W (Finset.univ \ {a, b, d}) := by
  intro cS k
  set c := glue (Finset.univ \ {a, b, d}) cS k
  have hcT : ∀ t ∈ ({a, b, d} : Finset V), c t = k := fun t ht =>
    glue_of_not_mem cS k (fun h' => (Finset.mem_sdiff.mp h').2 ht)
  rw [crossOne_compl]
  obtain ⟨t, ht, hdead⟩ := h k
  have hdead' : ∀ v, v ≠ a → v ≠ b → v ≠ d → W (Sym2.map (paint c) s(t, v)) = 0 := by
    intro v h1 h2 h3
    show W s((t, c t), (v, c v)) = 0
    rw [hcT t ht]
    exact hdead v h1 h2 h3 (c v)
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl
  · exact amplitude_eq_crossOne_of_dead W c hab had hbd hdead'
  · rw [← triple_rotate]
    exact amplitude_eq_crossOne_of_dead W c (Ne.symm hab) hbd had
      (fun v h1 h2 h3 => hdead' v h2 h1 h3)
  · rw [← triple_rotate']
    exact amplitude_eq_crossOne_of_dead W c (Ne.symm had) (Ne.symm hbd) hab
      (fun v h1 h2 h3 => hdead' v h2 h3 h1)

/-- **Import criterion.**  If for every colour `k` one of three sites has no weight to the sites
outside the three that is coloured `k` at the far end, then the three sites are shore-tight. -/
theorem shoreTight_of_import_dead {W : Sym2 (V × Fin 3) → F} {a b d : V}
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (h : ∀ k : Fin 3, ∃ t ∈ ({a, b, d} : Finset V),
      ∀ v, v ≠ a → v ≠ b → v ≠ d → ∀ i, W s((t, i), (v, k)) = 0) :
    ShoreTight W {a, b, d} := by
  intro cS k
  set c := glue ({a, b, d} : Finset V) cS k
  have hcO : ∀ v, v ≠ a → v ≠ b → v ≠ d → c v = k := fun v h1 h2 h3 =>
    glue_of_not_mem cS k (by simp [h1, h2, h3])
  obtain ⟨t, ht, hdead⟩ := h k
  have hdead' : ∀ v, v ≠ a → v ≠ b → v ≠ d → W (Sym2.map (paint c) s(t, v)) = 0 := by
    intro v h1 h2 h3
    show W s((t, c t), (v, c v)) = 0
    rw [hcO v h1 h2 h3]
    exact hdead v h1 h2 h3 (c t)
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl
  · exact amplitude_eq_crossOne_of_dead W c hab had hbd hdead'
  · rw [← triple_rotate]
    exact amplitude_eq_crossOne_of_dead W c (Ne.symm hab) hbd had
      (fun v h1 h2 h3 => hdead' v h2 h1 h3)
  · rw [← triple_rotate']
    exact amplitude_eq_crossOne_of_dead W c (Ne.symm had) (Ne.symm hbd) hab
      (fun v h1 h2 h3 => hdead' v h2 h3 h1)

/-- **Three sites always export a common colour** once no cut keeping five or more sites is
shore-tight: for some colour `k`, each of the three sites has weight of colour `k`, at its own
end, to a site outside the three. -/
theorem exists_common_export {W : Sym2 (V × Fin 3) → F} (hcard : 8 ≤ Fintype.card V)
    (hheart : ∀ S : Finset V, 5 ≤ S.card → 3 ≤ (Finset.univ \ S).card → ¬ ShoreTight W S)
    {a b d : V} (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    ∃ k : Fin 3, ∀ t ∈ ({a, b, d} : Finset V),
      ∃ v, v ≠ a ∧ v ≠ b ∧ v ≠ d ∧ ∃ j, W s((t, k), (v, j)) ≠ 0 := by
  classical
  by_contra hno
  push Not at hno
  have hT : ({a, b, d} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, had]),
      Finset.card_insert_of_notMem (by simp [hbd]), Finset.card_singleton]
  refine hheart _ ?_ ?_ (shoreTight_of_export_dead hab had hbd fun k => ?_)
  · rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hT]
    omega
  · rw [Finset.sdiff_sdiff_eq_self (Finset.subset_univ _), hT]
  · obtain ⟨t, ht, hall⟩ := hno k
    exact ⟨t, ht, fun v h1 h2 h3 j => hall v h1 h2 h3 j⟩

end ThreeSite

end KrennTightCut
