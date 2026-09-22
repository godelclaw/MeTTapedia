import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card

/-!
# What a cross-free or laminar family of sets does and does not force

A spherical separating cycle selects one of two complementary face shores, and
which one is named is arbitrary.  Consequently the compatibility relation two
such selections satisfy is not laminarity but the four-way *cross-free*
disjunction

`A ⊆ B ∨ B ⊆ A ∨ Disjoint A B ∨ A ∪ B = univ`,

which is laminarity together with its complement-symmetric shadow.  This file
settles, for arbitrary finite ground types, exactly how much nesting such a
family is forced to contain.

The answer is: **none**.  `singletonFamily_chain_length_le_one` exhibits, for
every `N`, a family of `N` distinct nonempty proper sets that is pairwise
disjoint — hence both laminar and cross-free — and whose longest strictly
nested chain has length one.  `singletonFamily_chain_length_le_two_of_orient`
strengthens this: re-reading each member by its complement, independently and
in every possible way, still never produces a chain of length three.  So the
freedom to choose shores does not help either.

What *is* equivalent to a long chain is a single point of large depth.  For a
laminar family `F` and a point `x`, the members containing `x` are pairwise
nested, so they form a chain of length `depth F x`
(`exists_strictChain_of_laminar`); conversely a strictly nested chain of
nonempty members supplies a point contained in all of them
(`le_depth_of_strictChain`).  Hence

> maximum chain length of a laminar family = maximum depth of a point,

and the cheap half of the passage from cross-free to laminar is free: fixing
one point *outside* every member kills the fourth disjunct
(`laminarPair_of_crossFreePair_of_notMem`).

The practical reading is that a chain hypothesis can always be traded for a
*pointwise* one — one point inside every member and one point outside every
member — and that nothing weaker than such a point will do.
-/

namespace Mettapedia.GraphTheory

namespace CrossFreeLaminarChain

variable {α : Type*} [DecidableEq α]

/-! ## The two pairwise conditions -/

/-- Two finite sets are **cross-free**: nested either way, disjoint, or jointly
exhausting.  This is the exact four-way disjunction produced by a spherical
bond argument, in which each set is only determined up to complement. -/
def CrossFreePair [Fintype α] (A B : Finset α) : Prop :=
  A ⊆ B ∨ B ⊆ A ∨ Disjoint A B ∨ A ∪ B = Finset.univ

/-- Two finite sets are **laminar**: nested either way, or disjoint. -/
def LaminarPair (A B : Finset α) : Prop :=
  A ⊆ B ∨ B ⊆ A ∨ Disjoint A B

/-- A single point outside both members removes the fourth, complement-shaped
disjunct.  Orienting a whole cross-free family away from one fixed point
therefore makes it laminar, at no geometric cost. -/
theorem laminarPair_of_crossFreePair_of_notMem [Fintype α] {A B : Finset α}
    {outside : α} (hcross : CrossFreePair A B)
    (hA : outside ∉ A) (hB : outside ∉ B) :
    LaminarPair A B := by
  rcases hcross with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · have hmem : outside ∈ A ∪ B := by
      rw [h]; exact Finset.mem_univ outside
    rcases Finset.mem_union.mp hmem with h' | h'
    · exact absurd h' hA
    · exact absurd h' hB

omit [DecidableEq α] in
/-- A single point inside both members removes the disjointness disjunct. -/
theorem subset_or_subset_of_laminarPair_of_mem {A B : Finset α} {inside : α}
    (hlam : LaminarPair A B) (hA : inside ∈ A) (hB : inside ∈ B) :
    A ⊆ B ∨ B ⊆ A := by
  rcases hlam with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd hB (Finset.disjoint_left.mp h hA)

/-- **The minimal sufficient hypothesis, pairwise.**  Two cross-free sets that
separate one fixed pair of points — one inside both, one outside both — are
nested. -/
theorem subset_or_subset_of_crossFreePair_of_separates [Fintype α]
    {A B : Finset α} {inside outside : α} (hcross : CrossFreePair A B)
    (hinA : inside ∈ A) (hinB : inside ∈ B)
    (houtA : outside ∉ A) (houtB : outside ∉ B) :
    A ⊆ B ∨ B ⊆ A :=
  subset_or_subset_of_laminarPair_of_mem
    (laminarPair_of_crossFreePair_of_notMem hcross houtA houtB) hinA hinB

/-! ## Chain extraction from a totally ordered finite family -/

omit [DecidableEq α] in
/-- A finite family of sets that is totally ordered by inclusion enumerates as
a strictly decreasing chain of its own cardinality.  The enumeration is by
cardinality, which is injective precisely because inclusion is total. -/
theorem exists_strictChain_of_total {k : ℕ} (T : Finset (Finset α))
    (hcard : T.card = k)
    (htotal : ∀ A ∈ T, ∀ B ∈ T, A ⊆ B ∨ B ⊆ A) :
    ∃ nodes : Fin k → Finset α,
      (∀ i, nodes i ∈ T) ∧ ∀ i j : Fin k, i < j → nodes j ⊂ nodes i := by
  classical
  have hinjOn : Set.InjOn Finset.card (T : Set (Finset α)) := by
    intro A hA B hB hcards
    rcases htotal A hA B hB with h | h
    · exact Finset.eq_of_subset_of_card_le h (le_of_eq hcards.symm)
    · exact (Finset.eq_of_subset_of_card_le h (le_of_eq hcards)).symm
  have himg : (T.image Finset.card).card = k := by
    rw [Finset.card_image_of_injOn hinjOn, hcard]
  have hmem : ∀ i : Fin k,
      (T.image Finset.card).orderEmbOfFin himg i ∈ T.image Finset.card :=
    fun i => Finset.orderEmbOfFin_mem _ _ i
  choose pick hpickMem hpickCard using
    fun i : Fin k => Finset.mem_image.mp (hmem i)
  refine ⟨fun i => pick i.rev, fun i => hpickMem i.rev, ?_⟩
  intro i j hij
  have hrev : j.rev < i.rev := Fin.rev_lt_rev.mpr hij
  have hlt : (pick j.rev).card < (pick i.rev).card := by
    rw [hpickCard j.rev, hpickCard i.rev]
    exact ((T.image Finset.card).orderEmbOfFin himg).strictMono hrev
  rcases htotal _ (hpickMem i.rev) _ (hpickMem j.rev) with h | h
  · exact absurd (Finset.card_le_card h) (by omega)
  · refine Finset.ssubset_iff_subset_ne.mpr ⟨h, ?_⟩
    intro heq
    have heq' : pick j.rev = pick i.rev := heq
    rw [heq'] at hlt
    omega

/-- The indexed form.  A family indexed by `Fin n`, injective and totally
ordered by inclusion, is a strictly decreasing chain after one reindexing. -/
theorem exists_strictChain_reindex_of_total {n : ℕ} (family : Fin n → Finset α)
    (hinj : Function.Injective family)
    (htotal : ∀ i j : Fin n, family i ⊆ family j ∨ family j ⊆ family i) :
    ∃ σ : Fin n → Fin n,
      ∀ i j : Fin n, i < j → family (σ j) ⊂ family (σ i) := by
  classical
  have hcard : (Finset.image family Finset.univ).card = n := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  obtain ⟨nodes, hnodesMem, hstrict⟩ :=
    exists_strictChain_of_total (Finset.image family Finset.univ) hcard (by
      intro A hA B hB
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hB
      exact htotal i j)
  choose σ _hσmem hσeq using
    fun i : Fin n => Finset.mem_image.mp (hnodesMem i)
  refine ⟨σ, ?_⟩
  intro i j hij
  rw [hσeq i, hσeq j]
  exact hstrict i j hij

/-! ## Depth is chain length -/

/-- The members of a family containing a given point. -/
def containing (F : Finset (Finset α)) (x : α) : Finset (Finset α) :=
  F.filter (fun A => x ∈ A)

/-- How many members of a family contain a given point. -/
def depth (F : Finset (Finset α)) (x : α) : ℕ := (containing F x).card

/-- A family all of whose pairs are laminar. -/
def Laminar (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, LaminarPair A B

/-- A family all of whose pairs are cross-free. -/
def CrossFree [Fintype α] (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, CrossFreePair A B

/-- Orienting a cross-free family away from one fixed point makes it laminar. -/
theorem laminar_of_crossFree_of_common_outside [Fintype α]
    {F : Finset (Finset α)} {outside : α} (hcross : CrossFree F)
    (hout : ∀ A ∈ F, outside ∉ A) :
    Laminar F := fun A hA B hB =>
  laminarPair_of_crossFreePair_of_notMem (hcross A hA B hB) (hout A hA) (hout B hB)

/-- In a laminar family, the members through one point are totally ordered. -/
theorem total_containing_of_laminar {F : Finset (Finset α)} (hlam : Laminar F)
    (x : α) :
    ∀ A ∈ containing F x, ∀ B ∈ containing F x, A ⊆ B ∨ B ⊆ A := by
  intro A hA B hB
  rw [containing, Finset.mem_filter] at hA hB
  exact subset_or_subset_of_laminarPair_of_mem (hlam A hA.1 B hB.1) hA.2 hB.2

/-- **Depth gives a chain.**  A laminar family contains a strictly nested chain
of length exactly the depth of any chosen point, every member of which contains
that point. -/
theorem exists_strictChain_of_laminar {F : Finset (Finset α)}
    (hlam : Laminar F) (x : α) :
    ∃ nodes : Fin (depth F x) → Finset α,
      (∀ i, nodes i ∈ F) ∧ (∀ i, x ∈ nodes i) ∧
        ∀ i j : Fin (depth F x), i < j → nodes j ⊂ nodes i := by
  obtain ⟨nodes, hmem, hstrict⟩ :=
    exists_strictChain_of_total (containing F x) rfl
      (total_containing_of_laminar hlam x)
  refine ⟨nodes, ?_, ?_, hstrict⟩
  · intro i
    have h := hmem i
    rw [containing, Finset.mem_filter] at h
    exact h.1
  · intro i
    have h := hmem i
    rw [containing, Finset.mem_filter] at h
    exact h.2

omit [DecidableEq α] in
/-- **A chain has a common point.**  Every member of a strictly nested chain
contains any point of its smallest member.  This is the exact converse of the
sufficient hypothesis: one point inside every member is not merely enough for a
chain, it is what a chain always supplies. -/
theorem exists_mem_of_strictChain {L : ℕ} (hL : 0 < L) (nodes : Fin L → Finset α)
    (hstrict : ∀ i j : Fin L, i < j → nodes j ⊂ nodes i)
    (hne : (nodes ⟨L - 1, by omega⟩).Nonempty) :
    ∃ x : α, ∀ i : Fin L, x ∈ nodes i := by
  obtain ⟨x, hx⟩ := hne
  refine ⟨x, fun i => ?_⟩
  rcases eq_or_lt_of_le (Nat.le_sub_one_of_lt i.isLt) with heq | hlt
  · have hi : i = (⟨L - 1, by omega⟩ : Fin L) := Fin.ext heq
    rw [hi]; exact hx
  · exact (hstrict i ⟨L - 1, by omega⟩ hlt).1 hx

omit [DecidableEq α] in
/-- A strictly nested chain is in particular laminar. -/
theorem laminarPair_of_strictChain {L : ℕ} (nodes : Fin L → Finset α)
    (hstrict : ∀ i j : Fin L, i < j → nodes j ⊂ nodes i) (i j : Fin L) :
    LaminarPair (nodes i) (nodes j) := by
  rcases lt_trichotomy i j with h | h | h
  · exact Or.inr (Or.inl (hstrict i j h).1)
  · exact Or.inl (by rw [h])
  · exact Or.inl (hstrict j i h).1

/-- **A chain gives depth.**  A strictly nested chain whose smallest member is
nonempty produces a point of at least that depth, so the depth reformulation
loses nothing. -/
theorem le_depth_of_strictChain {F : Finset (Finset α)} {L : ℕ} (hL : 0 < L)
    (nodes : Fin L → Finset α) (hmem : ∀ i, nodes i ∈ F)
    (hstrict : ∀ i j : Fin L, i < j → nodes j ⊂ nodes i)
    (hne : (nodes ⟨L - 1, by omega⟩).Nonempty) :
    ∃ x : α, L ≤ depth F x := by
  classical
  obtain ⟨x, hlast⟩ := exists_mem_of_strictChain hL nodes hstrict hne
  refine ⟨x, ?_⟩
  have hinj : Function.Injective nodes := by
    intro i j heq
    by_contra hne'
    rcases lt_or_gt_of_ne hne' with h | h
    · exact (hstrict i j h).ne heq.symm
    · exact (hstrict j i h).ne heq
  have hsubset : Finset.image nodes Finset.univ ⊆ containing F x := by
    intro A hA
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hA
    rw [containing, Finset.mem_filter]
    exact ⟨hmem i, hlast i⟩
  have hle := Finset.card_le_card hsubset
  rwa [Finset.card_image_of_injective _ hinj, Finset.card_univ,
    Fintype.card_fin] at hle

/-! ## Laminarity alone forces nothing -/

/-- `N` pairwise disjoint singletons inside a ground type with one spare
point, so that every member is both nonempty and proper. -/
def singletonFamily (N : ℕ) (i : Fin N) : Finset (Fin (N + 1)) := {i.castSucc}

theorem singletonFamily_nonempty (N : ℕ) (i : Fin N) :
    (singletonFamily N i).Nonempty :=
  ⟨i.castSucc, Finset.mem_singleton_self _⟩

theorem singletonFamily_ne_univ (N : ℕ) (i : Fin N) :
    singletonFamily N i ≠ Finset.univ := by
  intro h
  have hlast : Fin.last N ∈ singletonFamily N i := by
    rw [h]; exact Finset.mem_univ _
  rw [singletonFamily, Finset.mem_singleton] at hlast
  exact (Fin.castSucc_lt_last i).ne' hlast

theorem singletonFamily_injective (N : ℕ) :
    Function.Injective (singletonFamily N) := by
  intro i j h
  rw [singletonFamily, singletonFamily, Finset.singleton_inj] at h
  exact Fin.castSucc_injective N h

theorem singletonFamily_disjoint (N : ℕ) {i j : Fin N} (hij : i ≠ j) :
    Disjoint (singletonFamily N i) (singletonFamily N j) := by
  rw [singletonFamily, singletonFamily, Finset.disjoint_singleton]
  exact fun hc => hij (Fin.castSucc_injective N hc)

theorem singletonFamily_laminarPair (N : ℕ) (i j : Fin N) :
    LaminarPair (singletonFamily N i) (singletonFamily N j) := by
  by_cases h : i = j
  · exact Or.inl (by rw [h])
  · exact Or.inr (Or.inr (singletonFamily_disjoint N h))

theorem singletonFamily_crossFreePair (N : ℕ) (i j : Fin N) :
    CrossFreePair (singletonFamily N i) (singletonFamily N j) := by
  rcases singletonFamily_laminarPair N i j with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))

/-- **Rung one, the sharp negative.**  A laminar — here even pairwise
disjoint — family of `N` distinct nonempty proper sets can have every strictly
nested chain of length at most one.  So no function of `N` alone bounds chain
length from below beyond the trivial `1`, and any chain must come from extra
structure, not from laminarity. -/
theorem singletonFamily_chain_length_le_one (N : ℕ) {L : ℕ} (nodes : Fin L → Fin N)
    (hstrict : ∀ i j : Fin L, i < j →
      singletonFamily N (nodes j) ⊂ singletonFamily N (nodes i)) :
    L ≤ 1 := by
  by_contra hcontra
  have hcontra : 1 < L := Nat.not_le.mp hcontra
  have hzero : (0 : ℕ) < L := by omega
  have hone : (1 : ℕ) < L := by omega
  have hlt : (⟨0, hzero⟩ : Fin L) < ⟨1, hone⟩ := by
    exact Fin.mk_lt_mk.mpr (by omega)
  have hss := hstrict ⟨0, hzero⟩ ⟨1, hone⟩ hlt
  rw [singletonFamily, singletonFamily] at hss
  have hsub := hss.1
  rw [Finset.singleton_subset_iff, Finset.mem_singleton] at hsub
  exact hss.ne (by rw [hsub])

/-! ### Choosing shores does not help -/

/-- Read the `i`-th member by whichever of its two complementary shores the
Boolean selects.  A spherical bond has exactly this freedom. -/
def orient (N : ℕ) (flip : Fin N → Bool) (i : Fin N) : Finset (Fin (N + 1)) :=
  if flip i then (singletonFamily N i)ᶜ else singletonFamily N i

theorem orient_of_false (N : ℕ) (flip : Fin N → Bool) (i : Fin N)
    (h : flip i = false) : orient N flip i = singletonFamily N i := by
  simp [orient, h]

theorem orient_of_true (N : ℕ) (flip : Fin N → Bool) (i : Fin N)
    (h : flip i = true) : orient N flip i = (singletonFamily N i)ᶜ := by
  simp [orient, h]

theorem singletonFamily_not_ssubset (N : ℕ) (a b : Fin N) :
    ¬ singletonFamily N b ⊂ singletonFamily N a := by
  intro hs
  rw [singletonFamily, singletonFamily] at hs
  have hsub := hs.1
  rw [Finset.singleton_subset_iff, Finset.mem_singleton] at hsub
  exact hs.ne (by rw [hsub])

theorem orient_not_ssubset (N : ℕ) (flip : Fin N → Bool) {i j : Fin N}
    (hflip : flip i = flip j) :
    ¬ orient N flip j ⊂ orient N flip i := by
  intro hss
  cases hcase : flip j with
  | false =>
      rw [orient_of_false N flip j hcase,
        orient_of_false N flip i (hflip.trans hcase)] at hss
      exact singletonFamily_not_ssubset N i j hss
  | true =>
      rw [orient_of_true N flip j hcase,
        orient_of_true N flip i (hflip.trans hcase),
        Finset.compl_ssubset_compl] at hss
      exact singletonFamily_not_ssubset N j i hss

/-- **Orientation freedom buys exactly one level.**  Even allowing every member
of the disjoint family to be re-read by its complementary shore, independently
and in all `2 ^ N` ways at once, no strictly nested chain of length three
exists.  The antichain extreme is therefore not an artifact of a bad choice of
shores: it survives every choice. -/
theorem singletonFamily_chain_length_le_two_of_orient (N : ℕ) (flip : Fin N → Bool)
    {L : ℕ} (nodes : Fin L → Fin N)
    (hstrict : ∀ i j : Fin L, i < j →
      orient N flip (nodes j) ⊂ orient N flip (nodes i)) :
    L ≤ 2 := by
  by_contra hcontra
  have hcontra : 2 < L := Nat.not_le.mp hcontra
  have h0 : (0 : ℕ) < L := by omega
  have h1 : (1 : ℕ) < L := by omega
  have h2 : (2 : ℕ) < L := by omega
  set a : Fin L := ⟨0, h0⟩ with ha
  set b : Fin L := ⟨1, h1⟩ with hb
  set c : Fin L := ⟨2, h2⟩ with hc
  have hab : a < b := Fin.mk_lt_mk.mpr (by omega)
  have hbc : b < c := Fin.mk_lt_mk.mpr (by omega)
  have hac : a < c := Fin.mk_lt_mk.mpr (by omega)
  by_cases h01 : flip (nodes a) = flip (nodes b)
  · exact orient_not_ssubset N flip h01 (hstrict a b hab)
  · by_cases h12 : flip (nodes b) = flip (nodes c)
    · exact orient_not_ssubset N flip h12 (hstrict b c hbc)
    · have h02 : flip (nodes a) = flip (nodes c) := by
        revert h01 h12
        cases flip (nodes a) <;> cases flip (nodes b) <;> cases flip (nodes c) <;> simp
      exact orient_not_ssubset N flip h02 (hstrict a c hac)

/-! ## Small instances -/

section Sanity

/-- A three-step concentric family: depth three at the common point. -/
example : depth ({{0}, {0, 1}, {0, 1, 2}} : Finset (Finset (Fin 4))) 0 = 3 := by
  decide

example : Laminar ({{0}, {0, 1}, {0, 1, 2}} : Finset (Finset (Fin 4))) := by
  unfold Laminar LaminarPair
  simp only [Finset.disjoint_left]
  decide

/-- The side-by-side family of the same size: every depth is one. -/
example : Laminar ({{0}, {1}, {2}} : Finset (Finset (Fin 4))) := by
  unfold Laminar LaminarPair
  simp only [Finset.disjoint_left]
  decide

example : ∀ x : Fin 4, depth ({{0}, {1}, {2}} : Finset (Finset (Fin 4))) x ≤ 1 := by
  decide

/-- Cross-freeness genuinely is weaker than laminarity: `{0,1}` and `{1,2}` in
a three-point ground set are neither nested nor disjoint, but they do cover. -/
example : CrossFreePair ({0, 1} : Finset (Fin 3)) ({1, 2} : Finset (Fin 3)) := by
  unfold CrossFreePair
  simp only [Finset.disjoint_left]
  decide

example : ¬ LaminarPair ({0, 1} : Finset (Fin 3)) ({1, 2} : Finset (Fin 3)) := by
  unfold LaminarPair
  simp only [Finset.disjoint_left]
  decide

end Sanity

end CrossFreeLaminarChain

end Mettapedia.GraphTheory
