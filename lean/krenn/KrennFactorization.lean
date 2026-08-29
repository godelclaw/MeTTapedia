/-
# Perfect-matching factorization for Krenn--Gu systems

This file defines the graph-indexed weight system and proves that, when the
weights are supported diagonally on two edge-disjoint perfect matchings, the
perfect-matching sum factors over their alternating components.
-/
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Tutte
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Sym.Sym2.Order

open SimpleGraph

namespace Krenn

/- `LinearOrder V` (rather than bare `DecidableEq`) so each edge has
canonical smaller/larger endpoints (`Sym2.inf`/`Sym2.sup`) — the
formal-conjectures weight-key convention. -/
variable {V : Type*} [Fintype V] [LinearOrder V]

/-- A weight system on graph `G` with `D` colours: a complex weight for each
edge and ordered pair of endpoint colours (colour at the lexicographically
smaller endpoint listed first, matching the formal-conjectures convention). -/
def WeightSystem (G : SimpleGraph V) (D : ℕ) : Type _ :=
  G.edgeSet → Fin D → Fin D → ℂ

/-- A vertex of a `Sym2` is its smaller or its larger endpoint. -/
lemma mem_iff_eq_inf_or_sup {v : V} {z : Sym2 V} :
    v ∈ z ↔ v = z.inf ∨ v = z.sup := by
  induction z with
  | _ a b =>
    rcases le_total a b with h | h <;>
      simp [Sym2.mem_iff, Sym2.inf_mk, Sym2.sup_mk, inf_eq_left.mpr h,
        sup_eq_right.mpr h, inf_eq_right.mpr h, sup_eq_left.mpr h, or_comm]

/-- Edge-set form of a perfect matching: a finite set of edges of `G`
covering every vertex exactly once. `pmSum` sums over these; the conversions
below identify this representation with `Subgraph.IsPerfectMatching`. -/
def IsPMFinset (G : SimpleGraph V) (M : Finset G.edgeSet) : Prop :=
  ∀ v : V, ∃! e : G.edgeSet, e ∈ M ∧ v ∈ (e : Sym2 V)

/-- Computable cardinality form of the unique-cover condition. -/
def pmUniqueAt {G : SimpleGraph V} (M : Finset G.edgeSet) (v : V) : Prop :=
  (M.filter fun e : G.edgeSet => v ∈ (e : Sym2 V)).card = 1

theorem pmUniqueAt_iff {G : SimpleGraph V} (M : Finset G.edgeSet) (v : V) :
    pmUniqueAt M v ↔ ∃! e : G.edgeSet, e ∈ M ∧ v ∈ (e : Sym2 V) := by
  rw [pmUniqueAt, Finset.card_eq_one]
  constructor
  · rintro ⟨e, heq⟩
    have hefilter : e ∈ M.filter fun e : G.edgeSet => v ∈ (e : Sym2 V) := by
      rw [heq]
      simp
    refine ⟨e, Finset.mem_filter.mp hefilter, ?_⟩
    intro e' he'
    have he'filter : e' ∈ M.filter fun e : G.edgeSet => v ∈ (e : Sym2 V) :=
      Finset.mem_filter.mpr he'
    rw [heq] at he'filter
    exact Finset.mem_singleton.mp he'filter
  · rintro ⟨e, he, huniq⟩
    refine ⟨e, Finset.ext fun e' => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · exact fun he' => huniq e' he'
    · rintro rfl
      exact he

/-- An executable decision procedure for finite perfect-matching edge sets.
Kept as a definition rather than a global instance so `pmSum` remains
independent of instance-selection details. -/
def decidableIsPMFinset {G : SimpleGraph V} (M : Finset G.edgeSet) :
    Decidable (IsPMFinset G M) :=
  letI : DecidablePred (pmUniqueAt M) := fun _ => by
    unfold pmUniqueAt
    infer_instance
  letI : Decidable (∀ v, pmUniqueAt M v) := Fintype.decidableForallFintype
  decidable_of_iff (∀ v, pmUniqueAt M v) (by
    simp only [pmUniqueAt_iff, IsPMFinset])

/-- The spanning subgraph whose edges are exactly a supplied finite subset
of `G.edgeSet`. -/
def subgraphOfFinset {G : SimpleGraph V} (M : Finset G.edgeSet) : G.Subgraph where
  verts := Set.univ
  Adj v w := ∃ e : G.edgeSet, e ∈ M ∧ (e : Sym2 V) = s(v, w)
  adj_sub := by
    rintro v w ⟨e, _, he⟩
    apply G.mem_edgeSet.mp
    rw [← he]
    exact e.property
  edge_vert := by simp
  symm := by
    constructor
    rintro v w ⟨e, heM, he⟩
    exact ⟨e, heM, he.trans Sym2.eq_swap⟩

omit [Fintype V] [LinearOrder V] in
/-- The edge-set and subgraph formulations of a perfect matching agree for
`subgraphOfFinset`. -/
theorem isPerfectMatching_subgraphOfFinset {G : SimpleGraph V}
    {M : Finset G.edgeSet} (hM : IsPMFinset G M) :
    (subgraphOfFinset M).IsPerfectMatching := by
  constructor
  · intro v _
    obtain ⟨e, ⟨heM, hve⟩, huniq⟩ := hM v
    obtain ⟨w, he⟩ := Sym2.mem_iff_exists.mp hve
    refine ⟨w, ⟨e, heM, he⟩, ?_⟩
    intro w' hw'
    obtain ⟨e', he'M, he'⟩ := hw'
    have hve' : v ∈ (e' : Sym2 V) := by
      rw [he']
      exact Sym2.mem_mk_left v w'
    have heq : e' = e := huniq e' ⟨he'M, hve'⟩
    apply Sym2.congr_right.mp
    exact he'.symm.trans (congrArg Subtype.val heq |>.trans he)
  · intro v
    simp [subgraphOfFinset]

/-- The finite edge-set carried by a graph subgraph. -/
noncomputable def edgeFinsetOfSubgraph {G : SimpleGraph V}
    (M : G.Subgraph) : Finset G.edgeSet := by
  classical
  exact Finset.univ.filter fun e : G.edgeSet => (e : Sym2 V) ∈ M.edgeSet

omit [LinearOrder V] in
@[simp] theorem mem_edgeFinsetOfSubgraph {G : SimpleGraph V} {M : G.Subgraph}
    {e : G.edgeSet} :
    e ∈ edgeFinsetOfSubgraph M ↔ (e : Sym2 V) ∈ M.edgeSet := by
  classical
  simp [edgeFinsetOfSubgraph]

omit [LinearOrder V] in
/-- A Mathlib perfect matching gives the finite-edge-set representation used by
the graph-indexed Krenn matching sum. -/
theorem isPMFinset_edgeFinsetOfSubgraph {G : SimpleGraph V} {M : G.Subgraph}
    (hM : M.IsPerfectMatching) : IsPMFinset G (edgeFinsetOfSubgraph M) := by
  intro v
  obtain ⟨w, hvw, huniq⟩ := hM.1 (hM.2 v)
  let e : G.edgeSet := ⟨s(v, w), M.edgeSet_subset (Subgraph.mem_edgeSet.2 hvw)⟩
  refine ⟨e, ⟨?_, Sym2.mem_mk_left v w⟩, ?_⟩
  · exact mem_edgeFinsetOfSubgraph.mpr (Subgraph.mem_edgeSet.2 hvw)
  · intro e' he'
    obtain ⟨he'M, hve'⟩ := he'
    obtain ⟨w', heq⟩ := Sym2.mem_iff_exists.mp hve'
    have hvw' : M.Adj v w' := Subgraph.mem_edgeSet.1 <| by
      rw [← heq]
      exact mem_edgeFinsetOfSubgraph.mp he'M
    have hww' : w' = w := huniq w' hvw'
    subst w'
    exact Subtype.ext heq

omit [LinearOrder V] in
/-- Converting a finite edge set to a subgraph and back preserves the edge set. -/
@[simp] theorem edgeFinsetOfSubgraph_subgraphOfFinset {G : SimpleGraph V}
    (M : Finset G.edgeSet) :
    edgeFinsetOfSubgraph (subgraphOfFinset M) = M := by
  classical
  apply Finset.ext
  rintro ⟨z, hz⟩
  induction z with
  | _ v w =>
      rw [mem_edgeFinsetOfSubgraph, Subgraph.mem_edgeSet]
      constructor
      · rintro ⟨e, heM, heq⟩
        have he : e = ⟨s(v, w), hz⟩ := Subtype.ext heq
        rw [he] at heM
        exact heM
      · intro heM
        exact ⟨⟨s(v, w), hz⟩, heM, rfl⟩

omit [LinearOrder V] in
/-- The finite-edge-set and Mathlib subgraph formulations of a perfect matching
are equivalent. -/
theorem isPerfectMatching_subgraphOfFinset_iff {G : SimpleGraph V}
    {M : Finset G.edgeSet} :
    (subgraphOfFinset M).IsPerfectMatching ↔ IsPMFinset G M := by
  constructor
  · intro hM
    simpa using isPMFinset_edgeFinsetOfSubgraph hM
  · exact isPerfectMatching_subgraphOfFinset

/-- Disjoint finite edge sets induce edge-disjoint spanning subgraphs. -/
theorem disjoint_edgeSet_subgraphOfFinset {G : SimpleGraph V}
    {M N : Finset G.edgeSet} (hMN : Disjoint M N) :
    Disjoint (subgraphOfFinset M).edgeSet (subgraphOfFinset N).edgeSet := by
  rw [Set.disjoint_left]
  intro z hzM hzN
  induction z with
  | _ v w =>
      rw [Subgraph.mem_edgeSet] at hzM hzN
      obtain ⟨eM, heM, hcoeM⟩ := hzM
      obtain ⟨eN, heN, hcoeN⟩ := hzN
      have heq : eM = eN := Subtype.ext (hcoeM.trans hcoeN.symm)
      subst eN
      exact Finset.disjoint_left.mp hMN heM heN

/-- The weight of one edge under a colouring: `W` looked up at the colours
of the smaller and larger endpoint (formal-conjectures key convention). -/
def edgeWeight {G : SimpleGraph V} {D : ℕ}
    (W : WeightSystem G D) (ι : V → Fin D) (e : G.edgeSet) : ℂ :=
  W e (ι (e : Sym2 V).inf) (ι (e : Sym2 V).sup)

open scoped Classical in
/-- Perfect-matching sum of a weight system under a colouring `ι`: over
all edge-set perfect matchings of `G`, the product of the matching edges'
weights at the endpoint colours. -/
noncomputable def pmSum {G : SimpleGraph V} {D : ℕ}
    (W : WeightSystem G D) (ι : V → Fin D) : ℂ :=
  ∑ M ∈ Finset.univ.filter (fun M : Finset G.edgeSet => IsPMFinset G M),
    ∏ e ∈ M, edgeWeight W ι e

open scoped Classical in
/-- Replace the implementation's enumeration of perfect matchings by any
extensionally equal finite enumeration. This keeps finite regression proofs
independent of the particular `Decidable` instances used by `pmSum`. -/
theorem pmSum_eq_sum_over {G : SimpleGraph V} {D : ℕ}
    (W : WeightSystem G D) (ι : V → Fin D) (S : Finset (Finset G.edgeSet))
    (hS : ∀ M : Finset G.edgeSet, IsPMFinset G M ↔ M ∈ S) :
    pmSum W ι = ∑ M ∈ S, ∏ e ∈ M, edgeWeight W ι e := by
  unfold pmSum
  apply Finset.sum_congr
  · ext M
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hS M
  · intro M _
    rfl

open Classical in
theorem pmSum_restrict {G : SimpleGraph V} {D : ℕ} {M₁ M₂ : G.Subgraph}
    (W : WeightSystem G D)
    (hsupp : ∀ (e : G.edgeSet) (i j : Fin D), W e i j ≠ 0 →
      ((e : Sym2 V) ∈ M₁.edgeSet ∨ (e : Sym2 V) ∈ M₂.edgeSet) ∧ i = j)
    (ι : V → Fin D) :
    pmSum W ι =
      ∑ F ∈ (Finset.univ.filter (fun F : Finset G.edgeSet => IsPMFinset G F)).filter
          (fun F : Finset G.edgeSet =>
            ∀ e ∈ F, (e : Sym2 V) ∈ M₁.edgeSet ∨ (e : Sym2 V) ∈ M₂.edgeSet),
        ∏ e ∈ F, edgeWeight W ι e := by
  classical
  -- An edge outside `M₁ ∪ M₂` has zero weight under EVERY colouring: this is
  -- just the contrapositive of `hsupp`, applied at the two endpoint colours.
  have hzero : ∀ e : G.edgeSet,
      ¬ ((e : Sym2 V) ∈ M₁.edgeSet ∨ (e : Sym2 V) ∈ M₂.edgeSet) →
      edgeWeight W ι e = 0 := by
    intro e hout
    by_contra hne
    exact hout (hsupp e _ _ hne).1
  rw [pmSum]
  refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
  intro F hFmem hFnot
  -- `F` is a perfect matching that is NOT drawn from `M₁ ∪ M₂`
  have hQ : ¬ ∀ e ∈ F, (e : Sym2 V) ∈ M₁.edgeSet ∨ (e : Sym2 V) ∈ M₂.edgeSet :=
    fun hall => hFnot (Finset.mem_filter.mpr ⟨hFmem, hall⟩)
  -- `push Not` also distributes through the disjunction, so the witness comes
  -- back as a conjunction of non-memberships; `not_or` puts it back.
  push Not at hQ
  obtain ⟨e, heF, hout⟩ := hQ
  exact Finset.prod_eq_zero heF (hzero e (not_or.mpr hout))

/-- `W` serves colour set `C`: monochromatic colourings in `C` sum to 1,
every other colouring (mixed, or mono outside `C`) sums to 0. -/
def Serves {G : SimpleGraph V} {D : ℕ}
    (W : WeightSystem G D) (C : Finset (Fin D)) : Prop :=
  (∀ c ∈ C, pmSum W (fun _ => c) = 1) ∧
  (∀ ι : V → Fin D, (¬ ∃ c ∈ C, ι = fun _ => c) → pmSum W ι = 0)

/-- The servable rank: the largest number of colours some weight system can
serve.  `r G D ≥ 3` for some `G` with `> 4` vertices would refute Krenn–Gu.
(`sSup` is honest here: the achievable set contains `0` — the zero weight
system serves `∅` — and is bounded by `D`, since `C : Finset (Fin D)`.) -/
noncomputable def servableRank (G : SimpleGraph V) (D : ℕ) : ℕ :=
  sSup {n : ℕ | ∃ W : WeightSystem G D, ∃ C : Finset (Fin D),
    C.card = n ∧ Serves W C}

open scoped symmDiff in
/-- Sub-step A (left): an `M₁`-edge at a vertex of the alternating subgraph
`M₁ △ M₂` cannot be shared, so it is itself an edge of `M₁ △ M₂`. -/
lemma adj_symmDiff_of_adj_of_mem_support_left {G : SimpleGraph V}
    {M₁ M₂ : G.Subgraph} (h₁ : M₁.IsPerfectMatching) (h₂ : M₂.IsPerfectMatching)
    {v u : V} (he : M₁.Adj v u)
    (hsupp : v ∈ (M₁.spanningCoe ∆ M₂.spanningCoe).support) :
    (M₁.spanningCoe ∆ M₂.spanningCoe).Adj v u := by
  obtain ⟨w₁, -, hw₁u⟩ := h₁.1 (h₁.2 v)
  obtain ⟨w₂, -, hw₂u⟩ := h₂.1 (h₂.2 v)
  obtain ⟨w, hw⟩ := hsupp
  simp only [symmDiff_def, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj,
    SimpleGraph.Subgraph.spanningCoe_adj] at hw ⊢
  rcases hw with ⟨hwM1, hwM2⟩ | ⟨hwM2, hwM1⟩
  · have hu : w = u := (hw₁u w hwM1).trans (hw₁u u he).symm
    subst hu
    exact Or.inl ⟨he, hwM2⟩
  · refine Or.inl ⟨he, fun hM2u => ?_⟩
    have hu : u = w := (hw₂u u hM2u).trans (hw₂u w hwM2).symm
    subst hu
    exact hwM1 he

open scoped symmDiff in
/-- Sub-step A (right): the `M₂` version, via symmetry of `△`. -/
lemma adj_symmDiff_of_adj_of_mem_support_right {G : SimpleGraph V}
    {M₁ M₂ : G.Subgraph} (h₁ : M₁.IsPerfectMatching) (h₂ : M₂.IsPerfectMatching)
    {v u : V} (he : M₂.Adj v u)
    (hsupp : v ∈ (M₁.spanningCoe ∆ M₂.spanningCoe).support) :
    (M₁.spanningCoe ∆ M₂.spanningCoe).Adj v u := by
  rw [symmDiff_comm] at hsupp ⊢
  exact adj_symmDiff_of_adj_of_mem_support_left h₂ h₁ he hsupp

open scoped symmDiff in
open scoped SimpleGraph in
/-- One direction of the mixing lemma: if `F` uses an `M₁` edge at `v` and
`v` is `H`-adjacent to `w`, then `F` uses an `M₁` edge at `w` too. -/
lemma mixing_key {G : SimpleGraph V} {M₁ M₂ : G.Subgraph}
    (h₁ : M₁.IsPerfectMatching) (h₂ : M₂.IsPerfectMatching)
    {F : Finset G.edgeSet} (hF : IsPMFinset G F)
    (hFsub : ∀ e ∈ F, (e : Sym2 V) ∈ M₁.edgeSet ∨ (e : Sym2 V) ∈ M₂.edgeSet)
    {v w : V} (hvw : (M₁.spanningCoe ∆ M₂.spanningCoe).Adj v w)
    (hv : ∃ e ∈ F, v ∈ (e : Sym2 V) ∧ (e : Sym2 V) ∈ M₁.edgeSet) :
    ∃ e ∈ F, w ∈ (e : Sym2 V) ∧ (e : Sym2 V) ∈ M₁.edgeSet := by
  classical
  obtain ⟨e, heF, hve, heM₁⟩ := hv
  have hvsupp : v ∈ (M₁.spanningCoe ∆ M₂.spanningCoe).support := ⟨w, hvw⟩
  have hwsupp : w ∈ (M₁.spanningCoe ∆ M₂.spanningCoe).support := ⟨v, hvw.symm⟩
  obtain ⟨u, hu⟩ := Sym2.mem_iff_exists.1 hve
  have hadj₁ : M₁.Adj v u := by
    have : (s(v, u) : Sym2 V) ∈ M₁.edgeSet := by rw [← hu]; exact heM₁
    exact Subgraph.mem_edgeSet.1 this
  have hHvu : (M₁.spanningCoe ∆ M₂.spanningCoe).Adj v u :=
    adj_symmDiff_of_adj_of_mem_support_left h₁ h₂ hadj₁ hvsupp
  have hnotM₂ : ¬ M₂.Adj v u := by
    simp only [symmDiff_def, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj,
      SimpleGraph.Subgraph.spanningCoe_adj] at hHvu
    rcases hHvu with ⟨-, h⟩ | ⟨-, h⟩
    · exact h
    · exact absurd hadj₁ h
  have hvw' := hvw
  simp only [symmDiff_def, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj,
    SimpleGraph.Subgraph.spanningCoe_adj] at hvw'
  rcases hvw' with ⟨hM₁vw, -⟩ | ⟨hM₂vw, hnM₁vw⟩
  · obtain ⟨w₁, -, huniq₁⟩ := h₁.1 (h₁.2 v)
    have huw : u = w := (huniq₁ u hadj₁).trans (huniq₁ w hM₁vw).symm
    refine ⟨e, heF, ?_, heM₁⟩
    rw [hu, huw]
    exact Sym2.mem_mk_right v w
  · obtain ⟨f, ⟨hfF, hwf⟩, -⟩ := hF w
    refine ⟨f, hfF, hwf, ?_⟩
    rcases hFsub f hfF with hfM₁ | hfM₂
    · exact hfM₁
    · exfalso
      obtain ⟨x, hx⟩ := Sym2.mem_iff_exists.1 hwf
      have hadj₂ : M₂.Adj w x := by
        have : (s(w, x) : Sym2 V) ∈ M₂.edgeSet := by rw [← hx]; exact hfM₂
        exact Subgraph.mem_edgeSet.1 this
      obtain ⟨w₂, -, huniq₂⟩ := h₂.1 (h₂.2 w)
      have hxv : x = v := (huniq₂ x hadj₂).trans (huniq₂ v hM₂vw.symm).symm
      have hvf : v ∈ (f : Sym2 V) := by
        rw [hx, hxv]
        exact Sym2.mem_mk_right w v
      obtain ⟨e₀, -, huniqF⟩ := hF v
      have hfe : f = e := (huniqF f ⟨hfF, hvf⟩).trans (huniqF e ⟨heF, hve⟩).symm
      refine hnotM₂ (Subgraph.mem_edgeSet.1 ?_)
      show (s(v, u) : Sym2 V) ∈ M₂.edgeSet
      rw [← hu, ← hfe]
      exact hfM₂

open scoped symmDiff in
/-- **Sub-step B (mixing lemma).**  Along an `H = M₁ △ M₂` edge, a perfect
matching `F` supported on `M₁ ∪ M₂` uses the same side at both endpoints. -/
theorem mixing {G : SimpleGraph V} {M₁ M₂ : G.Subgraph}
    (h₁ : M₁.IsPerfectMatching) (h₂ : M₂.IsPerfectMatching)
    {F : Finset G.edgeSet} (hF : IsPMFinset G F)
    (hFsub : ∀ e ∈ F, (e : Sym2 V) ∈ M₁.edgeSet ∨ (e : Sym2 V) ∈ M₂.edgeSet)
    {v w : V} (hvw : (M₁.spanningCoe ∆ M₂.spanningCoe).Adj v w) :
    (∃ e ∈ F, v ∈ (e : Sym2 V) ∧ (e : Sym2 V) ∈ M₁.edgeSet) ↔
    (∃ e ∈ F, w ∈ (e : Sym2 V) ∧ (e : Sym2 V) ∈ M₁.edgeSet) :=
  ⟨mixing_key h₁ h₂ hF hFsub hvw, mixing_key h₁ h₂ hF hFsub hvw.symm⟩
def usesM₁ {G : SimpleGraph V} (M₁ : G.Subgraph) (F : Finset G.edgeSet) (v : V) : Prop :=
  ∃ e ∈ F, v ∈ (e : Sym2 V) ∧ (e : Sym2 V) ∈ M₁.edgeSet

open scoped symmDiff in
/-- **C2a (i): the side predicate is constant along any `H`-walk.**
Induction on the walk, applying `mixing` at each edge. -/
theorem usesM₁_iff_of_walk {G : SimpleGraph V} {M₁ M₂ : G.Subgraph}
    (h₁ : M₁.IsPerfectMatching) (h₂ : M₂.IsPerfectMatching)
    {F : Finset G.edgeSet} (hF : IsPMFinset G F)
    (hFsub : ∀ e ∈ F, (e : Sym2 V) ∈ M₁.edgeSet ∨ (e : Sym2 V) ∈ M₂.edgeSet)
    {v w : V} (p : (M₁.spanningCoe ∆ M₂.spanningCoe).Walk v w) :
    usesM₁ M₁ F v ↔ usesM₁ M₁ F w := by
  induction p with
  | nil => exact Iff.rfl
  | cons hadj _ ih => exact (mixing h₁ h₂ hF hFsub hadj).trans ih

open scoped symmDiff in
/-- **C2a (i), component form.**  Constant on each `H`-connected component. -/
theorem usesM₁_iff_of_reachable {G : SimpleGraph V} {M₁ M₂ : G.Subgraph}
    (h₁ : M₁.IsPerfectMatching) (h₂ : M₂.IsPerfectMatching)
    {F : Finset G.edgeSet} (hF : IsPMFinset G F)
    (hFsub : ∀ e ∈ F, (e : Sym2 V) ∈ M₁.edgeSet ∨ (e : Sym2 V) ∈ M₂.edgeSet)
    {v w : V} (hreach : (M₁.spanningCoe ∆ M₂.spanningCoe).Reachable v w) :
    usesM₁ M₁ F v ↔ usesM₁ M₁ F w :=
  hreach.elim fun p => usesM₁_iff_of_walk h₁ h₂ hF hFsub p

open scoped symmDiff in
/-- **C2a (ii), off-support half.**  At a vertex outside `H.support` the two
matchings agree, so the `F`-edge there lies in BOTH `M₁` and `M₂`. -/
theorem shared_of_not_mem_support {G : SimpleGraph V} {M₁ M₂ : G.Subgraph}
    (h₁ : M₁.IsPerfectMatching) (h₂ : M₂.IsPerfectMatching)
    {F : Finset G.edgeSet}
    (hFsub : ∀ e ∈ F, (e : Sym2 V) ∈ M₁.edgeSet ∨ (e : Sym2 V) ∈ M₂.edgeSet)
    {v : V} (hv : v ∉ (M₁.spanningCoe ∆ M₂.spanningCoe).support)
    {e : G.edgeSet} (heF : e ∈ F) (hve : v ∈ (e : Sym2 V)) :
    (e : Sym2 V) ∈ M₁.edgeSet ∧ (e : Sym2 V) ∈ M₂.edgeSet := by
  classical
  obtain ⟨w₁, hw₁, huniq₁⟩ := h₁.1 (h₁.2 v)
  obtain ⟨w₂, hw₂, huniq₂⟩ := h₂.1 (h₂.2 v)
  -- the two partners coincide, else the M₁ edge at `v` would be an H-edge
  have hww : w₁ = w₂ := by
    by_contra hne
    refine hv ⟨w₁, ?_⟩
    simp only [symmDiff_def, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj,
      SimpleGraph.Subgraph.spanningCoe_adj]
    exact Or.inl ⟨hw₁, fun hM₂ => hne (huniq₂ w₁ hM₂)⟩
  -- the F-edge at `v` is on one of the two sides, and both name the same edge
  obtain ⟨u, hu⟩ := Sym2.mem_iff_exists.1 hve
  have huw₁ : u = w₁ := by
    rcases hFsub e heF with hM₁ | hM₂
    · have : M₁.Adj v u := by
        have h' : (s(v, u) : Sym2 V) ∈ M₁.edgeSet := by rw [← hu]; exact hM₁
        exact Subgraph.mem_edgeSet.1 h'
      exact huniq₁ u this
    · have : M₂.Adj v u := by
        have h' : (s(v, u) : Sym2 V) ∈ M₂.edgeSet := by rw [← hu]; exact hM₂
        exact Subgraph.mem_edgeSet.1 h'
      rw [hww]
      exact huniq₂ u this
  subst huw₁
  refine ⟨?_, ?_⟩
  · rw [hu]; exact Subgraph.mem_edgeSet.2 hw₁
  · rw [hu, hww]; exact Subgraph.mem_edgeSet.2 hw₂

section Build

open Finset

open scoped symmDiff

variable {G : SimpleGraph V} (M₁ M₂ : G.Subgraph)

/-- The alternating subgraph. -/
abbrev altGraph : SimpleGraph V := M₁.spanningCoe ∆ M₂.spanningCoe

/-- An `M`-edge, packaged as an element of `G.edgeSet`. -/
def mkEdge {M : G.Subgraph} {v w : V} (h : M.Adj v w) : G.edgeSet :=
  ⟨s(v, w), M.edgeSet_subset (Subgraph.mem_edgeSet.2 h)⟩

/-- In a matching, any edge at `v` lying in `M` IS the `M`-edge at `v`. -/
lemma coe_eq_of_mem_edgeSet {M : G.Subgraph} {v w : V}
    (huniq : ∀ y, M.Adj v y → y = w)
    {f : G.edgeSet} (hvf : v ∈ (f : Sym2 V)) (hfM : (f : Sym2 V) ∈ M.edgeSet) :
    (f : Sym2 V) = s(v, w) := by
  obtain ⟨u, hu⟩ := Sym2.mem_iff_exists.1 hvf
  have hadj : M.Adj v u := by
    rw [hu] at hfM
    exact Subgraph.mem_edgeSet.1 hfM
  rw [hu, huniq u hadj]

/-- **Off the support the two matchings agree at `v`.** -/
lemma partners_eq_of_not_mem_support
    (h₂ : M₂.IsPerfectMatching) {v w₁ w₂ : V}
    (hw₁ : M₁.Adj v w₁) (huniq₂ : ∀ y, M₂.Adj v y → y = w₂)
    (hv : v ∉ (altGraph M₁ M₂).support) : w₁ = w₂ := by
  by_contra hne
  refine hv ⟨w₁, ?_⟩
  simp only [altGraph, symmDiff_def, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj,
    SimpleGraph.Subgraph.spanningCoe_adj]
  exact Or.inl ⟨hw₁, fun hM₂ => hne (huniq₂ w₁ hM₂)⟩

/-- **On the support the two matchings disagree at `v`.** -/
lemma partners_ne_of_mem_support {v w₁ w₂ : V}
    (huniq₁ : ∀ y, M₁.Adj v y → y = w₁) (huniq₂ : ∀ y, M₂.Adj v y → y = w₂)
    (hw₁ : M₁.Adj v w₁) (hw₂ : M₂.Adj v w₂)
    (hv : v ∈ (altGraph M₁ M₂).support) : w₁ ≠ w₂ := by
  rintro rfl
  obtain ⟨u, hu⟩ := hv
  simp only [altGraph, symmDiff_def, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj,
    SimpleGraph.Subgraph.spanningCoe_adj] at hu
  rcases hu with ⟨hM₁, hM₂⟩ | ⟨hM₂, hM₁⟩
  · exact hM₂ (by rw [← huniq₁ u hM₁] at hw₂; exact hw₂)
  · exact hM₁ (by rw [← huniq₂ u hM₂] at hw₁; exact hw₁)

/-- **With edge-disjoint matchings every vertex lies on the support.**
Otherwise the two partners coincide and the common edge is shared. -/
lemma mem_support_of_disjoint
    (h₁ : M₁.IsPerfectMatching) (h₂ : M₂.IsPerfectMatching)
    (hdisj : Disjoint M₁.edgeSet M₂.edgeSet) (v : V) :
    v ∈ (altGraph M₁ M₂).support := by
  classical
  obtain ⟨w₁, hw₁, huniq₁⟩ := h₁.1 (h₁.2 v)
  obtain ⟨w₂, hw₂, huniq₂⟩ := h₂.1 (h₂.2 v)
  by_contra hv
  have hww : w₁ = w₂ := partners_eq_of_not_mem_support M₁ M₂ h₂ hw₁ huniq₂ hv
  exact Set.disjoint_left.mp hdisj (Subgraph.mem_edgeSet.2 hw₁)
    (by rw [hww]; exact Subgraph.mem_edgeSet.2 hw₂)

open scoped Classical in
/-- `M₁`-edges meeting a given component (as in C2b). -/
noncomputable def compM₁Edges (c : (altGraph M₁ M₂).ConnectedComponent) :
    Finset G.edgeSet :=
  univ.filter fun e : G.edgeSet =>
    (e : Sym2 V) ∈ M₁.edgeSet ∧
      (∀ v : V, v ∈ (e : Sym2 V) → v ∈ (altGraph M₁ M₂).support) ∧
      ∃ v : V, v ∈ (e : Sym2 V) ∧ (altGraph M₁ M₂).connectedComponentMk v = c

open scoped Classical in
/-- `M₂`-edges meeting a given component (as in C2b). -/
noncomputable def compM₂Edges (c : (altGraph M₁ M₂).ConnectedComponent) :
    Finset G.edgeSet :=
  univ.filter fun e : G.edgeSet =>
    (e : Sym2 V) ∈ M₂.edgeSet ∧
      (∀ v : V, v ∈ (e : Sym2 V) → v ∈ (altGraph M₁ M₂).support) ∧
      ∃ v : V, v ∈ (e : Sym2 V) ∧ (altGraph M₁ M₂).connectedComponentMk v = c

open scoped Classical in
/-- Edges shared by both matchings. -/
noncomputable def sharedEdges : Finset G.edgeSet :=
  univ.filter fun e : G.edgeSet =>
    (e : Sym2 V) ∈ M₁.edgeSet ∧ (e : Sym2 V) ∈ M₂.edgeSet

/-- With edge-disjoint matchings there are no shared edges. -/
lemma sharedEdges_empty_of_disjoint (hdisj : Disjoint M₁.edgeSet M₂.edgeSet) :
    sharedEdges M₁ M₂ = ∅ := by
  classical
  unfold sharedEdges
  rw [Finset.filter_eq_empty_iff]
  intro e _ he
  exact Set.disjoint_left.mp hdisj he.1 he.2

open scoped Classical in
/-- **The construction.**  Take `M₁` on the chosen components, `M₂` on the
rest, and the shared edges everywhere. -/
noncomputable def buildPM [Fintype (altGraph M₁ M₂).ConnectedComponent]
    (t : Finset ((altGraph M₁ M₂).ConnectedComponent)) : Finset G.edgeSet :=
  (t.biUnion (compM₁Edges M₁ M₂)) ∪
    ((univ \ t).biUnion (compM₂Edges M₁ M₂)) ∪ sharedEdges M₁ M₂

open scoped Classical in
/-- **C2c / (O2-surjectivity): `buildPM t` is a perfect matching.** -/
theorem isPMFinset_buildPM [Fintype (altGraph M₁ M₂).ConnectedComponent]
    (h₁ : M₁.IsPerfectMatching) (h₂ : M₂.IsPerfectMatching)
    (t : Finset ((altGraph M₁ M₂).ConnectedComponent)) :
    IsPMFinset G (buildPM M₁ M₂ t) := by
  classical
  intro v
  obtain ⟨w₁, hw₁, huniq₁⟩ := h₁.1 (h₁.2 v)
  obtain ⟨w₂, hw₂, huniq₂⟩ := h₂.1 (h₂.2 v)
  have hvmem₁ : v ∈ (mkEdge hw₁ : G.edgeSet).1 := Sym2.mem_mk_left v w₁
  have hvmem₂ : v ∈ (mkEdge hw₂ : G.edgeSet).1 := Sym2.mem_mk_left v w₂
  by_cases hv : v ∈ (altGraph M₁ M₂).support
  · -- ON the support: partners differ, and both edges are H-edges of v's component
    have hne : w₁ ≠ w₂ := partners_ne_of_mem_support M₁ M₂ huniq₁ huniq₂ hw₁ hw₂ hv
    -- a shared edge at `v` is impossible here
    have hnotshared : ∀ f : G.edgeSet, v ∈ (f : Sym2 V) →
        (f : Sym2 V) ∈ M₁.edgeSet → (f : Sym2 V) ∈ M₂.edgeSet → False := by
      intro f hvf hf₁ hf₂
      have e₁ := coe_eq_of_mem_edgeSet huniq₁ hvf hf₁
      have hM₂ : M₂.Adj v w₁ := by
        have : (s(v, w₁) : Sym2 V) ∈ M₂.edgeSet := by rw [← e₁]; exact hf₂
        exact Subgraph.mem_edgeSet.1 this
      exact hne (huniq₂ w₁ hM₂)
    -- both incident edges are H-edges, so BOTH their endpoints are in the
    -- support — this is what the new support conjunct needs.
    have hH₁ : (altGraph M₁ M₂).Adj v w₁ := by
      simp only [altGraph, symmDiff_def, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj,
        SimpleGraph.Subgraph.spanningCoe_adj]
      exact Or.inl ⟨hw₁, fun hM₂ => hne (huniq₂ w₁ hM₂)⟩
    have hH₂ : (altGraph M₁ M₂).Adj v w₂ := by
      simp only [altGraph, symmDiff_def, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj,
        SimpleGraph.Subgraph.spanningCoe_adj]
      exact Or.inr ⟨hw₂, fun hM₁ => hne (huniq₁ w₂ hM₁).symm⟩
    have hsupp₁ : ∀ u : V, u ∈ (mkEdge hw₁ : G.edgeSet).1 →
        u ∈ (altGraph M₁ M₂).support := by
      intro u hu
      rcases Sym2.mem_iff.1 hu with rfl | rfl
      · exact hv
      · exact ⟨v, hH₁.symm⟩
    have hsupp₂ : ∀ u : V, u ∈ (mkEdge hw₂ : G.edgeSet).1 →
        u ∈ (altGraph M₁ M₂).support := by
      intro u hu
      rcases Sym2.mem_iff.1 hu with rfl | rfl
      · exact hv
      · exact ⟨v, hH₂.symm⟩
    by_cases hc : (altGraph M₁ M₂).connectedComponentMk v ∈ t
    · refine ⟨mkEdge hw₁, ⟨?_, hvmem₁⟩, ?_⟩
      · refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
        refine Finset.mem_biUnion.mpr ⟨_, hc, ?_⟩
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, Subgraph.mem_edgeSet.2 hw₁, hsupp₁, v, hvmem₁, rfl⟩
      · rintro f ⟨hfmem, hvf⟩
        rcases Finset.mem_union.1 hfmem with hf | hf
        · rcases Finset.mem_union.1 hf with hf | hf
          · obtain ⟨c', -, hfc'⟩ := Finset.mem_biUnion.1 hf
            obtain ⟨_, hf₁, -, -⟩ := Finset.mem_filter.1 hfc'
            exact Subtype.ext (coe_eq_of_mem_edgeSet huniq₁ hvf hf₁)
          · exfalso
            obtain ⟨c', hc'not, hfc'⟩ := Finset.mem_biUnion.1 hf
            obtain ⟨_, hf₂, -, u, huf, hcu⟩ := Finset.mem_filter.1 hfc'
            -- `f` is the M₂-edge at `v`, hence an H-edge, so `u`'s component is `v`'s
            have hfeq : (f : Sym2 V) = s(v, w₂) := coe_eq_of_mem_edgeSet huniq₂ hvf hf₂
            have hHadj : (altGraph M₁ M₂).Adj v w₂ := hH₂
            have hcv : (altGraph M₁ M₂).connectedComponentMk v = c' := by
              rw [← hcu]
              rw [hfeq] at huf
              rcases Sym2.mem_iff.1 huf with rfl | rfl
              · rfl
              · exact (ConnectedComponent.sound hHadj.reachable)
            rw [Finset.mem_sdiff] at hc'not
            exact hc'not.2 (hcv ▸ hc)
        · exfalso
          obtain ⟨_, hf₁, hf₂⟩ := Finset.mem_filter.1 hf
          exact hnotshared f hvf hf₁ hf₂
    · refine ⟨mkEdge hw₂, ⟨?_, hvmem₂⟩, ?_⟩
      · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
        refine Finset.mem_biUnion.mpr ⟨_, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hc⟩, ?_⟩
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, Subgraph.mem_edgeSet.2 hw₂, hsupp₂, v, hvmem₂, rfl⟩
      · rintro f ⟨hfmem, hvf⟩
        rcases Finset.mem_union.1 hfmem with hf | hf
        · rcases Finset.mem_union.1 hf with hf | hf
          · exfalso
            obtain ⟨c', hc'mem, hfc'⟩ := Finset.mem_biUnion.1 hf
            obtain ⟨_, hf₁, -, u, huf, hcu⟩ := Finset.mem_filter.1 hfc'
            have hfeq : (f : Sym2 V) = s(v, w₁) := coe_eq_of_mem_edgeSet huniq₁ hvf hf₁
            have hHadj : (altGraph M₁ M₂).Adj v w₁ := hH₁
            have hcv : (altGraph M₁ M₂).connectedComponentMk v = c' := by
              rw [← hcu]
              rw [hfeq] at huf
              rcases Sym2.mem_iff.1 huf with rfl | rfl
              · rfl
              · exact (ConnectedComponent.sound hHadj.reachable)
            exact hc (hcv ▸ hc'mem)
          · obtain ⟨c', -, hfc'⟩ := Finset.mem_biUnion.1 hf
            obtain ⟨_, hf₂, -, -⟩ := Finset.mem_filter.1 hfc'
            exact Subtype.ext (coe_eq_of_mem_edgeSet huniq₂ hvf hf₂)
        · exfalso
          obtain ⟨_, hf₁, hf₂⟩ := Finset.mem_filter.1 hf
          exact hnotshared f hvf hf₁ hf₂
  · -- OFF the support: the two partners coincide, so the edge is shared
    have hww : w₁ = w₂ := partners_eq_of_not_mem_support M₁ M₂ h₂ hw₁ huniq₂ hv
    refine ⟨mkEdge hw₁, ⟨?_, hvmem₁⟩, ?_⟩
    · refine Finset.mem_union_right _ ?_
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Subgraph.mem_edgeSet.2 hw₁, ?_⟩
      -- `mkEdge hw₁`'s TYPE mentions `w₁`, so rewriting `w₁ → w₂` inside it
      -- gives "motive is not type correct"; strip to the plain `Sym2` first.
      show (s(v, w₁) : Sym2 V) ∈ M₂.edgeSet
      rw [hww]
      exact Subgraph.mem_edgeSet.2 hw₂
    · rintro f ⟨hfmem, hvf⟩
      refine Subtype.ext ?_
      rcases Finset.mem_union.1 hfmem with hf | hf
      · rcases Finset.mem_union.1 hf with hf | hf
        · -- impossible now: the support conjunct would put `v` in the support
          obtain ⟨c', -, hfc'⟩ := Finset.mem_biUnion.1 hf
          obtain ⟨_, -, hsup, -⟩ := Finset.mem_filter.1 hfc'
          exact absurd (hsup v hvf) hv
        · obtain ⟨c', -, hfc'⟩ := Finset.mem_biUnion.1 hf
          obtain ⟨_, -, hsup, -⟩ := Finset.mem_filter.1 hfc'
          exact absurd (hsup v hvf) hv
      · obtain ⟨_, hf₁, -⟩ := Finset.mem_filter.1 hf
        exact coe_eq_of_mem_edgeSet huniq₁ hvf hf₁

end Build

section Factorization

open Finset

open scoped symmDiff

variable {G : SimpleGraph V} (M₁ M₂ : G.Subgraph)

open scoped Classical in
/-- **The side choice, as a function on components.**  `usesM₁` is constant
along walks (C2a), which is exactly what `ConnectedComponent.lift` wants —
and since my walk lemma holds for arbitrary walks, the path-restricted
hypothesis is discharged by ignoring the path proof. -/
noncomputable def sideOf {F : Finset G.edgeSet}
    (hconst : ∀ (v w : V) (_p : (altGraph M₁ M₂).Walk v w),
      usesM₁ M₁ F v = usesM₁ M₁ F w) :
    (altGraph M₁ M₂).ConnectedComponent → Prop :=
  ConnectedComponent.lift (usesM₁ M₁ F) (fun v w p _ => hconst v w p)

open scoped Classical in
/-- The `M₁` factor of a component. -/
noncomputable def A {D : ℕ} (W : WeightSystem G D) (ι : V → Fin D)
    (c : (altGraph M₁ M₂).ConnectedComponent) : ℂ :=
  ∏ e ∈ compM₁Edges M₁ M₂ c, edgeWeight W ι e

open scoped Classical in
/-- The `M₂` factor of a component. -/
noncomputable def B {D : ℕ} (W : WeightSystem G D) (ι : V → Fin D)
    (c : (altGraph M₁ M₂).ConnectedComponent) : ℂ :=
  ∏ e ∈ compM₂Edges M₁ M₂ c, edgeWeight W ι e

open scoped Classical in
/-- **The distributivity end of C2b**, instantiated at the component factors:
choosing a side per component and summing gives the product of the sums.
This is `Finset.prod_add`; the content of C2b is matching the left side to
`pmSum`, which is obligations (O1) and (O2) in the header. -/
theorem prod_add_components {D : ℕ} (W : WeightSystem G D) (ι : V → Fin D)
    :
    ∏ c : (altGraph M₁ M₂).ConnectedComponent,
        (A M₁ M₂ W ι c + B M₁ M₂ W ι c)
      = ∑ t ∈ (univ : Finset ((altGraph M₁ M₂).ConnectedComponent)).powerset,
          (∏ c ∈ t, A M₁ M₂ W ι c) * ∏ c ∈ univ \ t, B M₁ M₂ W ι c :=
  Finset.prod_add _ _ _


/-- **O1a.** A perfect-matching finset contained in M₁ ∪ M₂ is `buildPM` of the
components on which it uses `M₁`.  Proof: per-component side constancy via
`usesM₁_iff_of_walk`, then edge partition. -/
lemma pm_eq_buildPM [Fintype (altGraph M₁ M₂).ConnectedComponent]
    (h₁ : M₁.IsPerfectMatching) (h₂ : M₂.IsPerfectMatching) {F : Finset G.edgeSet}
    (hPM : IsPMFinset G F)
    (hsub : ∀ e ∈ F, (e : Sym2 V) ∈ M₁.edgeSet ∨ (e : Sym2 V) ∈ M₂.edgeSet) :
    ∃ t : Finset ((altGraph M₁ M₂).ConnectedComponent), F = buildPM M₁ M₂ t := by
  classical
  refine ⟨univ.filter
    (fun c => ∃ v, (altGraph M₁ M₂).connectedComponentMk v = c ∧ usesM₁ M₁ F v), ?_⟩
  ext e
  constructor
  · -- fwd: e ∈ F → e ∈ buildPM (shared / compM₁ / compM₂ partition)
    intro he
    by_cases hsh : (e : Sym2 V) ∈ M₁.edgeSet ∧ (e : Sym2 V) ∈ M₂.edgeSet
    · -- shared edge of F → third union
      exact Finset.mem_union.2 (Or.inr (Finset.mem_filter.2 ⟨Finset.mem_univ e, hsh⟩))
    · push Not at hsh
      obtain ⟨v, hve⟩ : ∃ v, v ∈ (e : Sym2 V) := by
        rcases e with ⟨z, hz⟩
        obtain ⟨⟨x, y⟩, rfl⟩ := Quot.exists_rep z
        exact ⟨x, Sym2.mem_mk_left x y⟩
      by_cases hv : v ∈ (altGraph M₁ M₂).support
      · by_cases hu : usesM₁ M₁ F v
        · -- compM₁ side: e is the M₁-edge at v
          obtain ⟨w₁, hw₁, huniq₁⟩ := h₁.1 (h₁.2 v)
          obtain ⟨w₂, hw₂, huniq₂⟩ := h₂.1 (h₂.2 v)
          have hne : w₁ ≠ w₂ := partners_ne_of_mem_support M₁ M₂ huniq₁ huniq₂ hw₁ hw₂ hv
          obtain ⟨f, hfF, hvf, hfM₁⟩ := hu
          obtain ⟨g, hg, huniqF⟩ := hPM v
          have heq : e = f :=
            (huniqF e ⟨he, hve⟩).trans (huniqF f ⟨hfF, hvf⟩).symm
          have heM₁ : (e : Sym2 V) ∈ M₁.edgeSet := by rw [heq]; exact hfM₁
          have e₁ : (e : Sym2 V) = s(v, w₁) := coe_eq_of_mem_edgeSet huniq₁ hve heM₁
          have hH₁ : (altGraph M₁ M₂).Adj v w₁ := by
            simp only [altGraph, symmDiff_def, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj,
              SimpleGraph.Subgraph.spanningCoe_adj]
            exact Or.inl ⟨hw₁, fun hM₂ => hne (huniq₂ w₁ hM₂)⟩
          have hsupp : ∀ u : V, u ∈ (e : Sym2 V) → u ∈ (altGraph M₁ M₂).support := by
            intro u hum
            rw [e₁] at hum
            rcases Sym2.mem_iff.1 hum with rfl | rfl
            · exact hv
            · exact ⟨v, hH₁.symm⟩
          have hmem : e ∈ compM₁Edges M₁ M₂ ((altGraph M₁ M₂).connectedComponentMk v) :=
            Finset.mem_filter.2 ⟨Finset.mem_univ e, heM₁, hsupp, ⟨v, hve, rfl⟩⟩
          exact Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl
            (Finset.mem_biUnion.2 ⟨(altGraph M₁ M₂).connectedComponentMk v,
              Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨v, rfl, ⟨f, hfF, hvf, hfM₁⟩⟩⟩, hmem⟩))))
        · -- compM₂ side: e is the M₂-edge at v
          obtain ⟨w₁, hw₁, huniq₁⟩ := h₁.1 (h₁.2 v)
          obtain ⟨w₂, hw₂, huniq₂⟩ := h₂.1 (h₂.2 v)
          have hne : w₁ ≠ w₂ := partners_ne_of_mem_support M₁ M₂ huniq₁ huniq₂ hw₁ hw₂ hv
          have heM₂ : (e : Sym2 V) ∈ M₂.edgeSet := by
            rcases hsub e he with hM₁ | hM₂
            · exact absurd ⟨e, he, hve, hM₁⟩ hu
            · exact hM₂
          have e₂ : (e : Sym2 V) = s(v, w₂) := coe_eq_of_mem_edgeSet huniq₂ hve heM₂
          have hH₂ : (altGraph M₁ M₂).Adj v w₂ := by
            simp only [altGraph, symmDiff_def, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj,
              SimpleGraph.Subgraph.spanningCoe_adj]
            exact Or.inr ⟨hw₂, fun hM₁ => hne (huniq₁ w₂ hM₁).symm⟩
          have hsupp : ∀ u : V, u ∈ (e : Sym2 V) → u ∈ (altGraph M₁ M₂).support := by
            intro u hum
            rw [e₂] at hum
            rcases Sym2.mem_iff.1 hum with rfl | rfl
            · exact hv
            · exact ⟨v, hH₂.symm⟩
          have hnot : (altGraph M₁ M₂).connectedComponentMk v ∉
              univ.filter
                (fun c => ∃ v, (altGraph M₁ M₂).connectedComponentMk v = c ∧ usesM₁ M₁ F v) := by
            intro hct
            obtain ⟨u, huq, hum1⟩ := (Finset.mem_filter.1 hct).2
            have hreach : (altGraph M₁ M₂).Reachable u v :=
              SimpleGraph.ConnectedComponent.exact huq
            exact hu ((usesM₁_iff_of_reachable h₁ h₂ hPM hsub hreach).1 hum1)
          have hmem : e ∈ compM₂Edges M₁ M₂ ((altGraph M₁ M₂).connectedComponentMk v) :=
            Finset.mem_filter.2 ⟨Finset.mem_univ e, heM₂, hsupp, ⟨v, hve, rfl⟩⟩
          exact Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inr
            (Finset.mem_biUnion.2 ⟨(altGraph M₁ M₂).connectedComponentMk v,
              Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hnot⟩, hmem⟩))))
      · have hboth := shared_of_not_mem_support h₁ h₂ hsub hv he hve
        exact absurd hboth.2 (hsh hboth.1)
  · -- rev: e ∈ buildPM → e ∈ F (PM-uniqueness + side constancy)
    intro he
    rcases Finset.mem_union.1 he with hab | hsh
    · rcases Finset.mem_union.1 hab with h1 | h2
      · -- e ∈ compM₁Edges of a chosen component
        obtain ⟨c, hct, hmem⟩ := Finset.mem_biUnion.1 h1
        obtain ⟨_, heM₁, -, v, hve, hvc⟩ := Finset.mem_filter.1 hmem
        obtain ⟨_, u, huq, hum1⟩ := Finset.mem_filter.1 hct
        have hreach : (altGraph M₁ M₂).Reachable u v :=
          SimpleGraph.ConnectedComponent.exact (huq.trans hvc.symm)
        obtain ⟨f, hfF, hvf, hfM₁⟩ :=
          (usesM₁_iff_of_reachable h₁ h₂ hPM hsub hreach).1 hum1
        obtain ⟨w₁, hw₁, huniq₁⟩ := h₁.1 (h₁.2 v)
        have e₁ : (e : Sym2 V) = s(v, w₁) := coe_eq_of_mem_edgeSet huniq₁ hve heM₁
        have f₁ : (f : Sym2 V) = s(v, w₁) := coe_eq_of_mem_edgeSet huniq₁ hvf hfM₁
        have hef : e = f := Subtype.ext (e₁.trans f₁.symm)
        rwa [hef]
      · -- e ∈ compM₂Edges of an unchosen component
        obtain ⟨c, hct, hmem⟩ := Finset.mem_biUnion.1 h2
        obtain ⟨_, heM₂, -, v, hve, hvc⟩ := Finset.mem_filter.1 hmem
        have hnot := (Finset.mem_sdiff.1 hct).2
        have hvnot : ¬ usesM₁ M₁ F v := by
          intro hu
          exact hnot (Finset.mem_filter.2 ⟨Finset.mem_univ c, ⟨v, hvc, hu⟩⟩)
        obtain ⟨f, ⟨hfF, hvf⟩, -⟩ := hPM v
        have hfM₂ : (f : Sym2 V) ∈ M₂.edgeSet := by
          rcases hsub f hfF with hM₁ | hM₂
          · exact absurd ⟨f, hfF, hvf, hM₁⟩ hvnot
          · exact hM₂
        obtain ⟨w₂, hw₂, huniq₂⟩ := h₂.1 (h₂.2 v)
        have e₂ : (e : Sym2 V) = s(v, w₂) := coe_eq_of_mem_edgeSet huniq₂ hve heM₂
        have f₂ : (f : Sym2 V) = s(v, w₂) := coe_eq_of_mem_edgeSet huniq₂ hvf hfM₂
        have hef : e = f := Subtype.ext (e₂.trans f₂.symm)
        rwa [hef]
    · -- shared edge: e equals the F-edge at either endpoint
      obtain ⟨_, heM₁, heM₂⟩ := Finset.mem_filter.1 hsh
      obtain ⟨v, hve⟩ : ∃ v, v ∈ (e : Sym2 V) := by
        rcases e with ⟨z, hz⟩
        obtain ⟨⟨x, y⟩, rfl⟩ := Quot.exists_rep z
        exact ⟨x, Sym2.mem_mk_left x y⟩
      obtain ⟨f, ⟨hfF, hvf⟩, -⟩ := hPM v
      rcases hsub f hfF with hM₁ | hM₂
      · obtain ⟨w₁, hw₁, huniq₁⟩ := h₁.1 (h₁.2 v)
        have e₁ : (e : Sym2 V) = s(v, w₁) := coe_eq_of_mem_edgeSet huniq₁ hve heM₁
        have f₁ : (f : Sym2 V) = s(v, w₁) := coe_eq_of_mem_edgeSet huniq₁ hvf hM₁
        have hef : e = f := Subtype.ext (e₁.trans f₁.symm)
        rwa [hef]
      · obtain ⟨w₂, hw₂, huniq₂⟩ := h₂.1 (h₂.2 v)
        have e₂ : (e : Sym2 V) = s(v, w₂) := coe_eq_of_mem_edgeSet huniq₂ hve heM₂
        have f₂ : (f : Sym2 V) = s(v, w₂) := coe_eq_of_mem_edgeSet huniq₂ hvf hM₂
        have hef : e = f := Subtype.ext (e₂.trans f₂.symm)
        rwa [hef]

/-- With edge-disjoint matchings, `buildPM t` uses the `M₁`-edge at `v` iff the component of `v` lies in `t`. Crux inverse law for the powerset bijection in `pmSum_factor`. -/
lemma buildPM_usesM₁_iff [Fintype (altGraph M₁ M₂).ConnectedComponent]
    (h₁ : M₁.IsPerfectMatching) (h₂ : M₂.IsPerfectMatching)
    (hdisj : Disjoint M₁.edgeSet M₂.edgeSet)
    (t : Finset ((altGraph M₁ M₂).ConnectedComponent)) (v : V) :
    usesM₁ M₁ (buildPM M₁ M₂ t) v ↔ (altGraph M₁ M₂).connectedComponentMk v ∈ t := by
  classical
  obtain ⟨w₁, hw₁, huniq₁⟩ := h₁.1 (h₁.2 v)
  obtain ⟨w₂, hw₂, huniq₂⟩ := h₂.1 (h₂.2 v)
  have hvmem₁ : v ∈ (mkEdge hw₁ : G.edgeSet).1 := Sym2.mem_mk_left v w₁
  have hv : v ∈ (altGraph M₁ M₂).support := mem_support_of_disjoint M₁ M₂ h₁ h₂ hdisj v
  have hne : w₁ ≠ w₂ := partners_ne_of_mem_support M₁ M₂ huniq₁ huniq₂ hw₁ hw₂ hv
  have hH₁ : (altGraph M₁ M₂).Adj v w₁ := by
    simp only [altGraph, symmDiff_def, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj,
      SimpleGraph.Subgraph.spanningCoe_adj]
    exact Or.inl ⟨hw₁, fun hM₂ => hne (huniq₂ w₁ hM₂)⟩
  have hsupp₁ : ∀ u : V, u ∈ (mkEdge hw₁ : G.edgeSet).1 → u ∈ (altGraph M₁ M₂).support := by
    intro u hu
    rcases Sym2.mem_iff.1 hu with rfl | rfl
    · exact hv
    · exact ⟨v, hH₁.symm⟩
  constructor
  · rintro ⟨e, heF, hv_e, he₁⟩
    unfold buildPM at heF
    rcases Finset.mem_union.1 heF with hf | hf
    · rcases Finset.mem_union.1 hf with hf | hf
      · obtain ⟨c₂, hc₂, hfc⟩ := Finset.mem_biUnion.1 hf
        obtain ⟨_, -, -, u, huf, hcu⟩ := Finset.mem_filter.1 hfc
        have hfeq : (e : Sym2 V) = s(v, w₁) := coe_eq_of_mem_edgeSet huniq₁ hv_e he₁
        rw [hfeq] at huf
        have hcv : (altGraph M₁ M₂).connectedComponentMk v = c₂ := by
          rcases Sym2.mem_iff.1 huf with rfl | rfl
          · exact hcu
          · rw [ConnectedComponent.sound hH₁.reachable]; exact hcu
        rw [hcv]; exact hc₂
      · exfalso
        obtain ⟨c₂, -, hfc⟩ := Finset.mem_biUnion.1 hf
        obtain ⟨_, hf₂, -, -⟩ := Finset.mem_filter.1 hfc
        exact Set.disjoint_left.mp hdisj he₁ hf₂
    · exfalso
      obtain ⟨_, hf₁, hf₂⟩ := Finset.mem_filter.1 hf
      exact Set.disjoint_left.mp hdisj he₁ hf₂

  · intro hc
    exact ⟨mkEdge hw₁,
      Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_biUnion.mpr ⟨_, hc, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, Subgraph.mem_edgeSet.2 hw₁, hsupp₁, v, hvmem₁, rfl⟩⟩)),
      hvmem₁, Subgraph.mem_edgeSet.2 hw₁⟩


lemma ccMk_eq_of_M₁_edge (hdisj : Disjoint M₁.edgeSet M₂.edgeSet)
    {e : G.edgeSet} (he₁ : (e : Sym2 V) ∈ M₁.edgeSet)
    {v w : V} (hv : v ∈ (e : Sym2 V)) (hw : w ∈ (e : Sym2 V)) :
    (altGraph M₁ M₂).connectedComponentMk v =
      (altGraph M₁ M₂).connectedComponentMk w := by
  classical
  obtain ⟨u, hu⟩ := Sym2.mem_iff_exists.1 hv
  have hadj₁ : M₁.Adj v u := by
    rw [hu] at he₁
    exact Subgraph.mem_edgeSet.1 he₁
  have hAg : (altGraph M₁ M₂).Adj v u := by
    simp only [altGraph, symmDiff_def, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj,
      SimpleGraph.Subgraph.spanningCoe_adj]
    exact Or.inl ⟨hadj₁, fun hM₂ =>
      Set.disjoint_left.mp hdisj (Subgraph.mem_edgeSet.2 hadj₁) (Subgraph.mem_edgeSet.2 hM₂)⟩
  rw [hu, Sym2.mem_iff] at hw
  rcases hw with rfl | rfl
  · rfl
  · exact ConnectedComponent.sound hAg.reachable
/-- Endpoints of an M₂-edge lie in the same alternating component. -/
lemma ccMk_eq_of_M₂_edge (hdisj : Disjoint M₁.edgeSet M₂.edgeSet)
    {e : G.edgeSet} (he₂ : (e : Sym2 V) ∈ M₂.edgeSet)
    {v w : V} (hv : v ∈ (e : Sym2 V)) (hw : w ∈ (e : Sym2 V)) :
    (altGraph M₁ M₂).connectedComponentMk v =
      (altGraph M₁ M₂).connectedComponentMk w := by
  classical
  obtain ⟨u, hu⟩ := Sym2.mem_iff_exists.1 hv
  have hadj₂ : M₂.Adj v u := by
    rw [hu] at he₂
    exact Subgraph.mem_edgeSet.1 he₂
  have hAg : (altGraph M₁ M₂).Adj v u := by
    simp only [altGraph, symmDiff_def, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj,
      SimpleGraph.Subgraph.spanningCoe_adj]
    exact Or.inr ⟨hadj₂, fun hM₁ =>
      Set.disjoint_left.mp hdisj (Subgraph.mem_edgeSet.2 hM₁) (Subgraph.mem_edgeSet.2 hadj₂)⟩
  rw [hu, Sym2.mem_iff] at hw
  rcases hw with rfl | rfl
  · rfl
  · exact ConnectedComponent.sound hAg.reachable

open Classical in
/-- Weight factorisation over `buildPM t`: the product of edge weights splits
into `A` over the chosen components and `B` over the rest. -/
lemma edgeWeight_prod_buildPM (W : WeightSystem G D) (ι : V → Fin D)
    (hdisj : Disjoint M₁.edgeSet M₂.edgeSet)
    [Fintype (altGraph M₁ M₂).ConnectedComponent]
    (t : Finset ((altGraph M₁ M₂).ConnectedComponent)) :
    ∏ e ∈ buildPM M₁ M₂ t, edgeWeight W ι e =
      (∏ c ∈ t, A M₁ M₂ W ι c) * ∏ c ∈ univ \ t, B M₁ M₂ W ι c := by
  classical
  have hdj : Disjoint (t.biUnion (compM₁Edges M₁ M₂))
      ((univ \ t).biUnion (compM₂Edges M₁ M₂)) := by
    rw [Finset.disjoint_left]
    intro e he₁ he₂
    rw [Finset.mem_biUnion] at he₁ he₂
    obtain ⟨c₁, -, he₁'⟩ := he₁
    obtain ⟨c₂, -, he₂'⟩ := he₂
    exact Set.disjoint_left.mp hdisj (Finset.mem_filter.1 he₁').2.1
      (Finset.mem_filter.1 he₂').2.1
  have hpw₁ : Set.PairwiseDisjoint (t : Set ((altGraph M₁ M₂).ConnectedComponent)) (compM₁Edges M₁ M₂) := by
    intro c₁ hc₁ c₂ hc₂ hne
    simp only [Function.onFun, Finset.disjoint_left]
    intro e he₁ he₂
    obtain ⟨hu₁, hMe, hx₁, v, hv, hcv⟩ := Finset.mem_filter.1 he₁
    obtain ⟨hu₂, hx₂, hx₃, w, hw, hcw⟩ := Finset.mem_filter.1 he₂
    exact hne (hcv.symm.trans ((ccMk_eq_of_M₁_edge M₁ M₂ hdisj hMe hv hw).trans hcw))
  have hpw₂ : (↑(univ \ t) : Set ((altGraph M₁ M₂).ConnectedComponent)).PairwiseDisjoint (compM₂Edges M₁ M₂) := by
    intro c₁ hc₁ c₂ hc₂ hne
    simp only [Function.onFun, Finset.disjoint_left]
    intro e he₁ he₂
    obtain ⟨hu₁, hMe, hx₁, v, hv, hcv⟩ := Finset.mem_filter.1 he₁
    obtain ⟨hu₂, hx₂, hx₃, w, hw, hcw⟩ := Finset.mem_filter.1 he₂
    exact hne (hcv.symm.trans ((ccMk_eq_of_M₂_edge M₁ M₂ hdisj hMe hv hw).trans hcw))
  unfold buildPM
  rw [sharedEdges_empty_of_disjoint M₁ M₂ hdisj, Finset.union_empty,
    Finset.prod_union hdj, Finset.prod_biUnion hpw₁, Finset.prod_biUnion hpw₂]
  congr 1

/-- **O1.** pmSum factorization over the symmetric-difference components:
the sum over PMs equals the shared-edge product times the product over
components of (A_c + B_c).  Proof: `pm_eq_buildPM` bijection over the
powerset, `prod_biUnion`, and `prod_add_components`.

NOTE: edge-disjointness `hdisj` is REQUIRED — without it, shared edges make
degenerate singleton ConnectedComponents with A = B = 1 (empty products),
contributing a spurious factor 2 each, so the equation fails.  With `hdisj`
there are no shared edges and every component is an alternating cycle of
length ≥ 4, so the bijection ranges over the full powerset. -/
theorem pmSum_factor {D : ℕ} (W : WeightSystem G D) (ι : V → Fin D)
    (h₁ : M₁.IsPerfectMatching) (h₂ : M₂.IsPerfectMatching)
    (hdisj : Disjoint M₁.edgeSet M₂.edgeSet)
    (hsupp : ∀ (e : G.edgeSet) (i j : Fin D), W e i j ≠ 0 →
      ((e : Sym2 V) ∈ M₁.edgeSet ∨ (e : Sym2 V) ∈ M₂.edgeSet) ∧ i = j)
    [Fintype (altGraph M₁ M₂).ConnectedComponent] :
    pmSum W ι = ∏ c, (A M₁ M₂ W ι c + B M₁ M₂ W ι c) := by
  classical
  rw [pmSum_restrict W hsupp ι]
  have hfin : ‹Fintype (altGraph M₁ M₂).ConnectedComponent› =
      (altGraph M₁ M₂).instFintypeConnectedComponent := Subsingleton.elim _ _
  rw [hfin]
  conv_rhs => rw [prod_add_components M₁ M₂ W ι]
  refine (Finset.sum_bij (fun t _ => buildPM M₁ M₂ t) ?hmem ?hinj ?hsurj ?hval).symm
  case hmem =>
    intro t ht
    rw [Finset.mem_filter, Finset.mem_filter]
    refine ⟨⟨Finset.mem_univ _, isPMFinset_buildPM M₁ M₂ h₁ h₂ t⟩, fun e he => ?_⟩
    simp only [buildPM, compM₁Edges, compM₂Edges, sharedEdges, Finset.mem_union,
      Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at he
    tauto
  case hinj =>
    intro t₁ ht₁ t₂ ht₂ heq
    ext c
    obtain ⟨v, rfl⟩ := Quot.exists_rep c
    change (altGraph M₁ M₂).connectedComponentMk v ∈ t₁ ↔
      (altGraph M₁ M₂).connectedComponentMk v ∈ t₂
    rw [← buildPM_usesM₁_iff M₁ M₂ h₁ h₂ hdisj t₁ v, ← buildPM_usesM₁_iff M₁ M₂ h₁ h₂ hdisj t₂ v, heq]
  case hsurj =>
    intro F hF
    rw [Finset.mem_filter, Finset.mem_filter] at hF
    obtain ⟨t, rfl⟩ := pm_eq_buildPM M₁ M₂ h₁ h₂ hF.1.2 hF.2
    exact ⟨t, by simpa using Finset.mem_powerset.2 (Finset.subset_univ t), rfl⟩
  case hval =>
    intro t ht
    rw [← hfin]
    exact (edgeWeight_prod_buildPM M₁ M₂ W ι hdisj t).symm
end Factorization

end Krenn
