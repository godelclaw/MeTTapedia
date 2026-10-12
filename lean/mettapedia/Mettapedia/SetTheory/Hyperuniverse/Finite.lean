import Mettapedia.SetTheory.Hyperuniverse.Membership
import Mettapedia.TypeTheory.MaterialSets.Hypersets.Hyperset
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Logic.Relation

/-!
# Finite hypersets inside the closed-set limit

A finite accessible pointed graph determines a thread: at each stage, the
picture of a node is the set of pictures of its children. Bisimilar nodes
determine the same thread, so the construction descends to hypersets that
have a finite presentation. Membership is preserved, the resulting map is
injective, and its image meets every basic neighbourhood of the limit.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Hyperuniverse

open Set Topology TopologicalSpace TopologicalSpace.Compacts
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Mettapedia.TypeTheory.MaterialSets.Hypersets.AccessiblePointedGraph

/-! ## Approximations of a finite graph -/

/-- The stage-`n` picture of a node: the set of stage-`n` pictures of its children. -/
def approxAt {α : Type} [Finite α] (r : α → α → Prop) (a : α) : (n : ℕ) → Stage n
  | 0 => PUnit.unit
  | n + 1 =>
    ⟨range (fun b : {b // r a b} => approxAt r b.1 n), (finite_range _).isCompact⟩

theorem approxAt_succ_coe {α : Type} [Finite α] (r : α → α → Prop) (a : α) (n : ℕ) :
    (approxAt r a (n + 1) : Set (Stage n)) =
      range (fun b : {b // r a b} => approxAt r b.1 n) :=
  rfl

theorem approxAt_compat {α : Type} [Finite α] (r : α → α → Prop) (a : α) :
    ∀ n, bond n (approxAt r a (n + 1)) = approxAt r a n
  | 0 => Subsingleton.elim _ _
  | n + 1 => by
      apply Compacts.ext
      ext x
      constructor
      · intro hx
        rw [bond_succ, coe_map, mem_image] at hx
        rcases hx with ⟨y, hy, hbond⟩
        rw [approxAt_succ_coe] at hy
        rcases hy with ⟨c, rfl⟩
        rw [approxAt_compat r c.1 n] at hbond
        rw [approxAt_succ_coe]
        exact ⟨c, hbond⟩
      · intro hx
        rw [approxAt_succ_coe] at hx
        rcases hx with ⟨c, rfl⟩
        rw [bond_succ, coe_map, mem_image]
        refine ⟨approxAt r c.1 (n + 1), ?_, approxAt_compat r c.1 n⟩
        rw [approxAt_succ_coe]
        exact ⟨c, rfl⟩

/-- The thread of pictures of a node. -/
def approx {α : Type} [Finite α] (r : α → α → Prop) (a : α) : N where
  atStage := approxAt r a
  compat := approxAt_compat r a

/-- A point with one childless child. -/
def oneEmpty : AccessiblePointedGraph.{0} :=
  sup (fun _ : PUnit.{1} => empty.{0})

example : oneEmpty.edge oneEmpty.point (some ⟨PUnit.unit, empty.point⟩) :=
  SupEdge.point PUnit.unit

example : ¬ oneEmpty.edge oneEmpty.point none := by
  intro h
  obtain ⟨_, hnone⟩ := supEdge_none_iff.mp h
  cases hnone

instance finite_empty_node : Finite empty.Node := by
  refine Finite.of_injective (fun _ : empty.Node => PUnit.unit) fun a b _ => ?_
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some w => exact PEmpty.elim w.1
  | some w => exact PEmpty.elim w.1

instance finite_oneEmpty_node : Finite oneEmpty.Node := by
  refine Finite.of_injective
      (fun x : oneEmpty.Node =>
        match x with
        | none => (false : Bool)
        | some _ => true)
      ?_
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some _ => cases h
  | some w =>
    cases b with
    | none => cases h
    | some w' =>
      cases w with
      | mk i n =>
        cases w' with
        | mk i' n' =>
          cases i
          cases i'
          cases n with
          | none =>
            cases n' with
            | none => rfl
            | some v => exact PEmpty.elim v.1
          | some v => exact PEmpty.elim v.1

theorem approxAt_empty_one :
    approxAt empty.edge empty.point 1 = ⊥ := by
  apply Compacts.ext
  rw [approxAt_succ_coe, coe_bot]
  exact range_eq_empty_iff.mpr ⟨fun b => not_edge_empty b.1 b.2⟩

theorem approxAt_oneEmpty_one :
    approxAt oneEmpty.edge oneEmpty.point 1 = ⊤ := by
  apply Compacts.ext
  rw [approxAt_succ_coe, coe_top, range_eq_univ]
  intro x
  exact ⟨⟨some ⟨PUnit.unit, empty.point⟩, SupEdge.point _⟩, Subsingleton.elim _ _⟩

example : approxAt empty.edge empty.point 1 = ⊥ := approxAt_empty_one

example : approxAt empty.edge empty.point 1 ≠ approxAt oneEmpty.edge oneEmpty.point 1 := by
  intro h
  exact stage_one_bot_ne_top (approxAt_empty_one.symm.trans (h.trans approxAt_oneEmpty_one))

example : proj 1 (approx empty.edge empty.point) = ⊥ := by
  simpa [approx, proj] using approxAt_empty_one

example : approx empty.edge empty.point ≠ approx oneEmpty.edge oneEmpty.point := by
  intro h
  have := congrArg (proj 1) h
  exact stage_one_bot_ne_top <|
    approxAt_empty_one.symm.trans (this.trans approxAt_oneEmpty_one)

theorem approxAt_mono_eq {α β : Type} [Finite α] [Finite β]
    {r : α → α → Prop} {s : β → β → Prop} {a : α} {b : β} {m n : ℕ}
    (h : approxAt r a m = approxAt s b m) (hn : n ≤ m) :
    approxAt r a n = approxAt s b n := by
  induction m generalizing n with
  | zero =>
    obtain rfl : n = 0 := Nat.eq_zero_of_le_zero hn
    exact h
  | succ m ih =>
    by_cases hn' : n = m + 1
    · subst hn'
      exact h
    · have hpred : approxAt r a m = approxAt s b m := by
        have hbnd := congrArg (bond m) h
        rw [approxAt_compat, approxAt_compat] at hbnd
        exact hbnd
      exact ih hpred (Nat.le_of_lt_succ (lt_of_le_of_ne hn hn'))

theorem approxAt_eq_of_bisimilar {α β : Type} [Finite α] [Finite β]
    {r : α → α → Prop} {s : β → β → Prop} {a : α} {b : β}
    (h : Bisimilar r s a b) : ∀ n, approxAt r a n = approxAt s b n
  | 0 => Subsingleton.elim _ _
  | n + 1 => by
      apply Compacts.ext
      ext x
      rw [approxAt_succ_coe, approxAt_succ_coe]
      constructor
      · rintro ⟨c, rfl⟩
        obtain ⟨d, hd, hbis⟩ := h.exists_child_left c.2
        exact ⟨⟨d, hd⟩, (approxAt_eq_of_bisimilar hbis n).symm⟩
      · rintro ⟨d, rfl⟩
        obtain ⟨c, hc, hbis⟩ := h.exists_child_right d.2
        exact ⟨⟨c, hc⟩, approxAt_eq_of_bisimilar hbis n⟩

theorem member_approx_of_edge {α : Type} [Finite α] (r : α → α → Prop) {a c : α}
    (h : r a c) : member (approx r c) (approx r a) := by
  rw [member, fixedHomeo_decode]
  intro n
  have hproj : proj n (approx r c) = approxAt r c n := rfl
  have hcoe : ((approx r a).atStage (n + 1) : Set (Stage n)) =
      (approxAt r a (n + 1) : Set (Stage n)) := rfl
  rw [hproj, hcoe, approxAt_succ_coe]
  exact ⟨⟨c, h⟩, rfl⟩

/-- Matching at a later level implies matching at every earlier level. -/
theorem match_le {γ : Type} (p : ℕ → γ → Prop)
    (hmono : ∀ n c, p (n + 1) c → p n c) {c : γ} {m n : ℕ}
    (h : p m c) (hn : n ≤ m) : p n c := by
  induction m generalizing n with
  | zero =>
    obtain rfl : n = 0 := Nat.eq_zero_of_le_zero hn
    exact h
  | succ m ih =>
    by_cases hn' : n = m + 1
    · subst hn'
      exact h
    · exact ih (hmono m c h) (Nat.le_of_lt_succ (lt_of_le_of_ne hn hn'))

/-- One index that matches at every level, from nested nonempty finite choices. -/
theorem exists_forever_match {γ : Type} [Finite γ] (p : ℕ → γ → Prop)
    (hmono : ∀ n c, p (n + 1) c → p n c) (hne : ∀ n, ∃ c, p n c) :
    ∃ c, ∀ n, p n c := by
  classical
  let f : ℕ → γ := fun n => Classical.choose (hne n)
  obtain ⟨c, hc⟩ := Finite.exists_infinite_fiber f
  refine ⟨c, ?_⟩
  intro n
  have hge : ∃ m, n ≤ m ∧ f m = c := by
    by_contra h
    push Not at h
    have hfin : Finite (f ⁻¹' {c}) := by
      let emb : (f ⁻¹' {c}) → Fin n := fun z =>
        ⟨z.1, by
          have hnot : ¬ n ≤ z.1 := fun hle => h z.1 hle z.2
          omega⟩
      exact Finite.of_injective emb fun a b hab => Subtype.ext (congrArg Fin.val hab)
    exact hc.not_finite hfin
  obtain ⟨m, hm, hfm⟩ := hge
  have hspec : p m (f m) := Classical.choose_spec (hne m)
  exact match_le p hmono (hfm ▸ hspec) hm

theorem bisimilar_of_approxAt {α β : Type} [Finite α] [Finite β]
    {r : α → α → Prop} {s : β → β → Prop} {a : α} {b : β}
    (h : ∀ n, approxAt r a n = approxAt s b n) : Bisimilar r s a b := by
  refine ⟨fun x y => ∀ n, approxAt r x n = approxAt s y n, ?_, h⟩
  intro x y hxy
  constructor
  · intro x' hx
    have hne : ∀ n, ∃ c : {c // s y c}, approxAt r x' n = approxAt s c.1 n := by
      intro n
      have hmem : approxAt r x' n ∈ (approxAt r x (n + 1) : Set (Stage n)) := by
        rw [approxAt_succ_coe]
        exact ⟨⟨x', hx⟩, rfl⟩
      rw [hxy (n + 1), approxAt_succ_coe] at hmem
      rcases hmem with ⟨c, hc⟩
      exact ⟨c, hc.symm⟩
    obtain ⟨c, hall⟩ := exists_forever_match
      (fun n (c : {c // s y c}) => approxAt r x' n = approxAt s c.1 n)
      (fun n c heq => approxAt_mono_eq heq (Nat.le_succ n)) hne
    exact ⟨c.1, c.2, hall⟩
  · intro y' hy
    have hne : ∀ n, ∃ c : {c // r x c}, approxAt s y' n = approxAt r c.1 n := by
      intro n
      have hmem : approxAt s y' n ∈ (approxAt s y (n + 1) : Set (Stage n)) := by
        rw [approxAt_succ_coe]
        exact ⟨⟨y', hy⟩, rfl⟩
      rw [(hxy (n + 1)).symm, approxAt_succ_coe] at hmem
      rcases hmem with ⟨c, hc⟩
      exact ⟨c, hc.symm⟩
    obtain ⟨c, hall⟩ := exists_forever_match
      (fun n (c : {c // r x c}) => approxAt s y' n = approxAt r c.1 n)
      (fun n c heq => approxAt_mono_eq heq (Nat.le_succ n)) hne
    exact ⟨c.1, c.2, fun n => (hall n).symm⟩

theorem member_approx_levels {α β : Type} [Finite α] [Finite β]
    {r : α → α → Prop} {s : β → β → Prop} {a : α} {b : β} :
    member (approx s b) (approx r a) ↔
      ∀ n, approxAt s b n ∈ (approxAt r a (n + 1) : Set (Stage n)) := by
  rw [member, fixedHomeo_decode]
  constructor
  · intro h n
    have hn : proj n (approx s b) ∈ ((approx r a).atStage (n + 1) : Set (Stage n)) := by
      simpa [decode, decodeCarrier, approx, proj] using h n
    exact hn
  · intro h n
    simpa [decode, decodeCarrier, approx, proj] using h n

theorem member_approx_iff_bisimilar {α β : Type} [Finite α] [Finite β]
    {r : α → α → Prop} {s : β → β → Prop} {a : α} {b : β} :
    member (approx s b) (approx r a) ↔ ∃ c, r a c ∧ Bisimilar s r b c := by
  constructor
  · intro hmem
    have hne : ∀ n, ∃ c : {c // r a c}, approxAt s b n = approxAt r c.1 n := by
      intro n
      have hmemn := (member_approx_levels.mp hmem) n
      rw [approxAt_succ_coe] at hmemn
      rcases hmemn with ⟨c, hc⟩
      exact ⟨c, hc.symm⟩
    obtain ⟨c, hall⟩ := exists_forever_match
      (fun n (c : {c // r a c}) => approxAt s b n = approxAt r c.1 n)
      (fun n c heq => approxAt_mono_eq heq (Nat.le_succ n)) hne
    exact ⟨c.1, c.2, bisimilar_of_approxAt hall⟩
  · rintro ⟨c, hc, hbis⟩
    have happ : approx s b = approx r c := by
      ext n
      exact approxAt_eq_of_bisimilar hbis n
    rw [happ]
    exact member_approx_of_edge r hc

theorem repoint_bisimilar {H : AccessiblePointedGraph.{0}} (c : H.Node) :
    Bisimilar (H.repoint c).edge H.edge (H.repoint c).point c :=
  bisimilar_generated H.edge c (H.repoint c).point

theorem equiv_repoint_iff {G H : AccessiblePointedGraph.{0}} {c : H.Node} :
    G ≈ H.repoint c ↔ Bisimilar G.edge H.edge G.point c := by
  constructor
  · intro h
    exact h.trans (repoint_bisimilar c)
  · intro h
    exact h.trans (repoint_bisimilar c).symm

/-! ## The finite-stage graph of a stage element -/

/-- The accessible pointed graph of a finite stage, read as a nested finite set.
`Nat.rec` is used so the successor step reduces definitionally. -/
def stageGraph : ∀ n, Stage n → AccessiblePointedGraph.{0} :=
  Nat.rec (motive := fun n => Stage n → AccessiblePointedGraph.{0})
    (fun _ => empty)
    (fun n ih s =>
      sup (fun y : {y : Stage n // y ∈ (s : Set (Stage n))} => ih y.1))

theorem finite_stageGraph : ∀ n (x : Stage n), Finite (stageGraph n x).Node
  | 0, _ => finite_empty_node
  | n + 1, s => by
      classical
      let ι := {y : Stage n // y ∈ (s : Set (Stage n))}
      let g : ι → AccessiblePointedGraph.{0} := fun y => stageGraph n y.1
      have hfold : (stageGraph (n + 1) s).Node = Option (Σ y : ι, (g y).Node) := rfl
      rw [hfold]
      let _ : ∀ y : ι, Finite (g y).Node := fun y => finite_stageGraph n y.1
      infer_instance

instance stageGraph_node_finite (n : ℕ) (x : Stage n) : Finite (stageGraph n x).Node :=
  finite_stageGraph n x

/-- A child of the stage graph is the point of the graph of one member. -/
theorem stageGraph_edge_iff (n : ℕ) (s : Stage (n + 1)) (x : (stageGraph (n + 1) s).Node) :
    (stageGraph (n + 1) s).edge (stageGraph (n + 1) s).point x ↔
      ∃ i : {y : Stage n // y ∈ (s : Set (Stage n))},
        x = some ⟨i, (stageGraph n i.1).point⟩ :=
  supEdge_none_iff

/-- The graph of a member sits inside the graph of the stage, up to bisimilarity. -/
theorem stageGraph_bisimilar_child (n : ℕ) (s : Stage (n + 1))
    (i : {y : Stage n // y ∈ (s : Set (Stage n))}) :
    Bisimilar (stageGraph n i.1).edge (stageGraph (n + 1) s).edge (stageGraph n i.1).point
      (some ⟨i, (stageGraph n i.1).point⟩) :=
  bisimilar_sup (g := fun z : {y : Stage n // y ∈ (s : Set (Stage n))} => stageGraph n z.1)
    i (stageGraph n i.1).point

example : stageGraph 0 PUnit.unit = empty := rfl

example : ∃ x, (stageGraph 1 (⊤ : Stage 1)).edge (stageGraph 1 ⊤).point x :=
  ⟨some ⟨⟨PUnit.unit, mem_top_stage _⟩, (stageGraph 0 PUnit.unit).point⟩,
    (stageGraph_edge_iff 0 (⊤ : Stage 1) _).mpr ⟨⟨PUnit.unit, mem_top_stage _⟩, rfl⟩⟩

theorem stageGraph_approx : ∀ n (x : Stage n),
    approxAt (stageGraph n x).edge (stageGraph n x).point n = x
  | 0, x => by
      cases x
      rfl
  | n + 1, s => by
      apply Compacts.ext
      ext y
      rw [approxAt_succ_coe]
      constructor
      · rintro ⟨c, hc⟩
        obtain ⟨i, hi⟩ := (stageGraph_edge_iff n s c.1).mp c.2
        have happ := approxAt_eq_of_bisimilar (stageGraph_bisimilar_child n s i) n
        rw [stageGraph_approx n i.1] at happ
        have hc' : approxAt (stageGraph (n + 1) s).edge c.1 n = y := hc
        rw [← hc', hi]
        exact happ ▸ i.2
      · intro hy
        let i : {y : Stage n // y ∈ (s : Set (Stage n))} := ⟨y, hy⟩
        refine ⟨⟨some ⟨i, (stageGraph n i.1).point⟩,
          (stageGraph_edge_iff n s _).mpr ⟨i, rfl⟩⟩, ?_⟩
        have happ := approxAt_eq_of_bisimilar (stageGraph_bisimilar_child n s i) n
        rw [stageGraph_approx n i.1] at happ
        change approxAt (stageGraph (n + 1) s).edge (some ⟨i, (stageGraph n i.1).point⟩) n = y
        exact happ.symm

/-- The thread of the finite-stage graph. -/
noncomputable def stagePoint (n : ℕ) (root : Stage n) : N :=
  approx (stageGraph n root).edge (stageGraph n root).point

theorem stagePoint_proj (n : ℕ) (root : Stage n) : proj n (stagePoint n root) = root := by
  simpa [stagePoint, approx, proj] using stageGraph_approx n root

example : proj 1 (stagePoint 1 (⊤ : Stage 1)) = ⊤ := stagePoint_proj 1 ⊤

example : proj 1 (stagePoint 1 (⊤ : Stage 1)) ≠ proj 1 (stagePoint 1 ⊥) := by
  intro h
  have := stagePoint_proj 1 (⊤ : Stage 1)
  have hbot := stagePoint_proj 1 (⊥ : Stage 1)
  exact stage_one_bot_ne_top (hbot.symm.trans (h.symm.trans this))

/-! ## The embedding -/

/-- A hyperset that has a finite presentation. -/
abbrev FinitePresented :=
  {x : HSet.{0} // ∃ G : AccessiblePointedGraph.{0}, HSet.mk G = x ∧ Finite G.Node}

/-- The thread of a chosen finite presentation. -/
noncomputable def finiteEmbed (x : FinitePresented) : N :=
  @approx (Classical.choose x.2).Node (Classical.choose_spec x.2).2
    (Classical.choose x.2).edge (Classical.choose x.2).point

theorem finiteEmbed_mk (G : AccessiblePointedGraph.{0}) [Finite G.Node] :
    finiteEmbed ⟨HSet.mk G, G, rfl, (inferInstance : Finite G.Node)⟩ =
      approx G.edge G.point := by
  classical
  let x : FinitePresented := ⟨HSet.mk G, G, rfl, inferInstance⟩
  have hspec := Classical.choose_spec x.2
  have hequiv : Classical.choose x.2 ≈ G := (HSet.mk_eq_mk_iff).mp hspec.1
  ext k
  simpa [finiteEmbed, approx] using
    @approxAt_eq_of_bisimilar _ _ hspec.2 _ _ _ _ _ hequiv k

theorem finitePresented_mem_iff {G H : AccessiblePointedGraph.{0}}
    [Finite G.Node] [Finite H.Node] :
    HSet.mk G ∈ HSet.mk H ↔
      member (approx G.edge G.point) (approx H.edge H.point) := by
  rw [HSet.mk_mem_mk_iff, member_approx_iff_bisimilar]
  constructor
  · rintro ⟨c, hc, he⟩
    exact ⟨c, hc, equiv_repoint_iff.mp he⟩
  · rintro ⟨c, hc, hb⟩
    exact ⟨c, hc, equiv_repoint_iff.mpr hb⟩

theorem finiteEmbed_mem_iff (x y : FinitePresented) :
    x.1 ∈ y.1 ↔ member (finiteEmbed x) (finiteEmbed y) := by
  classical
  have hG := Classical.choose_spec x.2
  have hH := Classical.choose_spec y.2
  have hxapp : finiteEmbed x =
      @approx _ hG.2 (Classical.choose x.2).edge (Classical.choose x.2).point := rfl
  have hyapp : finiteEmbed y =
      @approx _ hH.2 (Classical.choose y.2).edge (Classical.choose y.2).point := rfl
  have hset : x.1 ∈ y.1 ↔
      HSet.mk (Classical.choose x.2) ∈ HSet.mk (Classical.choose y.2) :=
    ⟨fun h => hH.1.symm ▸ hG.1.symm ▸ h, fun h => hH.1 ▸ hG.1 ▸ h⟩
  have hmem := @finitePresented_mem_iff (Classical.choose x.2) (Classical.choose y.2) hG.2 hH.2
  constructor
  · intro h
    exact hyapp.symm ▸ hxapp.symm ▸ hmem.mp (hset.mp h)
  · intro h
    exact hset.mpr (hmem.mpr (hxapp ▸ hyapp ▸ h))

theorem finiteEmbed_injective : Function.Injective finiteEmbed := by
  intro x y hxy
  classical
  have hG := Classical.choose_spec x.2
  have hH := Classical.choose_spec y.2
  have happ :
      @approx _ hG.2 (Classical.choose x.2).edge (Classical.choose x.2).point =
        @approx _ hH.2 (Classical.choose y.2).edge (Classical.choose y.2).point := by
    simpa [finiteEmbed] using hxy
  have hbis : Bisimilar (Classical.choose x.2).edge (Classical.choose y.2).edge
      (Classical.choose x.2).point (Classical.choose y.2).point :=
    @bisimilar_of_approxAt _ _ hG.2 hH.2 _ _ _ _ fun n => by
      have := congrArg (fun p : N => p.atStage n) happ
      simpa [approx] using this
  apply Subtype.ext
  calc
    x.1 = HSet.mk (Classical.choose x.2) := hG.1.symm
    _ = HSet.mk (Classical.choose y.2) := HSet.sound hbis
    _ = y.1 := hH.1

example : finiteEmbed ⟨HSet.mk empty, empty, rfl, inferInstance⟩ ≠
    finiteEmbed ⟨HSet.mk oneEmpty, oneEmpty, rfl, inferInstance⟩ := by
  intro h
  have hempty := finiteEmbed_mk empty
  have hone := finiteEmbed_mk oneEmpty
  have : approx empty.edge empty.point = approx oneEmpty.edge oneEmpty.point := by
    calc
      approx empty.edge empty.point =
          finiteEmbed ⟨HSet.mk empty, empty, rfl, inferInstance⟩ := hempty.symm
      _ = finiteEmbed ⟨HSet.mk oneEmpty, oneEmpty, rfl, inferInstance⟩ := h
      _ = approx oneEmpty.edge oneEmpty.point := hone
  exact (show approx empty.edge empty.point ≠ approx oneEmpty.edge oneEmpty.point from by
    intro h'
    have := congrArg (proj 1) h'
    exact stage_one_bot_ne_top <|
      approxAt_empty_one.symm.trans (this.trans approxAt_oneEmpty_one)) this

example : member
    (finiteEmbed ⟨HSet.mk empty, empty, rfl, inferInstance⟩)
    (finiteEmbed ⟨HSet.mk oneEmpty, oneEmpty, rfl, inferInstance⟩) := by
  rw [← finiteEmbed_mem_iff]
  rw [HSet.mk_mem_mk_iff]
  refine ⟨some ⟨PUnit.unit, empty.point⟩, SupEdge.point _, ?_⟩
  -- the re-pointed child is the empty graph
  exact (repoint_sup_equiv (g := fun _ : PUnit.{1} => empty.{0}) PUnit.unit).symm

/-- A thread agrees with the iterated bonding maps of any later stage. -/
theorem proj_below (p : N) (n k : ℕ) (hk : k ≤ n) :
    below n (proj n p) k hk = proj k p := by
  induction n generalizing k with
  | zero =>
    obtain rfl : k = 0 := Nat.eq_zero_of_le_zero hk
    simp [below, proj_zero]
  | succ n ih =>
    by_cases hk' : k = n + 1
    · subst hk'
      simp [below]
    · have hk'' : k ≤ n := Nat.le_of_lt_succ (lt_of_le_of_ne hk hk')
      have hbl : below (n + 1) (proj (n + 1) p) k hk =
          below n (bond n (proj (n + 1) p)) k hk'' := by
        simp [below, hk']
      have hcompat : bond n (proj (n + 1) p) = proj n p := by
        simpa [proj] using p.compat n
      rw [hbl, hcompat]
      exact ih k hk''

/-- Every basic stage neighbourhood contains the picture of that stage. -/
theorem finiteEmbed_dense : Dense (Set.range finiteEmbed) := by
  intro p
  rw [mem_closure_iff]
  intro U hU hpU
  obtain ⟨V, hV, hUV⟩ := isOpen_induced_iff.mp hU
  have hpV : toPi p ∈ V := by
    have : p ∈ toPi ⁻¹' V := by simpa [hUV] using hpU
    simpa [toPi] using this
  obtain ⟨I, u, hIu, hsub⟩ := (isOpen_pi_iff.mp hV) (toPi p) hpV
  classical
  let K : ℕ := I.sup id
  let root : Stage K := proj K p
  let x : FinitePresented :=
    ⟨HSet.mk (stageGraph K root), stageGraph K root, rfl, inferInstance⟩
  have hproj : proj K (finiteEmbed x) = root := by
    rw [finiteEmbed_mk (stageGraph K root)]
    simpa [stagePoint] using stagePoint_proj K root
  have hU : finiteEmbed x ∈ U := by
    have hbasic : proj K (finiteEmbed x) = proj K p := by
      simpa [root] using hproj
    have hsubU : {q : N | proj K q = proj K p} ⊆ U := by
      intro q hq
      have hqK : proj K q = proj K p := hq
      have hqpi : toPi q ∈ (I : Set ℕ).pi u := by
        intro i hi
        have hik : i ≤ K := Finset.le_sup (f := id) hi
        have hagree : proj i q = proj i p := by
          rw [← proj_below q K i hik, ← proj_below p K i hik, hqK]
        have hpi : proj i p ∈ u i := by
          simpa [toPi, proj] using (hIu i hi).2
        change proj i q ∈ u i
        rw [hagree]
        exact hpi
      have hqV : toPi q ∈ V := hsub hqpi
      rw [← hUV]
      exact hqV
    exact hsubU hbasic
  exact ⟨finiteEmbed x, hU, x, rfl⟩

end Mettapedia.SetTheory.Hyperuniverse
