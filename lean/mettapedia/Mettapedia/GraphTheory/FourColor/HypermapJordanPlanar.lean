import Mettapedia.GraphTheory.FourColor.HypermapWalkupGenus
import Mettapedia.GraphTheory.FourColor.HypermapJordan

/-!
# A planar hypermap has no Moebius path

This is one half of the combinatorial Jordan curve theorem: vanishing Euler
defect forbids a C-path whose two node links cross.

## The argument

Take a planar map with a Moebius path, on as few darts as possible.  Every
single-dart deletion — `walkupE`, `walkupN` or `walkupF` — is again planar and
smaller, so it has no Moebius path.  The proof consists of showing that, unless
the map is the three-dart genus-one map, *some* deletion carries the Moebius
path along with it, which is absurd.

Write the path as `x, y, z, …`, and `t` for the dart with `node t` the last one.

0. **Every dart lies on the path.**  Deleting a dart off the path with
   `walkupE` changes no link of the path.
1. **`face x = y`.**  Otherwise `x = node y`; delete `x` with `walkupE`, and the
   remaining path starts at `y`, whose new node image is the old `node x`.
2. **`face y = z`.**  Otherwise `y = node z`; delete `y` with `walkupF`, which
   turns the two links `x → y → z` into the single face link `x → z`.
3. **`t = y`.**  Otherwise delete `y` with `walkupE`, which fuses two
   consecutive face links.
4. **`node x = y`.**  Otherwise delete `y` with `walkupN`, whose repaired node
   permutation sends `z` to the last dart, making `z` the new `t`.
5. If the path has only three darts, the map *is* the three darts, all three
   permutations are the 3-cycle, and the genus is one — not planar.
6. Otherwise, with fourth dart `w`, **`z = node w`**: else delete `z` with
   `walkupE`, fusing two face links again.
7. Delete `z` with `walkupF`, fusing `y → z → w` into a face link.  The path
   `x, y, w, …` is still Moebius, with `t = y = node x`.

Each deletion is justified by the genus results of `HypermapWalkupGenus`, and
each link that survives a deletion is checked by the lifting lemmas below: in
`walkupE` every link avoiding the deleted dart survives; in `walkupF` face links
survive unless they point at `node⁻¹` of it; in `walkupN` node links survive
unless they point at `face` of it.
-/

namespace Mettapedia.GraphTheory.FourColor

open Equiv Equiv.Perm
open GoertzelV24PermutationOrbitSurgery GoertzelV24WordReachability
open Mettapedia.GraphTheory.OrbitCountSplitting

namespace Hypermap

/-! ## Lists, and their transport to a punctured carrier -/

section Lists

variable {α β : Type*}

theorem mem2_nil {x y : α} : ¬ Mem2 ([] : List α) x y := fun h => h.ne_nil rfl

theorem mem2_cons_iff {a x y : α} {l : List α} :
    Mem2 (a :: l) x y ↔ (a = x ∧ y ∈ a :: l) ∨ (a ≠ x ∧ Mem2 l x y) := by
  constructor
  · rintro ⟨l₁, l₂, hl, hx, hy⟩
    cases l₁ with
    | nil =>
        simp only [List.nil_append, List.cons.injEq] at hl
        obtain ⟨rfl, rfl⟩ := hl
        exact Or.inl ⟨rfl, hy⟩
    | cons b l₁ =>
        simp only [List.cons_append, List.cons.injEq] at hl
        obtain ⟨rfl, rfl⟩ := hl
        simp only [List.mem_cons, not_or] at hx
        exact Or.inr ⟨fun h => hx.1 h.symm, l₁, l₂, rfl, hx.2, hy⟩
  · rintro (⟨rfl, hy⟩ | ⟨hne, l₁, l₂, rfl, hx, hy⟩)
    · exact ⟨[], l, rfl, by simp, hy⟩
    · refine ⟨a :: l₁, l₂, rfl, ?_, hy⟩
      simp only [List.mem_cons, not_or]
      exact ⟨fun h => hne h.symm, hx⟩

theorem mem2_head {x y : α} {l : List α} (hy : y ∈ x :: l) : Mem2 (x :: l) x y :=
  mem2_cons_iff.2 (Or.inl ⟨rfl, hy⟩)

theorem mem2_map_iff {f : α → β} (hf : Function.Injective f) {l : List α} {x y : α} :
    Mem2 (l.map f) (f x) (f y) ↔ Mem2 l x y := by
  induction l with
  | nil => exact ⟨fun h => absurd h mem2_nil, fun h => absurd h mem2_nil⟩
  | cons a l ih =>
      rw [List.map_cons, mem2_cons_iff, mem2_cons_iff, ih, hf.eq_iff, hf.ne_iff,
        ← List.map_cons, List.mem_map_of_injective hf]

theorem lastOf_map (f : α → β) (a : α) (l : List α) :
    lastOf (f a) (l.map f) = f (lastOf a l) := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih => exact ih b

theorem lastOf_mem_cons (a : α) (l : List α) : lastOf a l ∈ a :: l := by
  induction l generalizing a with
  | nil => exact List.mem_cons_self
  | cons b l ih => exact List.mem_cons_of_mem _ (ih b)

end Lists

section Lift

variable {D : Type*} [Fintype D] [DecidableEq D] {z : D}

/-- A list avoiding `z`, read in the punctured carrier. -/
def liftAvoid : (l : List D) → (∀ w ∈ l, w ≠ z) → List {x : D // x ≠ z}
  | [], _ => []
  | w :: l, h => ⟨w, h w List.mem_cons_self⟩ :: liftAvoid l (fun v hv => h v (List.mem_cons_of_mem w hv))

omit [Fintype D] [DecidableEq D] in
theorem map_val_liftAvoid : ∀ (l : List D) (h : ∀ w ∈ l, w ≠ z),
    (liftAvoid l h).map Subtype.val = l
  | [], _ => rfl
  | w :: l, h => by
      simp only [liftAvoid, List.map_cons, map_val_liftAvoid l]

/-- The relation "C-linked in `K`", read on darts of the unpunctured carrier. -/
def LinkedIn (K : Hypermap {x : D // x ≠ z}) (u v : D) : Prop :=
  ∀ (hu : u ≠ z) (hv : v ≠ z), Clink K ⟨u, hu⟩ ⟨v, hv⟩

/-- **Transport of a Moebius path to a punctured map.**  Everything is checked on
the unpunctured darts: the list, its links, and the two node values. -/
theorem moebiusPath_of_lift {K : Hypermap {x : D // x ≠ z}} {a : D} {l : List D}
    (ha : a ≠ z) (hl : ∀ w ∈ l, w ≠ z) (hnodup : (a :: l).Nodup)
    (hchain : List.IsChain (LinkedIn K) (a :: l))
    {t n : D} (hmem2 : Mem2 l t n)
    (ht : ∀ w : {x : D // x ≠ z}, (w : D) = lastOf a l →
      ((K.node⁻¹ w : {x : D // x ≠ z}) : D) = t)
    (hn : ((K.node ⟨a, ha⟩ : {x : D // x ≠ z}) : D) = n) :
    MoebiusPath K ⟨a, ha⟩ (liftAvoid l hl) := by
  have hmap : (⟨a, ha⟩ :: liftAvoid l hl).map Subtype.val = a :: l := by
    rw [List.map_cons, map_val_liftAvoid]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hmap] at hnodup
    exact hnodup.of_map _
  · rw [← hmap, List.isChain_map] at hchain
    exact hchain.imp fun u v h => h u.2 v.2
  · set T := K.node⁻¹ (lastOf ⟨a, ha⟩ (liftAvoid l hl)) with hT
    have hTval : (T : D) = t := by
      refine ht _ ?_
      have := lastOf_map Subtype.val (⟨a, ha⟩ : {x : D // x ≠ z}) (liftAvoid l hl)
      rw [map_val_liftAvoid] at this
      exact this.symm
    rw [← mem2_map_iff Subtype.val_injective, map_val_liftAvoid, hTval, hn]
    exact hmem2

/-- Lifting a chain whose every link survives the deletion. -/
theorem isChain_linkedIn {H : Hypermap D} {K : Hypermap {x : D // x ≠ z}} {l : List D}
    {P : D → Prop} (hP : ∀ w ∈ l.tail, P w)
    (hlift : ∀ u v : {x : D // x ≠ z}, Clink H u v → P v → Clink K u v)
    (hch : List.IsChain (Clink H) l) : List.IsChain (LinkedIn K) l :=
  hch.imp_of_mem_tail_imp fun _ b _ hb hr hu hv => hlift ⟨_, hu⟩ ⟨b, hv⟩ hr (hP b hb)

end Lift

/-! ## The three punctured maps, read on darts -/

section Values

variable {D : Type*} [Fintype D] [DecidableEq D] (H : Hypermap D) (z : D)

omit [Fintype D] [DecidableEq D] in
theorem inv_apply_eq_of_apply_eq {σ : Perm D} {a b : D} (h : σ a = b) : σ⁻¹ b = a := by
  rw [← h, inv_apply_apply]

theorem walkupE_node_val (u : {x : D // x ≠ z}) :
    (((walkupE H z).node u : {x : D // x ≠ z}) : D) = skipFun H.node z u := rfl

theorem walkupE_nodeInv_val (u : {x : D // x ≠ z}) :
    (((walkupE H z).node⁻¹ u : {x : D // x ≠ z}) : D) = skipFun H.node⁻¹ z u := rfl

theorem walkupE_face_val (u : {x : D // x ≠ z}) :
    (((walkupE H z).face u : {x : D // x ≠ z}) : D) = skipFun H.face z u := rfl

theorem walkupF_node_val (u : {x : D // x ≠ z}) :
    (((walkupF H z).node u : {x : D // x ≠ z}) : D) = skipFun H.node z u := rfl

theorem walkupF_nodeInv_val (u : {x : D // x ≠ z}) :
    (((walkupF H z).node⁻¹ u : {x : D // x ≠ z}) : D) = skipFun H.node⁻¹ z u := rfl

/-- `walkupF` repairs the face permutation. -/
theorem walkupF_face_val (u : {x : D // x ≠ z}) :
    (((walkupF H z).face u : {x : D // x ≠ z}) : D)
      = if H.face z = z then H.face u
        else if H.node (H.face u) = z then H.face z
        else if H.face u = z then H.face (H.edge z)
        else H.face u :=
  walkupE_edge_apply (permF H) z u

theorem walkupN_face_val (u : {x : D // x ≠ z}) :
    (((walkupN H z).face u : {x : D // x ≠ z}) : D) = skipFun H.face z u := rfl

/-- `walkupN` repairs the node permutation. -/
theorem walkupN_node_val (u : {x : D // x ≠ z}) :
    (((walkupN H z).node u : {x : D // x ≠ z}) : D)
      = if H.node z = z then H.node u
        else if H.edge (H.node u) = z then H.node z
        else if H.node u = z then H.node (H.face z)
        else H.node u :=
  walkupE_edge_apply (permN H) z u

end Values

/-! ## Which links survive which deletion -/

section Links

variable {D : Type*} [Fintype D] [DecidableEq D] {H : Hypermap D} {z : D}

/-- In `walkupE` every link between surviving darts survives. -/
theorem clink_walkupE_of_clink {u v : {x : D // x ≠ z}} (h : Clink H u v) :
    Clink (walkupE H z) u v := by
  rcases h with h | h
  · refine Or.inl (Subtype.ext ?_)
    rw [walkupE_node_val, skipFun_of_ne (by rw [← h]; exact u.2), h]
  · refine Or.inr (Subtype.ext ?_)
    rw [walkupE_face_val, skipFun_of_ne (by rw [h]; exact v.2), h]

/-- In `walkupF` a face link survives unless it points at `node⁻¹ z`. -/
theorem clink_walkupF_of_clink {u v : {x : D // x ≠ z}} (h : Clink H u v)
    (hv : (v : D) ≠ H.node⁻¹ z) : Clink (walkupF H z) u v := by
  rcases h with h | h
  · refine Or.inl (Subtype.ext ?_)
    rw [walkupF_node_val, skipFun_of_ne (by rw [← h]; exact u.2), h]
  · refine Or.inr (Subtype.ext ?_)
    rw [walkupF_face_val]
    by_cases h1 : H.face z = z
    · rw [if_pos h1, h]
    · rw [if_neg h1, if_neg, if_neg]
      · exact h
      · rw [h]; exact v.2
      · intro hc
        rw [h] at hc
        exact hv (inv_apply_eq_of_apply_eq hc).symm

/-- In `walkupN` a node link survives unless it points at `face z`. -/
theorem clink_walkupN_of_clink {u v : {x : D // x ≠ z}} (h : Clink H u v)
    (hv : (v : D) ≠ H.face z) : Clink (walkupN H z) u v := by
  rcases h with h | h
  · refine Or.inl (Subtype.ext ?_)
    rw [walkupN_node_val]
    by_cases h1 : H.node z = z
    · rw [if_pos h1, h]
    · rw [if_neg h1, if_neg, if_neg]
      · exact h
      · rw [← h]; exact u.2
      · intro hc
        exact hv (H.node.injective ((edge_eq_iff H z _).1 hc))
  · refine Or.inr (Subtype.ext ?_)
    rw [walkupN_face_val, skipFun_of_ne (by rw [h]; exact v.2), h]

/-- Two face links through `z` fuse into one in `walkupE`. -/
theorem clink_walkupE_face_face {a b : D} (ha : a ≠ z) (hb : b ≠ z)
    (h1 : H.face a = z) (h2 : H.face z = b) : Clink (walkupE H z) ⟨a, ha⟩ ⟨b, hb⟩ := by
  refine Or.inr (Subtype.ext ?_)
  rw [walkupE_face_val, skipFun_of_eq h1, h2]

/-- Two face links through `z` fuse into one in `walkupN`. -/
theorem clink_walkupN_face_face {a b : D} (ha : a ≠ z) (hb : b ≠ z)
    (h1 : H.face a = z) (h2 : H.face z = b) : Clink (walkupN H z) ⟨a, ha⟩ ⟨b, hb⟩ := by
  refine Or.inr (Subtype.ext ?_)
  rw [walkupN_face_val, skipFun_of_eq h1, h2]

/-- A face link into `z` followed by a node link out of it fuse into one face
link in `walkupF`. -/
theorem clink_walkupF_face_node {a b : D} (ha : a ≠ z) (hb : b ≠ z)
    (h1 : H.face a = z) (h2 : z = H.node b) : Clink (walkupF H z) ⟨a, ha⟩ ⟨b, hb⟩ := by
  refine Or.inr (Subtype.ext ?_)
  rw [walkupF_face_val]
  have hfz : H.face z ≠ z := fun hc => ha (H.face.injective (h1.trans hc.symm))
  have hnz : H.node (H.face a) ≠ z := by
    rw [h1]
    intro hc
    exact hb (H.node.injective (by rw [← h2, hc]))
  rw [if_neg hfz, if_neg hnz, if_pos h1]
  exact H.node.injective ((H.cancel3 z).trans h2)

end Links

/-! ## The minimal counterexample, step by step

Throughout, `hJ` is the inductive hypothesis at every single-dart deletion, and
the Moebius path is written out as `x :: y :: z :: q`, with `lastOf z q` its last
dart and `H.node⁻¹ (lastOf z q)` the dart `t` of the module docstring. -/

universe u

section Steps

variable {D : Type u} [Fintype D] [DecidableEq D] {H : Hypermap D}

/-- The inductive hypothesis, at every single-dart deletion. -/
def JordanBelow (_H : Hypermap D) : Prop :=
  ∀ z : D, ∀ K : Hypermap {x : D // x ≠ z}, Planar K → Jordan K

/-- A Moebius path has at least three darts. -/
theorem MoebiusPath.exists_cons_cons {x : D} {p : List D} (hM : MoebiusPath H x p) :
    ∃ y z q, p = y :: z :: q := by
  obtain ⟨hnd, -, hm⟩ := hM
  match p, hnd, hm with
  | [], _, hm => exact absurd hm mem2_nil
  | [y], hnd, hm =>
      exfalso
      rcases mem2_cons_iff.1 hm with ⟨h, hn⟩ | ⟨_, h⟩
      · have hinv : H.node⁻¹ y = y := h.symm
        have hny : H.node y = y := by
          have := apply_inv_apply H.node y
          rwa [hinv] at this
        have hnx : H.node x = y := List.mem_singleton.1 hn
        have hxy : x = y := H.node.injective (hnx.trans hny.symm)
        exact (List.nodup_cons.1 hnd).1 (by rw [hxy]; exact List.mem_singleton_self y)
      · exact mem2_nil h
  | y :: z :: q, _, _ => exact ⟨y, z, q, rfl⟩

section PathFacts

variable {x y z : D} {q : List D}

/-- **Step 0.**  Every dart lies on the path. -/
theorem jb_all_on_path (hJ : JordanBelow H) (hP : Planar H)
    (hnd : (x :: y :: z :: q).Nodup) (hch : List.IsChain (Clink H) (x :: y :: z :: q))
    (hm : Mem2 (y :: z :: q) (H.node⁻¹ (lastOf z q)) (H.node x)) :
    ∀ d : D, d ∈ x :: y :: z :: q := by
  intro d
  by_contra hd
  have hne : ∀ w ∈ x :: y :: z :: q, w ≠ d := fun w hw h => hd (by rw [← h]; exact hw)
  have hxd : x ≠ d := hne x List.mem_cons_self
  have htail : ∀ w ∈ y :: z :: q, w ≠ d := fun w hw => hne w (List.mem_cons_of_mem _ hw)
  refine hJ d (walkupE H d) (planar_walkupE H d hP) ⟨x, hxd⟩ (liftAvoid (y :: z :: q) htail)
    (moebiusPath_of_lift hxd htail hnd ?_ hm ?_ ?_)
  · exact isChain_linkedIn (P := fun _ => True) (fun _ _ => trivial)
      (fun _ _ h _ => clink_walkupE_of_clink h) hch
  · intro w hw
    rw [walkupE_nodeInv_val, hw]
    exact skipFun_of_ne (htail _ hm.left_mem)
  · rw [walkupE_node_val]
    exact skipFun_of_ne (htail _ hm.right_mem)

/-- **Step 1.**  The path leaves `x` by a face link. -/
theorem jb_face_x (hJ : JordanBelow H) (hP : Planar H)
    (hnd : (x :: y :: z :: q).Nodup) (hch : List.IsChain (Clink H) (x :: y :: z :: q))
    (hm : Mem2 (y :: z :: q) (H.node⁻¹ (lastOf z q)) (H.node x)) :
    H.face x = y := by
  have hx : x ∉ y :: z :: q := (List.nodup_cons.1 hnd).1
  have hnd1 : (y :: z :: q).Nodup := (List.nodup_cons.1 hnd).2
  have hL : lastOf z q ∈ z :: q := lastOf_mem_cons z q
  have htmem : H.node⁻¹ (lastOf z q) ∈ y :: z :: q := hm.left_mem
  by_contra hfx
  have hxy : x = H.node y := by
    rcases (List.isChain_cons_cons.1 hch).1 with h | h
    · exact h
    · exact absurd h hfx
  have hyx : y ≠ x := fun h => hx (by rw [← h]; exact List.mem_cons_self)
  have htail : ∀ w ∈ z :: q, w ≠ x := fun w hw =>
    ne_of_mem_of_not_mem hw (fun h => hx (List.mem_cons_of_mem _ h))
  have hty : H.node⁻¹ (lastOf z q) ≠ y := by
    intro h
    have hLx : lastOf z q = x := by
      calc lastOf z q = H.node (H.node⁻¹ (lastOf z q)) := (apply_inv_apply _ _).symm
        _ = H.node y := by rw [h]
        _ = x := hxy.symm
    exact hx (List.mem_cons_of_mem _ (by rw [← hLx]; exact hL))
  have hm' : Mem2 (z :: q) (H.node⁻¹ (lastOf z q)) (H.node x) := by
    rcases mem2_cons_iff.1 hm with ⟨h, _⟩ | ⟨_, h⟩
    · exact absurd h.symm hty
    · exact h
  refine hJ x (walkupE H x) (planar_walkupE H x hP) ⟨y, hyx⟩ (liftAvoid (z :: q) htail)
    (moebiusPath_of_lift hyx htail hnd1 ?_ hm' ?_ ?_)
  · exact isChain_linkedIn (P := fun _ => True) (fun _ _ => trivial)
      (fun _ _ h _ => clink_walkupE_of_clink h) (List.isChain_cons_cons.1 hch).2
  · intro w hw
    rw [walkupE_nodeInv_val, hw]
    exact skipFun_of_ne (fun h => hx (by rw [← h]; exact htmem))
  · rw [walkupE_node_val]
    exact skipFun_of_eq hxy.symm

/-- **Step 2.**  The path leaves `y` by a face link. -/
theorem jb_face_y (hJ : JordanBelow H) (hP : Planar H)
    (hnd : (x :: y :: z :: q).Nodup) (hch : List.IsChain (Clink H) (x :: y :: z :: q))
    (hm : Mem2 (y :: z :: q) (H.node⁻¹ (lastOf z q)) (H.node x))
    (h1 : H.face x = y) : H.face y = z := by
  have hx : x ∉ y :: z :: q := (List.nodup_cons.1 hnd).1
  have hnd1 : (y :: z :: q).Nodup := (List.nodup_cons.1 hnd).2
  have hy : y ∉ z :: q := (List.nodup_cons.1 hnd1).1
  have hz : z ∉ q := (List.nodup_cons.1 (List.nodup_cons.1 hnd1).2).1
  have hnmem : H.node x ∈ y :: z :: q := hm.right_mem
  have hch1 := List.isChain_cons_cons.1 hch
  have hch2 := List.isChain_cons_cons.1 hch1.2
  by_contra hfy
  have hyz : y = H.node z := by
    rcases hch2.1 with h | h
    · exact h
    · exact absurd h hfy
  have hxy : x ≠ y := fun h => hx (by rw [h]; exact List.mem_cons_self)
  have hxz : x ≠ z := fun h => hx (by rw [h]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  have hxq : ∀ w ∈ z :: q, w ≠ y := fun w hw => ne_of_mem_of_not_mem hw hy
  have hninv : H.node⁻¹ y = z := inv_apply_eq_of_apply_eq hyz.symm
  have hnxy : H.node x ≠ y := fun h => hxz (H.node.injective (h.trans hyz))
  have hndxz : (x :: z :: q).Nodup :=
    List.Nodup.sublist (List.Sublist.cons_cons x (List.sublist_cons_self y (z :: q))) hnd
  have hchain : List.IsChain (LinkedIn (walkupF H y)) (x :: z :: q) := by
    refine List.isChain_cons_cons.2 ⟨fun hu hv => clink_walkupF_face_node hu hv h1 hyz, ?_⟩
    refine isChain_linkedIn (P := fun v => v ≠ H.node⁻¹ y) ?_
      (fun _ _ h hv => clink_walkupF_of_clink h hv) hch2.2
    intro w hw
    rw [hninv]
    exact ne_of_mem_of_not_mem hw hz
  have hn : (((walkupF H y).node ⟨x, hxy⟩ : {w : D // w ≠ y}) : D) = H.node x := by
    rw [walkupF_node_val]
    exact skipFun_of_ne hnxy
  by_cases ht : H.node⁻¹ (lastOf z q) = y
  · refine hJ y (walkupF H y) (planar_walkupF H y hP) ⟨x, hxy⟩ (liftAvoid (z :: q) hxq)
      (moebiusPath_of_lift (t := z) hxy hxq hndxz hchain ?_ ?_ hn)
    · refine mem2_head ?_
      rcases List.mem_cons.1 hnmem with h | h
      · exact absurd h hnxy
      · exact h
    · intro w hw
      rw [walkupF_nodeInv_val, hw]
      show skipFun H.node⁻¹ y (lastOf z q) = z
      exact (skipFun_of_eq ht).trans hninv
  · refine hJ y (walkupF H y) (planar_walkupF H y hP) ⟨x, hxy⟩ (liftAvoid (z :: q) hxq)
      (moebiusPath_of_lift (t := H.node⁻¹ (lastOf z q)) hxy hxq hndxz hchain ?_ ?_ hn)
    · rcases mem2_cons_iff.1 hm with ⟨h, _⟩ | ⟨_, h⟩
      · exact absurd h.symm ht
      · exact h
    · intro w hw
      rw [walkupF_nodeInv_val, hw]
      show skipFun H.node⁻¹ y (lastOf z q) = H.node⁻¹ (lastOf z q)
      exact skipFun_of_ne ht

/-- **Step 3.**  The dart `t` is `y`: the last dart is `node y`. -/
theorem jb_t_eq_y (hJ : JordanBelow H) (hP : Planar H)
    (hnd : (x :: y :: z :: q).Nodup) (hch : List.IsChain (Clink H) (x :: y :: z :: q))
    (hm : Mem2 (y :: z :: q) (H.node⁻¹ (lastOf z q)) (H.node x))
    (h1 : H.face x = y) (h2 : H.face y = z) : H.node⁻¹ (lastOf z q) = y := by
  have hx : x ∉ y :: z :: q := (List.nodup_cons.1 hnd).1
  have hnd1 : (y :: z :: q).Nodup := (List.nodup_cons.1 hnd).2
  have hy : y ∉ z :: q := (List.nodup_cons.1 hnd1).1
  have hch2 := (List.isChain_cons_cons.1 (List.isChain_cons_cons.1 hch).2).2
  by_contra ht
  have hxy : x ≠ y := fun h => hx (by rw [h]; exact List.mem_cons_self)
  have hxq : ∀ w ∈ z :: q, w ≠ y := fun w hw => ne_of_mem_of_not_mem hw hy
  have hm' : Mem2 (z :: q) (H.node⁻¹ (lastOf z q)) (H.node x) := by
    rcases mem2_cons_iff.1 hm with ⟨h, _⟩ | ⟨_, h⟩
    · exact absurd h.symm ht
    · exact h
  have hnxy : H.node x ≠ y := by
    intro hn
    rw [hn] at hm'
    exact hy hm'.right_mem
  have hndxz : (x :: z :: q).Nodup :=
    List.Nodup.sublist (List.Sublist.cons_cons x (List.sublist_cons_self y (z :: q))) hnd
  refine hJ y (walkupE H y) (planar_walkupE H y hP) ⟨x, hxy⟩ (liftAvoid (z :: q) hxq)
    (moebiusPath_of_lift hxy hxq hndxz ?_ hm' ?_ ?_)
  · refine List.isChain_cons_cons.2 ⟨fun hu hv => clink_walkupE_face_face hu hv h1 h2, ?_⟩
    exact isChain_linkedIn (P := fun _ => True) (fun _ _ => trivial)
      (fun _ _ h _ => clink_walkupE_of_clink h) hch2
  · intro w hw
    rw [walkupE_nodeInv_val, hw]
    show skipFun H.node⁻¹ y (lastOf z q) = H.node⁻¹ (lastOf z q)
    exact skipFun_of_ne ht
  · rw [walkupE_node_val]
    exact skipFun_of_ne hnxy

/-- **Step 4.**  The path's first node link is `x ↦ y`. -/
theorem jb_node_x (hJ : JordanBelow H) (hP : Planar H)
    (hnd : (x :: y :: z :: q).Nodup) (hch : List.IsChain (Clink H) (x :: y :: z :: q))
    (hm : Mem2 (y :: z :: q) (H.node⁻¹ (lastOf z q)) (H.node x))
    (h1 : H.face x = y) (h2 : H.face y = z) (h3 : H.node⁻¹ (lastOf z q) = y) :
    H.node x = y := by
  have hx : x ∉ y :: z :: q := (List.nodup_cons.1 hnd).1
  have hnd1 : (y :: z :: q).Nodup := (List.nodup_cons.1 hnd).2
  have hy : y ∉ z :: q := (List.nodup_cons.1 hnd1).1
  have hz : z ∉ q := (List.nodup_cons.1 (List.nodup_cons.1 hnd1).2).1
  have hL : lastOf z q ∈ z :: q := lastOf_mem_cons z q
  have hnmem : H.node x ∈ y :: z :: q := hm.right_mem
  have hch2 := (List.isChain_cons_cons.1 (List.isChain_cons_cons.1 hch).2).2
  by_contra hnxy
  have hxy : x ≠ y := fun h => hx (by rw [h]; exact List.mem_cons_self)
  have hzy : z ≠ y := fun h => hy (by rw [h]; exact List.mem_cons_self)
  have hxq : ∀ w ∈ z :: q, w ≠ y := fun w hw => ne_of_mem_of_not_mem hw hy
  have hLy : H.node y = lastOf z q := by
    rw [← h3]
    exact apply_inv_apply _ _
  have hny : H.node y ≠ y := by
    intro h
    rw [← hLy, h] at hL
    exact hy hL
  have hex : H.edge (H.node x) ≠ y := by
    intro h
    have hxz := (edge_eq_iff H y (H.node x)).1 h
    rw [h2] at hxz
    exact hx (List.mem_cons_of_mem _
      (by rw [H.node.injective hxz]; exact List.mem_cons_self))
  have hndxz : (x :: z :: q).Nodup :=
    List.Nodup.sublist (List.Sublist.cons_cons x (List.sublist_cons_self y (z :: q))) hnd
  refine hJ y (walkupN H y) (planar_walkupN H y hP) ⟨x, hxy⟩ (liftAvoid (z :: q) hxq)
    (moebiusPath_of_lift (t := z) (n := H.node x) hxy hxq hndxz ?_ ?_ ?_ ?_)
  · refine List.isChain_cons_cons.2 ⟨fun hu hv => clink_walkupN_face_face hu hv h1 h2, ?_⟩
    refine isChain_linkedIn (P := fun v => v ≠ H.face y) ?_
      (fun _ _ h hv => clink_walkupN_of_clink h hv) hch2
    intro w hw
    rw [h2]
    exact ne_of_mem_of_not_mem hw hz
  · refine mem2_head ?_
    rcases List.mem_cons.1 hnmem with h | h
    · exact absurd h hnxy
    · exact h
  · intro w hw
    have hnode : (walkupN H y).node ⟨z, hzy⟩ = w := by
      apply Subtype.ext
      rw [walkupN_node_val, hw]
      show (if H.node y = y then H.node z
        else if H.edge (H.node z) = y then H.node y
        else if H.node z = y then H.node (H.face y) else H.node z) = lastOf z q
      rw [if_neg hny, if_pos (by rw [← h2]; exact edge_node_face H y), hLy]
    rw [inv_apply_eq_of_apply_eq hnode]
  · rw [walkupN_node_val]
    show (if H.node y = y then H.node x
      else if H.edge (H.node x) = y then H.node y
      else if H.node x = y then H.node (H.face y) else H.node x) = H.node x
    rw [if_neg hny, if_neg hex, if_neg hnxy]

omit [DecidableEq D] in
/-- A permutation that moves `a ↦ b ↦ c` on a three-dart carrier has one orbit. -/
theorem orbitCount_eq_one_of_three {σ : Perm D} {a b c : D} (hab : σ a = b) (hbc : σ b = c)
    (hall : ∀ d : D, d ∈ [a, b, c]) : orbitCount σ = 1 := by
  have hto : ∀ d : D, σ.SameCycle a d := by
    intro d
    rcases List.mem_cons.1 (hall d) with h | h
    · rw [h]
    · rcases List.mem_cons.1 h with h | h
      · rw [h, ← hab]; exact sameCycle_step σ a
      · rw [List.mem_singleton.1 h, ← hbc, ← hab]
        exact (sameCycle_step σ a).trans (sameCycle_step σ (σ a))
  have h := orbitCount_eq_card_of_completeInvariant (σ := σ) (fun _ : D => ())
    (fun u v => ⟨fun _ => rfl, fun _ => (hto u).symm.trans (hto v)⟩) (fun _ => ⟨a, rfl⟩)
  rw [h]
  simp

/-- **Step 5.**  A three-dart Moebius path forces genus one. -/
theorem jb_base (hP : Planar H) (hnd : [x, y, z].Nodup) (hall : ∀ d : D, d ∈ [x, y, z])
    (h1 : H.face x = y) (h2 : H.face y = z) (h3 : H.node⁻¹ z = y) (h4 : H.node x = y) :
    False := by
  have hxy : x ≠ y := fun h => (List.nodup_cons.1 hnd).1 (by rw [h]; exact List.mem_cons_self)
  have hxz : x ≠ z := fun h => (List.nodup_cons.1 hnd).1
    (by rw [h]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  have hyz : y ≠ z := fun h => (List.nodup_cons.1 (List.nodup_cons.1 hnd).2).1
    (by rw [h]; exact List.mem_cons_self)
  -- a bijection moving `a ↦ b ↦ c` on the three darts must close the cycle
  have third : ∀ σ : Perm D, σ x = y → σ y = z → σ z = x := by
    intro σ hσx hσy
    rcases List.mem_cons.1 (hall (σ z)) with h | h
    · exact h
    · rcases List.mem_cons.1 h with h | h
      · exact absurd (σ.injective (h.trans hσx.symm)) hxz.symm
      · exact absurd (σ.injective ((List.mem_singleton.1 h).trans hσy.symm)) hyz.symm
  have hny : H.node y = z := by
    have := apply_inv_apply H.node z
    rwa [h3] at this
  have hnz : H.node z = x := third H.node h4 hny
  have hfz : H.face z = x := third H.face h1 h2
  have hex : H.edge x = y := by
    have hfe : H.face (H.edge x) = z := H.node.injective ((H.cancel3 x).trans hnz.symm)
    exact H.face.injective (hfe.trans h2.symm)
  have hey : H.edge y = z := by
    have hfe : H.face (H.edge y) = x := H.node.injective ((H.cancel3 y).trans h4.symm)
    exact H.face.injective (hfe.trans hfz.symm)
  have hE := orbitCount_eq_one_of_three hex hey hall
  have hN := orbitCount_eq_one_of_three h4 hny hall
  have hF := orbitCount_eq_one_of_three h1 h2 hall
  have hcard : 3 ≤ Fintype.card D := by
    have h := List.toFinset_card_of_nodup hnd
    have hle := Finset.card_le_univ [x, y, z].toFinset
    simp only [List.length_cons, List.length_nil] at h
    omega
  have hcomp : 1 ≤ compCount H := by
    show 1 ≤ Fintype.card (Quotient (wordSetoid [H.edge, H.node, H.face]))
    exact Fintype.card_pos_iff.2 ⟨Quotient.mk _ x⟩
  rw [planar_iff_eulerRhs_eq, eulerRhs_eq_card_add_two_mul_compCount, eulerLhs_eq_orbit_sum,
    hE, hN, hF] at hP
  omega

end PathFacts

section LongPath

variable {x y z w : D} {r : List D}

/-- **Step 6.**  On a path of four or more darts, `z` is followed by a node link. -/
theorem jb_node_w (hJ : JordanBelow H) (hP : Planar H)
    (hnd : (x :: y :: z :: w :: r).Nodup) (hch : List.IsChain (Clink H) (x :: y :: z :: w :: r))
    (h2 : H.face y = z) (h3 : H.node⁻¹ (lastOf w r) = y)
    (h4 : H.node x = y) : z = H.node w := by
  have hx : x ∉ y :: z :: w :: r := (List.nodup_cons.1 hnd).1
  have hnd1 : (y :: z :: w :: r).Nodup := (List.nodup_cons.1 hnd).2
  have hy : y ∉ z :: w :: r := (List.nodup_cons.1 hnd1).1
  have hnd2 : (z :: w :: r).Nodup := (List.nodup_cons.1 hnd1).2
  have hz : z ∉ w :: r := (List.nodup_cons.1 hnd2).1
  have hch1 := List.isChain_cons_cons.1 hch
  have hch2 := List.isChain_cons_cons.1 hch1.2
  have hch3 := List.isChain_cons_cons.1 hch2.2
  by_contra hzw
  have hfz : H.face z = w := by
    rcases hch3.1 with h | h
    · exact absurd h hzw
    · exact h
  have hxz : x ≠ z := fun h => hx (by rw [h]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  have hyz : y ≠ z := fun h => hy (by rw [h]; exact List.mem_cons_self)
  have htail : ∀ v ∈ y :: w :: r, v ≠ z := by
    intro v hv
    rcases List.mem_cons.1 hv with h | h
    · rw [h]; exact hyz
    · exact ne_of_mem_of_not_mem h hz
  have hndxz : (x :: y :: w :: r).Nodup :=
    List.Nodup.sublist (List.Sublist.cons_cons x (List.Sublist.cons_cons y
      (List.sublist_cons_self z (w :: r)))) hnd
  refine hJ z (walkupE H z) (planar_walkupE H z hP) ⟨x, hxz⟩ (liftAvoid (y :: w :: r) htail)
    (moebiusPath_of_lift (t := y) (n := y) hxz htail hndxz ?_
      (mem2_head List.mem_cons_self) ?_ ?_)
  · refine List.isChain_cons_cons.2 ⟨fun hu hv => clink_walkupE_of_clink hch1.1, ?_⟩
    refine List.isChain_cons_cons.2 ⟨fun hu hv => clink_walkupE_face_face hu hv h2 hfz, ?_⟩
    exact isChain_linkedIn (P := fun _ => True) (fun _ _ => trivial)
      (fun _ _ h _ => clink_walkupE_of_clink h) hch3.2
  · intro v hv
    rw [walkupE_nodeInv_val, hv]
    show skipFun H.node⁻¹ z (lastOf w r) = y
    exact (skipFun_of_ne (by rw [h3]; exact hyz)).trans h3
  · rw [walkupE_node_val]
    exact (skipFun_of_ne (by rw [h4]; exact hyz)).trans h4

/-- **Step 7.**  Fusing `y → z → w` in `walkupF` keeps the path Moebius. -/
theorem jb_final (hJ : JordanBelow H) (hP : Planar H)
    (hnd : (x :: y :: z :: w :: r).Nodup) (hch : List.IsChain (Clink H) (x :: y :: z :: w :: r))
    (h2 : H.face y = z) (h3 : H.node⁻¹ (lastOf w r) = y)
    (h4 : H.node x = y) (hzw : z = H.node w) : False := by
  have hx : x ∉ y :: z :: w :: r := (List.nodup_cons.1 hnd).1
  have hnd1 : (y :: z :: w :: r).Nodup := (List.nodup_cons.1 hnd).2
  have hy : y ∉ z :: w :: r := (List.nodup_cons.1 hnd1).1
  have hnd2 : (z :: w :: r).Nodup := (List.nodup_cons.1 hnd1).2
  have hz : z ∉ w :: r := (List.nodup_cons.1 hnd2).1
  have hw : w ∉ r := (List.nodup_cons.1 (List.nodup_cons.1 hnd2).2).1
  have hch1 := List.isChain_cons_cons.1 hch
  have hch3 := List.isChain_cons_cons.1 (List.isChain_cons_cons.1 hch1.2).2
  have hxz : x ≠ z := fun h => hx (by rw [h]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  have hyz : y ≠ z := fun h => hy (by rw [h]; exact List.mem_cons_self)
  have hyw : y ≠ w := fun h => hy (by rw [h]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  have hninv : H.node⁻¹ z = w := inv_apply_eq_of_apply_eq hzw.symm
  have htail : ∀ v ∈ y :: w :: r, v ≠ z := by
    intro v hv
    rcases List.mem_cons.1 hv with h | h
    · rw [h]; exact hyz
    · exact ne_of_mem_of_not_mem h hz
  have hndxz : (x :: y :: w :: r).Nodup :=
    List.Nodup.sublist (List.Sublist.cons_cons x (List.Sublist.cons_cons y
      (List.sublist_cons_self z (w :: r)))) hnd
  refine hJ z (walkupF H z) (planar_walkupF H z hP) ⟨x, hxz⟩ (liftAvoid (y :: w :: r) htail)
    (moebiusPath_of_lift (t := y) (n := y) hxz htail hndxz ?_
      (mem2_head List.mem_cons_self) ?_ ?_)
  · refine List.isChain_cons_cons.2
      ⟨fun hu hv => clink_walkupF_of_clink hch1.1 (by rw [hninv]; exact hyw), ?_⟩
    refine List.isChain_cons_cons.2 ⟨fun hu hv => clink_walkupF_face_node hu hv h2 hzw, ?_⟩
    refine isChain_linkedIn (P := fun v => v ≠ H.node⁻¹ z) ?_
      (fun _ _ h hv => clink_walkupF_of_clink h hv) hch3.2
    intro v hv
    rw [hninv]
    exact ne_of_mem_of_not_mem hv hw
  · intro v hv
    rw [walkupF_nodeInv_val, hv]
    show skipFun H.node⁻¹ z (lastOf w r) = y
    exact (skipFun_of_ne (by rw [h3]; exact hyz)).trans h3
  · rw [walkupF_node_val]
    exact (skipFun_of_ne (by rw [h4]; exact hyz)).trans h4

end LongPath

/-- **No minimal counterexample.**  A planar map all of whose single-dart
deletions satisfy the Jordan property satisfies it too. -/
theorem jordan_of_jordanBelow (hJ : JordanBelow H) (hP : Planar H) : Jordan H := by
  intro x p hM
  obtain ⟨y, z, q, rfl⟩ := hM.exists_cons_cons
  obtain ⟨hnd, hch, hm⟩ := hM
  have hm' : Mem2 (y :: z :: q) (H.node⁻¹ (lastOf z q)) (H.node x) := hm
  have hall := jb_all_on_path hJ hP hnd hch hm'
  have h1 := jb_face_x hJ hP hnd hch hm'
  have h2 := jb_face_y hJ hP hnd hch hm' h1
  have h3 := jb_t_eq_y hJ hP hnd hch hm' h1 h2
  have h4 := jb_node_x hJ hP hnd hch hm' h1 h2 h3
  cases q with
  | nil => exact jb_base hP hnd hall h1 h2 h3 h4
  | cons w r => exact jb_final hJ hP hnd hch h2 h3 h4 (jb_node_w hJ hP hnd hch h2 h3 h4)

end Steps

/-! ## The theorem -/

theorem jordan_of_planar_of_card_le :
    ∀ (n : ℕ) (D : Type u) [Fintype D] [DecidableEq D] (H : Hypermap D),
      Fintype.card D ≤ n → Planar H → Jordan H := by
  intro n
  induction n with
  | zero =>
      intro D _ _ H hcard _ x _ _
      have hempty : IsEmpty D := Fintype.card_eq_zero_iff.mp (Nat.le_zero.mp hcard)
      exact hempty.elim x
  | succ n ih =>
      intro D _ _ H hcard hP
      refine jordan_of_jordanBelow (fun z K hK => ih {x : D // x ≠ z} K ?_ hK) hP
      have hc := card_subtype_ne_succ z
      omega

/-- **A planar hypermap satisfies the Jordan property.**  This is the source's
`planar_Jordan`: vanishing Euler defect forbids every Moebius path. -/
theorem jordan_of_planar {D : Type u} [Fintype D] [DecidableEq D] (H : Hypermap D)
    (hP : Planar H) : Jordan H :=
  jordan_of_planar_of_card_le _ D H le_rfl hP

/-- The half of the equivalence recorded in `HypermapJordan`, discharged on every
carrier. -/
theorem planarImpliesJordanOn (D : Type u) [Fintype D] [DecidableEq D] :
    PlanarImpliesJordanOn D :=
  fun H hP => jordan_of_planar H hP

/-- **Cross-check.**  The explicit Moebius path on the genus-one map, fed through
`jordan_of_planar`, re-derives that the map is not planar — agreeing with the
direct Euler count `not_planar_torusTriple`, which was obtained independently. -/
theorem not_planar_torusTriple_of_moebius : ¬ Planar torusTriple :=
  fun hP => not_jordan_torusTriple (jordan_of_planar torusTriple hP)

end Hypermap

end Mettapedia.GraphTheory.FourColor
