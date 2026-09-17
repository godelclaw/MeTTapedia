import Mettapedia.GraphTheory.FourColor.HypermapJordanPlanar

/-!
# The Jordan property survives deleting a dart

If `H` has no Moebius path then neither does `walkupE H z`.  Equivalently, a
Moebius path of the punctured map lifts to one of `H`.  This is the source's
`Jordan_WalkupE`, and it is what lets the converse `Jordan → Planar` run by
Walkup induction.

## Why lifting is not immediate

A C-link of the punctured map either is a C-link of `H`, or it *skips* `z`:
a node link `node z ⟶ node⁻¹ z` that jumped over `z` on its node cycle, or a face
link `face⁻¹ z ⟶ face z` that jumped over it on its face cycle.  Re-inserting `z`
repairs the path.  But `z` may need to be inserted twice, which breaks
duplicate-freeness, and the two crossing node links of the Moebius condition may
themselves skip `z`.  So the lift has to *choose* a Moebius path of `H` among
several candidates, and which one works depends on where the skips fall relative
to the crossing links.

## The argument

Everything is read on the darts of `H`: a punctured Moebius path becomes a list
`x :: p` avoiding `z`, linked by `Clink2` (either kind of link may skip), whose
crossing darts are `y` (with `skipFun node z y` the last dart) and
`skipFun node z x`.  Suppose `H` has no Moebius path.

1. The path skips somewhere: otherwise it, or it with `z` prepended or appended,
   is already Moebius in `H`.
2. It skips on its node cycle: otherwise `z` is inserted once, at the face skip,
   and one of three candidate paths is Moebius in `H`.
3. So `t₀ = node⁻¹ z` lies on the path, reached by the node skip from `node z`.
   Splitting there, `y ≠ t₀`, the part before `t₀` has no face skip, and the part
   after it has exactly one; the remaining configuration is contradictory, by
   four more candidate paths.

Each candidate is certified by the same three checks — duplicate-freeness (by
counting occurrences against the original list), the chain of C-links (by
splicing chains at shared endpoints), and the occurrence order of the crossing
darts (by the `Mem2` splicing lemmas below).
-/

namespace Mettapedia.GraphTheory.FourColor

open Equiv Equiv.Perm
open GoertzelV24PermutationOrbitSurgery GoertzelV24WordReachability

namespace Hypermap

/-! ## More list surgery -/

section Lists

variable {α : Type*}

theorem mem2_append_right {l r : List α} {a b : α} (h : Mem2 l a b) : Mem2 (l ++ r) a b := by
  induction l with
  | nil => exact absurd h mem2_nil
  | cons d l ih =>
      rcases mem2_cons_iff.1 h with ⟨hd, hb⟩ | ⟨hd, h'⟩
      · refine mem2_cons_iff.2 (Or.inl ⟨hd, ?_⟩)
        rcases List.mem_cons.1 hb with hb | hb
        · rw [hb]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_append_left _ hb)
      · exact mem2_cons_iff.2 (Or.inr ⟨hd, ih h'⟩)

/-- Inserting a dart other than the first crossing dart preserves the order. -/
theorem mem2_splice {l₁ l₂ : List α} {a b c : α} (hac : a ≠ c)
    (h : Mem2 (l₁ ++ l₂) a b) : Mem2 (l₁ ++ c :: l₂) a b := by
  induction l₁ with
  | nil => exact mem2_cons_iff.2 (Or.inr ⟨fun h' => hac h'.symm, h⟩)
  | cons d l₁ ih =>
      rcases mem2_cons_iff.1 h with ⟨hd, hb⟩ | ⟨hd, h'⟩
      · refine mem2_cons_iff.2 (Or.inl ⟨hd, ?_⟩)
        simp only [List.mem_cons, List.mem_append, List.append_eq] at hb ⊢
        tauto
      · exact mem2_cons_iff.2 (Or.inr ⟨hd, ih h'⟩)

theorem mem2_of_append_left_not_mem {l₁ l₂ : List α} {a b : α} (ha : a ∉ l₁)
    (h : Mem2 (l₁ ++ l₂) a b) : Mem2 l₂ a b := by
  induction l₁ with
  | nil => exact h
  | cons d l₁ ih =>
      rcases mem2_cons_iff.1 h with ⟨hd, _⟩ | ⟨_, h'⟩
      · exact absurd (hd ▸ List.mem_cons_self) ha
      · exact ih (fun h'' => ha (List.mem_cons_of_mem _ h'')) h'

theorem mem2_of_append_right_not_mem {l₁ l₂ : List α} {a b : α} (hb : b ∉ l₂)
    (h : Mem2 (l₁ ++ l₂) a b) : Mem2 l₁ a b := by
  induction l₁ with
  | nil => exact absurd h.right_mem hb
  | cons d l₁ ih =>
      rcases mem2_cons_iff.1 h with ⟨hd, hb'⟩ | ⟨hd, h'⟩
      · refine mem2_cons_iff.2 (Or.inl ⟨hd, ?_⟩)
        simp only [List.mem_cons, List.mem_append, List.append_eq] at hb' ⊢
        tauto
      · exact mem2_cons_iff.2 (Or.inr ⟨hd, ih h'⟩)

theorem mem2_append_of_mem {l₁ l₂ : List α} {a b : α} (ha : a ∈ l₁) (hb : b ∈ l₂) :
    Mem2 (l₁ ++ l₂) a b := by
  induction l₁ with
  | nil => exact absurd ha (by simp)
  | cons d l₁ ih =>
      by_cases hd : d = a
      · exact mem2_cons_iff.2 (Or.inl ⟨hd, List.mem_cons_of_mem _ (List.mem_append_right _ hb)⟩)
      · rcases List.mem_cons.1 ha with h | h
        · exact absurd h.symm hd
        · exact mem2_cons_iff.2 (Or.inr ⟨hd, ih h⟩)

theorem mem2_append_cons_of_not_mem {l₁ r : List α} {a b : α} (ha : a ∉ l₁)
    (hb : b ∈ a :: r) : Mem2 (l₁ ++ a :: r) a b :=
  ⟨l₁, r, rfl, ha, hb⟩

/-- Deleting a block containing neither crossing dart preserves the order. -/
theorem mem2_remove_middle {l₁ m l₂ : List α} {a b : α} (ha : a ∉ m) (hb : b ∉ m)
    (h : Mem2 (l₁ ++ (m ++ l₂)) a b) : Mem2 (l₁ ++ l₂) a b := by
  induction l₁ with
  | nil => exact mem2_of_append_left_not_mem ha h
  | cons d l₁ ih =>
      rcases mem2_cons_iff.1 h with ⟨hd, hb'⟩ | ⟨hd, h'⟩
      · refine mem2_cons_iff.2 (Or.inl ⟨hd, ?_⟩)
        simp only [List.mem_cons, List.mem_append, List.append_eq] at hb' ⊢
        tauto
      · exact mem2_cons_iff.2 (Or.inr ⟨hd, ih h'⟩)

theorem lastOf_append_cons (a b : α) (l₁ l₂ : List α) :
    lastOf a (l₁ ++ b :: l₂) = lastOf b l₂ := by
  induction l₁ generalizing a with
  | nil => rfl
  | cons d l₁ ih => exact ih d

theorem isChain_cons_append_cons {R : α → α → Prop} {a b : α} {l₁ l₂ : List α}
    (h1 : List.IsChain R (a :: l₁)) (hj : R (lastOf a l₁) b) (h2 : List.IsChain R (b :: l₂)) :
    List.IsChain R (a :: (l₁ ++ b :: l₂)) := by
  induction l₁ generalizing a with
  | nil => exact List.isChain_cons_cons.2 ⟨hj, h2⟩
  | cons d l₁ ih =>
      have h1' := List.isChain_cons_cons.1 h1
      exact List.isChain_cons_cons.2 ⟨h1'.1, ih h1'.2 hj⟩

theorem isChain_cons_append_cons_iff {R : α → α → Prop} {a b : α} {l₁ l₂ : List α} :
    List.IsChain R (a :: (l₁ ++ b :: l₂)) ↔
      List.IsChain R (a :: l₁) ∧ R (lastOf a l₁) b ∧ List.IsChain R (b :: l₂) := by
  induction l₁ generalizing a with
  | nil => exact ⟨fun h => ⟨List.IsChain.singleton _, (List.isChain_cons_cons.1 h).1,
      (List.isChain_cons_cons.1 h).2⟩, fun h => List.isChain_cons_cons.2 ⟨h.2.1, h.2.2⟩⟩
  | cons d l₁ ih =>
      constructor
      · intro h
        have h' := List.isChain_cons_cons.1 h
        obtain ⟨ha, hj, hb⟩ := ih.1 h'.2
        exact ⟨List.isChain_cons_cons.2 ⟨h'.1, ha⟩, hj, hb⟩
      · rintro ⟨ha, hj, hb⟩
        exact isChain_cons_append_cons ha hj hb

theorem isChain_cons_of_append {R : α → α → Prop} {a : α} {l₁ l₂ : List α}
    (h : List.IsChain R (a :: (l₁ ++ l₂))) : List.IsChain R (a :: l₁) := by
  induction l₁ generalizing a with
  | nil => exact List.IsChain.singleton _
  | cons d l₁ ih =>
      have h' := List.isChain_cons_cons.1 h
      exact List.isChain_cons_cons.2 ⟨h'.1, ih h'.2⟩

theorem nodup_of_count_le [DecidableEq α] {R O : List α} (hO : O.Nodup)
    (h : ∀ a, R.count a ≤ O.count a) : R.Nodup :=
  List.nodup_iff_count_le_one.2 fun a => le_trans (h a) (List.nodup_iff_count_le_one.1 hO a)

end Lists

/-! ## Links of the punctured map, read on darts -/

section Skip

variable {D : Type*} [Fintype D] [DecidableEq D] (H : Hypermap D) (z : D)

/-- A link in which only the face step may skip `z`. -/
def Clink1 (a b : D) : Prop := a = H.node b ∨ skipFun H.face z a = b

/-- A link of `walkupE H z`, read on darts: either step may skip `z`. -/
def Clink2 (a b : D) : Prop := a = skipFun H.node z b ∨ skipFun H.face z a = b

variable {H z}

theorem clink2_of_walkupE {u v : {x : D // x ≠ z}} (h : Clink (walkupE H z) u v) :
    Clink2 H z u v := by
  rcases h with h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (congrArg Subtype.val h)

theorem node_eq_iff_eq_nodeInv {a b : D} : H.node a = b ↔ a = H.node⁻¹ b :=
  ⟨fun h => (inv_apply_eq_of_apply_eq h).symm, fun h => by rw [h]; exact apply_inv_apply _ _⟩

/-- Without a node skip, a `Clink2` chain is a `Clink1` chain. -/
theorem isChain_clink1_of_clink2 {x : D} {p : List D} (h : List.IsChain (Clink2 H z) (x :: p))
    (ht : H.node⁻¹ z ∉ p) : List.IsChain (Clink1 H z) (x :: p) :=
  h.imp_of_mem_tail_imp fun a b _ hb hr => by
    rcases hr with hr | hr
    · refine Or.inl ?_
      rw [hr, skipFun_of_ne]
      intro hc
      exact ht (by rw [← node_eq_iff_eq_nodeInv.1 hc]; exact hb)
    · exact Or.inr hr

/-- Without a face skip, a `Clink1` chain is a chain of C-links of `H`. -/
theorem isChain_clink_of_clink1 {x : D} {p : List D} (h : List.IsChain (Clink1 H z) (x :: p))
    (hf : H.face z ∉ p) : List.IsChain (Clink H) (x :: p) :=
  h.imp_of_mem_tail_imp fun a b _ hb hr => by
    rcases hr with hr | hr
    · exact Or.inl hr
    · refine Or.inr ?_
      by_cases hc : H.face a = z
      · rw [skipFun_of_eq hc] at hr
        exact absurd (hr ▸ hb) hf
      · rwa [skipFun_of_ne hc] at hr

/-- **A `Clink1` chain that is not a chain of `H` has exactly one face skip**, and
inserting `z` there repairs it. -/
theorem split_of_clink1 {x : D} {p : List D} (hU : (z :: x :: p).Nodup)
    (h1 : List.IsChain (Clink1 H z) (x :: p)) (hn : ¬ List.IsChain (Clink H) (x :: p)) :
    ∃ p1 p2, p = p1 ++ H.face z :: p2 ∧ List.IsChain (Clink H) (x :: p1) ∧
      H.face (lastOf x p1) = z ∧ List.IsChain (Clink H) (H.face z :: p2) := by
  have hzx : z ∉ x :: p := (List.nodup_cons.1 hU).1
  have hnd : (x :: p).Nodup := (List.nodup_cons.1 hU).2
  have hfp : H.face z ∈ p := by
    by_contra hf
    exact hn (isChain_clink_of_clink1 h1 hf)
  obtain ⟨p1, p2, rfl⟩ := List.append_of_mem hfp
  obtain ⟨ha, hj, hb⟩ := isChain_cons_append_cons_iff.1 h1
  have hdisj := List.nodup_append.1 (List.nodup_cons.1 hnd).2
  have hf1 : H.face z ∉ p1 := fun h => hdisj.2.2 _ h _ List.mem_cons_self rfl
  have hf2 : H.face z ∉ p2 := (List.nodup_cons.1 hdisj.2.1).1
  have hc1 := isChain_clink_of_clink1 ha hf1
  have hc2 := isChain_clink_of_clink1 hb hf2
  refine ⟨p1, p2, rfl, hc1, ?_, hc2⟩
  have hlast : lastOf x p1 ∈ x :: p1 := lastOf_mem_cons x p1
  rcases hj with hj | hj
  · exact absurd (isChain_cons_append_cons hc1 (Or.inl hj) hc2) hn
  · by_contra hc
    rw [skipFun_of_ne hc] at hj
    have : lastOf x p1 = z := H.face.injective hj
    exact hzx (by
      rw [← this]
      rcases List.mem_cons.1 hlast with h | h
      · rw [h]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ h))

/-- Certifying a Moebius path of `H` from its parts. -/
theorem moebiusPath_intro {x : D} {p : List D} {L t n : D}
    (hnd : (x :: p).Nodup) (hch : List.IsChain (Clink H) (x :: p))
    (hL : lastOf x p = L) (ht : H.node t = L) (hn : H.node x = n) (hm : Mem2 p t n) :
    MoebiusPath H x p := by
  refine ⟨hnd, hch, ?_⟩
  rw [hL, ← ht, inv_apply_apply, hn]
  exact hm

end Skip

/-! ## Lifting a Moebius path through the deletion -/

section Lift

variable {D : Type*} [Fintype D] [DecidableEq D] {H : Hypermap D} {z : D}

/-- **Stage 1.**  A lifted path with no skip at all would already give a Moebius
path of `H`. -/
theorem jw_plain (hJ : Jordan H) {x y : D} {p : List D} (hU : (z :: x :: p).Nodup)
    (hL : skipFun H.node z y = lastOf x p) (hpy : Mem2 p y (skipFun H.node z x)) :
    ¬ List.IsChain (Clink H) (x :: p) := by
  intro hc
  have hnd : (x :: p).Nodup := (List.nodup_cons.1 hU).2
  have hxp : x ∉ p := (List.nodup_cons.1 hnd).1
  have hxy : x ≠ y := fun h => hxp (by rw [h]; exact hpy.left_mem)
  by_cases hyt : H.node y = z
  · -- the last dart is `node z`: append `z`
    have hLz : lastOf x p = H.node z := by rw [← hL, skipFun_of_eq hyt]
    have hnx : H.node x ≠ z := fun h => hxy (H.node.injective (h.trans hyt.symm))
    rw [skipFun_of_ne hnx] at hpy
    refine hJ x (p ++ [z]) (moebiusPath_intro (L := z) (t := y) (n := H.node x) ?_
      (isChain_cons_append_cons hc (Or.inl hLz) (List.IsChain.singleton z))
      (lastOf_append_cons x z p []) hyt rfl (mem2_append_right hpy))
    exact nodup_of_count_le hU (fun a => by simp only [List.count_cons, List.count_append, List.count_nil]; omega)
  · have hLy : lastOf x p = H.node y := by rw [← hL, skipFun_of_ne hyt]
    by_cases hxt : H.node x = z
    · -- the first crossing link skips: prepend `z`
      rw [skipFun_of_eq hxt] at hpy
      exact hJ z (x :: p) (moebiusPath_intro (L := H.node y) (t := y) (n := H.node z) hU
        (List.isChain_cons_cons.2 ⟨Or.inl hxt.symm, hc⟩) hLy rfl rfl
        (mem2_cons_iff.2 (Or.inr ⟨hxy, hpy⟩)))
    · rw [skipFun_of_ne hxt] at hpy
      exact hJ x p (moebiusPath_intro hnd hc hLy rfl rfl hpy)

/-- **Stage 2.**  A lifted path whose only skips are face skips would give a
Moebius path of `H`. -/
theorem jw_clink1 (hJ : Jordan H) {x y : D} {p : List D} (hU : (z :: x :: p).Nodup)
    (hL : skipFun H.node z y = lastOf x p) (hpy : Mem2 p y (skipFun H.node z x)) :
    ¬ List.IsChain (Clink1 H z) (x :: p) := by
  intro h1
  obtain ⟨p1, p2, rfl, hc1, hj, hc2⟩ := split_of_clink1 hU h1 (jw_plain hJ hU hL hpy)
  have hnd : (x :: (p1 ++ H.face z :: p2)).Nodup := (List.nodup_cons.1 hU).2
  have hzx : z ∉ x :: (p1 ++ H.face z :: p2) := (List.nodup_cons.1 hU).1
  have hz1 : z ∉ p1 := fun h => hzx (List.mem_cons_of_mem _ (List.mem_append_left _ h))
  have hxy : x ≠ y := fun h => (List.nodup_cons.1 hnd).1 (by rw [h]; exact hpy.left_mem)
  have hyz : y ≠ z := by
    intro h
    have hm := hpy.left_mem
    rw [h] at hm
    exact hzx (List.mem_cons_of_mem _ hm)
  have hchP : List.IsChain (Clink H) (x :: (p1 ++ z :: H.face z :: p2)) :=
    isChain_cons_append_cons hc1 (Or.inr hj) (List.isChain_cons_cons.2 ⟨Or.inr rfl, hc2⟩)
  have hndP : (x :: (p1 ++ z :: H.face z :: p2)).Nodup := nodup_of_count_le hU (fun a => by simp only [List.count_cons, List.count_append]; omega)
  have hlastP : lastOf x (p1 ++ z :: H.face z :: p2) = lastOf x (p1 ++ H.face z :: p2) := by
    rw [lastOf_append_cons, lastOf_append_cons]
    rfl
  by_cases hyt : H.node y = z
  · have hLz : lastOf x (p1 ++ H.face z :: p2) = H.node z := by rw [← hL, skipFun_of_eq hyt]
    have hnx : H.node x ≠ z := fun h => hxy (H.node.injective (h.trans hyt.symm))
    rw [skipFun_of_ne hnx] at hpy
    by_cases hn2 : H.node x ∈ H.face z :: p2
    · exact hJ x _ (moebiusPath_intro (L := H.node z) (t := z) (n := H.node x) hndP hchP
        (hlastP.trans hLz) rfl rfl (mem2_append_cons_of_not_mem hz1 (List.mem_cons_of_mem _ hn2)))
    · have hpy1 : Mem2 p1 y (H.node x) := mem2_of_append_right_not_mem hn2 hpy
      refine hJ x (p1 ++ [z]) (moebiusPath_intro (L := z) (t := y) (n := H.node x) ?_
        (isChain_cons_append_cons hc1 (Or.inr hj) (List.IsChain.singleton z))
        (lastOf_append_cons x z p1 []) hyt rfl (mem2_append_right hpy1))
      exact nodup_of_count_le hU (fun a => by simp only [List.count_cons, List.count_append, List.count_nil]; omega)
  · have hLy : lastOf x (p1 ++ H.face z :: p2) = H.node y := by rw [← hL, skipFun_of_ne hyt]
    by_cases hxt : H.node x = z
    · rw [skipFun_of_eq hxt] at hpy
      by_cases hy1 : y ∈ p1
      · exact hJ x _ (moebiusPath_intro (L := H.node y) (t := y) (n := z) hndP hchP
          (hlastP.trans hLy) rfl hxt (mem2_append_of_mem hy1 List.mem_cons_self))
      · have hpy2 : Mem2 (H.face z :: p2) y (H.node z) := mem2_of_append_left_not_mem hy1 hpy
        refine hJ z (H.face z :: p2) (moebiusPath_intro (L := H.node y) (t := y) (n := H.node z) ?_
          (List.isChain_cons_cons.2 ⟨Or.inr rfl, hc2⟩) ?_ rfl rfl hpy2)
        · exact nodup_of_count_le hU (fun a => by simp only [List.count_cons, List.count_append]; omega)
        · show lastOf (H.face z) p2 = H.node y
          rw [← lastOf_append_cons x (H.face z) p1 p2]
          exact hLy
    · rw [skipFun_of_ne hxt] at hpy
      exact hJ x _ (moebiusPath_intro (L := H.node y) (t := y) (n := H.node x) hndP hchP
        (hlastP.trans hLy) rfl rfl (mem2_splice hyz hpy))

/-- **Stage 3.**  The remaining configuration — a node skip into `node⁻¹ z` — is
contradictory. -/
theorem jw_final (hJ : Jordan H) {x y : D} {p : List D} (hU : (z :: x :: p).Nodup)
    (hch : List.IsChain (Clink2 H z) (x :: p))
    (hL : skipFun H.node z y = lastOf x p) (hpy : Mem2 p y (skipFun H.node z x)) : False := by
  have hnc1 := jw_clink1 hJ hU hL hpy
  have hzx : z ∉ x :: p := (List.nodup_cons.1 hU).1
  have hnd : (x :: p).Nodup := (List.nodup_cons.1 hU).2
  have hxp : x ∉ p := (List.nodup_cons.1 hnd).1
  have ht₀ : H.node⁻¹ z ∈ p := by
    by_contra h
    exact hnc1 (isChain_clink1_of_clink2 hch h)
  have hnt : H.node (H.node⁻¹ z) = z := apply_inv_apply _ _
  have hnxz : H.node x ≠ z := fun h => hxp (by rw [node_eq_iff_eq_nodeInv.1 h]; exact ht₀)
  rw [skipFun_of_ne hnxz] at hpy
  have hyz : y ≠ z := fun h => hzx (List.mem_cons_of_mem _ (by rw [← h]; exact hpy.left_mem))
  obtain ⟨p1, p2, rfl⟩ := List.append_of_mem ht₀
  obtain ⟨hc2a, hj, hc2b⟩ := isChain_cons_append_cons_iff.1 hch
  have hnd' := List.nodup_append.1 (List.nodup_cons.1 hnd).2
  have ht1 : H.node⁻¹ z ∉ p1 := fun h => hnd'.2.2 _ h _ List.mem_cons_self rfl
  have ht2 : H.node⁻¹ z ∉ p2 := (List.nodup_cons.1 hnd'.2.1).1
  have h1a := isChain_clink1_of_clink2 hc2a ht1
  have h1b := isChain_clink1_of_clink2 hc2b ht2
  have hz1 : z ∉ p1 := fun h => hzx (List.mem_cons_of_mem _ (List.mem_append_left _ h))
  have hLp1 : lastOf x p1 = H.node z := by
    rcases hj with h | h
    · rw [h, skipFun_of_eq hnt]
    · exact absurd (isChain_cons_append_cons h1a (Or.inr h) h1b) hnc1
  have hLast : lastOf x (p1 ++ H.node⁻¹ z :: p2) = lastOf (H.node⁻¹ z) p2 :=
    lastOf_append_cons _ _ p1 p2
  have hyt : H.node y ≠ z := by
    intro hyt
    have h1 : lastOf (H.node⁻¹ z) p2 = H.node z := by rw [← hLast, ← hL, skipFun_of_eq hyt]
    have hm1 : H.node z ∈ x :: p1 := hLp1 ▸ lastOf_mem_cons x p1
    have hm2 : H.node z ∈ H.node⁻¹ z :: p2 := h1 ▸ lastOf_mem_cons _ p2
    have hdis : ((x :: p1) ++ (H.node⁻¹ z :: p2)).Nodup := hnd
    exact (List.nodup_append.1 hdis).2.2 _ hm1 _ hm2 rfl
  have hLp2 : lastOf (H.node⁻¹ z) p2 = H.node y := by rw [← hLast, ← hL, skipFun_of_ne hyt]
  -- the part before `node⁻¹ z` has no face skip
  have hc1 : List.IsChain (Clink H) (x :: p1) := by
    by_contra hnc
    have hU1 : (z :: x :: p1).Nodup := nodup_of_count_le hU (fun a => by simp only [List.count_cons, List.count_append]; omega)
    obtain ⟨q1, q2, rfl, hq1, hqj, hq2⟩ := split_of_clink1 hU1 h1a hnc
    have hfz2 : H.face z ∉ H.node⁻¹ z :: p2 := fun h =>
      hnd'.2.2 _ (List.mem_append_right _ List.mem_cons_self) _ h rfl
    have htc : List.IsChain (Clink H) (H.node⁻¹ z :: p2) :=
      isChain_clink_of_clink1 h1b (fun h => hfz2 (List.mem_cons_of_mem _ h))
    have hLq2 : lastOf (H.face z) q2 = H.node z := by
      rw [← lastOf_append_cons x (H.face z) q1 q2]
      exact hLp1
    have hzq1 : z ∉ q1 := fun h => hz1 (List.mem_append_left _ h)
    have hq2nx : H.node x ∉ H.face z :: q2 := by
      intro hn
      refine hJ x (q1 ++ z :: H.face z :: q2) (moebiusPath_intro (L := H.node z) (t := z)
        (n := H.node x) ?_
        (isChain_cons_append_cons hq1 (Or.inr hqj) (List.isChain_cons_cons.2 ⟨Or.inr rfl, hq2⟩))
        ?_ rfl rfl (mem2_append_cons_of_not_mem hzq1 (List.mem_cons_of_mem _ hn)))
      · exact nodup_of_count_le hU (fun a => by simp only [List.count_cons, List.count_append]; omega)
      · rw [lastOf_append_cons]
        exact hLq2
    have h0 : Mem2 (q1 ++ ((H.face z :: q2) ++ H.node⁻¹ z :: p2)) y (H.node x) := by
      simpa only [List.append_assoc, List.cons_append] using hpy
    have hq2y : y ∈ H.face z :: q2 := by
      by_contra hy
      have hpy' : Mem2 (q1 ++ z :: H.node⁻¹ z :: p2) y (H.node x) :=
        mem2_splice hyz (mem2_remove_middle hy hq2nx h0)
      refine hJ x (q1 ++ z :: H.node⁻¹ z :: p2) (moebiusPath_intro (L := H.node y) (t := y)
        (n := H.node x) ?_
        (isChain_cons_append_cons hq1 (Or.inr hqj) (List.isChain_cons_cons.2 ⟨Or.inl hnt.symm, htc⟩))
        ?_ rfl rfl hpy')
      · exact nodup_of_count_le hU (fun a => by simp only [List.count_cons, List.count_append]; omega)
      · rw [lastOf_append_cons]
        exact hLp2
    have hyq1 : y ∉ q1 := by
      intro hy
      have hdis : (q1 ++ ((H.face z :: q2) ++ H.node⁻¹ z :: p2)).Nodup := by
        have := (List.nodup_cons.1 hnd).2
        simpa only [List.append_assoc, List.cons_append] using this
      exact (List.nodup_append.1 hdis).2.2 _ hy _ (List.mem_append_left _ hq2y) rfl
    have hp2nx : H.node x ∈ H.node⁻¹ z :: p2 := by
      rcases List.mem_append.1 (mem2_of_append_left_not_mem hyq1 h0).right_mem with h | h
      · exact absurd h hq2nx
      · exact h
    obtain ⟨q21, q22, hq2eq⟩ := List.append_of_mem hq2y
    have hzq2 : List.IsChain (Clink H) (z :: H.face z :: q2) :=
      List.isChain_cons_cons.2 ⟨Or.inr rfl, hq2⟩
    rw [hq2eq] at hzq2
    have hyq22 : List.IsChain (Clink H) (y :: q22) := (isChain_cons_append_cons_iff.1 hzq2).2.2
    have hLq22 : lastOf y q22 = H.node z := by
      have e : lastOf z (H.face z :: q2) = lastOf z (q21 ++ y :: q22) := by rw [hq2eq]
      rw [lastOf_append_cons] at e
      rw [← e]
      exact hLq2
    refine hJ x (q1 ++ z :: H.node⁻¹ z :: (p2 ++ y :: q22)) (moebiusPath_intro (L := H.node z)
      (t := z) (n := H.node x) ?_ ?_ ?_ rfl rfl ?_)
    · refine nodup_of_count_le hU (fun a => ?_)
      have e := congrArg (List.count a) hq2eq
      simp only [List.count_cons, List.count_append] at e ⊢
      omega
    · exact isChain_cons_append_cons hq1 (Or.inr hqj)
        (List.isChain_cons_cons.2 ⟨Or.inl hnt.symm,
          isChain_cons_append_cons htc (Or.inl hLp2) hyq22⟩)
    · rw [lastOf_append_cons]
      show lastOf (H.node⁻¹ z) (p2 ++ y :: q22) = H.node z
      rw [lastOf_append_cons]
      exact hLq22
    · exact mem2_append_cons_of_not_mem hzq1 (by
        rcases List.mem_cons.1 hp2nx with h | h
        · rw [h]; exact List.mem_cons_of_mem _ List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ h)))
  -- the part after `node⁻¹ z` does have a face skip
  have hnc2 : ¬ List.IsChain (Clink H) (H.node⁻¹ z :: p2) := by
    intro hc2
    refine hJ x (p1 ++ z :: H.node⁻¹ z :: p2) (moebiusPath_intro (L := H.node y) (t := y)
      (n := H.node x) ?_
      (isChain_cons_append_cons hc1 (Or.inl hLp1) (List.isChain_cons_cons.2 ⟨Or.inl hnt.symm, hc2⟩))
      ?_ rfl rfl (mem2_splice hyz hpy))
    · exact nodup_of_count_le hU (fun a => by simp only [List.count_cons, List.count_append]; omega)
    · rw [lastOf_append_cons]
      exact hLp2
  have hU2 : (z :: H.node⁻¹ z :: p2).Nodup := nodup_of_count_le hU (fun a => by simp only [List.count_cons, List.count_append]; omega)
  obtain ⟨r1, r2, rfl, hr1, hrj, hr2⟩ := split_of_clink1 hU2 h1b hnc2
  have hLr2 : lastOf (H.face z) r2 = H.node y := by
    rw [← lastOf_append_cons (H.node⁻¹ z) (H.face z) r1 r2]
    exact hLp2
  have hzr : List.IsChain (Clink H) (z :: H.face z :: r2) := List.isChain_cons_cons.2 ⟨Or.inr rfl, hr2⟩
  have hyr1 : y ∉ H.node⁻¹ z :: r1 := by
    intro hy
    have hy' : y ∈ r1 := (List.mem_cons.1 hy).resolve_left (fun h => hyt (by rw [h]; exact hnt))
    refine hJ (H.node⁻¹ z) (r1 ++ z :: H.face z :: r2) (moebiusPath_intro (L := H.node y) (t := y)
      (n := z) ?_ (isChain_cons_append_cons hr1 (Or.inr hrj) hzr) ?_ rfl hnt
      (mem2_append_of_mem hy' List.mem_cons_self))
    · exact nodup_of_count_le hU (fun a => by simp only [List.count_cons, List.count_append]; omega)
    · rw [lastOf_append_cons]
      exact hLr2
  have h0 : Mem2 (p1 ++ ((H.node⁻¹ z :: r1) ++ H.face z :: r2)) y (H.node x) := by
    simpa only [List.append_assoc, List.cons_append] using hpy
  have hr1nx : H.node x ∈ H.node⁻¹ z :: r1 := by
    by_contra hn
    refine hJ x (p1 ++ z :: H.face z :: r2) (moebiusPath_intro (L := H.node y) (t := y)
      (n := H.node x) ?_ (isChain_cons_append_cons hc1 (Or.inl hLp1) hzr) ?_ rfl rfl
      (mem2_splice hyz (mem2_remove_middle hyr1 hn h0)))
    · exact nodup_of_count_le hU (fun a => by simp only [List.count_cons, List.count_append]; omega)
    · rw [lastOf_append_cons]
      exact hLr2
  have hyp1 : y ∈ p1 := by
    have hdis : ((H.node⁻¹ z :: r1) ++ H.face z :: r2).Nodup := hnd'.2.1
    have hnr2 : H.node x ∉ H.face z :: r2 := fun h =>
      (List.nodup_append.1 hdis).2.2 _ hr1nx _ h rfl
    have h0' : Mem2 ((p1 ++ H.node⁻¹ z :: r1) ++ H.face z :: r2) y (H.node x) := by
      simpa only [List.append_assoc, List.cons_append] using hpy
    rcases List.mem_append.1 (mem2_of_append_right_not_mem hnr2 h0').left_mem with h | h
    · exact h
    · exact absurd h hyr1
  obtain ⟨r11, r12, rfl, hLr11⟩ : ∃ r11 r12, r1 = r11 ++ r12 ∧ lastOf (H.node⁻¹ z) r11 = H.node x := by
    by_cases hnt' : H.node x = H.node⁻¹ z
    · exact ⟨[], r1, rfl, hnt'.symm⟩
    · obtain ⟨s, s', rfl⟩ := List.append_of_mem ((List.mem_cons.1 hr1nx).resolve_left hnt')
      exact ⟨s ++ [H.node x], s', by simp, lastOf_append_cons _ (H.node x) s []⟩
  have hr11 : List.IsChain (Clink H) (H.node⁻¹ z :: r11) := isChain_cons_of_append hr1
  refine hJ (H.node⁻¹ z) (r11 ++ x :: (p1 ++ z :: H.face z :: r2)) (moebiusPath_intro
    (L := H.node y) (t := y) (n := z) ?_ ?_ ?_ rfl hnt ?_)
  · exact nodup_of_count_le hU (fun a => by simp only [List.count_cons, List.count_append]; omega)
  · exact isChain_cons_append_cons hr11 (Or.inl hLr11)
      (isChain_cons_append_cons hc1 (Or.inl hLp1) hzr)
  · rw [lastOf_append_cons]
    show lastOf x (p1 ++ z :: H.face z :: r2) = H.node y
    rw [lastOf_append_cons]
    exact hLr2
  · have hm : Mem2 ((r11 ++ x :: p1) ++ z :: H.face z :: r2) y z :=
      mem2_append_of_mem (List.mem_append_right _ (List.mem_cons_of_mem _ hyp1)) List.mem_cons_self
    simpa only [List.append_assoc, List.cons_append] using hm

/-- **The Jordan property survives the Walkup transform.**  This is the source's
`Jordan_WalkupE`. -/
theorem jordan_walkupE (H : Hypermap D) (z : D) (hJ : Jordan H) : Jordan (walkupE H z) := by
  intro u q hM
  obtain ⟨hnd, hch, hm⟩ := hM
  have hmap : (u :: q).map Subtype.val = (u : D) :: q.map Subtype.val := rfl
  have hU : (z :: (u : D) :: q.map Subtype.val).Nodup := by
    refine List.nodup_cons.2 ⟨?_, ?_⟩
    · intro hz
      rw [← hmap, List.mem_map] at hz
      obtain ⟨w, _, hw⟩ := hz
      exact w.2 hw
    · rw [← hmap]
      exact hnd.map Subtype.val_injective
  have hch2 : List.IsChain (Clink2 H z) ((u : D) :: q.map Subtype.val) := by
    rw [← hmap, List.isChain_map]
    exact hch.imp fun _ _ h => clink2_of_walkupE h
  have hL : skipFun H.node z (((walkupE H z).node⁻¹ (lastOf u q) : {x : D // x ≠ z}) : D)
      = lastOf (u : D) (q.map Subtype.val) := by
    rw [lastOf_map]
    exact congrArg Subtype.val (apply_inv_apply (walkupE H z).node (lastOf u q))
  have hpy : Mem2 (q.map Subtype.val)
      (((walkupE H z).node⁻¹ (lastOf u q) : {x : D // x ≠ z}) : D) (skipFun H.node z u) :=
    (mem2_map_iff Subtype.val_injective).2 hm
  exact jw_final hJ hU hch2 hL hpy

end Lift

end Hypermap

end Mettapedia.GraphTheory.FourColor
