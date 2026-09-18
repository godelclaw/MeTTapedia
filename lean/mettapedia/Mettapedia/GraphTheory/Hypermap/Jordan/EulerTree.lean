import Mettapedia.GraphTheory.Hypermap.Jordan.Walkup

/-!
# Break the dikes: a Jordan map has a leaf on every edge cycle

**`euler_tree`.**  If `H` has no Moebius path then every edge cycle contains a
dart `y` that is either C-linked to itself (fixed by `node` or by `face`) or
not cross-edge (`y` and `node y` on different edge cycles).  This is the
source's `Euler_tree`, the combinatorial heart of the "break the dikes" proof of
Euler's formula: a connected map with a single face is a tree and has a
terminal node.  It is exactly what the converse `Jordan → Planar` needs, because
deleting such a dart preserves the genus.

## The argument

Suppose some edge cycle has no such dart.

1. **A face-simple arc.**  Among all darts `w` of the cycle and all `d ≥ 1` with
   `edge^d w` in the face of `w`, take `d` least.  The arc
   `x = edge w, …, z₁ = edge^d w` then visits pairwise distinct faces — a shorter
   repetition would contradict minimality — and its last dart shares a face with
   `w = node (face x)`.
2. **The contour.**  Walk around the face of each arc dart in turn, crossing
   from one face to the next by the node link `a ⟶ face (edge a)`, and stop at
   `w` in the last face.  This is a duplicate-free C-path from `face x` to `w`,
   and every dart whose face successor lies on it is `z₁` or a non-final dart of
   it: the contour can only be *entered* by a face step from `z₁`.
3. **The dike.**  `face x` lies on the edge cycle but not on the arc, so there is
   an edge path from `face x` back to `w` avoiding `z₁`.  Walking it backwards,
   and around each node cycle on the way, builds a C-path from `w` to `face x`
   that never touches the contour: a face step could only enter from `z₁`, which
   the path avoids, and a node step onto the contour would close a Moebius path.
   But `face x` is the contour's first dart — contradiction.

The source picks the arc by walking the edge cycle with a face-root function.
Here the arc comes from a single minimality argument over hitting times
(`hitList`), which gives face-simplicity with no bookkeeping.
-/

namespace Mettapedia.GraphTheory

open Mettapedia.GraphTheory.FourColor

open Equiv Equiv.Perm
open GoertzelV24PermutationOrbitSurgery GoertzelV24WordReachability

namespace Hypermap

/-! ## Hitting lists -/

section HitList

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- `hitList f a n = [f a, f² a, …, fⁿ a]`. -/
def hitList (f : Perm D) : D → ℕ → List D
  | _, 0 => []
  | a, n + 1 => f a :: hitList f (f a) n

omit [Fintype D] [DecidableEq D] in
@[simp] theorem hitList_zero (f : Perm D) (a : D) : hitList f a 0 = [] := rfl

omit [Fintype D] [DecidableEq D] in
@[simp] theorem hitList_succ (f : Perm D) (a : D) (n : ℕ) :
    hitList f a (n + 1) = f a :: hitList f (f a) n := rfl

omit [Fintype D] [DecidableEq D] in
theorem pow_succ_apply' (f : Perm D) (a : D) (k : ℕ) : (f ^ (k + 1)) a = (f ^ k) (f a) := by
  rw [pow_succ, Perm.mul_apply]

omit [Fintype D] [DecidableEq D] in
theorem isChain_hitList (f : Perm D) (a : D) (n : ℕ) :
    List.IsChain (fun u v => f u = v) (a :: hitList f a n) := by
  induction n generalizing a with
  | zero => exact List.IsChain.singleton a
  | succ n ih => exact List.isChain_cons_cons.2 ⟨rfl, ih (f a)⟩

omit [Fintype D] [DecidableEq D] in
theorem lastOf_hitList (f : Perm D) (a : D) (n : ℕ) : lastOf a (hitList f a n) = (f ^ n) a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
      show lastOf (f a) (hitList f (f a) n) = _
      rw [ih, pow_succ_apply']

omit [Fintype D] [DecidableEq D] in
theorem mem_hitList (f : Perm D) (a v : D) (n : ℕ) :
    v ∈ hitList f a n ↔ ∃ k, 1 ≤ k ∧ k ≤ n ∧ (f ^ k) a = v := by
  induction n generalizing a with
  | zero =>
      constructor
      · intro h; simp at h
      · rintro ⟨k, hk1, hk0, _⟩; omega
  | succ n ih =>
      rw [hitList_succ, List.mem_cons, ih]
      constructor
      · rintro (h | ⟨k, hk1, hkn, hk⟩)
        · exact ⟨1, le_rfl, by omega, by rw [pow_one]; exact h.symm⟩
        · exact ⟨k + 1, by omega, by omega, by rw [pow_succ_apply']; exact hk⟩
      · rintro ⟨k, hk1, hkn, hk⟩
        rcases Nat.lt_or_ge k 2 with h | h
        · left
          have hk' : k = 1 := by omega
          subst hk'
          rw [pow_one] at hk
          exact hk.symm
        · right
          refine ⟨k - 1, by omega, by omega, ?_⟩
          rw [← pow_succ_apply', Nat.sub_add_cancel (by omega)]
          exact hk

omit [Fintype D] [DecidableEq D] in
theorem hitList_pairwise {R : D → D → Prop} (f : Perm D) (a : D) (n : ℕ)
    (h : ∀ i j, 1 ≤ i → i < j → j ≤ n → R ((f ^ i) a) ((f ^ j) a)) :
    (hitList f a n).Pairwise R := by
  induction n generalizing a with
  | zero => exact List.Pairwise.nil
  | succ n ih =>
      rw [hitList_succ, List.pairwise_cons]
      refine ⟨fun b hb => ?_, ih (f a) (fun i j hi hij hjn => ?_)⟩
      · obtain ⟨k, hk1, hkn, rfl⟩ := (mem_hitList f (f a) b n).1 hb
        have hR := h 1 (k + 1) le_rfl (by omega) (by omega)
        rwa [pow_one, pow_succ_apply'] at hR
      · have hR := h (i + 1) (j + 1) (by omega) (by omega) (by omega)
        rwa [pow_succ_apply', pow_succ_apply'] at hR

omit [Fintype D] [DecidableEq D] in
theorem sameCycle_pow_apply (σ : Perm D) (x : D) (k : ℕ) : σ.SameCycle x ((σ ^ k) x) :=
  ⟨k, by rw [zpow_natCast]⟩

/-- The first positive hitting time. -/
theorem exists_min_hit (f : Perm D) {a b : D} (h : f.SameCycle a b) :
    ∃ n, 1 ≤ n ∧ (f ^ n) a = b ∧ ∀ j, 1 ≤ j → j < n → (f ^ j) a ≠ b := by
  classical
  have hex : ∃ n, 1 ≤ n ∧ (f ^ n) a = b := by
    obtain ⟨k, hk⟩ := exists_nat_pow_apply_eq h
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · refine ⟨orderOf f, orderOf_pos f, ?_⟩
      rw [pow_orderOf_eq_one]
      simpa using hk
    · exact ⟨k, hk0, hk⟩
  exact ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
    fun j hj1 hjn hjb => Nat.find_min hex hjn ⟨hj1, hjb⟩⟩

omit [Fintype D] [DecidableEq D] in
theorem pow_sub_apply_eq {f : Perm D} {a : D} {i j : ℕ} (hij : i ≤ j)
    (heq : (f ^ i) a = (f ^ j) a) : (f ^ (j - i)) a = a := by
  apply (f ^ i).injective
  rw [← Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hij]
  exact heq.symm

omit [Fintype D] [DecidableEq D] in
/-- Up to the first hit, a hitting list has no repetition. -/
theorem hitList_nodup_of_min (f : Perm D) (a : D) (n : ℕ)
    (hmin : ∀ j, 1 ≤ j → j < n → (f ^ j) a ≠ (f ^ n) a) : (hitList f a n).Nodup := by
  refine hitList_pairwise f a n (fun i j hi hij hjn heq => ?_)
  have hret := pow_sub_apply_eq hij.le heq
  apply hmin (n - (j - i)) (by omega) (by omega)
  conv_rhs => rw [show n = (n - (j - i)) + (j - i) by omega, pow_add, Perm.mul_apply, hret]

omit [Fintype D] [DecidableEq D] in
/-- Up to the first hit, a hitting list does not return to its start. -/
theorem not_mem_hitList_self (f : Perm D) (a : D) (n : ℕ)
    (hmin : ∀ j, 1 ≤ j → j < n → (f ^ j) a ≠ (f ^ n) a) (hne : (f ^ n) a ≠ a) :
    a ∉ hitList f a n := by
  intro h
  obtain ⟨k, hk1, hkn, hk⟩ := (mem_hitList f a a n).1 h
  rcases Nat.lt_or_ge k n with hlt | hge
  · apply hmin (n - k) (by omega) (by omega)
    conv_rhs => rw [show n = (n - k) + k by omega, pow_add, Perm.mul_apply, hk]
  · exact hne (by rw [show n = k by omega]; exact hk)

omit [Fintype D] [DecidableEq D] in
/-- A periodic orbit is reached within one period. -/
theorem pow_apply_mod {f : Perm D} {a : D} {p : ℕ} (hp : (f ^ p) a = a) (j : ℕ) :
    (f ^ j) a = (f ^ (j % p)) a := by
  conv_lhs => rw [← Nat.mod_add_div j p, pow_add, Perm.mul_apply, pow_mul_apply_eq_self hp]

end HitList

/-! ## Paths: splicing and extension -/

section Paths

variable {α : Type*}

theorem lastOf_append (a : α) (l₁ l₂ : List α) : lastOf a (l₁ ++ l₂) = lastOf (lastOf a l₁) l₂ := by
  induction l₁ generalizing a with
  | nil => rfl
  | cons b l₁ ih => exact ih b

theorem isChain_cons_append {R : α → α → Prop} {a : α} {l₁ l₂ : List α}
    (h1 : List.IsChain R (a :: l₁)) (h2 : List.IsChain R (lastOf a l₁ :: l₂)) :
    List.IsChain R (a :: (l₁ ++ l₂)) := by
  induction l₁ generalizing a with
  | nil => exact h2
  | cons b l₁ ih =>
      have h1' := List.isChain_cons_cons.1 h1
      exact List.isChain_cons_cons.2 ⟨h1'.1, ih h1'.2 h2⟩

theorem mem2_lastOf {l : List α} {a v : α} (hv : v ∈ l) : Mem2 l v (lastOf a l) := by
  induction l generalizing a with
  | nil => simp at hv
  | cons b l ih =>
      by_cases hb : b = v
      · exact mem2_cons_iff.2 (Or.inl ⟨hb, lastOf_mem_cons b l⟩)
      · rcases List.mem_cons.1 hv with h | h
        · exact absurd h.symm hb
        · exact mem2_cons_iff.2 (Or.inr ⟨hb, ih h⟩)

variable [DecidableEq α]

/-- **Extending a duplicate-free path by one step**, cutting back to the new
dart if it was already visited. -/
theorem extend_path {R : α → α → Prop} {w v u : α} {q C : List α}
    (hch : List.IsChain R (w :: q)) (hl : lastOf w q = v) (hnd : (w :: q).Nodup)
    (hav : ∀ t ∈ q, t ∉ C) (hR : R v u) (hu : u ∉ C) (huw : u ≠ w) :
    ∃ q', List.IsChain R (w :: q') ∧ lastOf w q' = u ∧ (w :: q').Nodup ∧ ∀ t ∈ q', t ∉ C := by
  by_cases huq : u ∈ q
  · obtain ⟨s, s', rfl⟩ := List.append_of_mem huq
    refine ⟨s ++ [u], ?_, lastOf_append_cons w u s [], ?_, ?_⟩
    · have hc : List.IsChain R (w :: ((s ++ [u]) ++ s')) := by
        simpa only [List.append_assoc, List.singleton_append] using hch
      exact isChain_cons_of_append hc
    · refine nodup_of_count_le hnd (fun a => ?_)
      simp only [List.count_cons, List.count_append, List.count_nil]
      omega
    · intro t ht
      exact hav t (by simp only [List.mem_append, List.mem_cons] at ht ⊢; tauto)
  · refine ⟨q ++ [u], isChain_cons_append_cons hch (hl ▸ hR) (List.IsChain.singleton u),
      lastOf_append_cons w u q [], ?_, ?_⟩
    · have hwq := (List.nodup_cons.1 hnd)
      refine List.nodup_cons.2 ⟨?_, ?_⟩
      · simp only [List.mem_append, List.mem_singleton, not_or]
        exact ⟨hwq.1, huw.symm⟩
      · exact List.nodup_append.2 ⟨hwq.2, List.nodup_singleton u,
          fun a ha b hb hab => huq (by rw [List.mem_singleton.1 hb] at hab; rw [← hab]; exact ha)⟩
    · intro t ht
      rcases List.mem_append.1 ht with h | h
      · exact hav t h
      · rw [List.mem_singleton.1 h]; exact hu

end Paths

/-! ## The contour around a face-simple arc -/

section Contour

variable {D : Type*} [Fintype D] [DecidableEq D] {H : Hypermap D}

/-- **The contour.**  Around a face-simple edge arc `x :: p1`, a duplicate-free
C-path from `face x` to any dart `z` in the face of the arc's last dart, which
visits only the arc's faces, and which can be entered by a face step only from
the arc's last dart. -/
theorem exists_contour (x : D) (p1 : List D) (z : D)
    (hchain : List.IsChain (fun u v => H.edge u = v) (x :: p1))
    (hsimple : (x :: p1).Pairwise (fun a b => ¬ H.face.SameCycle a b))
    (hz : H.face.SameCycle (lastOf x p1) z) :
    ∃ q1, List.IsChain (Clink H) (H.face x :: q1) ∧ lastOf (H.face x) q1 = z ∧
      (H.face x :: q1).Nodup ∧
      (∀ v ∈ H.face x :: q1, ∃ a ∈ x :: p1, H.face.SameCycle a v) ∧
      (∀ v, H.face v ∈ H.face x :: q1 → v = lastOf x p1 ∨ (v ∈ H.face x :: q1 ∧ v ≠ z)) := by
  induction p1 generalizing x with
  | nil =>
      have hz' : H.face.SameCycle x z := hz
      obtain ⟨n, hn1, hnz, hnmin⟩ := exists_min_hit H.face hz'
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      refine ⟨hitList H.face (H.face x) m, ?_, ?_, ?_, ?_, ?_⟩
      · exact (isChain_hitList H.face (H.face x) m).imp fun _ _ h => Or.inr h
      · show lastOf x (hitList H.face x (m + 1)) = z
        rw [lastOf_hitList]
        exact hnz
      · show (hitList H.face x (m + 1)).Nodup
        exact hitList_nodup_of_min _ _ _ (fun j hj1 hjn => by rw [hnz]; exact hnmin j hj1 hjn)
      · intro v hv
        obtain ⟨k, _, _, rfl⟩ := (mem_hitList H.face x v (m + 1)).1 hv
        exact ⟨x, List.mem_cons_self, sameCycle_pow_apply H.face x k⟩
      · intro v hv
        obtain ⟨k, hk1, hkn, hk⟩ := (mem_hitList H.face x (H.face v) (m + 1)).1 hv
        rcases Nat.lt_or_ge k 2 with h | h
        · left
          have hk' : k = 1 := by omega
          subst hk'
          rw [pow_one] at hk
          exact (H.face.injective hk).symm
        · right
          have hv' : (H.face ^ (k - 1)) x = v := by
            apply H.face.injective
            rw [← hk, ← Perm.mul_apply, ← pow_succ', Nat.sub_add_cancel (by omega)]
          refine ⟨(mem_hitList H.face x v (m + 1)).2 ⟨k - 1, by omega, by omega, hv'⟩, ?_⟩
          rw [← hv']
          exact hnmin (k - 1) (by omega) (by omega)
  | cons y p ih =>
      have hxy : H.edge x = y := (List.isChain_cons_cons.1 hchain).1
      have hsx := (List.pairwise_cons.1 hsimple)
      obtain ⟨qy, hcy, hly, hndy, hfy, hby⟩ :=
        ih y (List.isChain_cons_cons.1 hchain).2 hsx.2 hz
      obtain ⟨n, hn1, hnx, hnmin⟩ := exists_min_hit H.face (SameCycle.refl H.face x)
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hseg : H.face x :: hitList H.face (H.face x) m = hitList H.face x (m + 1) := rfl
      refine ⟨hitList H.face (H.face x) m ++ H.face y :: qy, ?_, ?_, ?_, ?_, ?_⟩
      · refine isChain_cons_append_cons
          ((isChain_hitList H.face (H.face x) m).imp fun _ _ h => Or.inr h) ?_ hcy
        refine Or.inl ?_
        show lastOf x (hitList H.face x (m + 1)) = H.node (H.face y)
        rw [lastOf_hitList, hnx, ← hxy]
        exact (H.cancel3 x).symm
      · rw [lastOf_append_cons]
        exact hly
      · rw [← List.cons_append, hseg]
        refine List.nodup_append.2 ⟨hitList_nodup_of_min _ _ _
          (fun j hj1 hjn => by rw [hnx]; exact hnmin j hj1 hjn), hndy, ?_⟩
        intro a ha b hb hab
        obtain ⟨k, _, _, rfl⟩ := (mem_hitList H.face x a (m + 1)).1 ha
        obtain ⟨c, hc, hcb⟩ := hfy b hb
        refine hsx.1 c hc ?_
        rw [← hab] at hcb
        exact SameCycle.trans (sameCycle_pow_apply H.face x k) hcb.symm
      · intro v hv
        rw [← List.cons_append, hseg] at hv
        rcases List.mem_append.1 hv with h | h
        · obtain ⟨k, _, _, rfl⟩ := (mem_hitList H.face x v (m + 1)).1 h
          exact ⟨x, List.mem_cons_self, sameCycle_pow_apply H.face x k⟩
        · obtain ⟨a, ha, hav⟩ := hfy v h
          exact ⟨a, List.mem_cons_of_mem _ ha, hav⟩
      · intro v hv
        rw [← List.cons_append, hseg] at hv ⊢
        rcases List.mem_append.1 hv with h | h
        · right
          obtain ⟨k, hk1, hkn, hk⟩ := (mem_hitList H.face x (H.face v) (m + 1)).1 h
          have hv' : v = (H.face ^ (k - 1)) x := by
            apply H.face.injective
            rw [← hk, ← Perm.mul_apply, ← pow_succ', Nat.sub_add_cancel (by omega)]
          have hvmem : v ∈ hitList H.face x (m + 1) := by
            rcases Nat.lt_or_ge k 2 with hk2 | hk2
            · have hk' : k = 1 := by omega
              subst hk'
              rw [hv', pow_zero, Perm.one_apply]
              exact (mem_hitList H.face x x (m + 1)).2 ⟨m + 1, by omega, le_rfl, hnx⟩
            · rw [hv']
              exact (mem_hitList H.face x _ (m + 1)).2 ⟨k - 1, by omega, by omega, rfl⟩
          refine ⟨List.mem_append_left _ hvmem, ?_⟩
          intro hvz
          have hxv : H.face.SameCycle x v := by rw [hv']; exact sameCycle_pow_apply H.face x (k - 1)
          rw [hvz] at hxv
          exact hsx.1 _ (lastOf_mem_cons y p) (hxv.trans hz.symm)
        · rcases hby v h with h1 | ⟨h2, h3⟩
          · exact Or.inl h1
          · exact Or.inr ⟨List.mem_append_right _ h2, h3⟩

end Contour

/-! ## The theorem -/

section EulerTree

variable {D : Type*} [Fintype D] [DecidableEq D] {H : Hypermap D}

/-- A duplicate-free C-path from `w` to `v` whose darts after `w` avoid `C`. -/
def AvoidPath (H : Hypermap D) (w v : D) (C : List D) : Prop :=
  ∃ q, List.IsChain (Clink H) (w :: q) ∧ lastOf w q = v ∧ (w :: q).Nodup ∧ ∀ t ∈ q, t ∉ C

/-- **Break the dikes.**  In a map with no Moebius path, every edge cycle
contains a dart that is C-linked to itself or is not cross-edge.  This is the
source's `Euler_tree`. -/
theorem euler_tree (hJ : Jordan H) (x₀ : D) :
    ∃ y, H.edge.SameCycle x₀ y ∧ (Clink H y y ∨ ¬ CrossEdge H y) := by
  classical
  by_contra hcon
  have hT : ∀ v, H.edge.SameCycle x₀ v → ¬ Clink H v v ∧ CrossEdge H v := by
    intro v hv
    refine ⟨fun hc => hcon ⟨v, hv, Or.inl hc⟩, ?_⟩
    by_contra hc
    exact hcon ⟨v, hv, Or.inr hc⟩
  -- the edge cycle is closed under `node`, hence under `node⁻¹`
  have hEnodePow : ∀ k : ℕ, ∀ v, H.edge.SameCycle x₀ v →
      H.edge.SameCycle x₀ ((H.node ^ k) v) := by
    intro k
    induction k with
    | zero => intro v hv; simpa using hv
    | succ k ih =>
        intro v hv
        rw [pow_succ', Perm.mul_apply]
        have hk := ih v hv
        exact hk.trans (hT _ hk).2
  have hEnodeInv : ∀ v, H.edge.SameCycle x₀ v → H.edge.SameCycle x₀ (H.node⁻¹ v) := by
    intro v hv
    have hinv : H.node⁻¹ = H.node ^ (orderOf H.node - 1) := by
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos _), pow_orderOf_eq_one]
    rw [hinv]
    exact hEnodePow _ v hv
  -- 1. the face-simple arc, by minimality of the face-repetition length
  have hex : ∃ d, 1 ≤ d ∧ ∃ w, H.edge.SameCycle x₀ w ∧ H.face.SameCycle w ((H.edge ^ d) w) :=
    ⟨orderOf H.edge, orderOf_pos _, x₀, SameCycle.refl _ _, by
      rw [pow_orderOf_eq_one]; exact SameCycle.refl _ _⟩
  obtain ⟨d, hd1, ⟨w, hwE, hwd⟩, hdmin⟩ : ∃ d, 1 ≤ d ∧
      (∃ w, H.edge.SameCycle x₀ w ∧ H.face.SameCycle w ((H.edge ^ d) w)) ∧
      ∀ d', 1 ≤ d' → d' < d → ∀ w', H.edge.SameCycle x₀ w' →
        ¬ H.face.SameCycle w' ((H.edge ^ d') w') :=
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      fun d' h1 hlt w' hw' hf => Nat.find_min hex hlt ⟨h1, w', hw', hf⟩⟩
  obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have harc : H.edge w :: hitList H.edge (H.edge w) d = hitList H.edge w (d + 1) := rfl
  have hchainArc : List.IsChain (fun u v => H.edge u = v)
      (H.edge w :: hitList H.edge (H.edge w) d) := isChain_hitList H.edge _ d
  have hz1 : lastOf (H.edge w) (hitList H.edge (H.edge w) d) = (H.edge ^ (d + 1)) w :=
    lastOf_hitList H.edge w (d + 1)
  have hsimple : (H.edge w :: hitList H.edge (H.edge w) d).Pairwise
      (fun a b => ¬ H.face.SameCycle a b) := by
    rw [harc]
    refine hitList_pairwise _ _ _ (fun i j hi hij hjd hf => ?_)
    have hiE : H.edge.SameCycle x₀ ((H.edge ^ i) w) := hwE.trans (sameCycle_pow_apply _ _ _)
    apply hdmin (j - i) (by omega) (by omega) _ hiE
    rw [← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hij.le]
    exact hf
  -- facts about `x = edge w` and `face x`
  have hnfx : H.node (H.face (H.edge w)) = w := H.cancel3 w
  have hxE : H.edge.SameCycle x₀ (H.edge w) := hwE.trans (sameCycle_step H.edge w)
  have hfxE : H.edge.SameCycle x₀ (H.face (H.edge w)) := by
    rw [← inv_apply_eq_of_apply_eq hnfx]
    exact hEnodeInv w hwE
  have hfxw : H.face (H.edge w) ≠ w := by
    intro h
    apply (hT w hwE).1
    refine Or.inl ?_
    conv_rhs => rw [← h]
    exact hnfx.symm
  have hfxx : H.face (H.edge w) ≠ H.edge w := fun h => (hT _ hxE).1 (Or.inr h)
  have hfx_arc : H.face (H.edge w) ∉ H.edge w :: hitList H.edge (H.edge w) d := by
    intro h
    rcases List.mem_cons.1 h with h | h
    · exact hfxx h
    · exact (List.pairwise_cons.1 hsimple).1 _ h (sameCycle_step H.face _)
  -- 2. the contour
  have hzw : H.face.SameCycle (lastOf (H.edge w) (hitList H.edge (H.edge w) d)) w := by
    rw [hz1]
    exact hwd.symm
  obtain ⟨q1, hC1, hC2, hC3, -, hC4⟩ := exists_contour _ _ w hchainArc hsimple hzw
  have hwC : w ∈ H.face (H.edge w) :: q1 := by
    have h := lastOf_mem_cons (H.face (H.edge w)) q1
    rwa [hC2] at h
  have hfxC : H.face (H.edge w) ∈ H.face (H.edge w) :: q1 := List.mem_cons_self
  -- 3a. an edge path from `face x` back to `w` avoiding the arc's end
  have hwfx : H.edge.SameCycle w (H.face (H.edge w)) := hwE.symm.trans hfxE
  obtain ⟨p2, hch2, hl2, hz1p2⟩ : ∃ p2, List.IsChain (fun u v => H.edge u = v)
      (H.face (H.edge w) :: p2) ∧ lastOf (H.face (H.edge w)) p2 = w ∧
      lastOf (H.edge w) (hitList H.edge (H.edge w) d) ∉ p2 := by
    by_cases hz1w : (H.edge ^ (d + 1)) w = w
    · exfalso
      obtain ⟨j, hj⟩ := exists_nat_pow_apply_eq hwfx
      rw [pow_apply_mod hz1w j] at hj
      have hjlt := Nat.mod_lt j (show 0 < d + 1 by omega)
      rcases Nat.eq_zero_or_pos (j % (d + 1)) with h0 | hpos
      · rw [h0, pow_zero, Perm.one_apply] at hj
        exact hfxw hj.symm
      · apply hfx_arc
        rw [harc]
        exact (mem_hitList _ _ _ _).2 ⟨j % (d + 1), hpos, hjlt.le, hj⟩
    · obtain ⟨n, hn1, hnw, hnmin⟩ :=
        exists_min_hit H.edge (sameCycle_pow_apply H.edge w (d + 1)).symm
      have hz1P : (H.edge ^ (d + 1)) w ∉ hitList H.edge ((H.edge ^ (d + 1)) w) n :=
        not_mem_hitList_self _ _ _ (fun j hj1 hjn => by rw [hnw]; exact hnmin j hj1 hjn)
          (by rw [hnw]; exact Ne.symm hz1w)
      have hper : (H.edge ^ (d + 1 + n)) w = w := by
        rw [add_comm, pow_add, Perm.mul_apply]
        exact hnw
      obtain ⟨j, hj⟩ := exists_nat_pow_apply_eq hwfx
      rw [pow_apply_mod hper j] at hj
      have hklt := Nat.mod_lt j (show 0 < d + 1 + n by omega)
      have hfxP : H.face (H.edge w) ∈ hitList H.edge ((H.edge ^ (d + 1)) w) n := by
        rcases Nat.eq_zero_or_pos (j % (d + 1 + n)) with h0 | hpos
        · exfalso
          rw [h0, pow_zero, Perm.one_apply] at hj
          exact hfxw hj.symm
        · rcases Nat.lt_or_ge (d + 1) (j % (d + 1 + n)) with hgt | hle
          · refine (mem_hitList _ _ _ _).2 ⟨j % (d + 1 + n) - (d + 1), by omega, by omega, ?_⟩
            rw [← hj, ← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hgt.le]
          · exfalso
            apply hfx_arc
            rw [harc]
            exact (mem_hitList _ _ _ _).2 ⟨j % (d + 1 + n), hpos, hle, hj⟩
      obtain ⟨s, p2, hsplit⟩ := List.append_of_mem hfxP
      have hchP := isChain_hitList H.edge ((H.edge ^ (d + 1)) w) n
      rw [hsplit] at hchP
      refine ⟨p2, (isChain_cons_append_cons_iff.1 hchP).2.2, ?_, ?_⟩
      · have hlast := lastOf_hitList H.edge ((H.edge ^ (d + 1)) w) n
        rw [hsplit, lastOf_append_cons] at hlast
        rw [hlast, hnw]
      · rw [hz1]
        intro h
        apply hz1P
        rw [hsplit]
        exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
  -- 3b. walking back: a node step onto the contour would close a Moebius path
  have step : ∀ v, H.node v ≠ w → AvoidPath H w (H.node v) (H.face (H.edge w) :: q1) →
      v ≠ w ∧ AvoidPath H w v (H.face (H.edge w) :: q1) := by
    rintro v hnvw ⟨q3, hch3, hl3, hnd3, hav3⟩
    have hvC : v ∉ H.face (H.edge w) :: q1 := by
      intro hv
      rcases List.mem_cons.1 hv with hv | hv
      · exact hnvw (by rw [hv]; exact hnfx)
      · refine hJ (H.face (H.edge w)) (q1 ++ q3) (moebiusPath_intro (L := H.node v) (t := v)
          (n := w) ?_ ?_ ?_ rfl hnfx ?_)
        · refine List.nodup_cons.2 ⟨?_, ?_⟩
          · simp only [List.mem_append, not_or]
            exact ⟨(List.nodup_cons.1 hC3).1, fun h => hav3 _ h hfxC⟩
          · exact List.nodup_append.2 ⟨(List.nodup_cons.1 hC3).2, (List.nodup_cons.1 hnd3).2,
              fun a ha b hb hab => hav3 b hb (by rw [← hab]; exact List.mem_cons_of_mem _ ha)⟩
        · exact isChain_cons_append hC1 (by rw [hC2]; exact hch3)
        · rw [lastOf_append, hC2]
          exact hl3
        · refine mem2_append_right ?_
          have hm := mem2_lastOf (a := H.face (H.edge w)) hv
          rwa [hC2] at hm
    have hvw : v ≠ w := fun h => hvC (by rw [h]; exact hwC)
    exact ⟨hvw, extend_path hch3 hl3 hnd3 hav3 (Or.inl rfl) hvC hvw⟩
  -- a face step onto the contour could only come from the arc's end
  have base : ∀ e, e ≠ lastOf (H.edge w) (hitList H.edge (H.edge w) d) →
      AvoidPath H w e (H.face (H.edge w) :: q1) →
      H.face e ≠ w ∧ AvoidPath H w (H.face e) (H.face (H.edge w) :: q1) := by
    rintro e hez1 ⟨q, hch, hl, hnd, hav⟩
    have hfeC : H.face e ∉ H.face (H.edge w) :: q1 := by
      intro h
      rcases hC4 e h with h1 | ⟨heC, hew⟩
      · exact hez1 h1
      · have hem : e ∈ w :: q := by rw [← hl]; exact lastOf_mem_cons w q
        rcases List.mem_cons.1 hem with h2 | h2
        · exact hew h2
        · exact hav e h2 heC
    have hfew : H.face e ≠ w := fun h => hfeC (by rw [h]; exact hwC)
    exact ⟨hfew, extend_path hch hl hnd hav (Or.inr rfl) hfeC hfew⟩
  -- going once around a node cycle
  have around : ∀ y, H.face (H.edge y) ≠ w →
      AvoidPath H w (H.face (H.edge y)) (H.face (H.edge w) :: q1) →
      AvoidPath H w y (H.face (H.edge w) :: q1) := by
    intro y hK1 hK2
    have hfy : H.face (H.edge y) = H.node⁻¹ y := (inv_apply_eq_of_apply_eq (H.cancel3 y)).symm
    rw [hfy] at hK1 hK2
    have hall : ∀ k : ℕ, (H.node⁻¹ ^ k) (H.node⁻¹ y) ≠ w ∧
        AvoidPath H w ((H.node⁻¹ ^ k) (H.node⁻¹ y)) (H.face (H.edge w) :: q1) := by
      intro k
      induction k with
      | zero => simpa using ⟨hK1, hK2⟩
      | succ k ih =>
          rw [pow_succ', Perm.mul_apply]
          refine step _ ?_ ?_
          · rw [apply_inv_apply]; exact ih.1
          · rw [apply_inv_apply]; exact ih.2
    have hy : (H.node⁻¹ ^ (orderOf H.node⁻¹ - 1)) (H.node⁻¹ y) = y := by
      rw [← pow_succ_apply', Nat.sub_add_cancel (orderOf_pos _), pow_orderOf_eq_one,
        Perm.one_apply]
    have hk := (hall (orderOf H.node⁻¹ - 1)).2
    rwa [hy] at hk
  have outer : ∀ (l : List D) (y : D), List.IsChain (fun u v => H.edge u = v) (y :: l) →
      lastOf y l = w → lastOf (H.edge w) (hitList H.edge (H.edge w) d) ∉ l →
      AvoidPath H w y (H.face (H.edge w) :: q1) := by
    intro l
    induction l with
    | nil =>
        intro y _ hl _
        have hyw : y = w := hl
        exact ⟨[], List.IsChain.singleton w, hyw.symm, List.nodup_singleton w, by simp⟩
    | cons e l ih =>
        intro y hch hl hz
        have hye : H.edge y = e := (List.isChain_cons_cons.1 hch).1
        have hQe := ih e (List.isChain_cons_cons.1 hch).2 hl
          (fun h => hz (List.mem_cons_of_mem _ h))
        have hez1 : e ≠ lastOf (H.edge w) (hitList H.edge (H.edge w) d) :=
          fun h => hz (by rw [← h]; exact List.mem_cons_self)
        obtain ⟨hK1, hK2⟩ := base e hez1 hQe
        rw [← hye] at hK1 hK2
        exact around y hK1 hK2
  -- 3c. but the walk must end on the contour's first dart
  obtain ⟨q, _, hl, _, hav⟩ := outer p2 _ hch2 hl2 hz1p2
  have hmem : H.face (H.edge w) ∈ w :: q := by
    rw [← hl]
    exact lastOf_mem_cons w q
  rcases List.mem_cons.1 hmem with h | h
  · exact hfxw h
  · exact hav _ h hfxC

end EulerTree

end Hypermap

end Mettapedia.GraphTheory
