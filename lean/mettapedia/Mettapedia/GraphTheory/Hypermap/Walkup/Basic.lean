import Mettapedia.GraphTheory.Hypermap.Symmetry
import Mettapedia.GraphTheory.OrbitCountSplitting

/-!
# The Walkup transformation: deleting one dart from a hypermap

A hypermap can be shrunk by one dart.  Choose a dart `z`; every orbit through
`z` is repaired by *skipping over* it, and the three permutations are adjusted
so that the composite law still holds.  The resulting map has one dart fewer,
which is what makes it an induction engine: every property of hypermaps that
survives the transformation can be proved by induction on the dart count.

This module builds the construction and its elementary theory.  It is the
engine `Hypermap.Walkup.Genus` and the Jordan theory run on.

## Skipping a point in a permutation

For a permutation `f` and a dart `z`, `skipFun f z` sends `x` to `f x`, except
that when `f x = z` it sends `x` to `f z` instead — one extra step, to step over
`z`.  On the subtype `{x // x ≠ z}` this is a permutation, `skipPerm f z`, and
its inverse is the same construction applied to `f⁻¹`, which is what makes it
computable rather than an abstract `Equiv.ofBijective`.

Its cycles are exactly the cycles of `f` with `z` deleted:
`sameCycle_skipPerm_iff`.  Consequently the orbit count drops by one when `z`
was a fixed point and is unchanged otherwise — `orbitCount_skipPerm`.

## Repairing the composite law

Skipping `z` in *two* of the three permutations breaks `node ∘ face ∘ edge = id`.
The repair is forced: the new edge permutation must be the inverse of the new
`node ∘ face`.  That is how `walkupE` is defined here, which makes the composite
law true by construction; the mathematical content then lives in
`walkupE_edge_apply`, which computes the forced inverse explicitly as Walkup's
four-case formula.  This is the content of Coq's `skip_edgeK`, stated the other
way round.

`walkupN` and `walkupF` are the same construction performed after cycling the
roles of the three permutations, using the `permN`/`permF` symmetries that
`Hypermap.Symmetry` already proves genus-invariant.
-/

namespace Mettapedia.GraphTheory

open Mettapedia.GraphTheory.FourColor

open Equiv Equiv.Perm
open GoertzelV24PermutationOrbitSurgery GoertzelV24WordReachability
open Mettapedia.GraphTheory.OrbitCountSplitting

namespace Hypermap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-! ## Skipping a point in a single permutation -/

omit [Fintype D] [DecidableEq D] in
theorem inv_apply_apply (σ : Perm D) (x : D) : σ⁻¹ (σ x) = x := by
  rw [← Perm.mul_apply, inv_mul_cancel]
  rfl

/-- `f` with the point `z` spliced out of its cycle: one extra step is taken
whenever the next point would be `z`. -/
def skipFun (f : Perm D) (z : D) (x : D) : D := if f x = z then f z else f x

omit [Fintype D] in
theorem skipFun_of_ne {f : Perm D} {z x : D} (h : f x ≠ z) : skipFun f z x = f x :=
  if_neg h

omit [Fintype D] in
theorem skipFun_of_eq {f : Perm D} {z x : D} (h : f x = z) : skipFun f z x = f z :=
  if_pos h

omit [Fintype D] in
/-- Skipping never lands on the deleted point. -/
theorem skipFun_ne (f : Perm D) (z : D) {x : D} (hx : x ≠ z) : skipFun f z x ≠ z := by
  unfold skipFun
  split
  · next h => exact fun hz => hx (f.injective (h.trans hz.symm))
  · next h => exact h

omit [Fintype D] in
/-- The construction applied to `f⁻¹` undoes it. -/
theorem skipFun_inv_skipFun (f : Perm D) (z : D) {x : D} (hx : x ≠ z) :
    skipFun f⁻¹ z (skipFun f z x) = x := by
  unfold skipFun
  by_cases h : f x = z
  · rw [if_pos h, inv_apply_apply, if_pos rfl, ← h, inv_apply_apply]
  · rw [if_neg h, inv_apply_apply, if_neg hx]

/-- **The punctured permutation.**  `f` with `z` deleted from its cycle,
as a permutation of the remaining darts. -/
def skipPerm (f : Perm D) (z : D) : Perm {x : D // x ≠ z} where
  toFun u := ⟨skipFun f z u.1, skipFun_ne f z u.2⟩
  invFun u := ⟨skipFun f⁻¹ z u.1, skipFun_ne f⁻¹ z u.2⟩
  left_inv u := Subtype.ext (skipFun_inv_skipFun f z u.2)
  right_inv u := Subtype.ext (by
    have h := skipFun_inv_skipFun f⁻¹ z u.2
    rwa [inv_inv] at h)

omit [Fintype D] in
@[simp] theorem skipPerm_apply_val (f : Perm D) (z : D) (u : {x : D // x ≠ z}) :
    ((skipPerm f z u : {x : D // x ≠ z}) : D) = skipFun f z (u : D) := rfl

/-! ### Cycles of the punctured permutation

Puncturing deletes `z` from its cycle and leaves every other cycle alone, so
two surviving darts share a cycle downstairs exactly when they shared one
upstairs.  This is Coq's `fconnect_skip`. -/

omit [Fintype D] [DecidableEq D] in
/-- A single step stays inside the cycle. -/
theorem sameCycle_step (σ : Perm D) (x : D) : σ.SameCycle x (σ x) := ⟨1, by simp⟩

omit [Fintype D] in
/-- One skipped step stays inside the original cycle. -/
theorem sameCycle_skipFun (f : Perm D) (z x : D) : f.SameCycle x (skipFun f z x) := by
  unfold skipFun
  split
  · next h =>
      refine ⟨2, ?_⟩
      have h2 : (f ^ (2 : ℕ)) x = f (f x) := by
        rw [pow_succ, Perm.mul_apply, pow_one]
      rw [zpow_ofNat, h2, h]
  · exact ⟨1, by simp⟩

omit [Fintype D] in
theorem sameCycle_val_pow (f : Perm D) (z : D) (u : {x : D // x ≠ z}) (n : ℕ) :
    f.SameCycle (u : D) (((skipPerm f z ^ n) u : {x : D // x ≠ z}) : D) := by
  induction n with
  | zero => simpa using SameCycle.refl f (u : D)
  | succ n ih =>
      have hstep : (skipPerm f z ^ (n + 1)) u = skipPerm f z ((skipPerm f z ^ n) u) := by
        rw [pow_succ', Perm.mul_apply]
      rw [hstep, skipPerm_apply_val]
      exact ih.trans (sameCycle_skipFun f z _)

/-- Sharing a cycle downstairs implies sharing one upstairs. -/
theorem sameCycle_of_skipPerm {f : Perm D} {z : D} {u v : {x : D // x ≠ z}}
    (h : (skipPerm f z).SameCycle u v) : f.SameCycle (u : D) (v : D) := by
  obtain ⟨n, hn⟩ := exists_nat_pow_apply_eq h
  have hv := sameCycle_val_pow f z u n
  rwa [hn] at hv

omit [Fintype D] in
/-- The converse, by induction on the number of steps: a step that would land
on `z` is absorbed into the next one, which is why the induction is on a bound
rather than on the exponent itself. -/
theorem skipPerm_sameCycle_aux (f : Perm D) (z : D) :
    ∀ n : ℕ, ∀ m ≤ n, ∀ u v : {x : D // x ≠ z}, (f ^ m) (u : D) = (v : D) →
      (skipPerm f z).SameCycle u v := by
  intro n
  induction n with
  | zero =>
      intro m hm u v hmv
      have hm0 : m = 0 := Nat.le_zero.mp hm
      subst hm0
      simp only [pow_zero, Perm.one_apply] at hmv
      exact (Subtype.ext hmv : u = v) ▸ SameCycle.refl _ u
  | succ n ih =>
      intro m hm u v hmv
      match m with
      | 0 =>
          simp only [pow_zero, Perm.one_apply] at hmv
          exact (Subtype.ext hmv : u = v) ▸ SameCycle.refl _ u
      | (j + 1) =>
          have hj : j ≤ n := Nat.succ_le_succ_iff.mp hm
          have hsplit : (f ^ j) (f (u : D)) = (v : D) := by
            rw [← Perm.mul_apply, ← pow_succ]
            exact hmv
          by_cases hz : f (u : D) = z
          · -- the next dart is the deleted one: absorb two steps into one
            rw [hz] at hsplit
            match j with
            | 0 =>
                simp only [pow_zero, Perm.one_apply] at hsplit
                exact absurd hsplit.symm v.2
            | (k + 1) =>
                have hk : k ≤ n := le_trans (Nat.le_succ k) hj
                have hstep : (f ^ k) (f z) = (v : D) := by
                  rw [← Perm.mul_apply, ← pow_succ]
                  exact hsplit
                have hval : ((skipPerm f z u : {x : D // x ≠ z}) : D) = f z := by
                  rw [skipPerm_apply_val, skipFun_of_eq hz]
                have hrec := ih k hk (skipPerm f z u) v (by rw [hval]; exact hstep)
                exact SameCycle.trans (sameCycle_step (skipPerm f z) u) hrec
          · have hval : ((skipPerm f z u : {x : D // x ≠ z}) : D) = f (u : D) := by
              rw [skipPerm_apply_val, skipFun_of_ne hz]
            have hrec := ih j hj (skipPerm f z u) v (by rw [hval]; exact hsplit)
            exact SameCycle.trans (sameCycle_step (skipPerm f z) u) hrec

theorem skipPerm_sameCycle_of_sameCycle {f : Perm D} {z : D} {u v : {x : D // x ≠ z}}
    (h : f.SameCycle (u : D) (v : D)) : (skipPerm f z).SameCycle u v := by
  obtain ⟨n, hn⟩ := exists_nat_pow_apply_eq h
  exact skipPerm_sameCycle_aux f z n n le_rfl u v hn

/-- **The cycles of the punctured permutation are the cycles of the original,
with `z` deleted.**  Coq's `fconnect_skip`. -/
theorem sameCycle_skipPerm_iff (f : Perm D) (z : D) (u v : {x : D // x ≠ z}) :
    (skipPerm f z).SameCycle u v ↔ f.SameCycle (u : D) (v : D) :=
  ⟨sameCycle_of_skipPerm, skipPerm_sameCycle_of_sameCycle⟩

/-! ### The orbit count of the punctured permutation

Deleting a point deletes one whole cycle when the point was a fixed point, and
shortens a cycle otherwise.  Coq's `fcard_skip`. -/

omit [Fintype D] [DecidableEq D] in
theorem pow_apply_fixed {f : Perm D} {z : D} (h : f z = z) (n : ℕ) : (f ^ n) z = z := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Perm.mul_apply, h, ih]

/-- **Puncturing loses exactly the fixed point.**  The orbit count drops by one
if `z` was a fixed point of `f`, and is unchanged otherwise. -/
theorem orbitCount_skipPerm (f : Perm D) (z : D) :
    (if f z = z then 1 else 0) + orbitCount (skipPerm f z) = orbitCount f := by
  classical
  set S : Set D := {x | f.SameCycle z x} with hSdef
  have hmemS : ∀ x : D, x ∈ S ↔ f.SameCycle z x := fun _ => Iff.rfl
  have hstepS : ∀ x : D, f x ∈ S ↔ x ∈ S := by
    intro x
    simp only [hmemS]
    exact ⟨fun h => h.trans (sameCycle_step f x).symm, fun h => h.trans (sameCycle_step f x)⟩
  have hSinv : ∀ x ∈ S, f x ∈ S := fun x hx => (hstepS x).2 hx
  have hScompl : ∀ x ∈ Sᶜ, f x ∈ Sᶜ := fun x hx hfx => hx ((hstepS x).1 hfx)
  have hzS : z ∈ S := SameCycle.refl f z
  -- upstairs the cycle of `z` is a single orbit
  have hup : orbitCountOn f S = 1 := by
    have hsec := classCountOn_eq_card_of_section (s := SameCycle.setoid f) (S := S)
      (A := Unit) (fun _ => z)
      (saturated_sameCycle_of_invariant hSinv)
      (fun _ => hzS)
      (fun x hx => ⟨(), (hx : f.SameCycle z x).symm⟩)
      (fun a b => ⟨fun _ => Subsingleton.elim a b, fun _ => SameCycle.refl f z⟩)
    rw [orbitCountOn, hsec]
    simp
  -- off the cycle of `z` the punctured map is the original map
  have hcompl : orbitCountOn f Sᶜ = orbitCountOn (skipPerm f z) (Subtype.val ⁻¹' Sᶜ) := by
    refine orbitCountOn_eq_orbitCountOn_of_equivariantOn hScompl
      Subtype.val_injective.injOn ?_ ?_
    · intro u hu
      have hne : f (u : D) ≠ z := by
        intro hfu
        have hc : f.SameCycle (u : D) z := ⟨1, by simpa using hfu⟩
        exact hu hc.symm
      rw [skipPerm_apply_val, skipFun_of_ne hne]
    · intro x hx
      have hxz : x ≠ z := fun h => hx (h ▸ hzS)
      exact ⟨⟨x, hxz⟩, SameCycle.refl f x⟩
  -- downstairs the surviving part of the cycle of `z`
  have hTinv : ∀ u ∈ (Subtype.val ⁻¹' S : Set {x : D // x ≠ z}),
      skipPerm f z u ∈ (Subtype.val ⁻¹' S : Set {x : D // x ≠ z}) := by
    intro u hu
    show ((skipPerm f z u : {x : D // x ≠ z}) : D) ∈ S
    exact (hu : f.SameCycle z (u : D)).trans (sameCycle_skipFun f z (u : D))
  have hdown : orbitCountOn (skipPerm f z) (Subtype.val ⁻¹' S) = if f z = z then 0 else 1 := by
    by_cases hfz : f z = z
    · rw [if_pos hfz]
      have hempty : (Subtype.val ⁻¹' S : Set {x : D // x ≠ z}) = ∅ := by
        ext u
        simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
        intro hu
        obtain ⟨n, hn⟩ := exists_nat_pow_apply_eq (hu : f.SameCycle z (u : D))
        exact u.2 (by rw [← hn, pow_apply_fixed hfz n])
      rw [orbitCountOn, hempty, classCountOn, classesOn, Set.image_empty, Set.ncard_empty]
    · rw [if_neg hfz]
      have hfzS : f z ∈ S := sameCycle_step f z
      have hsec := classCountOn_eq_card_of_section (s := SameCycle.setoid (skipPerm f z))
        (S := (Subtype.val ⁻¹' S : Set {x : D // x ≠ z})) (A := Unit)
        (fun _ => (⟨f z, hfz⟩ : {x : D // x ≠ z}))
        (saturated_sameCycle_of_invariant hTinv)
        (fun _ => hfzS)
        (fun u hu => ⟨(), (sameCycle_skipPerm_iff f z u ⟨f z, hfz⟩).2
          ((hu : f.SameCycle z (u : D)).symm.trans hfzS)⟩)
        (fun a b => ⟨fun _ => Subsingleton.elim a b, fun _ => SameCycle.refl _ _⟩)
      rw [orbitCountOn, hsec]
      simp
  have hsplitup := orbitCount_eq_orbitCountOn_add_compl f hSinv
  have hsplitdown := orbitCount_eq_orbitCountOn_add_compl (skipPerm f z) hTinv
  rw [hup, hcompl] at hsplitup
  rw [hdown, ← Set.preimage_compl] at hsplitdown
  split_ifs at hsplitdown ⊢ with hfz
  · omega
  · omega

/-! ## The Walkup transformation

Puncturing `node` and `face` breaks the composite law; the repair is forced,
since the new edge permutation can only be the inverse of the new
`node ∘ face`.  Walkup's explicit four-case formula for that inverse is
`walkupE_edge_apply`. -/

/-- **Walkup's formula** for the edge permutation of the punctured map. -/
def skipEdgeFun (H : Hypermap D) (z : D) (x : D) : D :=
  if H.edge z = z then H.edge x
  else if H.face (H.edge x) = z then H.edge z
  else if H.edge x = z then H.edge (H.node z)
  else H.edge x

/-! ### The three readings of the composite law, and what they characterise -/

theorem face_eq_iff (H : Hypermap D) (z y : D) :
    H.face y = z ↔ y = H.edge (H.node z) := by
  constructor
  · intro h
    have := edge_node_face H y
    rw [h] at this
    exact this.symm
  · rintro rfl
    exact face_edge_node H z

theorem node_face_eq_iff (H : Hypermap D) (z y : D) :
    H.node (H.face y) = z ↔ y = H.edge z := by
  constructor
  · intro h
    have := edge_node_face H y
    rw [h] at this
    exact this.symm
  · rintro rfl
    exact H.cancel3 z

/-- The composite of the two punctured permutations, in closed form. -/
theorem skipFun_node_skipFun_face (H : Hypermap D) (z y : D) :
    skipFun H.node z (skipFun H.face z y)
      = if y = H.edge (H.node z) then
          (if H.edge z = z then H.node z else H.node (H.face z))
        else if y = H.edge z then H.node z
        else H.node (H.face y) := by
  unfold skipFun
  by_cases h1 : H.face y = z
  · rw [if_pos h1, if_pos ((face_eq_iff H z y).1 h1)]
    by_cases h2 : H.node (H.face z) = z
    · rw [if_pos h2, if_pos]
      exact ((node_face_eq_iff H z z).1 h2).symm
    · rw [if_neg h2, if_neg]
      exact fun hc => h2 ((node_face_eq_iff H z z).2 hc.symm)
  · rw [if_neg h1, if_neg (fun hc => h1 ((face_eq_iff H z y).2 hc))]
    by_cases h3 : H.node (H.face y) = z
    · rw [if_pos h3, if_pos ((node_face_eq_iff H z y).1 h3)]
    · rw [if_neg h3, if_neg (fun hc => h3 ((node_face_eq_iff H z y).2 hc))]

theorem skipEdgeFun_ne (H : Hypermap D) (z : D) {x : D} (hx : x ≠ z) :
    skipEdgeFun H z x ≠ z := by
  unfold skipEdgeFun
  by_cases h1 : H.edge z = z
  · rw [if_pos h1]
    exact fun hc => hx (H.edge.injective (hc.trans h1.symm))
  · rw [if_neg h1]
    by_cases h2 : H.face (H.edge x) = z
    · rw [if_pos h2]; exact h1
    · rw [if_neg h2]
      by_cases h3 : H.edge x = z
      · rw [if_pos h3]
        intro hc
        -- `edge (node z) = z` would force `face z = z`, contradicting `h2`
        have hfz : H.face z = z := by
          have := face_edge_node H z
          rw [hc] at this
          exact this
        exact h2 (by rw [h3, hfz])
      · rw [if_neg h3]; exact h3

/-- **The punctured data still satisfies the composite law.**  This is Coq's
`skip_edgeK`: the punctured `node ∘ face` undoes Walkup's edge formula. -/
theorem skipEdgeK (H : Hypermap D) (z : D) {x : D} (hx : x ≠ z) :
    skipFun H.node z (skipFun H.face z (skipEdgeFun H z x)) = x := by
  rw [skipFun_node_skipFun_face]
  unfold skipEdgeFun
  by_cases h1 : H.edge z = z
  · rw [if_pos h1]
    by_cases ha : H.edge x = H.edge (H.node z)
    · rw [if_pos ha, if_pos h1]
      exact (H.edge.injective ha).symm
    · rw [if_neg ha]
      have hb : H.edge x ≠ H.edge z := fun hc => hx (H.edge.injective hc)
      rw [if_neg hb]
      exact H.cancel3 x
  · rw [if_neg h1]
    by_cases h2 : H.face (H.edge x) = z
    · -- `x = node z`
      have hxn : x = H.node z := H.edge.injective ((face_eq_iff H z (H.edge x)).1 h2)
      rw [if_pos h2]
      by_cases ha : H.edge z = H.edge (H.node z)
      · exact absurd (hxn.trans (H.edge.injective ha).symm) hx
      · rw [if_neg ha, if_pos rfl]
        exact hxn.symm
    · rw [if_neg h2]
      by_cases h3 : H.edge x = z
      · -- `x = node (face z)`
        have hxnf : x = H.node (H.face z) := by
          have := H.cancel3 x
          rw [h3] at this
          exact this.symm
        rw [if_pos h3, if_pos rfl, if_neg h1]
        exact hxnf.symm
      · rw [if_neg h3]
        have ha : H.edge x ≠ H.edge (H.node z) := by
          intro hc
          exact h2 (by rw [hc]; exact face_edge_node H z)
        have hb : H.edge x ≠ H.edge z := fun hc => hx (H.edge.injective hc)
        rw [if_neg ha, if_neg hb]
        exact H.cancel3 x

/-- **The Walkup map**: the hypermap on the darts other than `z`. -/
def walkupE (H : Hypermap D) (z : D) : Hypermap {x : D // x ≠ z} where
  edge := (skipPerm H.node z * skipPerm H.face z)⁻¹
  node := skipPerm H.node z
  face := skipPerm H.face z
  cancel3 := by
    intro u
    show (skipPerm H.node z) ((skipPerm H.face z)
      ((skipPerm H.node z * skipPerm H.face z)⁻¹ u)) = u
    rw [← Perm.mul_apply]
    exact apply_inv_apply _ u

@[simp] theorem walkupE_node (H : Hypermap D) (z : D) :
    (walkupE H z).node = skipPerm H.node z := rfl

@[simp] theorem walkupE_face (H : Hypermap D) (z : D) :
    (walkupE H z).face = skipPerm H.face z := rfl

/-- **Walkup's edge formula.**  The forced inverse is computed explicitly; this
is where `skipEdgeK` earns its keep. -/
theorem walkupE_edge_apply (H : Hypermap D) (z : D) (u : {x : D // x ≠ z}) :
    (((walkupE H z).edge u : {x : D // x ≠ z}) : D) = skipEdgeFun H z (u : D) := by
  have hne := skipEdgeFun_ne H z u.2
  have key : (skipPerm H.node z * skipPerm H.face z)
      (⟨skipEdgeFun H z (u : D), hne⟩ : {x : D // x ≠ z}) = u := by
    apply Subtype.ext
    rw [Perm.mul_apply, skipPerm_apply_val, skipPerm_apply_val]
    exact skipEdgeK H z u.2
  have hedge : ((walkupE H z).edge u) = (⟨skipEdgeFun H z (u : D), hne⟩ : {x : D // x ≠ z}) := by
    refine (skipPerm H.node z * skipPerm H.face z).injective ?_
    rw [key]
    show (skipPerm H.node z * skipPerm H.face z)
      ((skipPerm H.node z * skipPerm H.face z)⁻¹ u) = u
    exact apply_inv_apply _ u
  rw [hedge]

/-! ## The carrier shrinks by exactly one -/

theorem card_subtype_ne_succ (z : D) : Fintype.card {x : D // x ≠ z} + 1 = Fintype.card D := by
  classical
  have h1 : Fintype.card {x : D // x ≠ z} = (Finset.univ.filter (fun x => x ≠ z)).card :=
    Fintype.card_subtype _
  have h2 : (Finset.univ.filter (fun x : D => x ≠ z)) = Finset.univ.erase z :=
    Finset.filter_ne' _ _
  have h3 : (Finset.univ.erase z).card = Finset.univ.card - 1 :=
    Finset.card_erase_of_mem (Finset.mem_univ z)
  have h4 : 0 < Fintype.card D := Fintype.card_pos_iff.mpr ⟨z⟩
  rw [h1, h2, h3, Finset.card_univ]
  omega

/-- **The Walkup carrier is one smaller.**  Coq's `card_S_Walkup`; this is what
makes Walkup induction well-founded. -/
theorem card_walkupE_succ (_H : Hypermap D) (z : D) :
    Fintype.card {x : D // x ≠ z} + 1 = Fintype.card D :=
  card_subtype_ne_succ z

/-! ## The two other Walkup transforms

`walkupN` and `walkupF` delete `z` from the same dart set, but repair a
different one of the three permutations.  They are `walkupE` conjugated by the
role-cycling symmetries of `Hypermap.Symmetry`. -/

/-- Delete `z`, repairing `node`. -/
noncomputable def walkupN (H : Hypermap D) (z : D) : Hypermap {x : D // x ≠ z} :=
  permF (walkupE (permN H) z)

/-- Delete `z`, repairing `face`. -/
noncomputable def walkupF (H : Hypermap D) (z : D) : Hypermap {x : D // x ≠ z} :=
  permN (walkupE (permF H) z)

@[simp] theorem walkupN_edge (H : Hypermap D) (z : D) :
    (walkupN H z).edge = skipPerm H.edge z := rfl

@[simp] theorem walkupN_face (H : Hypermap D) (z : D) :
    (walkupN H z).face = skipPerm H.face z := rfl

@[simp] theorem walkupF_edge (H : Hypermap D) (z : D) :
    (walkupF H z).edge = skipPerm H.edge z := rfl

@[simp] theorem walkupF_node (H : Hypermap D) (z : D) :
    (walkupF H z).node = skipPerm H.node z := rfl

end Hypermap

end Mettapedia.GraphTheory
