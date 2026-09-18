import Mettapedia.GraphTheory.Hypermap.SmallExamples

/-!
# The Jordan property of a hypermap

The Jordan curve theorem, read combinatorially, says that a closed contour on a
sphere cannot cross itself in a way that leaves it with only one side.  On a
hypermap the contours are **C-paths** — walks that step either backwards along a
node orbit or forwards along a face orbit — and the forbidden configuration is a
**Moebius path**: a duplicate-free C-path `x :: p` carrying two node links that
cross each other.

Precisely, write `t` for the dart with `node t = last (x :: p)`.  The path is
Moebius when `t` and `node x` both occur in `p`, with `t` first.  Reading the
path as a contour, the link into its last dart and the link out of its first
dart then interleave: on a sphere one would separate the other, and only on a
Moebius strip or a higher-genus surface can they cross.

`Jordan H` says no such path exists.  It is the planarity condition this module
exists to state.  That it is equivalent to vanishing Euler defect is recorded at
the end as two propositions; the direction `Planar → Jordan` is proved in
`Hypermap.Jordan.OfPlanar` (`jordan_of_planar`).

## Faithfulness

The source states the predicate on a single list `q`, false when `q` is empty.
Splitting the head off, as `MoebiusPath H x p`, is the same predicate: the empty
case is excluded automatically, because `Mem2 [] _ _` is false.

`Mem2 l x y` is "y occurs at or after the *first* occurrence of x in l".  The
first-occurrence clause `x ∉ l₁` is not decoration: without it the predicate is
strictly weaker, and although every use below also assumes `l` duplicate-free —
which makes the two agree — the definition is kept faithful rather than
convenient.

## What the small maps establish

A planarity-style predicate is worth nothing unless something satisfies it and
something fails it.  Both are exhibited:

* `moebius_torusTriple` — the genus-one map on three darts carries the explicit
  Moebius path `0, 1, 2`, so `¬ Jordan torusTriple`;
* `jordan_pointMap` and `jordan_spherePair` — the one- and two-dart planar maps
  have none.

Together with `not_planar_torusTriple` and `planar_spherePair` these are three
independent confirmations that `Jordan` and `Planar` agree where they can
currently both be evaluated.
-/

namespace Mettapedia.GraphTheory

open Mettapedia.GraphTheory.FourColor

open Equiv Equiv.Perm
open GoertzelV24PermutationOrbitSurgery GoertzelV24WordReachability
open Mettapedia.GraphTheory.OrbitCountSplitting

namespace Hypermap

/-! ## Occurrence order in a list -/

section Mem2

variable {α : Type*}

/-- `y` occurs at or after the *first* occurrence of `x` in `l`.  This is the
source's `mem2`: the suffix of `l` beginning at the first `x` contains `y`. -/
def Mem2 (l : List α) (x y : α) : Prop :=
  ∃ l₁ l₂ : List α, l = l₁ ++ x :: l₂ ∧ x ∉ l₁ ∧ y ∈ x :: l₂

theorem Mem2.left_mem {l : List α} {x y : α} (h : Mem2 l x y) : x ∈ l := by
  obtain ⟨l₁, l₂, rfl, _, _⟩ := h
  exact List.mem_append_right _ List.mem_cons_self

theorem Mem2.right_mem {l : List α} {x y : α} (h : Mem2 l x y) : y ∈ l := by
  obtain ⟨l₁, l₂, rfl, _, hy⟩ := h
  exact List.mem_append_right _ hy

theorem Mem2.ne_nil {l : List α} {x y : α} (h : Mem2 l x y) : l ≠ [] := by
  intro hnil
  rw [hnil] at h
  exact absurd h.left_mem (by simp)

/-- The last entry of the path `x :: l`. -/
def lastOf : α → List α → α
  | x, [] => x
  | _, y :: l => lastOf y l

theorem lastOf_mem {l : List α} (hl : l ≠ []) (x : α) : lastOf x l ∈ l := by
  induction l generalizing x with
  | nil => exact absurd rfl hl
  | cons y l ih =>
      rcases l with _ | ⟨w, l⟩
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih (by simp) w)

end Mem2

variable {D : Type*} [Fintype D] [DecidableEq D]

/-! ## C-links and C-paths -/

/-- The **C-link**: a step backwards along a node orbit, or forwards along a
face orbit. -/
def Clink (H : Hypermap D) (x y : D) : Prop := x = H.node y ∨ H.face x = y

instance instDecidableClink (H : Hypermap D) : DecidableRel (Clink H) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

theorem clink_node (H : Hypermap D) (x : D) : Clink H (H.node x) x := Or.inl rfl

theorem clink_face (H : Hypermap D) (x : D) : Clink H x (H.face x) := Or.inr rfl

/-- A C-path `x :: p`: consecutive darts are C-linked.  This is the source's
`path clink x p`. -/
abbrev CPath (H : Hypermap D) (x : D) (p : List D) : Prop := List.IsChain (Clink H) (x :: p)

/-! ## Moebius paths and the Jordan property -/

/-- A **Moebius path**: a duplicate-free C-path whose two node links cross.

`H.node⁻¹ (lastOf x p)` is the dart whose node image ends the path; the path is
Moebius when that dart occurs in `p` before `H.node x` does. -/
def MoebiusPath (H : Hypermap D) (x : D) (p : List D) : Prop :=
  (x :: p).Nodup ∧ CPath H x p ∧ Mem2 p (H.node⁻¹ (lastOf x p)) (H.node x)

/-- **The Jordan planarity condition**: the map carries no Moebius path. -/
def Jordan (H : Hypermap D) : Prop := ∀ (x : D) (p : List D), ¬ MoebiusPath H x p

theorem not_jordan_iff_exists (H : Hypermap D) :
    ¬ Jordan H ↔ ∃ x p, MoebiusPath H x p :=
  ⟨fun h => by
    by_contra hc
    exact h fun x p hm => hc ⟨x, p, hm⟩,
   fun ⟨x, p, hm⟩ h => h x p hm⟩

/-! ## The predicate is satisfiable, and refutable

### Refutable: the genus-one map carries a Moebius path -/

/-- On the genus-one map, `0, 1, 2` is a Moebius path.  Its C-links are both
face steps, it ends at `2 = node 1`, and `1 = node 0` — so the two node links
coincide and trivially cross. -/
theorem moebius_torusTriple : MoebiusPath torusTriple 0 [1, 2] := by
  refine ⟨by decide, ?_, ?_⟩
  · exact List.isChain_cons_cons.2 ⟨Or.inr (by decide),
      List.isChain_cons_cons.2 ⟨Or.inr (by decide), List.IsChain.singleton _⟩⟩
  · have h1 : torusTriple.node⁻¹ (lastOf (0 : Fin 3) [1, 2]) = 1 := by decide
    have h2 : torusTriple.node (0 : Fin 3) = 1 := by decide
    rw [h1, h2]
    exact ⟨[], [2], rfl, by simp, by simp⟩

/-- **`Jordan` is not vacuously true.**  The genus-one map fails it — and by
`not_planar_torusTriple` it also fails `Planar`, as the equivalence demands. -/
theorem not_jordan_torusTriple : ¬ Jordan torusTriple :=
  fun h => h 0 [1, 2] moebius_torusTriple

/-! ### Satisfiable: two planar maps have no Moebius path -/

private theorem fin_two_eq_of_ne : ∀ u v x : Fin 2, u ≠ x → v ≠ x → u = v := by decide

private theorem spherePair_node_ne : ∀ b : Fin 2, spherePair.node b ≠ b := by decide

/-- The one-dart map: every permutation is the identity. -/
def pointMap : Hypermap (Fin 1) where
  edge := 1
  node := 1
  face := 1
  cancel3 := by decide

/-- **`Jordan` is not vacuously false.**  On one dart there is no room for a
duplicate-free path that revisits anything. -/
theorem jordan_pointMap : Jordan pointMap := by
  rintro x p ⟨hnodup, -, hmem2⟩
  have hxp : x ∉ p := (List.nodup_cons.mp hnodup).1
  have ha : pointMap.node⁻¹ (lastOf x p) ∈ p := hmem2.left_mem
  exact hxp (by rwa [Subsingleton.elim x (pointMap.node⁻¹ (lastOf x p))])

/-- **The planar two-dart map has no Moebius path.**  Any nonempty
duplicate-free tail of a path in a two-element carrier is constant, which forces
the crossing dart to be fixed by `node` — and `node` here is a transposition. -/
theorem jordan_spherePair : Jordan spherePair := by
  rintro x p ⟨hnodup, -, hmem2⟩
  set a := spherePair.node⁻¹ (lastOf x p) with hadef
  have hxp : x ∉ p := (List.nodup_cons.mp hnodup).1
  have ha : a ∈ p := hmem2.left_mem
  have hlast : lastOf x p ∈ p := lastOf_mem hmem2.ne_nil x
  -- in a two-element carrier every dart of `p` is the one that is not `x`
  have hfix : spherePair.node a = a := by
    have h1 : lastOf x p = a :=
      fin_two_eq_of_ne _ _ x (fun h => hxp (h ▸ hlast)) (fun h => hxp (h ▸ ha))
    have h2 : spherePair.node a = lastOf x p := by
      rw [hadef]
      exact apply_inv_apply _ _
    rw [h2, h1]
  exact spherePair_node_ne a hfix

/-! ## The equivalence this module is aiming at

`Planar` is an Euler count; `Jordan` is a statement about contours.  Their
equivalence is the combinatorial Jordan curve theorem.  The two halves are
recorded here as propositions about a fixed carrier so that they can be cited
and discharged without ever being assumed. -/

/-- One half of the combinatorial Jordan curve theorem, on a fixed carrier. -/
def PlanarImpliesJordanOn (D : Type*) [Fintype D] [DecidableEq D] : Prop :=
  ∀ H : Hypermap D, Planar H → Jordan H

/-- The other half, on a fixed carrier. -/
def JordanImpliesPlanarOn (D : Type*) [Fintype D] [DecidableEq D] : Prop :=
  ∀ H : Hypermap D, Jordan H → Planar H

/-- Both halves hold for a one-dart carrier, where everything is planar and
nothing is Moebius. -/
theorem jordan_iff_planar_fin_one : PlanarImpliesJordanOn (Fin 1) ∧ JordanImpliesPlanarOn (Fin 1) := by
  have hsub : ∀ H : Hypermap (Fin 1), Jordan H := by
    rintro H x p ⟨hnodup, -, hmem2⟩
    have hxp : x ∉ p := (List.nodup_cons.mp hnodup).1
    exact hxp (by
      rw [Subsingleton.elim x (H.node⁻¹ (lastOf x p))]
      exact hmem2.left_mem)
  refine ⟨fun H _ => hsub H, fun H _ => ?_⟩
  -- on one dart every permutation is the identity, so all four counts are one
  have hone : ∀ σ : Perm (Fin 1), σ = 1 := fun σ => Subsingleton.elim σ 1
  rw [planar_iff_eulerRhs_eq, eulerRhs_eq_card_add_two_mul_compCount,
    eulerLhs_eq_orbit_sum, hone H.edge, hone H.node, hone H.face]
  have hcomp : compCount H = 1 := by
    have h := wordOrbitCount_eq_card_of_completeInvariant (L := [H.edge, H.node, H.face])
      (fun _ : Fin 1 => ())
      (fun x y => ⟨fun _ => rfl, fun _ => by
        rw [Subsingleton.elim x y]
        exact WordReachable.refl _ _⟩) (fun _ => ⟨0, rfl⟩)
    show wordOrbitCount [H.edge, H.node, H.face] = 1
    rw [h]; simp
  rw [hcomp, PermSwapDecomposition.orbitCount_one]
  simp

end Hypermap

end Mettapedia.GraphTheory
