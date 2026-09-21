import Mettapedia.GraphTheory.FourColor.EdgeShoreFaceFork
import Mettapedia.GraphTheory.FourColor.GoertzelV24ForkFold

/-!
# The physical face law folded up a whole edge-leaf tree

`EdgeShoreFaceFork` proves a two-child law: one edge shore splits into two,
and the parent face data is recovered from the children by a correction
supported on the shared vertices.  This file runs that law up an arbitrary
`EdgeLeafTree` and proves the fold exact at *every* node, not only at a
single fork.

The object at a node with edge shore `S` is the shore's own carrier
`{d // InShore edgeOf S d}`, its first-return rotation `shoreRot`, the
restricted edge involution `shoreEdge`, and their product `shoreFace`.  This
is not a new notion of a child: `shoreFace_eq_raw_return` identifies it with
the literal raw edge-shore presentation `nextHitPerm (rho * ofSubtype …) …`
already used in this directory, and `nodeRet_eq_raw` does the same for the
interface return.  Everything below rests on those two identifications.

The state carried at a node has two coordinates: `ret`, the face-return
permutation on the node's interface darts, and the node's face count, carried
in the form `closed` — the number of node faces that never meet the
interface.  The total is `ret`'s cycle count plus `closed`
(`nodeState_faces`), so the face count is folded exactly; carrying `closed`
rather than the total is what keeps the fork rule additive, exactly as
`EdgeShoreFaceFork.parent_face_count` is stated with terms on both sides
rather than with `-` on `ℕ`.

A leaf state is read off its single edge.  Every fork is
`forkStep`, which sees only the two child states plus the gluing data at that
node: it merges the two interface returns (`mergeRet`), applies the boundary
correction (`forkRewire`, the fork law's own `boundaryRewireOn`), and forgets
the marks that just became internal.  The induction closes because
`PermutationFirstReturnRestriction.nextHit_nested` makes the first return of a
first return the direct first return, so a child of a node really is the child
shore's own object (`leftFace_eq_child`, `rightFace_eq_child`).

No planarity, cubicity, or bound on the interface is used: `rho` is an
arbitrary permutation of the darts and `alpha` an arbitrary one respecting
`edgeOf`.

Both fields are load-bearing, and the refutations already exist:

* dropping `ret` and keeping a scalar summary of a child cannot determine the
  parent, by `GoertzelV24ForkFaceOrderObstruction.no_exact_coarse_defect_fork`
  and `no_exact_scalar_face_fork`, while
  `EdgeShoreFaceForkChecks.boundary_correction_distinguishes` shows the
  return field does separate that same pair;
* `closed` cannot be read off `ret`, because a node's face permutation may
  have whole cycles missing the interface.  The root of any covering tree is
  such a node: its interface is empty, its `ret` is the identity on the empty
  carrier, and every face is counted by `closed` alone.

## Scope

Fold exactness is not a finite-base audit.  It changes none of the later
obligations — finite-state closure, coverage, adequacy, rejecting-root
emptiness — and it does not produce cuts: the tree and its shores are given.
What it supplies is the exact structural transition those obligations would
have to be stated over.
-/

namespace Mettapedia.GraphTheory.FourColor.EdgeShoreFaceForkFold

open Equiv Equiv.Perm
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24RetainedSpliceFaceCount
open GoertzelV24FaceOrbitPartitionBridge
open GoertzelV24ConnectedBranchDecompositionForest
open PermutationFirstReturnRestriction
open EdgeShoreFaceFork

noncomputable section

/-! ## Two bookkeeping lemmas -/

section Transport

variable {A B C : Type*}

theorem permCongr_symm_permCongr (e : A ≃ B) (p : Perm A) :
    e.symm.permCongr (e.permCongr p) = p := by
  apply Equiv.ext
  intro x
  simp

theorem permCongr_permCongr (e : A ≃ B) (f : B ≃ C) (p : Perm A) :
    f.permCongr (e.permCongr p) = (e.trans f).permCongr p := by
  apply Equiv.ext
  intro x
  simp

end Transport

section Generic

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Every cycle either meets the marked set — and those cycles are counted by
the first-return permutation — or misses it entirely. -/
theorem partition_split (p : Perm A) (hit : A → Prop) :
    p.partition.parts.card =
      (nextHitPerm p hit).partition.parts.card +
        Fintype.card (NonHitOrbit p hit) := by
  rw [← card_permOrbit_eq_card_partition_parts p,
    card_permOrbit_eq_hit_add_nonHit p hit,
    card_hitOrbit_eq_nextHit_partition_card]

/-- First return does not depend on the syntactic form of the marked set. -/
theorem nextHit_val_congr_pred (p : Perm A) (u v : A → Prop)
    (huv : ∀ a, u a ↔ v a) (x : {a // u a}) :
    (nextHitPerm p v ⟨x.val, (huv x.val).mp x.property⟩).val =
      (nextHitPerm p u x).val :=
  FaceReturnSum.nextHit_map p p id (fun _ => rfl) u v (fun a => (huv a).symm) x

end Generic

/-! ## The object attached to an edge shore -/

variable {D E : Type*} [Fintype D] [DecidableEq D] [DecidableEq E]
variable (rho alpha : Perm D) (edgeOf : D → E)

/-- Darts whose edge belongs to the shore. -/
def InShore (S : Finset E) (d : D) : Prop := edgeOf d ∈ S

instance instDecidableInShore (S : Finset E) :
    DecidablePred (InShore edgeOf S) :=
  fun d => inferInstanceAs (Decidable (edgeOf d ∈ S))

/-- Interface darts of a shore: the dart is retained, but the rotation step
taken after crossing its edge leaves the shore.  These are exactly the darts
at which the shore's own face permutation skips over foreign territory. -/
def Iface (S : Finset E) (d : D) : Prop :=
  InShore edgeOf S d ∧ ¬ InShore edgeOf S (rho (alpha d))

instance instDecidableIface (S : Finset E) :
    DecidablePred (Iface rho alpha edgeOf S) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

omit [Fintype D] [DecidableEq D] [DecidableEq E] in
theorem iface_inShore {S : Finset E} {d : D} (h : Iface rho alpha edgeOf S d) :
    InShore edgeOf S d := h.1

variable (halpha : ∀ d, edgeOf (alpha d) = edgeOf d)

omit [Fintype D] [DecidableEq D] [DecidableEq E] in
include halpha in
theorem inShore_alpha (S : Finset E) (d : D) :
    InShore edgeOf S (alpha d) ↔ InShore edgeOf S d := by
  unfold InShore
  rw [halpha d]

/-- The edge involution restricted to the shore. -/
def shoreEdge (S : Finset E) : Perm {d // InShore edgeOf S d} :=
  alpha.subtypePerm (inShore_alpha alpha edgeOf halpha S)

/-- The ambient vertex rotation restricted to the shore by first return. -/
def shoreRot (S : Finset E) : Perm {d // InShore edgeOf S d} :=
  nextHitPerm rho (InShore edgeOf S)

/-- The shore's own face permutation. -/
def shoreFace (S : Finset E) : Perm {d // InShore edgeOf S d} :=
  shoreRot rho edgeOf S * shoreEdge alpha edgeOf halpha S

omit [DecidableEq E] in
theorem shoreFace_eq_leftFace (S : Finset E) :
    shoreFace rho alpha edgeOf halpha S =
      leftFace rho alpha (InShore edgeOf S)
        (inShore_alpha alpha edgeOf halpha S) := rfl

/-- The node object is the literal raw edge-shore presentation already used
in this directory: keep the ambient rotation, fix the darts of omitted edges,
and read first returns to the retained darts. -/
theorem shoreFace_eq_raw_return (S : Finset E) :
    shoreFace rho alpha edgeOf halpha S =
      nextHitPerm (rho * ofSubtype (shoreEdge alpha edgeOf halpha S))
        (InShore edgeOf S) :=
  leftFace_eq_raw_return rho alpha (InShore edgeOf S)
    (inShore_alpha alpha edgeOf halpha S)

/-! ## The folded state -/

/-- The bounded data carried up the tree: the cyclic order in which the
node's faces return to its interface, and the number of node faces which
never reach that interface at all. -/
structure ShoreFaceState (S : Finset E) where
  ret : Perm {d // Iface rho alpha edgeOf S d}
  closed : ℕ

/-- The node's total face count, reconstructed from the two fields. -/
def ShoreFaceState.faces {S : Finset E}
    (st : ShoreFaceState rho alpha edgeOf S) : ℕ :=
  st.ret.partition.parts.card + st.closed

/-- The literal interface return of the node's own face permutation. -/
def nodeRet (S : Finset E) : Perm {d // Iface rho alpha edgeOf S d} :=
  (nestedMarks (Iface rho alpha edgeOf S) (InShore edgeOf S)
      (fun _ h => iface_inShore rho alpha edgeOf h)).symm.permCongr
    (nextHitPerm (shoreFace rho alpha edgeOf halpha S)
      (fun d => Iface rho alpha edgeOf S d.val))

/-- The literal number of node faces which miss the interface. -/
def nodeClosed (S : Finset E) : ℕ :=
  Fintype.card (NonHitOrbit (shoreFace rho alpha edgeOf halpha S)
    (fun d => Iface rho alpha edgeOf S d.val))

/-- The literal state of a node, read off the physical edge shore. -/
def nodeState (S : Finset E) : ShoreFaceState rho alpha edgeOf S where
  ret := nodeRet rho alpha edgeOf halpha S
  closed := nodeClosed rho alpha edgeOf halpha S

omit [DecidableEq E] in
/-- The reconstructed face count of the literal state is the literal face
count of the node's own face permutation. -/
theorem nodeState_faces (S : Finset E) :
    (nodeState rho alpha edgeOf halpha S).faces =
      (shoreFace rho alpha edgeOf halpha S).partition.parts.card := by
  rw [ShoreFaceState.faces, nodeState, nodeRet, nodeClosed,
    card_permCongr_partition_parts, ← partition_split]

omit [DecidableEq E] in
/-- The same reconstruction, written on the two fields directly. -/
theorem node_faces (S : Finset E) :
    (nodeRet rho alpha edgeOf halpha S).partition.parts.card +
        nodeClosed rho alpha edgeOf halpha S =
      (shoreFace rho alpha edgeOf halpha S).partition.parts.card :=
  nodeState_faces rho alpha edgeOf halpha S

omit [Fintype D] [DecidableEq D] [DecidableEq E] in
theorem state_ext {S : Finset E} :
    ∀ a b : ShoreFaceState rho alpha edgeOf S, a.ret = b.ret → a.closed = b.closed →
      a = b
  | ⟨_, _⟩, ⟨_, _⟩, hr, hc => by
      have hr' := hr
      have hc' := hc
      subst hr'
      subst hc'
      rfl

/-- The interface return is the first return of the raw edge-shore face
permutation to the interface darts. -/
theorem nodeRet_eq_raw (S : Finset E) :
    nodeRet rho alpha edgeOf halpha S =
      nextHitPerm (rho * ofSubtype (shoreEdge alpha edgeOf halpha S))
        (Iface rho alpha edgeOf S) := by
  rw [nodeRet, shoreFace_eq_raw_return,
    nextHit_nested (rho * ofSubtype (shoreEdge alpha edgeOf halpha S))
      (Iface rho alpha edgeOf S) (InShore edgeOf S)
      (fun _ h => iface_inShore rho alpha edgeOf h),
    permCongr_symm_permCongr]

/-! ## One fork -/

section Fork

variable (S T : Finset E)

omit [Fintype D] [DecidableEq D] in
theorem inShore_left {d : D} (h : InShore edgeOf S d) :
    InShore edgeOf (S ∪ T) d := Finset.mem_union_left _ h

omit [Fintype D] [DecidableEq D] in
theorem inShore_right {d : D} (h : InShore edgeOf T d) :
    InShore edgeOf (S ∪ T) d := Finset.mem_union_right _ h

omit [Fintype D] [DecidableEq D] in
theorem inShore_right_of_parent {d : D} (hP : InShore edgeOf (S ∪ T) d)
    (hS : ¬ InShore edgeOf S d) : InShore edgeOf T d :=
  (Finset.mem_union.mp hP).resolve_left hS

omit [Fintype D] [DecidableEq D] [DecidableEq E] in
theorem not_inShore_right (hdisj : Disjoint S T) {d : D}
    (h : InShore edgeOf S d) : ¬ InShore edgeOf T d :=
  Finset.disjoint_left.mp hdisj h

/-- The union of the two child interfaces.  It contains both the fork's own
crossing marks and the parent's outgoing interface, so a fork needs no more
boundary information than the two children already carry. -/
def IfaceUnion (d : D) : Prop :=
  Iface rho alpha edgeOf S d ∨ Iface rho alpha edgeOf T d

instance instDecidableIfaceUnion :
    DecidablePred (IfaceUnion rho alpha edgeOf S T) :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- The fork's side predicate, read inside the parent carrier. -/
def forkSide : {d // InShore edgeOf (S ∪ T) d} → Prop :=
  fun d => InShore edgeOf S d.val

instance instDecidableForkSide : DecidablePred (forkSide edgeOf S T) :=
  fun d => inferInstanceAs (Decidable (InShore edgeOf S d.val))

/-- The marked set carried across the fork, inside the parent carrier. -/
def forkHit : {d // InShore edgeOf (S ∪ T) d} → Prop :=
  fun d => IfaceUnion rho alpha edgeOf S T d.val

instance instDecidableForkHit : DecidablePred (forkHit rho alpha edgeOf S T) :=
  fun d => inferInstanceAs (Decidable (IfaceUnion rho alpha edgeOf S T d.val))

/-- The parent's own outgoing interface, inside the parent carrier. -/
def forkKeep : {d // InShore edgeOf (S ∪ T) d} → Prop :=
  fun d => Iface rho alpha edgeOf (S ∪ T) d.val

omit [Fintype D] [DecidableEq D] in
include halpha in
theorem forkSide_alpha (d : {d // InShore edgeOf (S ∪ T) d}) :
    forkSide edgeOf S T (shoreEdge alpha edgeOf halpha (S ∪ T) d) ↔
      forkSide edgeOf S T d :=
  inShore_alpha alpha edgeOf halpha S d.val

/-- One rotation step that stays in the parent shore is already the parent's
first return. -/
theorem parentRot_step (d : {d // InShore edgeOf (S ∪ T) d})
    (h : InShore edgeOf (S ∪ T) (rho d.val)) :
    (shoreRot rho edgeOf (S ∪ T) d).val = rho d.val :=
  nextHit_apply_of_step rho (InShore edgeOf (S ∪ T)) d h

include halpha in
/-- Every crossing mark produced by the fork already lies in the union of the
two child interfaces. -/
theorem mark_subset_forkHit (hdisj : Disjoint S T)
    (d : {d // InShore edgeOf (S ∪ T) d})
    (hm : Mark (shoreRot rho edgeOf (S ∪ T))
      (shoreEdge alpha edgeOf halpha (S ∪ T)) (forkSide edgeOf S T) d) :
    forkHit rho alpha edgeOf S T d := by
  have hedge : (shoreEdge alpha edgeOf halpha (S ∪ T) d).val = alpha d.val := rfl
  have hparent : InShore edgeOf (S ∪ T) (alpha d.val) :=
    (inShore_alpha alpha edgeOf halpha (S ∪ T) d.val).mpr d.property
  have hstep : InShore edgeOf (S ∪ T) (rho (alpha d.val)) →
      (shoreRot rho edgeOf (S ∪ T)
        (shoreEdge alpha edgeOf halpha (S ∪ T) d)).val = rho (alpha d.val) := by
    intro h
    exact parentRot_step rho edgeOf S T
      (shoreEdge alpha edgeOf halpha (S ∪ T) d) h
  unfold Mark Crossing forkSide at hm
  rw [hedge] at hm
  by_cases hS : InShore edgeOf S d.val
  · have hsa : InShore edgeOf S (alpha d.val) :=
      (inShore_alpha alpha edgeOf halpha S d.val).mpr hS
    refine Or.inl ⟨hS, ?_⟩
    intro hcontra
    refine hm ⟨fun _ => hsa, fun _ => ?_⟩
    rw [hstep (inShore_left edgeOf S T hcontra)]
    exact hcontra
  · have hT : InShore edgeOf T d.val :=
      inShore_right_of_parent edgeOf S T d.property hS
    have hsa : ¬ InShore edgeOf S (alpha d.val) := fun h =>
      hS ((inShore_alpha alpha edgeOf halpha S d.val).mp h)
    have hX : InShore edgeOf S (shoreRot rho edgeOf (S ∪ T)
        (shoreEdge alpha edgeOf halpha (S ∪ T) d)).val := by
      by_contra hX
      exact hm ⟨fun h => absurd h hX, fun h => absurd h hsa⟩
    refine Or.inr ⟨hT, ?_⟩
    intro hcontra
    rw [hstep (inShore_right edgeOf S T hcontra)] at hX
    exact not_inShore_right edgeOf S T hdisj hX hcontra

omit [Fintype D] [DecidableEq D] in
theorem keep_subset_forkHit (d : {d // InShore edgeOf (S ∪ T) d})
    (h : forkKeep rho alpha edgeOf S T d) : forkHit rho alpha edgeOf S T d := by
  by_cases hS : InShore edgeOf S d.val
  · exact Or.inl ⟨hS, fun hx => h.2 (inShore_left edgeOf S T hx)⟩
  · exact Or.inr ⟨inShore_right_of_parent edgeOf S T d.property hS,
      fun hx => h.2 (inShore_right edgeOf S T hx)⟩

/-! ### The bounded fork transition -/

/-- The left child's interface, seen inside the parent's marked set. -/
def forkLeftPart :
    {y : {x : {d // InShore edgeOf (S ∪ T) d} // forkHit rho alpha edgeOf S T x} //
        Iface rho alpha edgeOf S y.val.val} ≃
      {d // Iface rho alpha edgeOf S d} where
  toFun y := ⟨y.val.val.val, y.property⟩
  invFun d :=
    ⟨⟨⟨d.val, inShore_left edgeOf S T d.property.1⟩, Or.inl d.property⟩, d.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The right child's interface, seen inside the parent's marked set.  The
two shores must be disjoint for this to be a bijection. -/
def forkRightPart (hdisj : Disjoint S T) :
    {y : {x : {d // InShore edgeOf (S ∪ T) d} // forkHit rho alpha edgeOf S T x} //
        ¬ Iface rho alpha edgeOf S y.val.val} ≃
      {d // Iface rho alpha edgeOf T d} where
  toFun y := ⟨y.val.val.val, Or.resolve_left y.val.property y.property⟩
  invFun d :=
    ⟨⟨⟨d.val, inShore_right edgeOf S T d.property.1⟩, Or.inr d.property⟩,
      fun h => not_inShore_right edgeOf S T hdisj h.1 d.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The two children's interface returns merged on the union of their
interfaces.  This is the only place a child's state enters the fork. -/
def mergeRet (hdisj : Disjoint S T)
    (retLeft : Perm {d // Iface rho alpha edgeOf S d})
    (retRight : Perm {d // Iface rho alpha edgeOf T d}) :
    Perm {x : {d // InShore edgeOf (S ∪ T) d} // forkHit rho alpha edgeOf S T x} :=
  (Equiv.sumCompl (fun y => Iface rho alpha edgeOf S y.val.val)).permCongr
    (Equiv.sumCongr
      ((forkLeftPart rho alpha edgeOf S T).symm.permCongr retLeft)
      ((forkRightPart rho alpha edgeOf S T hdisj).symm.permCongr retRight))

omit [Fintype D] [DecidableEq D] in
theorem mergeRet_apply_left (hdisj : Disjoint S T)
    (retLeft : Perm {d // Iface rho alpha edgeOf S d})
    (retRight : Perm {d // Iface rho alpha edgeOf T d})
    (x : {x : {d // InShore edgeOf (S ∪ T) d} // forkHit rho alpha edgeOf S T x})
    (hx : Iface rho alpha edgeOf S x.val.val) :
    (mergeRet rho alpha edgeOf S T hdisj retLeft retRight x).val.val =
      (retLeft ⟨x.val.val, hx⟩).val := by
  simp only [mergeRet, Equiv.permCongr_apply,
    Equiv.sumCompl_symm_apply_of_pos
      (p := fun y : {x : {d // InShore edgeOf (S ∪ T) d} //
        forkHit rho alpha edgeOf S T x} => Iface rho alpha edgeOf S y.val.val) hx,
    Equiv.sumCongr_apply, Sum.map_inl,
    Equiv.sumCompl_apply_inl, Equiv.symm_symm]
  rfl

omit [Fintype D] [DecidableEq D] in
theorem mergeRet_apply_right (hdisj : Disjoint S T)
    (retLeft : Perm {d // Iface rho alpha edgeOf S d})
    (retRight : Perm {d // Iface rho alpha edgeOf T d})
    (x : {x : {d // InShore edgeOf (S ∪ T) d} // forkHit rho alpha edgeOf S T x})
    (hx : ¬ Iface rho alpha edgeOf S x.val.val) :
    (mergeRet rho alpha edgeOf S T hdisj retLeft retRight x).val.val =
      (retRight ⟨x.val.val, Or.resolve_left x.property hx⟩).val := by
  simp only [mergeRet, Equiv.permCongr_apply,
    Equiv.sumCompl_symm_apply_of_neg
      (p := fun y : {x : {d // InShore edgeOf (S ∪ T) d} //
        forkHit rho alpha edgeOf S T x} => Iface rho alpha edgeOf S y.val.val) hx,
    Equiv.sumCongr_apply, Sum.map_inr,
    Equiv.sumCompl_apply_inr, Equiv.symm_symm]
  rfl

/-- The boundary correction the fork must apply. -/
def forkRewire (hdisj : Disjoint S T) :
    Perm {x : {d // InShore edgeOf (S ∪ T) d} // forkHit rho alpha edgeOf S T x} :=
  boundaryRewireOn (shoreRot rho edgeOf (S ∪ T))
    (shoreEdge alpha edgeOf halpha (S ∪ T)) (forkSide edgeOf S T)
    (forkHit rho alpha edgeOf S T)
    (mark_subset_forkHit rho alpha edgeOf halpha S T hdisj)

/-- Off the marked set the parent's face permutation is already the
pre-gluing one: the correction is supported on the marks. -/
theorem shoreFace_eq_before_of_not_hit (hdisj : Disjoint S T)
    (d : {d // InShore edgeOf (S ∪ T) d})
    (hd : ¬ forkHit rho alpha edgeOf S T d) :
    shoreFace rho alpha edgeOf halpha (S ∪ T) d =
      before (shoreRot rho edgeOf (S ∪ T))
        (shoreEdge alpha edgeOf halpha (S ∪ T)) (forkSide edgeOf S T) d := by
  have hfix : rewire (shoreRot rho edgeOf (S ∪ T))
      (shoreEdge alpha edgeOf halpha (S ∪ T)) (forkSide edgeOf S T) d = d :=
    rewire_fixed_of_not_mark _ _ _ d
      (fun hm => hd (mark_subset_forkHit rho alpha edgeOf halpha S T hdisj d hm))
  have hmul := before_mul_rewire (shoreRot rho edgeOf (S ∪ T))
    (shoreEdge alpha edgeOf halpha (S ∪ T)) (forkSide edgeOf S T)
  show (shoreRot rho edgeOf (S ∪ T) * shoreEdge alpha edgeOf halpha (S ∪ T)) d =
    before (shoreRot rho edgeOf (S ∪ T)) (shoreEdge alpha edgeOf halpha (S ∪ T))
      (forkSide edgeOf S T) d
  rw [← hmul, Perm.mul_apply, hfix]

/-- The faces that never reach the marked set are the same before and after
the gluing correction. -/
theorem card_nonHit_parent_eq_before (hdisj : Disjoint S T) :
    Fintype.card (NonHitOrbit (shoreFace rho alpha edgeOf halpha (S ∪ T))
        (forkHit rho alpha edgeOf S T)) =
      Fintype.card (NonHitOrbit (before (shoreRot rho edgeOf (S ∪ T))
        (shoreEdge alpha edgeOf halpha (S ∪ T)) (forkSide edgeOf S T))
        (forkHit rho alpha edgeOf S T)) :=
  (Fintype.card_congr (BoundaryRewireCycles.nonHitEquiv _ _ _
    (fun d hd =>
      shoreFace_eq_before_of_not_hit rho alpha edgeOf halpha S T hdisj d hd))).symm

/-- The parent's own interface, seen inside the parent's marked set. -/
def deepMarks :
    {d // Iface rho alpha edgeOf (S ∪ T) d} ≃
      {y : {x : {d // InShore edgeOf (S ∪ T) d} // forkHit rho alpha edgeOf S T x} //
        forkKeep rho alpha edgeOf S T y.val} where
  toFun d :=
    ⟨⟨⟨d.val, d.property.1⟩,
      keep_subset_forkHit rho alpha edgeOf S T ⟨d.val, d.property.1⟩ d.property⟩,
      d.property⟩
  invFun y := ⟨y.val.val.val, y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-! ### The children are the fork's own two sides -/

/-- A left-child dart, seen in the parent carrier. -/
def leftIncl (a : {d // InShore edgeOf S d}) : {d // InShore edgeOf (S ∪ T) d} :=
  ⟨a.val, inShore_left edgeOf S T a.property⟩

/-- A right-child dart, seen in the parent carrier. -/
def rightIncl (a : {d // InShore edgeOf T d}) : {d // InShore edgeOf (S ∪ T) d} :=
  ⟨a.val, inShore_right edgeOf S T a.property⟩

def leftCarrier : {d // InShore edgeOf S d} ≃
    {x : {d // InShore edgeOf (S ∪ T) d} // forkSide edgeOf S T x} where
  toFun a := ⟨leftIncl edgeOf S T a, a.property⟩
  invFun z := ⟨z.val.val, z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def rightCarrier (hdisj : Disjoint S T) : {d // InShore edgeOf T d} ≃
    {x : {d // InShore edgeOf (S ∪ T) d} // ¬ forkSide edgeOf S T x} where
  toFun a := ⟨rightIncl edgeOf S T a,
    fun h => not_inShore_right edgeOf S T hdisj h a.property⟩
  invFun z := ⟨z.val.val,
    inShore_right_of_parent edgeOf S T z.val.property z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype D] [DecidableEq D] in
theorem forkHit_leftIncl_iff (hdisj : Disjoint S T)
    (a : {d // InShore edgeOf S d}) :
    forkHit rho alpha edgeOf S T (leftIncl edgeOf S T a) ↔
      Iface rho alpha edgeOf S a.val :=
  ⟨fun h => h.resolve_right
      (fun hT => not_inShore_right edgeOf S T hdisj a.property hT.1),
    fun h => Or.inl h⟩

omit [Fintype D] [DecidableEq D] in
theorem forkHit_rightIncl_iff (hdisj : Disjoint S T)
    (a : {d // InShore edgeOf T d}) :
    forkHit rho alpha edgeOf S T (rightIncl edgeOf S T a) ↔
      Iface rho alpha edgeOf T a.val :=
  ⟨fun h => h.resolve_left
      (fun hS => not_inShore_right edgeOf S T hdisj hS.1 a.property),
    fun h => Or.inr h⟩

/-- Restricting the parent's rotation to the left side is the left child's
own rotation: the first return of a first return is the direct first
return. -/
theorem splitRotation_left (b : {d // InShore edgeOf S d}) :
    splitRotation (shoreRot rho edgeOf (S ∪ T)) (forkSide edgeOf S T)
        (leftIncl edgeOf S T b) =
      leftIncl edgeOf S T (shoreRot rho edgeOf S b) := by
  have hb : forkSide edgeOf S T (leftIncl edgeOf S T b) := b.property
  rw [splitRotation_apply_pos _ _ _ hb]
  have hnest := nextHit_nested rho (InShore edgeOf S) (InShore edgeOf (S ∪ T))
    (fun _ h => inShore_left edgeOf S T h)
  exact congrArg Subtype.val
    (congrArg (fun p : Perm {d : {d // InShore edgeOf (S ∪ T) d} //
      InShore edgeOf S d.val} => p ⟨leftIncl edgeOf S T b, hb⟩) hnest)

theorem splitRotation_right (hdisj : Disjoint S T)
    (b : {d // InShore edgeOf T d}) :
    splitRotation (shoreRot rho edgeOf (S ∪ T)) (forkSide edgeOf S T)
        (rightIncl edgeOf S T b) =
      rightIncl edgeOf S T (shoreRot rho edgeOf T b) := by
  have huv : ∀ x : {d // InShore edgeOf (S ∪ T) d},
      ¬ forkSide edgeOf S T x ↔ InShore edgeOf T x.val :=
    fun x => ⟨fun h => inShore_right_of_parent edgeOf S T x.property h,
      fun h hs => not_inShore_right edgeOf S T hdisj hs h⟩
  have hb : ¬ forkSide edgeOf S T (rightIncl edgeOf S T b) :=
    fun h => not_inShore_right edgeOf S T hdisj h b.property
  rw [splitRotation_apply_neg _ _ _ hb,
    ← nextHit_val_congr_pred (shoreRot rho edgeOf (S ∪ T))
      (fun x => ¬ forkSide edgeOf S T x) (fun x => InShore edgeOf T x.val) huv
      ⟨rightIncl edgeOf S T b, hb⟩]
  have hnest := nextHit_nested rho (InShore edgeOf T) (InShore edgeOf (S ∪ T))
    (fun _ h => inShore_right edgeOf S T h)
  exact congrArg Subtype.val
    (congrArg (fun p : Perm {d : {d // InShore edgeOf (S ∪ T) d} //
      InShore edgeOf T d.val} => p ⟨rightIncl edgeOf S T b, b.property⟩) hnest)

/-- Before the shared vertex turns are restored, the parent's face
permutation acts on the left child exactly as the child's own does. -/
theorem before_step_left (a : {d // InShore edgeOf S d}) :
    before (shoreRot rho edgeOf (S ∪ T)) (shoreEdge alpha edgeOf halpha (S ∪ T))
        (forkSide edgeOf S T) (leftIncl edgeOf S T a) =
      leftIncl edgeOf S T (shoreFace rho alpha edgeOf halpha S a) := by
  show splitRotation (shoreRot rho edgeOf (S ∪ T)) (forkSide edgeOf S T)
      (leftIncl edgeOf S T (shoreEdge alpha edgeOf halpha S a)) = _
  rw [splitRotation_left rho edgeOf S T (shoreEdge alpha edgeOf halpha S a)]
  rfl

theorem before_step_right (hdisj : Disjoint S T)
    (a : {d // InShore edgeOf T d}) :
    before (shoreRot rho edgeOf (S ∪ T)) (shoreEdge alpha edgeOf halpha (S ∪ T))
        (forkSide edgeOf S T) (rightIncl edgeOf S T a) =
      rightIncl edgeOf S T (shoreFace rho alpha edgeOf halpha T a) := by
  show splitRotation (shoreRot rho edgeOf (S ∪ T)) (forkSide edgeOf S T)
      (rightIncl edgeOf S T (shoreEdge alpha edgeOf halpha T a)) = _
  rw [splitRotation_right rho edgeOf S T hdisj (shoreEdge alpha edgeOf halpha T a)]
  rfl

/-- The fork's left child *is* the left shore's own object. -/
theorem leftFace_eq_child :
    leftFace (shoreRot rho edgeOf (S ∪ T))
        (shoreEdge alpha edgeOf halpha (S ∪ T)) (forkSide edgeOf S T)
        (forkSide_alpha alpha edgeOf halpha S T) =
      (leftCarrier edgeOf S T).permCongr (shoreFace rho alpha edgeOf halpha S) := by
  apply Equiv.ext
  intro z
  obtain ⟨a, rfl⟩ := (leftCarrier edgeOf S T).surjective z
  apply Subtype.ext
  rw [← before_left (shoreRot rho edgeOf (S ∪ T))
    (shoreEdge alpha edgeOf halpha (S ∪ T)) (forkSide edgeOf S T)
    (forkSide_alpha alpha edgeOf halpha S T) (leftCarrier edgeOf S T a)]
  exact before_step_left rho alpha edgeOf halpha S T a

theorem rightFace_eq_child (hdisj : Disjoint S T) :
    rightFace (shoreRot rho edgeOf (S ∪ T))
        (shoreEdge alpha edgeOf halpha (S ∪ T)) (forkSide edgeOf S T)
        (forkSide_alpha alpha edgeOf halpha S T) =
      (rightCarrier edgeOf S T hdisj).permCongr
        (shoreFace rho alpha edgeOf halpha T) := by
  apply Equiv.ext
  intro z
  obtain ⟨a, rfl⟩ := (rightCarrier edgeOf S T hdisj).surjective z
  apply Subtype.ext
  rw [← before_right (shoreRot rho edgeOf (S ∪ T))
    (shoreEdge alpha edgeOf halpha (S ∪ T)) (forkSide edgeOf S T)
    (forkSide_alpha alpha edgeOf halpha S T) (rightCarrier edgeOf S T hdisj a)]
  exact before_step_right rho alpha edgeOf halpha S T hdisj a

/-- The pre-gluing face count is the sum of the two children's face counts. -/
theorem before_card_eq (hdisj : Disjoint S T) :
    (before (shoreRot rho edgeOf (S ∪ T))
        (shoreEdge alpha edgeOf halpha (S ∪ T)) (forkSide edgeOf S T)).partition.parts.card =
      (shoreFace rho alpha edgeOf halpha S).partition.parts.card +
        (shoreFace rho alpha edgeOf halpha T).partition.parts.card := by
  rw [before_face_count (shoreRot rho edgeOf (S ∪ T))
      (shoreEdge alpha edgeOf halpha (S ∪ T)) (forkSide edgeOf S T)
      (forkSide_alpha alpha edgeOf halpha S T),
    leftFace_eq_child rho alpha edgeOf halpha S T,
    rightFace_eq_child rho alpha edgeOf halpha S T hdisj,
    card_permCongr_partition_parts, card_permCongr_partition_parts]

/-- The fork transition: merge the children's interface returns, apply the
boundary correction, then forget the marks that became internal. -/
def forkStep (hdisj : Disjoint S T)
    (stateLeft : ShoreFaceState rho alpha edgeOf S)
    (stateRight : ShoreFaceState rho alpha edgeOf T) :
    ShoreFaceState rho alpha edgeOf (S ∪ T) where
  ret := (deepMarks rho alpha edgeOf S T).symm.permCongr
    (nextHitPerm
      (mergeRet rho alpha edgeOf S T hdisj stateLeft.ret stateRight.ret *
        forkRewire rho alpha edgeOf halpha S T hdisj)
      (fun y => forkKeep rho alpha edgeOf S T y.val))
  closed := stateLeft.closed + stateRight.closed +
    Fintype.card (NonHitOrbit
      (mergeRet rho alpha edgeOf S T hdisj stateLeft.ret stateRight.ret *
        forkRewire rho alpha edgeOf halpha S T hdisj)
      (fun y => forkKeep rho alpha edgeOf S T y.val))

/-! ### The fork is exact -/

/-- The merged child returns are literally the pre-gluing parent return on
the marked set.  This is the step that makes the fold a function of the two
children's bounded states. -/
theorem merge_eq_before_return (hdisj : Disjoint S T) :
    mergeRet rho alpha edgeOf S T hdisj (nodeRet rho alpha edgeOf halpha S)
        (nodeRet rho alpha edgeOf halpha T) =
      nextHitPerm (before (shoreRot rho edgeOf (S ∪ T))
          (shoreEdge alpha edgeOf halpha (S ∪ T)) (forkSide edgeOf S T))
        (forkHit rho alpha edgeOf S T) := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  by_cases hx : Iface rho alpha edgeOf S x.val.val
  · rw [mergeRet_apply_left rho alpha edgeOf S T hdisj _ _ x hx]
    exact (congrArg Subtype.val (FaceReturnSum.nextHit_map
      (shoreFace rho alpha edgeOf halpha S)
      (before (shoreRot rho edgeOf (S ∪ T))
        (shoreEdge alpha edgeOf halpha (S ∪ T)) (forkSide edgeOf S T))
      (leftIncl edgeOf S T)
      (before_step_left rho alpha edgeOf halpha S T)
      (fun a => Iface rho alpha edgeOf S a.val)
      (forkHit rho alpha edgeOf S T)
      (forkHit_leftIncl_iff rho alpha edgeOf S T hdisj)
      ⟨⟨x.val.val, hx.1⟩, hx⟩)).symm
  · rw [mergeRet_apply_right rho alpha edgeOf S T hdisj _ _ x hx]
    exact (congrArg Subtype.val (FaceReturnSum.nextHit_map
      (shoreFace rho alpha edgeOf halpha T)
      (before (shoreRot rho edgeOf (S ∪ T))
        (shoreEdge alpha edgeOf halpha (S ∪ T)) (forkSide edgeOf S T))
      (rightIncl edgeOf S T)
      (before_step_right rho alpha edgeOf halpha S T hdisj)
      (fun a => Iface rho alpha edgeOf T a.val)
      (forkHit rho alpha edgeOf S T)
      (forkHit_rightIncl_iff rho alpha edgeOf S T hdisj)
      ⟨⟨x.val.val, (Or.resolve_left x.property hx).1⟩,
        Or.resolve_left x.property hx⟩)).symm

theorem mergeRet_card (hdisj : Disjoint S T)
    (retLeft : Perm {d // Iface rho alpha edgeOf S d})
    (retRight : Perm {d // Iface rho alpha edgeOf T d}) :
    (mergeRet rho alpha edgeOf S T hdisj retLeft retRight).partition.parts.card =
      retLeft.partition.parts.card + retRight.partition.parts.card := by
  rw [mergeRet, card_permCongr_partition_parts,
    OpenTangleReplacementEuler.cycle_count_sum,
    card_permCongr_partition_parts, card_permCongr_partition_parts]

theorem forkStep_ret (hdisj : Disjoint S T) :
    (forkStep rho alpha edgeOf halpha S T hdisj
        (nodeState rho alpha edgeOf halpha S)
        (nodeState rho alpha edgeOf halpha T)).ret =
      nodeRet rho alpha edgeOf halpha (S ∪ T) := by
  have hproj :
      nextHitPerm (nextHitPerm (before (shoreRot rho edgeOf (S ∪ T))
            (shoreEdge alpha edgeOf halpha (S ∪ T)) (forkSide edgeOf S T))
            (forkHit rho alpha edgeOf S T) *
          forkRewire rho alpha edgeOf halpha S T hdisj)
          (fun y => forkKeep rho alpha edgeOf S T y.val) =
        (nestedMarks (forkKeep rho alpha edgeOf S T) (forkHit rho alpha edgeOf S T)
          (keep_subset_forkHit rho alpha edgeOf S T)).permCongr
          (nextHitPerm (shoreFace rho alpha edgeOf halpha (S ∪ T))
            (forkKeep rho alpha edgeOf S T)) :=
    parent_return_project (shoreRot rho edgeOf (S ∪ T))
      (shoreEdge alpha edgeOf halpha (S ∪ T)) (forkSide edgeOf S T)
      (forkHit rho alpha edgeOf S T) (forkKeep rho alpha edgeOf S T)
      (mark_subset_forkHit rho alpha edgeOf halpha S T hdisj)
      (keep_subset_forkHit rho alpha edgeOf S T)
  have hnest : (nestedMarks (forkKeep rho alpha edgeOf S T)
        (forkHit rho alpha edgeOf S T)
        (keep_subset_forkHit rho alpha edgeOf S T)).trans
        (deepMarks rho alpha edgeOf S T).symm =
      (nestedMarks (Iface rho alpha edgeOf (S ∪ T)) (InShore edgeOf (S ∪ T))
        (fun _ h => iface_inShore rho alpha edgeOf h)).symm := by
    apply Equiv.ext
    intro z
    rfl
  show (deepMarks rho alpha edgeOf S T).symm.permCongr
      (nextHitPerm (mergeRet rho alpha edgeOf S T hdisj
          (nodeRet rho alpha edgeOf halpha S) (nodeRet rho alpha edgeOf halpha T) *
        forkRewire rho alpha edgeOf halpha S T hdisj)
        (fun y => forkKeep rho alpha edgeOf S T y.val)) = _
  rw [merge_eq_before_return rho alpha edgeOf halpha S T hdisj, hproj,
    permCongr_permCongr, hnest]
  rfl

theorem forkStep_closed (hdisj : Disjoint S T) :
    (forkStep rho alpha edgeOf halpha S T hdisj
        (nodeState rho alpha edgeOf halpha S)
        (nodeState rho alpha edgeOf halpha T)).closed =
      nodeClosed rho alpha edgeOf halpha (S ∪ T) := by
  have hmerge := merge_eq_before_return rho alpha edgeOf halpha S T hdisj
  have hon :
      nextHitPerm (shoreFace rho alpha edgeOf halpha (S ∪ T))
          (forkHit rho alpha edgeOf S T) =
        nextHitPerm (before (shoreRot rho edgeOf (S ∪ T))
            (shoreEdge alpha edgeOf halpha (S ∪ T)) (forkSide edgeOf S T))
            (forkHit rho alpha edgeOf S T) *
          forkRewire rho alpha edgeOf halpha S T hdisj :=
    parent_return_on (shoreRot rho edgeOf (S ∪ T))
      (shoreEdge alpha edgeOf halpha (S ∪ T)) (forkSide edgeOf S T)
      (forkHit rho alpha edgeOf S T)
      (mark_subset_forkHit rho alpha edgeOf halpha S T hdisj)
  have hproj :
      nextHitPerm (nextHitPerm (before (shoreRot rho edgeOf (S ∪ T))
            (shoreEdge alpha edgeOf halpha (S ∪ T)) (forkSide edgeOf S T))
            (forkHit rho alpha edgeOf S T) *
          forkRewire rho alpha edgeOf halpha S T hdisj)
          (fun y => forkKeep rho alpha edgeOf S T y.val) =
        (nestedMarks (forkKeep rho alpha edgeOf S T) (forkHit rho alpha edgeOf S T)
          (keep_subset_forkHit rho alpha edgeOf S T)).permCongr
          (nextHitPerm (shoreFace rho alpha edgeOf halpha (S ∪ T))
            (forkKeep rho alpha edgeOf S T)) :=
    parent_return_project (shoreRot rho edgeOf (S ∪ T))
      (shoreEdge alpha edgeOf halpha (S ∪ T)) (forkSide edgeOf S T)
      (forkHit rho alpha edgeOf S T) (forkKeep rho alpha edgeOf S T)
      (mark_subset_forkHit rho alpha edgeOf halpha S T hdisj)
      (keep_subset_forkHit rho alpha edgeOf S T)
  have h1 : (shoreFace rho alpha edgeOf halpha (S ∪ T)).partition.parts.card =
      (nextHitPerm (shoreFace rho alpha edgeOf halpha (S ∪ T))
          (forkKeep rho alpha edgeOf S T)).partition.parts.card +
        nodeClosed rho alpha edgeOf halpha (S ∪ T) :=
    partition_split (shoreFace rho alpha edgeOf halpha (S ∪ T))
      (forkKeep rho alpha edgeOf S T)
  have h2 := partition_split (shoreFace rho alpha edgeOf halpha (S ∪ T))
    (forkHit rho alpha edgeOf S T)
  have h3 := card_nonHit_parent_eq_before rho alpha edgeOf halpha S T hdisj
  have h4 := partition_split (before (shoreRot rho edgeOf (S ∪ T))
    (shoreEdge alpha edgeOf halpha (S ∪ T)) (forkSide edgeOf S T))
    (forkHit rho alpha edgeOf S T)
  have h5 := before_card_eq rho alpha edgeOf halpha S T hdisj
  have h6 : (nextHitPerm (shoreFace rho alpha edgeOf halpha (S ∪ T))
        (forkHit rho alpha edgeOf S T)).partition.parts.card =
      (mergeRet rho alpha edgeOf S T hdisj (nodeRet rho alpha edgeOf halpha S)
          (nodeRet rho alpha edgeOf halpha T) *
        forkRewire rho alpha edgeOf halpha S T hdisj).partition.parts.card := by
    rw [hmerge]
    exact congrArg (fun p : Perm _ => p.partition.parts.card) hon
  have h7 := partition_split (mergeRet rho alpha edgeOf S T hdisj
      (nodeRet rho alpha edgeOf halpha S) (nodeRet rho alpha edgeOf halpha T) *
    forkRewire rho alpha edgeOf halpha S T hdisj)
    (fun y => forkKeep rho alpha edgeOf S T y.val)
  have h8 : (nextHitPerm (mergeRet rho alpha edgeOf S T hdisj
          (nodeRet rho alpha edgeOf halpha S) (nodeRet rho alpha edgeOf halpha T) *
        forkRewire rho alpha edgeOf halpha S T hdisj)
        (fun y => forkKeep rho alpha edgeOf S T y.val)).partition.parts.card =
      (nextHitPerm (shoreFace rho alpha edgeOf halpha (S ∪ T))
        (forkKeep rho alpha edgeOf S T)).partition.parts.card := by
    rw [hmerge, hproj, card_permCongr_partition_parts]
  have h9 : (mergeRet rho alpha edgeOf S T hdisj (nodeRet rho alpha edgeOf halpha S)
        (nodeRet rho alpha edgeOf halpha T)).partition.parts.card =
      (nodeRet rho alpha edgeOf halpha S).partition.parts.card +
        (nodeRet rho alpha edgeOf halpha T).partition.parts.card :=
    mergeRet_card rho alpha edgeOf S T hdisj _ _
  have h9' : (nextHitPerm (before (shoreRot rho edgeOf (S ∪ T))
          (shoreEdge alpha edgeOf halpha (S ∪ T)) (forkSide edgeOf S T))
        (forkHit rho alpha edgeOf S T)).partition.parts.card =
      (nodeRet rho alpha edgeOf halpha S).partition.parts.card +
        (nodeRet rho alpha edgeOf halpha T).partition.parts.card := by
    rw [← hmerge]
    exact h9
  have hS := node_faces rho alpha edgeOf halpha S
  have hT := node_faces rho alpha edgeOf halpha T
  show nodeClosed rho alpha edgeOf halpha S + nodeClosed rho alpha edgeOf halpha T +
      Fintype.card (NonHitOrbit (mergeRet rho alpha edgeOf S T hdisj
          (nodeRet rho alpha edgeOf halpha S) (nodeRet rho alpha edgeOf halpha T) *
        forkRewire rho alpha edgeOf halpha S T hdisj)
        (fun y => forkKeep rho alpha edgeOf S T y.val)) =
      nodeClosed rho alpha edgeOf halpha (S ∪ T)
  omega

theorem forkRewire_extend (hdisj : Disjoint S T) :
    ofSubtype (forkRewire rho alpha edgeOf halpha S T hdisj) =
      rewire (shoreRot rho edgeOf (S ∪ T))
        (shoreEdge alpha edgeOf halpha (S ∪ T)) (forkSide edgeOf S T) := by
  refine ofSubtype_subtypePerm
    (rewire_hit_iff (shoreRot rho edgeOf (S ∪ T))
      (shoreEdge alpha edgeOf halpha (S ∪ T)) (forkSide edgeOf S T)
      (forkHit rho alpha edgeOf S T)
      (mark_subset_forkHit rho alpha edgeOf halpha S T hdisj)) ?_
  intro d hd
  by_contra h
  exact hd (rewire_fixed_of_not_mark _ _ _ d
    (fun hm => h (mark_subset_forkHit rho alpha edgeOf halpha S T hdisj d hm)))

theorem before_mul_forkRewire (hdisj : Disjoint S T) :
    before (shoreRot rho edgeOf (S ∪ T))
        (shoreEdge alpha edgeOf halpha (S ∪ T)) (forkSide edgeOf S T) *
      ofSubtype (forkRewire rho alpha edgeOf halpha S T hdisj) =
      shoreFace rho alpha edgeOf halpha (S ∪ T) := by
  rw [forkRewire_extend, before_mul_rewire]
  rfl

theorem forkStep_eq (hdisj : Disjoint S T) :
    forkStep rho alpha edgeOf halpha S T hdisj
        (nodeState rho alpha edgeOf halpha S)
        (nodeState rho alpha edgeOf halpha T) =
      nodeState rho alpha edgeOf halpha (S ∪ T) := by
  exact state_ext rho alpha edgeOf _ _
    (forkStep_ret rho alpha edgeOf halpha S T hdisj)
    (forkStep_closed rho alpha edgeOf halpha S T hdisj)

/-- The fork's face-count rule, in the two-sided shape of
`EdgeShoreFaceFork.parent_face_count`: the parent's face count plus the cycle
count of the merged child returns equals the two children's face counts plus
the cycle count of the corrected return.  No `-` on `ℕ` anywhere. -/
theorem forkStep_faces (hdisj : Disjoint S T) :
    (forkStep rho alpha edgeOf halpha S T hdisj
          (nodeState rho alpha edgeOf halpha S)
          (nodeState rho alpha edgeOf halpha T)).faces +
        (mergeRet rho alpha edgeOf S T hdisj (nodeRet rho alpha edgeOf halpha S)
          (nodeRet rho alpha edgeOf halpha T)).partition.parts.card =
      (nodeState rho alpha edgeOf halpha S).faces +
        (nodeState rho alpha edgeOf halpha T).faces +
        (mergeRet rho alpha edgeOf S T hdisj (nodeRet rho alpha edgeOf halpha S)
            (nodeRet rho alpha edgeOf halpha T) *
          forkRewire rho alpha edgeOf halpha S T hdisj).partition.parts.card := by
  have hrewire := BoundaryRewireCycles.cycle_count_rewire
    (before (shoreRot rho edgeOf (S ∪ T))
      (shoreEdge alpha edgeOf halpha (S ∪ T)) (forkSide edgeOf S T))
    (forkHit rho alpha edgeOf S T) (forkRewire rho alpha edgeOf halpha S T hdisj)
  rw [before_mul_forkRewire rho alpha edgeOf halpha S T hdisj] at hrewire
  rw [forkStep_eq rho alpha edgeOf halpha S T hdisj]
  simp only [nodeState_faces]
  rw [← before_card_eq rho alpha edgeOf halpha S T hdisj,
    merge_eq_before_return rho alpha edgeOf halpha S T hdisj]
  exact hrewire

end Fork

/-! ## The fold over a whole tree -/

open GoertzelV24ForkFold (computedShore computedShore_eq_shore)

theorem shore_disjoint (left right : EdgeLeafTree E)
    (hnodup : (EdgeLeafTree.fork left right).leafList.Nodup) :
    Disjoint (computedShore left) (computedShore right) := by
  rw [computedShore_eq_shore, computedShore_eq_shore]
  apply Finset.disjoint_left.mpr
  intro edge heLeft heRight
  exact (List.disjoint_of_nodup_append hnodup)
    (by simpa [EdgeLeafTree.shore] using heLeft)
    (by simpa [EdgeLeafTree.shore] using heRight)

/-- Evaluate the face state of every subtree from the leaves up.  A leaf is
read off its single edge; every fork is the bounded transition above.  The
duplicate-free leaf labelling is what makes the two child shores at a fork
disjoint, so the merge is defined. -/
def fold : (tree : EdgeLeafTree E) → tree.leafList.Nodup →
    ShoreFaceState rho alpha edgeOf (computedShore tree)
  | .leaf edge, _ => nodeState rho alpha edgeOf halpha {edge}
  | .fork left right, hnodup =>
      forkStep rho alpha edgeOf halpha (computedShore left) (computedShore right)
        (shore_disjoint left right hnodup)
        (fold left (List.Nodup.of_append_left hnodup))
        (fold right (List.Nodup.of_append_right hnodup))

/-- **Fold exactness.**  At every node of a duplicate-free edge-leaf tree the
folded state is the literal state of that node's physical edge shore: the same
face-return permutation on the node's interface, and the same face count. -/
theorem fold_exact : ∀ (tree : EdgeLeafTree E) (hnodup : tree.leafList.Nodup),
    fold rho alpha edgeOf halpha tree hnodup =
      nodeState rho alpha edgeOf halpha (computedShore tree) := by
  intro tree
  induction tree with
  | leaf edge => intro _; rfl
  | fork left right ihLeft ihRight =>
      intro hnodup
      show forkStep rho alpha edgeOf halpha (computedShore left) (computedShore right)
          (shore_disjoint left right hnodup)
          (fold rho alpha edgeOf halpha left (List.Nodup.of_append_left hnodup))
          (fold rho alpha edgeOf halpha right (List.Nodup.of_append_right hnodup)) =
        nodeState rho alpha edgeOf halpha
          (computedShore left ∪ computedShore right)
      rw [ihLeft, ihRight]
      exact forkStep_eq rho alpha edgeOf halpha _ _ _

theorem fold_ret (tree : EdgeLeafTree E) (hnodup : tree.leafList.Nodup) :
    (fold rho alpha edgeOf halpha tree hnodup).ret =
      nodeRet rho alpha edgeOf halpha (computedShore tree) := by
  rw [fold_exact]
  rfl

theorem fold_faces (tree : EdgeLeafTree E) (hnodup : tree.leafList.Nodup) :
    (fold rho alpha edgeOf halpha tree hnodup).faces =
      (shoreFace rho alpha edgeOf halpha (computedShore tree)).partition.parts.card := by
  rw [fold_exact, nodeState_faces]

/-! ## The root of a covering tree -/

omit [Fintype D] [DecidableEq D] [DecidableEq E] in
/-- A shore that retains every dart has no interface, so all of its faces are
counted by `closed`.  This is why `closed` cannot be dropped. -/
theorem not_iface_of_cover {S : Finset E} (hall : ∀ d, InShore edgeOf S d) (d : D) :
    ¬ Iface rho alpha edgeOf S d := fun h => h.2 (hall _)

omit [DecidableEq E] in
/-- A shore that retains every dart carries the ambient face permutation. -/
theorem shoreFace_card_of_cover {S : Finset E} (hall : ∀ d, InShore edgeOf S d) :
    (shoreFace rho alpha edgeOf halpha S).partition.parts.card =
      (rho * alpha).partition.parts.card := by
  have he : shoreFace rho alpha edgeOf halpha S =
      (Equiv.subtypeUnivEquiv hall).symm.permCongr (rho * alpha) := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    show (shoreRot rho edgeOf S (shoreEdge alpha edgeOf halpha S x)).val =
      rho (alpha x.val)
    exact nextHit_apply_of_step rho (InShore edgeOf S) _ (hall _)
  rw [he, card_permCongr_partition_parts]

/-- **The regression statement.**  A duplicate-free tree whose leaves cover
every edge folds to the physical face count of the whole map. -/
theorem fold_faces_of_cover [Fintype E] (tree : EdgeLeafTree E)
    (hnodup : tree.leafList.Nodup)
    (hcover : tree.shore = Finset.univ) :
    (fold rho alpha edgeOf halpha tree hnodup).faces =
      (rho * alpha).partition.parts.card := by
  have hall : ∀ d, InShore edgeOf (computedShore tree) d := by
    intro d
    show edgeOf d ∈ computedShore tree
    rw [computedShore_eq_shore, hcover]
    exact Finset.mem_univ _
  rw [fold_faces, shoreFace_card_of_cover rho alpha edgeOf halpha hall]

end

end Mettapedia.GraphTheory.FourColor.EdgeShoreFaceForkFold
