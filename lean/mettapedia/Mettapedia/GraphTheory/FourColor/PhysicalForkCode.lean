import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedCutFaceReturnProfile
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.DeriveFintype

/-!
# A finite code for the physical fork fold

The fork fold of `PhysicalProfileFold` carries, at a node with edge shore `S`,
the realized boundary colour support on the middle vertices, the face-return
permutation on the interface darts, and the number `closed` of shore faces that
miss the interface.  Its carriers are subtypes of the ambient map, `closed` is
an unrestricted natural number, and its fork step reads the ambient rotation.

This file states the finite object those data are to be represented by.  A node
with `n` middle vertices is coded on the positions `Fin n`:

* `two i` records whether the vertex at position `i` carries two shore edges
  rather than one;
* `colour` is the set of realized per-position colour presentations;
* `ret` is the face return, one interface dart per middle vertex;
* `cut` is the set of realized records of vertex sets crossed by at most one
  shore edge: their bits on the positions, whether the set and its complement
  are nonempty, and whether one edge (rather than none) crosses.

There is no `closed` field.  The fork law below needs only the cycle counts of
the returns, and the Euler guard `Euler` (a planar fork changes no genus) is
what replaces the count of closed faces.

A fork is described by a `Glue`: an involution of the child positions pairing
the positions that name the same vertex, and the marks kept on the parent
interface, in parent order.  Nothing else of the ambient map is read.  Whether
a physical fork is coded by this data is proved separately; this file is the
finite side only.
-/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCode

open Equiv Equiv.Perm
open GoertzelV24OrderedCutFaceReturnProfile

noncomputable section
attribute [local instance] Classical.propDecidable

/-- A cut record on `n` positions: the membership bits of the vertex set at the
positions, whether the set is nonempty, whether its complement in the piece is
nonempty, and whether exactly one shore edge (`true`) or none (`false`)
crosses it. -/
@[ext] structure CutRecord (n : ℕ) where
  bits : Fin n → Bool
  inside : Bool
  outside : Bool
  cost : Bool
  deriving DecidableEq, Fintype

/-- The finite code of a node with `n` middle vertices. -/
@[ext] structure Code (n : ℕ) where
  two : Fin n → Bool
  colour : Finset (Fin n → Finset (Fin 3))
  ret : Perm (Fin n)
  cut : Finset (CutRecord n)
  deriving DecidableEq

/-- The code carrier as a plain product, for counting. -/
def codeEquiv (n : ℕ) :
    Code n ≃ (Fin n → Bool) × Finset (Fin n → Finset (Fin 3)) × Perm (Fin n) ×
      Finset (CutRecord n) where
  toFun c := ⟨c.two, c.colour, c.ret, c.cut⟩
  invFun c := ⟨c.1, c.2.1, c.2.2.1, c.2.2.2⟩
  left_inv c := by cases c; rfl
  right_inv c := by rcases c with ⟨a, b, c, d⟩; rfl

instance (n : ℕ) : Fintype (Code n) := Fintype.ofEquiv _ (codeEquiv n).symm

theorem card_cutRecord (n : ℕ) : Fintype.card (CutRecord n) = 2 ^ n * 8 := by
  let e : CutRecord n ≃ (Fin n → Bool) × Bool × Bool × Bool :=
    ⟨fun r => ⟨r.bits, r.inside, r.outside, r.cost⟩,
      fun r => ⟨r.1, r.2.1, r.2.2.1, r.2.2.2⟩,
      by intro r; cases r; rfl, by intro r; rcases r with ⟨a, b, c, d⟩; rfl⟩
  rw [Fintype.card_congr e]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- **The carrier is finite, with an explicit count depending only on `n`.**
No vertex count, edge count or ambient name enters. -/
theorem card_code (n : ℕ) :
    Fintype.card (Code n) =
      2 ^ n * 2 ^ (8 ^ n) * n.factorial * 2 ^ (2 ^ n * 8) := by
  rw [Fintype.card_congr (codeEquiv n)]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Fintype.card_finset, Fintype.card_perm, card_cutRecord]
  norm_num [mul_assoc]

/-! ## Gluing descriptors -/

/-- The local data of a fork.  `pair` exchanges a left and a right position that
name the same vertex and fixes every other position; `keep` lists, in parent
order, the child marks which remain interface marks of the parent. -/
structure Glue (nL nR nP : ℕ) where
  pair : Perm (Fin nL ⊕ Fin nR)
  keep : Fin nP ↪ Fin nL ⊕ Fin nR

variable {nL nR nP : ℕ}

/-- The `two` field read on the disjoint union of the child positions. -/
def twoOf (L : Code nL) (R : Code nR) : Fin nL ⊕ Fin nR → Bool
  | .inl i => L.two i
  | .inr j => R.two j

/-- A glued pair of child positions is *open* when both carry one edge, so the
vertex keeps a third edge outside the parent shore. -/
def OpenAt (L : Code nL) (R : Code nR) (g : Glue nL nR nP) (x : Fin nL ⊕ Fin nR) : Prop :=
  twoOf L R x = false ∧ twoOf L R (g.pair x) = false

/-- Legality of a descriptor.  These are exactly the constraints a physical
fork of a cubic map satisfies: a nonempty matching of left with right
positions, at most three edges at a shared vertex, every unshared mark kept,
no mark kept at a shared vertex which closes, and exactly one of the two marks
kept at a shared vertex which stays open. -/
structure Legal (L : Code nL) (R : Code nR) (g : Glue nL nR nP) : Prop where
  pair_invol : ∀ x, g.pair (g.pair x) = x
  pair_left : ∀ i, g.pair (.inl i) = .inl i ∨ ∃ j, g.pair (.inl i) = .inr j
  pair_right : ∀ j, g.pair (.inr j) = .inr j ∨ ∃ i, g.pair (.inr j) = .inl i
  shared : ∃ x, g.pair x ≠ x
  degree : ∀ x, g.pair x ≠ x → twoOf L R x = false ∨ twoOf L R (g.pair x) = false
  keep_fixed : ∀ x, g.pair x = x → x ∈ Set.range g.keep
  keep_closed : ∀ x, g.pair x ≠ x → ¬ OpenAt L R g x → x ∉ Set.range g.keep
  keep_open : ∀ x, g.pair x ≠ x → OpenAt L R g x →
    (x ∈ Set.range g.keep ↔ g.pair x ∉ Set.range g.keep)

/-- The number of shared vertices, counted on the left. -/
def sharedCount (g : Glue nL nR nP) : ℕ :=
  (Finset.univ.filter fun i : Fin nL => g.pair (.inl i) ≠ .inl i).card

/-- The merged child returns. -/
def merged (L : Code nL) (R : Code nR) : Perm (Fin nL ⊕ Fin nR) :=
  Equiv.sumCongr L.ret R.ret

/-- Number of cycles, fixed points included. -/
def cyc {A : Type*} [Fintype A] [DecidableEq A] (p : Perm A) : ℕ :=
  p.partition.parts.card

/-- **The Euler guard.**  For connected pieces sharing at least one vertex the
parent genus is the children's plus `sharedCount - 2 + cyc retL + cyc retR -
cyc (merged * pair)`, halved.  A planar fork is one where that change is zero;
it is stated without subtraction. -/
def Euler (L : Code nL) (R : Code nR) (g : Glue nL nR nP) : Prop :=
  sharedCount g + cyc L.ret + cyc R.ret = 2 + cyc (merged L R * g.pair)

/-! ## The abstract fork -/

/-- Read a child word on the disjoint union of positions. -/
def valOf {α : Type*} (bL : Fin nL → α) (bR : Fin nR → α) : Fin nL ⊕ Fin nR → α
  | .inl i => bL i
  | .inr j => bR j

/-- Colour words glue when they are disjoint at every shared vertex. -/
def ColourCompatible (g : Glue nL nR nP) (bL : Fin nL → Finset (Fin 3))
    (bR : Fin nR → Finset (Fin 3)) : Prop :=
  ∀ x, g.pair x ≠ x → Disjoint (valOf bL bR x) (valOf bL bR (g.pair x))

/-- The parent word: the kept mark's colours together with its partner's. -/
def colourOut (g : Glue nL nR nP) (bL : Fin nL → Finset (Fin 3))
    (bR : Fin nR → Finset (Fin 3)) : Fin nP → Finset (Fin 3) :=
  fun k => valOf bL bR (g.keep k) ∪ valOf bL bR (g.pair (g.keep k))

/-- Cut records glue when their bits agree at every shared vertex and at most
one edge crosses in total. -/
def CutCompatible (g : Glue nL nR nP) (rL : CutRecord nL) (rR : CutRecord nR) : Prop :=
  (∀ x, valOf rL.bits rR.bits (g.pair x) = valOf rL.bits rR.bits x) ∧
    ¬ (rL.cost = true ∧ rR.cost = true)

def cutOut (g : Glue nL nR nP) (rL : CutRecord nL) (rR : CutRecord nR) : CutRecord nP where
  bits k := valOf rL.bits rR.bits (g.keep k)
  inside := rL.inside || rR.inside
  outside := rL.outside || rR.outside
  cost := rL.cost || rR.cost

/-- The kept marks, named by parent positions. -/
def keepEquiv (g : Glue nL nR nP) : Fin nP ≃ {x // x ∈ Set.range g.keep} :=
  Equiv.ofInjective g.keep g.keep.injective

/-- **The abstract fork.**  It reads the two child codes and the descriptor,
and nothing else. -/
def fork (L : Code nL) (R : Code nR) (g : Glue nL nR nP) : Code nP where
  two k := if g.pair (g.keep k) = g.keep k then twoOf L R (g.keep k) else true
  colour := ((L.colour ×ˢ R.colour).filter fun p => ColourCompatible g p.1 p.2).image
    fun p => colourOut g p.1 p.2
  ret := (keepEquiv g).symm.permCongr
    (nextHitPerm (merged L R * g.pair) (fun x => x ∈ Set.range g.keep))
  cut := ((L.cut ×ˢ R.cut).filter fun p => CutCompatible g p.1 p.2).image
    fun p => cutOut g p.1 p.2

/-! ## The leaf and the closure -/

/-- The code of a single edge.  Both ends carry one shore edge, the three
colourings present equal colours at the two ends, the single face returns each
interface dart to the other, and the four vertex sets of the two ends are
recorded with their crossing counts. -/
def leafCode : Code 2 where
  two := fun _ => false
  colour := (Finset.univ : Finset (Fin 3)).image fun c => fun _ => {c}
  ret := swap 0 1
  cut := {⟨![false, false], false, true, false⟩, ⟨![true, false], true, true, true⟩,
    ⟨![false, true], true, true, true⟩, ⟨![true, true], true, false, false⟩}

/-- Codes reachable from the leaf by legal planar forks whose parent interface
has at most `bound` positions. -/
inductive Reach (bound : ℕ) : (n : ℕ) → Code n → Prop
  | leaf : Reach bound 2 leafCode
  | fork {nL nR nP : ℕ} {L : Code nL} {R : Code nR} (g : Glue nL nR nP) :
      Reach bound nL L → Reach bound nR R → Legal L R g → Euler L R g → nP ≤ bound →
      Reach bound nP (fork L R g)

/-! ## Root codes -/

/-- A closed code has a small cut when some record splits the vertices
nontrivially.  Every record of a root code has cost at most one. -/
def HasSmallCut (c : Code 0) : Prop := ∃ r ∈ c.cut, r.inside = true ∧ r.outside = true

/-- The condition a counterexample forces at the root: no colouring, and
neither a disconnecting set nor a bridge. -/
def Rejecting (c : Code 0) : Prop := c.colour = ∅ ∧ ¬ HasSmallCut c

/-- The finite set of reachable root codes. -/
def reachableRoots (bound : ℕ) : Finset (Code 0) :=
  Finset.univ.filter (Reach bound 0)

/-- **The audit.**  No reachable root code is rejecting. -/
def Audit (bound : ℕ) : Prop := ∀ c : Code 0, Reach bound 0 c → ¬ Rejecting c

theorem audit_iff_filter_eq_empty (bound : ℕ) :
    Audit bound ↔ (reachableRoots bound).filter Rejecting = ∅ := by
  constructor
  · intro h
    apply Finset.eq_empty_of_forall_notMem
    intro c hc
    obtain ⟨hr, hbad⟩ := Finset.mem_filter.mp hc
    exact h c (Finset.mem_filter.mp hr).2 hbad
  · intro h c hc hbad
    have : c ∈ (reachableRoots bound).filter Rejecting :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩, hbad⟩
    rw [h] at this
    simp at this

end

end Mettapedia.GraphTheory.FourColor.PhysicalForkCode
