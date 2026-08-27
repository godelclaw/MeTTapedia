import Mettapedia.GraphTheory.FourColor.GoertzelV24FiniteTreeInterfacePumping
import Mettapedia.GraphTheory.FourColor.GoertzelV24RawNooseCountPumping
import Mettapedia.GraphTheory.FourColor.GoertzelV24SphereCutMaterial
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Powerset

/-!
# The bounded-branchwidth descent, with its state count

A least counterexample of bounded branchwidth has bounded size.  This is the
half of the branchwidth dichotomy that the existing machinery closes, and this
file assembles it with the typed-state count made explicit.

The supply is a sphere-cut decomposition: a rooted binary decomposition tree in
which every separation is a noose crossing at most `2w` edges (a noose through
`w` vertices of a cubic graph perturbs to one crossing at most `2w` edges).
The typed state of a node is its seam type together with the support of the
piece below it -- the set of cut words that piece realizes.  With seam types
finite at each width and supports drawn from `2^(3^j)` possibilities at width
`j`, the state type is finite, and its cardinality is the sum displayed below.

Two facts feed the replacement step, and both are already proved: a repeated
support along a descent lets the piece below the ancestor be replaced by the
piece below the descendant without changing zero Count
(`GoertzelV24ClosedCountReplacement`), and the physical splice makes the result
a strictly smaller instance of the class.  The tree pumping then gives the
bound.  Both physical inputs are carried as explicit fields of the supply, not
proved here; the sphere-cut theorem and the splice are separate obligations.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SphereCutDescent

open GoertzelV24FiniteTreeInterfacePumping
open GoertzelV24FiniteTreeInterfacePumping.DecompTree
open GoertzelV24RawNooseCountPumping

open scoped Classical

/-- The typed state at a node of a sphere-cut decomposition of width at most
`2w`: a cut width `j ≤ 2w`, a seam type of that width, and the support of the
piece below, as a set of cut words on `j` crossed edges. -/
abbrev TypedState (w : ℕ) (SeamType : ℕ → Type) :=
  Σ j : Fin (2 * w + 1), SeamType j × Set (CutWord (Fin j))

/-- **The state count.**  `∑_{j ≤ 2w} |SeamType j| · 2^(3^j)`. -/
theorem card_typedState (w : ℕ) (SeamType : ℕ → Type) [∀ j, Fintype (SeamType j)] :
    Fintype.card (TypedState w SeamType) =
      ∑ j : Fin (2 * w + 1), Fintype.card (SeamType j) * 2 ^ (3 ^ (j : ℕ)) := by
  rw [Fintype.card_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.card_prod]
  congr 1
  rw [Fintype.card_set, card_cutWord, Fintype.card_fin]

/-- Add a depth phase modulo `6w+1` to force two repeated states far enough
apart for the cubic slab-material bound. -/
abbrev SpacedTypedState (w : ℕ) (SeamType : ℕ → Type) :=
  Fin (6 * w + 1) × TypedState w SeamType

/-- The spacing repair costs exactly the finite factor `6w+1`. -/
theorem card_spacedTypedState (w : ℕ) (SeamType : ℕ → Type)
    [∀ j, Fintype (SeamType j)] :
    Fintype.card (SpacedTypedState w SeamType) =
      (6 * w + 1) *
        (∑ j : Fin (2 * w + 1),
          Fintype.card (SeamType j) * 2 ^ (3 ^ (j : ℕ))) := by
  rw [Fintype.card_prod, Fintype.card_fin, card_typedState]

/-- **A sphere-cut descent supply.**  Everything the tree pumping needs, as
explicit data on one instance `X`: a decomposition tree whose nodes carry typed
states, the vertex accounting, and the replacement property.

The replacement field is where the geometry lives.  It says a repeated typed
state on a descent yields a strictly smaller instance with the same target
truth value; producing it is the physical splice together with support-equal
replacement.  Nothing here proves it. -/
structure Supply {Inst : Type} (size vertexCount : Inst → ℕ) (Target : Inst → Prop)
    (X : Inst) (w : ℕ) (SeamType : ℕ → Type) where
  /-- The sphere-cut decomposition, labelled by typed states. -/
  tree : DecompTree (TypedState w SeamType)
  /-- Leaves are edges, so vertices are at most twice the node count. -/
  vertices_le : vertexCount X ≤ 2 * nodeCount tree
  /-- A repeated typed state on a descent splices to a strictly smaller target
  instance. -/
  replace : ∀ p : List (TypedState w SeamType), OnPath tree p →
    ∀ i j : Fin p.length, i < j → p.get i = p.get j →
      ∃ Y, Target Y ∧ size Y < size X

/-- **The bounded-branchwidth descent.**  A minimal target instance with a
sphere-cut supply of width `w` has at most `2 (2^q − 1)` vertices, where `q` is
the state count. -/
theorem vertexCount_le_of_supply {Inst : Type} {size vertexCount : Inst → ℕ}
    {Target : Inst → Prop} {X : Inst} {w : ℕ} {SeamType : ℕ → Type}
    [∀ j, Fintype (SeamType j)]
    (supply : Supply size vertexCount Target X w SeamType)
    (hmin : ∀ Y, Target Y → size X ≤ size Y) :
    vertexCount X ≤ 2 * (2 ^ Fintype.card (TypedState w SeamType) - 1) :=
  vertexCount_le_of_minimal (state := id) (tree := fun _ => supply.tree)
    supply.vertices_le
    (fun p hp i j hij heq => supply.replace p hp i j hij (by simpa using heq))
    hmin

/-- The same bound with the state count written out. -/
theorem vertexCount_le_of_supply' {Inst : Type} {size vertexCount : Inst → ℕ}
    {Target : Inst → Prop} {X : Inst} {w : ℕ} {SeamType : ℕ → Type}
    [∀ j, Fintype (SeamType j)]
    (supply : Supply size vertexCount Target X w SeamType)
    (hmin : ∀ Y, Target Y → size X ≤ size Y) :
    vertexCount X ≤
      2 * (2 ^ (∑ j : Fin (2 * w + 1), Fintype.card (SeamType j) * 2 ^ (3 ^ (j : ℕ))) - 1) := by
  rw [← card_typedState]
  exact vertexCount_le_of_supply supply hmin

end GoertzelV24SphereCutDescent

end Mettapedia.GraphTheory.FourColor
