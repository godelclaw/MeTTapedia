import Mettapedia.GraphTheory.FourColor.EdgeShoreFaceForkFold

/-!
# Both coordinates of the physical profile, folded over one tree

The colour coordinate of a fork fold was already proved exact against the
literal edge shore, and the structural coordinate -- the interface face-return
permutation and the face count -- is proved exact in `EdgeShoreFaceForkFold`.
Both evaluators run over the same `EdgeLeafTree` and read the same
`computedShore` at each node, so they are coordinates of a single state rather
than two unrelated folds.

This file records that state and the combined exactness theorem.  The content
is the conjunction: at every node of a duplicate-free tree, both coordinates of
the folded profile are the literal ones of that node's physical edge shore.

What this does **not** do.  Exactness of a fold is not a finite-base audit.
Finite-state closure, coverage, adequacy and empty rejecting-root closure each
need their own argument, and the global production of suitable cuts is a
separate obligation entirely.  None of them is touched here; what is supplied
is the exact transition they would consume.
-/

namespace Mettapedia.GraphTheory.FourColor.PhysicalProfileFold

open Equiv
open Mettapedia.GraphTheory.FourColor.GoertzelV24ForkProjection
open Mettapedia.GraphTheory.FourColor.GoertzelV24ConnectedBranchDecompositionForest
open Mettapedia.GraphTheory.FourColor.GoertzelV24ForkFold
open Mettapedia.GraphTheory.FourColor.EdgeShoreFaceForkFold

variable {V E D : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable [Fintype D] [DecidableEq D]
variable (inc : E → Finset V) (rho alpha : Perm D) (edgeOf : D → E)
variable (halpha : ∀ d, edgeOf (alpha d) = edgeOf d)

/-- The bounded state carried at a node: realized boundary colour support, and
the structural face state of the node's own edge shore. -/
structure PhysicalProfile (S : Finset E) where
  colour : Finset (Boundary inc S)
  face : ShoreFaceState rho alpha edgeOf S

/-- Both coordinates evaluated from the leaves up, over one tree. -/
noncomputable def profileFold (tree : EdgeLeafTree E) (hnodup : tree.leafList.Nodup) :
    PhysicalProfile inc rho alpha edgeOf (computedShore tree) where
  colour := GoertzelV24ForkFold.fold inc tree
  face := EdgeShoreFaceForkFold.fold rho alpha edgeOf halpha tree hnodup

/-- The literal profile of a node's physical edge shore. -/
noncomputable def nodeProfile (S : Finset E) : PhysicalProfile inc rho alpha edgeOf S where
  colour := boundarySupport inc S
  face := nodeState rho alpha edgeOf halpha S

/-- **Physical-profile exactness.**  At every node of a duplicate-free
edge-leaf tree, both coordinates of the folded profile are the literal ones of
that node's physical edge shore: the realized boundary colour support, the
interface face-return permutation, and the face count. -/
theorem profileFold_exact
    (hcubic : ∀ v : V, (Finset.univ.filter fun e => v ∈ inc e).card = 3)
    (tree : EdgeLeafTree E) (hnodup : tree.leafList.Nodup) :
    profileFold inc rho alpha edgeOf halpha tree hnodup =
      nodeProfile inc rho alpha edgeOf halpha (computedShore tree) := by
  have hcolour : GoertzelV24ForkFold.fold inc tree = boundarySupport inc (computedShore tree) :=
    GoertzelV24ForkFold.fold_exact inc hcubic tree hnodup
  have hface : EdgeShoreFaceForkFold.fold rho alpha edgeOf halpha tree hnodup =
      nodeState rho alpha edgeOf halpha (computedShore tree) :=
    EdgeShoreFaceForkFold.fold_exact rho alpha edgeOf halpha tree hnodup
  simp only [profileFold, nodeProfile, hcolour, hface]

/-- The face count of the folded profile is the literal face count of the
node's own face permutation. -/
theorem profileFold_faces
    (hcubic : ∀ v : V, (Finset.univ.filter fun e => v ∈ inc e).card = 3)
    (tree : EdgeLeafTree E) (hnodup : tree.leafList.Nodup) :
    (profileFold inc rho alpha edgeOf halpha tree hnodup).face.faces =
      (shoreFace rho alpha edgeOf halpha (computedShore tree)).partition.parts.card := by
  rw [profileFold_exact inc rho alpha edgeOf halpha hcubic tree hnodup]
  exact nodeState_faces rho alpha edgeOf halpha (computedShore tree)

end Mettapedia.GraphTheory.FourColor.PhysicalProfileFold
