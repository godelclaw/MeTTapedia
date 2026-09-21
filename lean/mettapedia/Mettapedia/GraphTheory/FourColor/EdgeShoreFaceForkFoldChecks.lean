import Mettapedia.GraphTheory.FourColor.EdgeShoreFaceForkFold
import Mettapedia.GraphTheory.FourColor.GoertzelV24ForkFaceOrderObstruction

/-!
# The folded tree, run on the tetrahedron that defeated the coarse state

`GoertzelV24ForkFaceOrderObstruction.no_exact_coarse_defect_fork` shows that no
fork rule on scalar child data can be exact: the planar and the twisted
rotation of the tetrahedron give the same child colour support, component count
and Euler defect, and different parents.  This file runs the structural fold of
`EdgeShoreFaceForkFold` on that very pair, over the same edge-leaf tree, and
recovers four parent faces against two.

Nothing here is a new gadget.  The rotations, the edge labelling and the tree
are the existing ones, so the file is a regression test of the richer state
rather than a fresh example chosen to succeed.
-/

namespace Mettapedia.GraphTheory.FourColor.EdgeShoreFaceForkFoldChecks

open Equiv Equiv.Perm
open Mettapedia.GraphTheory.FourColor.GoertzelV24V23ZeroContractionCrossing
open Mettapedia.GraphTheory.FourColor.GoertzelV24ForkFaceOrderObstruction
open Mettapedia.GraphTheory.FourColor.EdgeShoreFaceForkFold

/-- Edge partners carry the same edge label; this is what makes an edge shore
a union of whole edges. -/
theorem tetra_halpha (d : TetraDart) : tetraEdgeOf (tetraAlpha d) = tetraEdgeOf d := by
  cases d <;> decide +kernel

/-- The ambient face counts of the two rotations, read directly. -/
theorem planar_ambient_faces : (tetraRho * tetraAlpha).partition.parts.card = 4 := by
  decide +kernel

theorem twisted_ambient_faces : (twistedRho * tetraAlpha).partition.parts.card = 2 := by
  decide +kernel

/-- **Regression, planar rotation.**  Folding the covering tree from its leaves
gives the true four faces. -/
theorem planar_fold_faces :
    (fold tetraRho tetraAlpha tetraEdgeOf tetra_halpha wholeTree wholeTree_nodup).faces = 4 := by
  rw [fold_faces_of_cover tetraRho tetraAlpha tetraEdgeOf tetra_halpha
    wholeTree wholeTree_nodup wholeTree_cover]
  exact planar_ambient_faces

/-- **Regression, twisted rotation.**  The same tree, the same edge labelling
and the same child data at the coarse level; the fold gives two faces. -/
theorem twisted_fold_faces :
    (fold twistedRho tetraAlpha tetraEdgeOf tetra_halpha wholeTree wholeTree_nodup).faces = 2 := by
  rw [fold_faces_of_cover twistedRho tetraAlpha tetraEdgeOf tetra_halpha
    wholeTree wholeTree_nodup wholeTree_cover]
  exact twisted_ambient_faces

/-- The two folds differ, on input that the scalar fork rule cannot separate. -/
theorem folds_differ :
    (fold tetraRho tetraAlpha tetraEdgeOf tetra_halpha wholeTree wholeTree_nodup).faces ≠
      (fold twistedRho tetraAlpha tetraEdgeOf tetra_halpha wholeTree wholeTree_nodup).faces := by
  rw [planar_fold_faces, twisted_fold_faces]
  decide

end Mettapedia.GraphTheory.FourColor.EdgeShoreFaceForkFoldChecks
