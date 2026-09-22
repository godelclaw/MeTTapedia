import Mettapedia.GraphTheory.FourColor.EdgeShoreFaceFork
import Mettapedia.GraphTheory.FourColor.EdgeShoreFaceForkFold
import Mettapedia.GraphTheory.FourColor.GoertzelV24ForkFaceOrderObstruction

/-!
# The structural fork on two spanning trees of the tetrahedron

The planar and twisted tetrahedron have identical induced rotations on each
of two spanning-tree children. Restoring their shared vertex turns recovers
different parent face counts. These tests consume the physical fork law on
the very pair which refutes scalar-only structural summaries.
-/

namespace Mettapedia.GraphTheory.FourColor.EdgeShoreFaceForkChecks

open Equiv Equiv.Perm
open GoertzelV24V23ZeroContractionCrossing GoertzelV24ForkFaceOrderObstruction
open EdgeShoreFaceFork

set_option maxRecDepth 12000

def side (d : TetraDart) : Prop := tetraEdgeOf d ∈ leftTree.shore
instance : DecidablePred side := fun _ => inferInstanceAs (Decidable (_ ∈ _))

theorem side_alpha (d : TetraDart) : side (tetraAlpha d) ↔ side d := by
  cases d <;> decide +kernel

/-- The edge-list child already used by the fork library is the same child
as the restricted edge permutation in the new first-return presentation. -/
theorem left_edge_word :
    GoertzelV24MapEulerBound.swapProduct (edgeWord leftTree) =
      ofSubtype (tetraAlpha.subtypePerm side_alpha) := by
  ext d
  by_cases h : side d
  · rw [ofSubtype_apply_of_mem _ h, subtypePerm_apply]
    have hh : ∀ d, side d →
        GoertzelV24MapEulerBound.swapProduct (edgeWord leftTree) d = tetraAlpha d := by
      decide +kernel
    exact hh d h
  · rw [ofSubtype_apply_of_not_mem _ h]
    have hh : ∀ d, ¬ side d →
        GoertzelV24MapEulerBound.swapProduct (edgeWord leftTree) d = d := by
      decide +kernel
    exact hh d h

theorem left_face_from_existing_edge_word (rho : Perm TetraDart) :
    leftFace rho tetraAlpha side side_alpha =
      GoertzelV24OrderedCutFaceReturnProfile.nextHitPerm
        (rho * GoertzelV24MapEulerBound.swapProduct (edgeWord leftTree)) side := by
  rw [left_edge_word]
  exact leftFace_eq_raw_return rho tetraAlpha side side_alpha

def splitFn : TetraDart → TetraDart
  | .abA => .adA | .adA => .abA | .acA => .acA
  | .abB => .abB | .bcB => .bdB | .bdB => .bcB
  | .acC => .bcC | .bcC => .acC | .cdC => .cdC
  | .adD => .cdD | .cdD => .adD | .bdD => .bdD

def split : Perm TetraDart where
  toFun := splitFn
  invFun := splitFn
  left_inv := by intro d; cases d <;> rfl
  right_inv := by intro d; cases d <;> rfl

theorem split_side (d : TetraDart) : side (split d) ↔ side d := by
  cases d <;> decide +kernel

theorem planar_split : splitRotation tetraRho side = split := by
  apply splitRotation_eq_of_arcs _ _ _ 4 split_side
  decide +kernel

theorem twisted_split : splitRotation twistedRho side = split := by
  apply splitRotation_eq_of_arcs _ _ _ 4 split_side
  decide +kernel

theorem same_split : splitRotation tetraRho side = splitRotation twistedRho side :=
  planar_split.trans twisted_split.symm

theorem split_faces : (split * tetraAlpha).partition.parts.card = 2 := by
  decide +kernel

/-- Each child has six darts: neither side of the example is empty. -/
theorem child_sizes : Fintype.card {d // side d} = 6 ∧
    Fintype.card {d // ¬ side d} = 6 := by
  simp only [Fintype.card_subtype]
  decide +kernel

/-- Concrete boundary corrections; all entries are determined by the given
vertex rotations, rather than chosen to force the desired face counts. -/
def planarRewire : Perm TetraDart := tetraAlpha⁻¹ * split⁻¹ * tetraRho * tetraAlpha
def twistedRewire : Perm TetraDart := tetraAlpha⁻¹ * split⁻¹ * twistedRho * tetraAlpha

theorem planar_rewire : rewire tetraRho tetraAlpha side = planarRewire := by
  simp only [rewire, planar_split, planarRewire]

theorem twisted_rewire : rewire twistedRho tetraAlpha side = twistedRewire := by
  simp only [rewire, twisted_split, twistedRewire]

theorem corrections_differ : planarRewire ≠ twistedRewire := by decide +kernel

/-- The general parent identity computes the real planar face permutation. -/
theorem planar_glued_faces :
    ((split * tetraAlpha) * planarRewire).partition.parts.card = 4 := by
  have h := before_mul_rewire tetraRho tetraAlpha side
  rw [before, planar_split, planar_rewire] at h
  rw [h]
  decide +kernel

/-- The same two children with the altered vertex turn produce a handle. -/
theorem twisted_glued_faces :
    ((split * tetraAlpha) * twistedRewire).partition.parts.card = 2 := by
  have h := before_mul_rewire twistedRho tetraAlpha side
  rw [before, twisted_split, twisted_rewire] at h
  rw [h]
  decide +kernel

/-- The boundary-only formula detects exactly the two-face loss which the
equal scalar child summaries missed. This consumes the general fork theorem. -/
theorem boundary_correction_distinguishes :
    (GoertzelV24OrderedCutFaceReturnProfile.nextHitPerm
      (before tetraRho tetraAlpha side) (Mark tetraRho tetraAlpha side) *
      boundaryRewire tetraRho tetraAlpha side).partition.parts.card =
      (GoertzelV24OrderedCutFaceReturnProfile.nextHitPerm
        (before tetraRho tetraAlpha side) (Mark tetraRho tetraAlpha side)).partition.parts.card + 2 ∧
    (GoertzelV24OrderedCutFaceReturnProfile.nextHitPerm
      (before twistedRho tetraAlpha side) (Mark twistedRho tetraAlpha side) *
      boundaryRewire twistedRho tetraAlpha side).partition.parts.card =
      (GoertzelV24OrderedCutFaceReturnProfile.nextHitPerm
        (before twistedRho tetraAlpha side) (Mark twistedRho tetraAlpha side)).partition.parts.card := by
  have hp := parent_face_count tetraRho tetraAlpha side
  have ht := parent_face_count twistedRho tetraAlpha side
  have bp : (before tetraRho tetraAlpha side).partition.parts.card = 2 := by
    rw [before, planar_split]; exact split_faces
  have bt : (before twistedRho tetraAlpha side).partition.parts.card = 2 := by
    rw [before, twisted_split]; exact split_faces
  have fp : (tetraRho * tetraAlpha).partition.parts.card = 4 := by decide +kernel
  have ft : (twistedRho * tetraAlpha).partition.parts.card = 2 := by decide +kernel
  rw [bp, fp] at hp
  rw [bt, ft] at ht
  omega

/-! ## The same fork, folded up the whole edge-leaf tree

`EdgeShoreFaceForkFold.fold` runs the physical fork law from the leaves of an
edge-leaf tree to its root.  Here it is run on the very tree used above: two
spanning trees of the tetrahedron whose children have identical coarse data
under both rotations.  The folded root still separates them.
-/

theorem tetra_edge_alpha (dart : TetraDart) :
    tetraEdgeOf (tetraAlpha dart) = tetraEdgeOf dart := by
  cases dart <;> rfl

theorem planar_face_card : (tetraRho * tetraAlpha).partition.parts.card = 4 := by
  rw [← whole_edgeProduct_eq_alpha]
  exact planar_parent_faceCount

theorem twisted_face_card : (twistedRho * tetraAlpha).partition.parts.card = 2 := by
  rw [← whole_edgeProduct_eq_alpha]
  exact twisted_parent_faceCount

/-- The folded tetrahedron has four faces in the spherical rotation. -/
theorem planar_fold_faces :
    (EdgeShoreFaceForkFold.fold tetraRho tetraAlpha tetraEdgeOf tetra_edge_alpha
      wholeTree wholeTree_nodup).faces = 4 := by
  rw [EdgeShoreFaceForkFold.fold_faces_of_cover tetraRho tetraAlpha tetraEdgeOf
    tetra_edge_alpha wholeTree wholeTree_nodup wholeTree_cover]
  exact planar_face_card

/-- The same fold on the same tree, with one vertex rotation reversed, has
two faces.  The children's colour support and face counts are identical in
the two worlds; only the interface return differs. -/
theorem twisted_fold_faces :
    (EdgeShoreFaceForkFold.fold twistedRho tetraAlpha tetraEdgeOf tetra_edge_alpha
      wholeTree wholeTree_nodup).faces = 2 := by
  rw [EdgeShoreFaceForkFold.fold_faces_of_cover twistedRho tetraAlpha tetraEdgeOf
    tetra_edge_alpha wholeTree wholeTree_nodup wholeTree_cover]
  exact twisted_face_card

theorem fold_separates_the_two_rotations :
    (EdgeShoreFaceForkFold.fold tetraRho tetraAlpha tetraEdgeOf tetra_edge_alpha
        wholeTree wholeTree_nodup).faces ≠
      (EdgeShoreFaceForkFold.fold twistedRho tetraAlpha tetraEdgeOf tetra_edge_alpha
        wholeTree wholeTree_nodup).faces := by
  rw [planar_fold_faces, twisted_fold_faces]
  decide

end Mettapedia.GraphTheory.FourColor.EdgeShoreFaceForkChecks
