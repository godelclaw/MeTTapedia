import Mettapedia.GraphTheory.FourColor.GoertzelV24ForkFold
import Mettapedia.GraphTheory.FourColor.GoertzelV24V23ZeroContractionCrossing
import Mettapedia.GraphTheory.FourColor.OpenTangleEulerPresentation
import Mettapedia.GraphTheory.FourColor.MapEulerDefect

/-!
# Scalar child topology cannot determine a branch fork's genus

The tetrahedron has a planar rotation and a rotation obtained by reversing
the cyclic order at one vertex. Its six edges split into two spanning trees.
Both children have one face under either rotation, while the complete map
has four faces in the planar rotation and two in the reversed rotation.

The fork colour support depends only on edge incidence, so it is identical
in the two maps. Thus a structural fork transition cannot recover the parent
face count from child colour support and child face counts alone. This is a
counterexample at a *physical edge-leaf fork* on a simple cubic graph, not a
new terminal test or a finite-base audit.
-/

namespace Mettapedia.GraphTheory.FourColor.GoertzelV24ForkFaceOrderObstruction

open Equiv Equiv.Perm
open GoertzelV24V23ZeroContractionCrossing
open GoertzelV24ConnectedBranchDecompositionForest
open GoertzelV24ForkProjection
open GoertzelV24MapEulerBound
open GoertzelV24PermutationOrbitSurgery
open GoertzelV24WordReachability
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FaceOrbitPartitionBridge
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24CurvatureScope

set_option Elab.async false
set_option maxRecDepth 12000

/-- Reverse the vertex-a three-cycle of the standard tetrahedral rotation,
leaving its incidence graph and the other three vertex cycles unchanged. -/
def twistedRhoFn : TetraDart → TetraDart
  | .abA => .adA | .adA => .acA | .acA => .abA
  | .abB => .bdB | .bdB => .bcB | .bcB => .abB
  | .acC => .bcC | .bcC => .cdC | .cdC => .acC
  | .adD => .cdD | .cdD => .bdD | .bdD => .adD

def twistedRhoInvFn : TetraDart → TetraDart
  | .abA => .acA | .acA => .adA | .adA => .abA
  | .abB => .bcB | .bdB => .abB | .bcB => .bdB
  | .acC => .cdC | .bcC => .acC | .cdC => .bcC
  | .adD => .bdD | .bdD => .cdD | .cdD => .adD

def twistedRho : Perm TetraDart where
  toFun := twistedRhoFn
  invFun := twistedRhoInvFn
  left_inv := by intro dart; cases dart <;> rfl
  right_inv := by intro dart; cases dart <;> rfl

/-- This is an actual cubic rotation map on the *same* simple K4 incidence
graph, not merely a permutation counterexample. -/
def twistedRotationSystem : RotationSystem TetraVertex TetraEdge where
  D := TetraDart
  edgeOf := tetraEdgeOf
  vertOf := tetraVertOf
  alpha := tetraAlpha
  rho := twistedRho
  alpha_involutive := tetraRotationSystem.alpha_involutive
  alpha_fixfree := tetraRotationSystem.alpha_fixfree
  edge_alpha := tetraRotationSystem.edge_alpha
  edge_fiber_two := tetraRotationSystem.edge_fiber_two
  vert_rho := by intro dart; cases dart <;> rfl
  outer := .abA
  no_self_loops := tetraRotationSystem.no_self_loops

@[simp] theorem twisted_endpoints_eq (edge : TetraEdge) :
    twistedRotationSystem.endpoints edge = tetraEndpoints edge := by
  cases edge <;> decide +kernel

theorem twisted_isCubic : twistedRotationSystem.IsCubic := by
  intro vertex
  cases vertex <;> decide +kernel

theorem same_edge_incidence :
    twistedRotationSystem.endpoints = tetraRotationSystem.endpoints := by
  funext edge
  rw [twisted_endpoints_eq, tetra_endpoints_eq]

/-- Distinct tetrahedral edges have distinct endpoint pairs, so the graph
underlying either rotation is simple. -/
theorem tetraEndpoints_injective : Function.Injective tetraEndpoints := by
  decide +kernel

theorem twisted_endpoints_injective :
    Function.Injective twistedRotationSystem.endpoints := by
  rw [same_edge_incidence]
  intro first second heq
  apply tetraEndpoints_injective
  simpa only [tetra_endpoints_eq] using heq

theorem same_primal_graph :
    rotationPrimalGraph twistedRotationSystem =
      rotationPrimalGraph tetraRotationSystem := rfl

theorem twisted_primalConnected :
    (rotationPrimalGraph twistedRotationSystem).Connected := by
  rw [same_primal_graph]
  exact tetra_primalConnected

/-- The altered cyclic order has two faces, versus four for the spherical
tetrahedron. Therefore this particular cubic embedding is not spherical. -/
theorem twisted_faceCycleCount_eq_two :
    (faceCycleLengths twistedRotationSystem).card = 2 := by
  decide +kernel

theorem twisted_not_spherical :
    ¬ OrbitSphericalCubicMapData twistedRotationSystem := by
  intro h
  have hfaces : Fintype.card (OrbitFace twistedRotationSystem) = 2 := by
    rw [card_orbitFace_eq_faceCycleLengths_card]
    exact twisted_faceCycleCount_eq_two
  have hvertices : Fintype.card TetraVertex = 4 := by decide +kernel
  have hedges : Fintype.card TetraEdge = 6 := by decide +kernel
  have heuler := h.euler
  rw [hfaces, hvertices, hedges] at heuler
  omega

/-- The two spanning trees are an actual fork of the K4 edge-leaf tree. -/
def leftTree : EdgeLeafTree TetraEdge :=
  .fork (.leaf .ab) (.fork (.leaf .ad) (.leaf .cd))

def rightTree : EdgeLeafTree TetraEdge :=
  .fork (.leaf .ac) (.fork (.leaf .bc) (.leaf .bd))

def wholeTree : EdgeLeafTree TetraEdge := .fork leftTree rightTree

theorem wholeTree_nodup : wholeTree.leafList.Nodup := by decide +kernel

theorem wholeTree_cover : wholeTree.shore = Finset.univ := by decide +kernel

theorem child_shores_disjoint : Disjoint leftTree.shore rightTree.shore := by
  decide +kernel

/-- A pair of darts belonging to each tetrahedral edge. -/
def edgeDarts : TetraEdge → TetraDart × TetraDart
  | .ab => (.abA, .abB)
  | .ac => (.acA, .acC)
  | .ad => (.adA, .adD)
  | .bc => (.bcB, .bcC)
  | .bd => (.bdB, .bdD)
  | .cd => (.cdC, .cdD)

def edgeWord (tree : EdgeLeafTree TetraEdge) : List (TetraDart × TetraDart) :=
  tree.leafList.map edgeDarts

/-- The whole edge-leaf fork really presents the fixed edge involution of
both tetrahedral rotation systems. -/
theorem whole_edgeProduct_eq_alpha :
    swapProduct (edgeWord wholeTree) = tetraAlpha := by
  ext dart
  cases dart <;> decide +kernel

/-- A computable face count; `orbitCount_eq_parts` identifies it with the
actual permutation-orbit count in the Euler defect. -/
def faceCount (rho : Perm TetraDart) (tree : EdgeLeafTree TetraEdge) : Nat :=
  (rho * swapProduct (edgeWord tree)).partition.parts.card

theorem faceCount_eq_orbitCount (rho : Perm TetraDart)
    (tree : EdgeLeafTree TetraEdge) :
    faceCount rho tree = orbitCount (rho * swapProduct (edgeWord tree)) := by
  exact (OpenTangleEulerPresentation.orbitCount_eq_parts _).symm

theorem planar_left_faceCount : faceCount tetraRho leftTree = 1 := by decide +kernel
theorem twisted_left_faceCount : faceCount twistedRho leftTree = 1 := by decide +kernel
theorem planar_right_faceCount : faceCount tetraRho rightTree = 1 := by decide +kernel
theorem twisted_right_faceCount : faceCount twistedRho rightTree = 1 := by decide +kernel

theorem planar_parent_faceCount : faceCount tetraRho wholeTree = 4 := by decide +kernel
theorem twisted_parent_faceCount : faceCount twistedRho wholeTree = 2 := by decide +kernel

theorem planar_rotationCount : tetraRho.partition.parts.card = 4 := by decide +kernel
theorem twisted_rotationCount : twistedRho.partition.parts.card = 4 := by decide +kernel

theorem orbitCount_twisted_eq_planar :
    orbitCount twistedRho = orbitCount tetraRho := by
  rw [OpenTangleEulerPresentation.orbitCount_eq_parts,
    OpenTangleEulerPresentation.orbitCount_eq_parts,
    planar_rotationCount, twisted_rotationCount]

/-- The reversal changes the cyclic order inside one vertex but not the
vertex connectedness relation generated by the rotation. -/
private theorem planar_step_reachable_twisted
    (edges : List (TetraDart × TetraDart)) (d : TetraDart) :
    WordReachable (twistedRho :: swapGenerators edges) d (tetraRho d) := by
  have hmem : twistedRho ∈ twistedRho :: swapGenerators edges := List.mem_cons_self
  have h1 := wordReachable_step hmem d
  have h2 := h1.trans (wordReachable_step hmem (twistedRho d))
  cases d <;>
    first
    | simpa [tetraRho, tetraRhoFn, twistedRho, twistedRhoFn] using h2
    | simpa [tetraRho, tetraRhoFn, twistedRho, twistedRhoFn] using h1

private theorem twisted_step_reachable_planar
    (edges : List (TetraDart × TetraDart)) (d : TetraDart) :
    WordReachable (tetraRho :: swapGenerators edges) d (twistedRho d) := by
  have hmem : tetraRho ∈ tetraRho :: swapGenerators edges := List.mem_cons_self
  have h1 := wordReachable_step hmem d
  have h2 := h1.trans (wordReachable_step hmem (tetraRho d))
  cases d <;>
    first
    | simpa [tetraRho, tetraRhoFn, twistedRho, twistedRhoFn] using h2
    | simpa [tetraRho, tetraRhoFn, twistedRho, twistedRhoFn] using h1

/-- Component counts agree for *every* edge shore, not only for the two
chosen spanning trees: reversing a cyclic vertex rotation changes no
underlying connectivity. -/
theorem wordOrbitCount_twisted_eq_planar
    (edges : List (TetraDart × TetraDart)) :
    wordOrbitCount (twistedRho :: swapGenerators edges) =
      wordOrbitCount (tetraRho :: swapGenerators edges) := by
  apply Nat.le_antisymm
  · apply wordOrbitCount_le_of_le
    intro x y h
    apply wordReachable_absorb (L := twistedRho :: swapGenerators edges)
      (L' := tetraRho :: swapGenerators edges) ?_ h
    intro g hg d
    rcases List.mem_cons.mp hg with rfl | hg
    · exact planar_step_reachable_twisted edges d
    · exact wordReachable_step (List.mem_cons_of_mem _ hg) d
  · apply wordOrbitCount_le_of_le
    intro x y h
    apply wordReachable_absorb (L := tetraRho :: swapGenerators edges)
      (L' := twistedRho :: swapGenerators edges) ?_ h
    intro g hg d
    rcases List.mem_cons.mp hg with rfl | hg
    · exact twisted_step_reachable_planar edges d
    · exact wordReachable_step (List.mem_cons_of_mem _ hg) d

/-- Across all shores the Euler defect difference is determined exactly by
the difference in their face counts; edge and component counts agree. -/
theorem defect_twisted_eq_planar_add_face_difference
    (tree : EdgeLeafTree TetraEdge) :
    MapEulerDefect.defect twistedRho (edgeWord tree) =
      MapEulerDefect.defect tetraRho (edgeWord tree) +
        (faceCount tetraRho tree : Int) - (faceCount twistedRho tree : Int) := by
  simp only [MapEulerDefect.defect, wordOrbitCount_twisted_eq_planar,
    orbitCount_twisted_eq_planar,
    ← faceCount_eq_orbitCount]
  ring

theorem left_child_defect_equal :
    MapEulerDefect.defect twistedRho (edgeWord leftTree) =
      MapEulerDefect.defect tetraRho (edgeWord leftTree) := by
  rw [defect_twisted_eq_planar_add_face_difference,
    planar_left_faceCount, twisted_left_faceCount]
  omega

theorem right_child_defect_equal :
    MapEulerDefect.defect twistedRho (edgeWord rightTree) =
      MapEulerDefect.defect tetraRho (edgeWord rightTree) := by
  rw [defect_twisted_eq_planar_add_face_difference,
    planar_right_faceCount, twisted_right_faceCount]
  omega

theorem parent_defect_differs_by_two :
    MapEulerDefect.defect twistedRho (edgeWord wholeTree) =
      MapEulerDefect.defect tetraRho (edgeWord wholeTree) + 2 := by
  rw [defect_twisted_eq_planar_add_face_difference,
    planar_parent_faceCount, twisted_parent_faceCount]
  omega

/-- This candidate retains all realized colour behaviour, the component
count, and the exact scalar Euler defect of each child. It deliberately does
not retain the boundary first-return permutation of the faces. -/
noncomputable def coarseState (rho : Perm TetraDart) (tree : EdgeLeafTree TetraEdge) :
    (Finset (Boundary tetraEndpoints tree.shore) × Nat) × Int :=
  ((boundarySupport tetraEndpoints tree.shore,
      wordOrbitCount (rho :: swapGenerators (edgeWord tree))),
    MapEulerDefect.defect rho (edgeWord tree))

theorem same_left_coarseState :
    coarseState tetraRho leftTree = coarseState twistedRho leftTree := by
  simp [coarseState, wordOrbitCount_twisted_eq_planar,
    left_child_defect_equal]

theorem same_right_coarseState :
    coarseState tetraRho rightTree = coarseState twistedRho rightTree := by
  simp [coarseState, wordOrbitCount_twisted_eq_planar,
    right_child_defect_equal]

/-- Even retaining a child's exact defect is insufficient for an exact fork
if the boundary face order is omitted. The two inputs agree in both worlds,
but the parent defect differs by one handle (two units here). -/
theorem no_exact_coarse_defect_fork :
    ¬ ∃ step : ((Finset (Boundary tetraEndpoints leftTree.shore) × Nat) × Int) →
        ((Finset (Boundary tetraEndpoints rightTree.shore) × Nat) × Int) → Int,
      step (coarseState tetraRho leftTree) (coarseState tetraRho rightTree) =
          MapEulerDefect.defect tetraRho (edgeWord wholeTree) ∧
      step (coarseState twistedRho leftTree) (coarseState twistedRho rightTree) =
          MapEulerDefect.defect twistedRho (edgeWord wholeTree) := by
  rintro ⟨step, hflat, htwist⟩
  rw [same_left_coarseState, same_right_coarseState] at hflat
  have heq := hflat.symm.trans htwist
  rw [parent_defect_differs_by_two] at heq
  omega

/-- The colour semantics and scalar face count offered to a proposed fork
transition. The boundary support does not depend on the rotation. -/
def childState (rho : Perm TetraDart) (tree : EdgeLeafTree TetraEdge) :=
  (boundarySupport tetraEndpoints tree.shore, faceCount rho tree)

theorem same_left_state : childState tetraRho leftTree = childState twistedRho leftTree := by
  simp [childState, planar_left_faceCount, twisted_left_faceCount]

theorem same_right_state : childState tetraRho rightTree = childState twistedRho rightTree := by
  simp [childState, planar_right_faceCount, twisted_right_faceCount]

/-- No fixed fork transition on these two child states can return the
physical face count of both tetrahedral rotations. A rotation-sensitive
interface coordinate, such as cyclic face-return order, is needed. -/
theorem no_exact_scalar_face_fork :
    ¬ ∃ step : (Finset (Boundary tetraEndpoints leftTree.shore) × Nat) →
        (Finset (Boundary tetraEndpoints rightTree.shore) × Nat) → Nat,
      step (childState tetraRho leftTree) (childState tetraRho rightTree) =
          faceCount tetraRho wholeTree ∧
      step (childState twistedRho leftTree) (childState twistedRho rightTree) =
          faceCount twistedRho wholeTree := by
  rintro ⟨step, hflat, htwist⟩
  rw [same_left_state, same_right_state] at hflat
  rw [planar_parent_faceCount] at hflat
  rw [twisted_parent_faceCount] at htwist
  omega

end Mettapedia.GraphTheory.FourColor.GoertzelV24ForkFaceOrderObstruction
