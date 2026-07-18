import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionProfileCommonRunEndpointSignedTransfer
import Mettapedia.GraphTheory.FourColor.GoertzelV24CurvatureScope

namespace Mettapedia.GraphTheory.FourColor

namespace RotationSystem.CommonRunFusionSkeleton

open GoertzelV24CurvatureScope

/-- The four branch vertices left after suppressing the interiors of the
four arms and the common trunk of a clean common-run splice. -/
inductive Vertex where
  | left
  | merge
  | split
  | right
  deriving DecidableEq, Fintype

/-- The six suppressed path edges of the common-run skeleton. -/
inductive Edge where
  | leftPrefix
  | leftSuffix
  | trunk
  | rightPrefix
  | rightSuffix
  | central
  deriving DecidableEq, Fintype

/-- Named half-edges of the common-run skeleton. The constructor suffix is
the branch vertex at which the half-edge is based. -/
inductive Dart where
  | leftPrefixAtLeft
  | leftPrefixAtMerge
  | leftSuffixAtLeft
  | leftSuffixAtMerge
  | trunkAtMerge
  | trunkAtSplit
  | rightPrefixAtSplit
  | rightPrefixAtRight
  | rightSuffixAtSplit
  | rightSuffixAtRight
  | centralAtRight
  | centralAtLeft
  deriving DecidableEq, Fintype

/-- The suppressed path containing a named half-edge. -/
def edgeOf : Dart → Edge
  | .leftPrefixAtLeft | .leftPrefixAtMerge => .leftPrefix
  | .leftSuffixAtLeft | .leftSuffixAtMerge => .leftSuffix
  | .trunkAtMerge | .trunkAtSplit => .trunk
  | .rightPrefixAtSplit | .rightPrefixAtRight => .rightPrefix
  | .rightSuffixAtSplit | .rightSuffixAtRight => .rightSuffix
  | .centralAtRight | .centralAtLeft => .central

/-- The branch vertex supporting a named half-edge. -/
def vertOf : Dart → Vertex
  | .leftPrefixAtLeft | .leftSuffixAtLeft | .centralAtLeft => .left
  | .leftPrefixAtMerge | .leftSuffixAtMerge | .trunkAtMerge => .merge
  | .trunkAtSplit | .rightPrefixAtSplit | .rightSuffixAtSplit => .split
  | .rightPrefixAtRight | .rightSuffixAtRight | .centralAtRight => .right

/-- Exchange the two ends of every suppressed path edge. -/
def alphaMap : Dart → Dart
  | .leftPrefixAtLeft => .leftPrefixAtMerge
  | .leftPrefixAtMerge => .leftPrefixAtLeft
  | .leftSuffixAtLeft => .leftSuffixAtMerge
  | .leftSuffixAtMerge => .leftSuffixAtLeft
  | .trunkAtMerge => .trunkAtSplit
  | .trunkAtSplit => .trunkAtMerge
  | .rightPrefixAtSplit => .rightPrefixAtRight
  | .rightPrefixAtRight => .rightPrefixAtSplit
  | .rightSuffixAtSplit => .rightSuffixAtRight
  | .rightSuffixAtRight => .rightSuffixAtSplit
  | .centralAtRight => .centralAtLeft
  | .centralAtLeft => .centralAtRight

/-- The half-edge reversal of the common-run skeleton. -/
def alpha : Equiv.Perm Dart where
  toFun := alphaMap
  invFun := alphaMap
  left_inv := by intro dart; cases dart <;> rfl
  right_inv := by intro dart; cases dart <;> rfl

/-- Cyclic successor at the four branch vertices. The deleted endpoints have
the rotation-ordered port orientation; the two parameters are the route-normal
orientations at the merge and split vertices. -/
def rhoMap (mergeOrientation splitOrientation : Bool) : Dart → Dart
  | .leftPrefixAtLeft => .leftSuffixAtLeft
  | .leftSuffixAtLeft => .centralAtLeft
  | .centralAtLeft => .leftPrefixAtLeft
  | .leftPrefixAtMerge =>
      if mergeOrientation then .leftSuffixAtMerge else .trunkAtMerge
  | .leftSuffixAtMerge =>
      if mergeOrientation then .trunkAtMerge else .leftPrefixAtMerge
  | .trunkAtMerge =>
      if mergeOrientation then .leftPrefixAtMerge else .leftSuffixAtMerge
  | .trunkAtSplit =>
      if splitOrientation then .rightPrefixAtSplit else .rightSuffixAtSplit
  | .rightPrefixAtSplit =>
      if splitOrientation then .rightSuffixAtSplit else .trunkAtSplit
  | .rightSuffixAtSplit =>
      if splitOrientation then .trunkAtSplit else .rightPrefixAtSplit
  | .centralAtRight => .rightPrefixAtRight
  | .rightPrefixAtRight => .rightSuffixAtRight
  | .rightSuffixAtRight => .centralAtRight

/-- Inverse cyclic successor at the four branch vertices. -/
def rhoInvMap (mergeOrientation splitOrientation : Bool) : Dart → Dart
  | .leftPrefixAtLeft => .centralAtLeft
  | .leftSuffixAtLeft => .leftPrefixAtLeft
  | .centralAtLeft => .leftSuffixAtLeft
  | .leftPrefixAtMerge =>
      if mergeOrientation then .trunkAtMerge else .leftSuffixAtMerge
  | .leftSuffixAtMerge =>
      if mergeOrientation then .leftPrefixAtMerge else .trunkAtMerge
  | .trunkAtMerge =>
      if mergeOrientation then .leftSuffixAtMerge else .leftPrefixAtMerge
  | .trunkAtSplit =>
      if splitOrientation then .rightSuffixAtSplit else .rightPrefixAtSplit
  | .rightPrefixAtSplit =>
      if splitOrientation then .trunkAtSplit else .rightSuffixAtSplit
  | .rightSuffixAtSplit =>
      if splitOrientation then .rightPrefixAtSplit else .trunkAtSplit
  | .centralAtRight => .rightSuffixAtRight
  | .rightPrefixAtRight => .centralAtRight
  | .rightSuffixAtRight => .rightPrefixAtRight

/-- Vertex rotation of the common-run skeleton. -/
def rho (mergeOrientation splitOrientation : Bool) : Equiv.Perm Dart where
  toFun := rhoMap mergeOrientation splitOrientation
  invFun := rhoInvMap mergeOrientation splitOrientation
  left_inv := by
    intro dart
    cases mergeOrientation <;> cases splitOrientation <;> cases dart <;> rfl
  right_inv := by
    intro dart
    cases mergeOrientation <;> cases splitOrientation <;> cases dart <;> rfl

/-- The cubic ribbon skeleton obtained by suppressing every unbranched part of
a clean common-run splice. -/
def rotationSystem (mergeOrientation splitOrientation : Bool) :
    RotationSystem Vertex Edge where
  D := Dart
  edgeOf := edgeOf
  vertOf := vertOf
  alpha := alpha
  rho := rho mergeOrientation splitOrientation
  alpha_involutive := by intro dart; cases dart <;> rfl
  alpha_fixfree := by intro dart; cases dart <;> decide
  edge_alpha := by intro dart; cases dart <;> rfl
  edge_fiber_two := by intro edge; cases edge <;> decide
  vert_rho := by
    intro dart
    cases mergeOrientation <;> cases splitOrientation <;> cases dart <;> rfl
  outer := .centralAtLeft
  no_self_loops := by intro dart; cases dart <;> decide

/-- Every branch vertex of the suppressed skeleton is cubic. -/
theorem rotationSystem_isCubic (mergeOrientation splitOrientation : Bool) :
    (rotationSystem mergeOrientation splitOrientation).IsCubic := by
  intro vertex
  cases mergeOrientation <;> cases splitOrientation <;> cases vertex <;> decide

/-- Number of facial walks in the suppressed ribbon skeleton. -/
def faceCount (mergeOrientation splitOrientation : Bool) : Nat :=
  (faceCycleLengths (rotationSystem mergeOrientation splitOrientation)).card

/-- The route-normal merge and split rotations give four facial walks
exactly when both follow the spherical ordering. Every other assignment
gives two facial walks. -/
theorem faceCount_eq_four_iff
    (mergeOrientation splitOrientation : Bool) :
    faceCount mergeOrientation splitOrientation = 4 ↔
      mergeOrientation = false ∧ splitOrientation = false := by
  cases mergeOrientation <;> cases splitOrientation <;> decide

/-- Equivalently, the suppressed skeleton satisfies the sphere Euler
identity exactly for the spherical ordering at both internal vertices. -/
theorem nonempty_sphericalCubicMapData_iff
    (mergeOrientation splitOrientation : Bool) :
    Nonempty (SphericalCubicMapData
      (rotationSystem mergeOrientation splitOrientation)) ↔
      mergeOrientation = false ∧ splitOrientation = false := by
  constructor
  · rintro ⟨sphere⟩
    apply (faceCount_eq_four_iff mergeOrientation splitOrientation).mp
    have heuler := sphere.euler
    change (4 : Int) - 6 + faceCount mergeOrientation splitOrientation = 2 at heuler
    omega
  · intro horientations
    refine ⟨{
      cubic := rotationSystem_isCubic mergeOrientation splitOrientation
      euler := ?_ }⟩
    have hfaces :=
      (faceCount_eq_four_iff mergeOrientation splitOrientation).mpr horientations
    change (4 : Int) - 6 + faceCount mergeOrientation splitOrientation = 2
    omega

/-- Reversing a displayed prefix--suffix route order toggles its orientation
to the canonical route-normal frame. -/
def routeNormalOrientation (routeOrderFlipped orientation : Bool) : Bool :=
  Bool.xor orientation routeOrderFlipped

/-- The endpoint-frame bit is equality of the two route-normal rotation
orientations. -/
theorem threeArmEndpointFrameParity_eq_routeNormalOrientation
    (mergeRouteOrderFlipped splitRouteOrderFlipped
      mergeOrientation splitOrientation : Bool) :
    threeArmEndpointFrameParity mergeRouteOrderFlipped
        splitRouteOrderFlipped mergeOrientation splitOrientation =
      decide
        (routeNormalOrientation mergeRouteOrderFlipped mergeOrientation =
          routeNormalOrientation splitRouteOrderFlipped splitOrientation) := by
  cases mergeRouteOrderFlipped <;> cases splitRouteOrderFlipped <;>
    cases mergeOrientation <;> cases splitOrientation <;> rfl

/-- A spherical common-run skeleton has odd endpoint-frame parity. -/
theorem threeArmEndpointFrameParity_eq_true_of_spherical
    (mergeRouteOrderFlipped splitRouteOrderFlipped
      mergeOrientation splitOrientation : Bool)
    (sphere : SphericalCubicMapData
      (rotationSystem
        (routeNormalOrientation mergeRouteOrderFlipped mergeOrientation)
        (routeNormalOrientation splitRouteOrderFlipped splitOrientation))) :
    threeArmEndpointFrameParity mergeRouteOrderFlipped
        splitRouteOrderFlipped mergeOrientation splitOrientation = true := by
  rw [threeArmEndpointFrameParity_eq_routeNormalOrientation]
  have horientations :=
    (nonempty_sphericalCubicMapData_iff
      (routeNormalOrientation mergeRouteOrderFlipped mergeOrientation)
      (routeNormalOrientation splitRouteOrderFlipped splitOrientation)).mp
        ⟨sphere⟩
  rw [horientations.1, horientations.2]
  decide

end RotationSystem.CommonRunFusionSkeleton

end Mettapedia.GraphTheory.FourColor
