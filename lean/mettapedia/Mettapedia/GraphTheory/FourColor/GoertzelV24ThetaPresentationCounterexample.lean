import Mathlib.Tactic
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutMinimality

/-!
# A spherical cubic rotation system with no simple-graph presentation

The route uses abstract rotation systems for several generic constructions,
but its minimal-counterexample spine is graph-backed.  These scopes cannot be
identified globally: the spherical theta multigraph has two vertices and
three parallel edges.  It is cubic, connected, bridge-free, and cellular on
the sphere, while a simple graph on two vertices has at most one edge.

The final theorem deliberately refutes even the weak requirement that the
edge carrier be equivalent to the edge set of a simple graph.  Consequently
any full graph-backed presentation theorem must restrict its source class;
the selected minimal-counterexample presentation remains the correct target.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ThetaPresentationCounterexample

open GoertzelV24CurvatureScope
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FaceOrbitPartitionBridge
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24RotationEdgeBridge
open GoertzelV24TwoEdgeCutMinimality

inductive ThetaVertex
  | left
  | right
  deriving DecidableEq, Repr

inductive ThetaEdge
  | first
  | second
  | third
  deriving DecidableEq, Repr

inductive ThetaDart
  | firstLeft
  | firstRight
  | secondLeft
  | secondRight
  | thirdLeft
  | thirdRight
  deriving DecidableEq, Repr

instance : Fintype ThetaVertex :=
  ⟨{ThetaVertex.left, ThetaVertex.right}, by
    intro vertex
    cases vertex <;> simp⟩

instance : Fintype ThetaEdge :=
  ⟨{ThetaEdge.first, ThetaEdge.second, ThetaEdge.third}, by
    intro edge
    cases edge <;> simp⟩

instance : Fintype ThetaDart :=
  ⟨{ThetaDart.firstLeft, ThetaDart.firstRight,
    ThetaDart.secondLeft, ThetaDart.secondRight,
    ThetaDart.thirdLeft, ThetaDart.thirdRight}, by
    intro dart
    cases dart <;> simp⟩

def thetaEdgeOf : ThetaDart → ThetaEdge
  | .firstLeft | .firstRight => .first
  | .secondLeft | .secondRight => .second
  | .thirdLeft | .thirdRight => .third

def thetaVertOf : ThetaDart → ThetaVertex
  | .firstLeft | .secondLeft | .thirdLeft => .left
  | .firstRight | .secondRight | .thirdRight => .right

def thetaAlphaFn : ThetaDart → ThetaDart
  | .firstLeft => .firstRight
  | .firstRight => .firstLeft
  | .secondLeft => .secondRight
  | .secondRight => .secondLeft
  | .thirdLeft => .thirdRight
  | .thirdRight => .thirdLeft

def thetaAlpha : Equiv.Perm ThetaDart where
  toFun := thetaAlphaFn
  invFun := thetaAlphaFn
  left_inv := by intro dart; cases dart <;> rfl
  right_inv := by intro dart; cases dart <;> rfl

/-- The two endpoint rotations have opposite orientations, giving the
standard three digon faces of the spherical theta embedding. -/
def thetaRhoFn : ThetaDart → ThetaDart
  | .firstLeft => .secondLeft
  | .secondLeft => .thirdLeft
  | .thirdLeft => .firstLeft
  | .firstRight => .thirdRight
  | .thirdRight => .secondRight
  | .secondRight => .firstRight

def thetaRhoInvFn : ThetaDart → ThetaDart
  | .firstLeft => .thirdLeft
  | .secondLeft => .firstLeft
  | .thirdLeft => .secondLeft
  | .firstRight => .secondRight
  | .thirdRight => .firstRight
  | .secondRight => .thirdRight

def thetaRho : Equiv.Perm ThetaDart where
  toFun := thetaRhoFn
  invFun := thetaRhoInvFn
  left_inv := by intro dart; cases dart <;> rfl
  right_inv := by intro dart; cases dart <;> rfl

def thetaRotationSystem : RotationSystem ThetaVertex ThetaEdge where
  D := ThetaDart
  edgeOf := thetaEdgeOf
  vertOf := thetaVertOf
  alpha := thetaAlpha
  rho := thetaRho
  alpha_involutive := by intro dart; cases dart <;> rfl
  alpha_fixfree := by intro dart; cases dart <;> decide
  edge_alpha := by intro dart; cases dart <;> rfl
  edge_fiber_two := by intro edge; cases edge <;> decide
  vert_rho := by intro dart; cases dart <;> rfl
  outer := .firstLeft
  no_self_loops := by intro dart; cases dart <;> decide

theorem theta_isCubic : thetaRotationSystem.IsCubic := by
  intro vertex
  cases vertex <;> decide

theorem theta_faceCycleCount_eq_three :
    (faceCycleLengths thetaRotationSystem).card = 3 := by
  decide

theorem theta_orbitFaceCount_eq_three :
    Fintype.card (OrbitFace thetaRotationSystem) = 3 := by
  rw [card_orbitFace_eq_faceCycleLengths_card]
  exact theta_faceCycleCount_eq_three

def thetaSpherical : OrbitSphericalCubicMapData thetaRotationSystem where
  cubic := theta_isCubic
  euler := by
    rw [theta_orbitFaceCount_eq_three]
    decide

theorem theta_primalConnected :
    (rotationPrimalGraph thetaRotationSystem).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨ThetaVertex.left, ?_⟩
  intro vertex
  cases vertex
  · rfl
  · apply SimpleGraph.Adj.reachable
    exact ⟨ThetaDart.firstLeft, rfl, rfl⟩

theorem theta_vertexRotationCyclic :
    VertexRotationCyclic thetaRotationSystem := by
  intro left right hvertex
  cases left <;> cases right <;>
    simp_all [thetaRotationSystem, thetaVertOf, thetaRho]
  all_goals
    first
    | exact Equiv.Perm.SameCycle.refl _ _
    | simpa [thetaRho, thetaRhoFn] using
        Mettapedia.GraphTheory.EquivPermSameCycle.step_right
          thetaRho ThetaDart.firstLeft
    | simpa [thetaRho, thetaRhoFn] using
        Mettapedia.GraphTheory.EquivPermSameCycle.step_right
          thetaRho ThetaDart.secondLeft
    | simpa [thetaRho, thetaRhoFn] using
        Mettapedia.GraphTheory.EquivPermSameCycle.step_right
          thetaRho ThetaDart.thirdLeft
    | simpa [thetaRho, thetaRhoFn] using
        Mettapedia.GraphTheory.EquivPermSameCycle.step_right
          thetaRho ThetaDart.firstRight
    | simpa [thetaRho, thetaRhoFn] using
        Mettapedia.GraphTheory.EquivPermSameCycle.step_right
          thetaRho ThetaDart.secondRight
    | simpa [thetaRho, thetaRhoFn] using
        Mettapedia.GraphTheory.EquivPermSameCycle.step_right
          thetaRho ThetaDart.thirdRight
    | simpa [thetaRho, thetaRhoFn] using
        (Mettapedia.GraphTheory.EquivPermSameCycle.step_right
          thetaRho ThetaDart.firstLeft).symm
    | simpa [thetaRho, thetaRhoFn] using
        (Mettapedia.GraphTheory.EquivPermSameCycle.step_right
          thetaRho ThetaDart.secondLeft).symm
    | simpa [thetaRho, thetaRhoFn] using
        (Mettapedia.GraphTheory.EquivPermSameCycle.step_right
          thetaRho ThetaDart.thirdLeft).symm
    | simpa [thetaRho, thetaRhoFn] using
        (Mettapedia.GraphTheory.EquivPermSameCycle.step_right
          thetaRho ThetaDart.firstRight).symm
    | simpa [thetaRho, thetaRhoFn] using
        (Mettapedia.GraphTheory.EquivPermSameCycle.step_right
          thetaRho ThetaDart.secondRight).symm
    | simpa [thetaRho, thetaRhoFn] using
        (Mettapedia.GraphTheory.EquivPermSameCycle.step_right
          thetaRho ThetaDart.thirdRight).symm

theorem theta_edgeBridgeFree : EdgeBridgeFree thetaRotationSystem := by
  intro dart
  cases dart
  · exact SimpleGraph.Adj.reachable
      ⟨ThetaDart.secondLeft, by decide, rfl, rfl⟩
  · exact SimpleGraph.Adj.reachable
      ⟨ThetaDart.secondRight, by decide, rfl, rfl⟩
  · exact SimpleGraph.Adj.reachable
      ⟨ThetaDart.firstLeft, by decide, rfl, rfl⟩
  · exact SimpleGraph.Adj.reachable
      ⟨ThetaDart.firstRight, by decide, rfl, rfl⟩
  · exact SimpleGraph.Adj.reachable
      ⟨ThetaDart.firstLeft, by decide, rfl, rfl⟩
  · exact SimpleGraph.Adj.reachable
      ⟨ThetaDart.firstRight, by decide, rfl, rfl⟩

/-- The theta embedding meets the entire rotation-level structural class used
by the minimality spine, except for graph backing itself. -/
def thetaBridgelessSphericalCubicMapData :
    BridgelessSphericalCubicMapData thetaRotationSystem where
  spherical := thetaSpherical
  primalConnected := theta_primalConnected
  vertexRotationCyclic := theta_vertexRotationCyclic
  edgeBridgeFree := theta_edgeBridgeFree

/-- A deliberately weak necessary condition for graph backing: its edge
identifier type can at least be bijected with the edge set of a simple graph
on the same vertices. -/
structure SimpleGraphEdgeCarrierPresentation
    (RS : RotationSystem ThetaVertex ThetaEdge) where
  graph : SimpleGraph ThetaVertex
  decidableAdj : DecidableRel graph.Adj
  edgeEquiv : ThetaEdge ≃ graph.edgeSet

/-- Even the weak edge-carrier condition fails: a simple graph on two
vertices has at most one edge, whereas the theta rotation system has three.
Thus graph backing cannot be derived for arbitrary rotation systems in the
structural class. -/
theorem theta_not_simpleGraphEdgeCarrierPresentable :
    ¬ Nonempty (SimpleGraphEdgeCarrierPresentation thetaRotationSystem) := by
  rintro ⟨presentation⟩
  letI : DecidableRel presentation.graph.Adj := presentation.decidableAdj
  have hcard :
      Fintype.card ThetaEdge = Fintype.card presentation.graph.edgeSet :=
    Fintype.card_congr presentation.edgeEquiv
  have hle :
      Fintype.card presentation.graph.edgeSet ≤
        (Fintype.card ThetaVertex).choose 2 := by
    rw [← SimpleGraph.edgeFinset_card]
    exact presentation.graph.card_edgeFinset_le_card_choose_two
  have hEdge : Fintype.card ThetaEdge = 3 := by decide
  have hVertex : Fintype.card ThetaVertex = 2 := by decide
  have hthree : 3 = Fintype.card presentation.graph.edgeSet :=
    hEdge.symm.trans hcard
  have hone : Fintype.card presentation.graph.edgeSet ≤ 1 := by
    simpa [hVertex] using hle
  omega

end GoertzelV24ThetaPresentationCounterexample

end Mettapedia.GraphTheory.FourColor
