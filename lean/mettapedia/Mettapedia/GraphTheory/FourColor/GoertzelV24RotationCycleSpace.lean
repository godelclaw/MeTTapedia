import Mathlib.LinearAlgebra.Matrix.Rank
import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceBoundaryLinearAlgebra
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceCycleSpace
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceCurvatureBulk
import Mettapedia.GraphTheory.FourColor.RotationSystemEdgeColoring

/-!
# The cycle space of a rotation-system multigraph

The graph-backed Tait-potential proof used a simple graph's edge subtype.
That carrier silently identifies parallel edges.  A stellar subdivision can
have parallel hub edges when a facial walk revisits a vertex, so the source's
integration argument must instead retain the literal rotation-system edge
carrier.

This module supplies that representation-invariant cycle space.  Its
incidence matrix has one column for every literal edge and one row for every
vertex.  Looplessness makes every column contain two distinct ones; parallel
columns are intentionally retained.  The usual connected rank calculation
and the facial-boundary spanning theorem therefore remain valid verbatim.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RotationCycleSpace

open GoertzelV24FaceBoundaryLinearAlgebra
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceCycleSpace
open GoertzelV24OrbitFaceTwoSided
open scoped BigOperators

noncomputable section

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- The unoriented incidence matrix on the literal multigraph edge carrier. -/
def incidenceMatrix (RS : RotationSystem V E) : Matrix V E F2 :=
  fun vertex edge => if edge ∈ RS.incidentEdges vertex then 1 else 0

/-- A fixed dart over a literal edge, used only to name its two endpoints. -/
def chosenDart (RS : RotationSystem V E) (edge : E) : RS.D :=
  Classical.choose (RS.dartsOn_nonempty edge)

theorem chosenDart_mem (RS : RotationSystem V E) (edge : E) :
    chosenDart RS edge ∈ RS.dartsOn edge :=
  Classical.choose_spec (RS.dartsOn_nonempty edge)

theorem chosenDart_edgeOf (RS : RotationSystem V E) (edge : E) :
    RS.edgeOf (chosenDart RS edge) = edge :=
  RS.mem_dartsOn.mp (chosenDart_mem RS edge)

/-- Evaluating the transpose incidence map on an edge adds its endpoint
potentials. -/
theorem transpose_incidenceMatrix_apply_edge
    (RS : RotationSystem V E) (potential : V → F2) (edge : E) :
    (Matrix.transpose (incidenceMatrix RS)).mulVecLin potential edge =
      potential (RS.vertOf (chosenDart RS edge)) +
        potential (RS.vertOf (RS.alpha (chosenDart RS edge))) := by
  classical
  let dart := chosenDart RS edge
  have hdart : dart ∈ RS.dartsOn edge := chosenDart_mem RS edge
  have hends := RS.endpoints_eq_pair_of_mem hdart
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, incidenceMatrix]
  change (∑ vertex : V,
      (if edge ∈ RS.incidentEdges vertex then 1 else 0) * potential vertex) = _
  have hincident : ∀ vertex : V,
      edge ∈ RS.incidentEdges vertex ↔
        vertex = RS.vertOf dart ∨ vertex = RS.vertOf (RS.alpha dart) := by
    intro vertex
    rw [← RS.mem_endpoints_iff_mem_incidentEdges]
    rw [hends]
    simp
  simp only [hincident, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hfilter :
      (Finset.univ.filter fun vertex : V =>
        vertex = RS.vertOf dart ∨
          vertex = RS.vertOf (RS.alpha dart)) =
        {RS.vertOf dart, RS.vertOf (RS.alpha dart)} := by
    ext vertex
    simp
  rw [hfilter]
  simp [dart, RS.no_self_loops dart]

/-- On a connected rotation multigraph, the transpose-incidence kernel is
the one-dimensional space of constant vertex potentials. -/
theorem mem_ker_transpose_incidenceMatrix_iff_constant
    (RS : RotationSystem V E)
    (hconnected : (rotationPrimalGraph RS).Connected)
    (potential : V → F2) :
    potential ∈ LinearMap.ker
        (Matrix.transpose (incidenceMatrix RS)).mulVecLin ↔
      ∀ left right, potential left = potential right := by
  constructor
  · intro hkernel
    have hzero :
        (Matrix.transpose (incidenceMatrix RS)).mulVecLin potential = 0 :=
      (LinearMap.mem_ker).1 hkernel
    have hadjacent : ∀ {left right : V},
        (rotationPrimalGraph RS).Adj left right →
          potential left = potential right := by
      intro left right hadj
      rcases (rotationPrimalGraph_adj_iff RS).1 hadj with
        ⟨dart, hleft, hright⟩
      have hedgeZero := congrFun hzero (RS.edgeOf dart)
      have hchosen := transpose_incidenceMatrix_apply_edge
        RS potential (RS.edgeOf dart)
      rw [Pi.zero_apply, hchosen] at hedgeZero
      have hsameEdge :
          RS.edgeOf (chosenDart RS (RS.edgeOf dart)) = RS.edgeOf dart :=
        chosenDart_edgeOf RS _
      have hadd : ∀ first second : F2,
          first + second = 0 → first = second := by
        intro first second hsum
        calc
          first = first + 0 := by simp
          _ = first + (second + second) := by rw [zmod2_add_self]
          _ = (first + second) + second := by rw [add_assoc]
          _ = second := by rw [hsum]; simp
      rcases RS.edge_fiber_two_cases hsameEdge rfl with hsame | hreverse
      · have hfirst :
            RS.vertOf (chosenDart RS (RS.edgeOf dart)) = left := by
          exact (congrArg RS.vertOf hsame).symm.trans hleft
        have hsecond :
            RS.vertOf (RS.alpha (chosenDart RS (RS.edgeOf dart))) = right := by
          exact (congrArg (fun current => RS.vertOf (RS.alpha current))
            hsame).symm.trans hright
        rw [hfirst, hsecond] at hedgeZero
        exact hadd _ _ hedgeZero
      · have hfirst :
            RS.vertOf (chosenDart RS (RS.edgeOf dart)) = right := by
          have hvalue := congrArg
            (fun current => RS.vertOf (RS.alpha current)) hreverse
          rw [RS.alpha_involutive] at hvalue
          exact hvalue.symm.trans hright
        have hsecond :
            RS.vertOf (RS.alpha (chosenDart RS (RS.edgeOf dart))) = left := by
          exact (congrArg RS.vertOf hreverse).symm.trans hleft
        rw [hfirst, hsecond, add_comm] at hedgeZero
        exact hadd _ _ hedgeZero
    intro left right
    rcases hconnected left right with ⟨walk⟩
    induction walk with
    | nil => rfl
    | @cons first second last hadj tail ih =>
        exact (hadjacent hadj).trans ih
  · intro hconstant
    rw [LinearMap.mem_ker]
    funext edge
    rw [transpose_incidenceMatrix_apply_edge]
    rw [hconstant (RS.vertOf (RS.alpha (chosenDart RS edge)))
      (RS.vertOf (chosenDart RS edge))]
    exact zmod2_add_self _

/-- The transpose-incidence kernel has dimension one. -/
theorem finrank_ker_transpose_incidenceMatrix_eq_one
    (RS : RotationSystem V E)
    (hconnected : (rotationPrimalGraph RS).Connected) :
    Module.finrank F2 (LinearMap.ker
      (Matrix.transpose (incidenceMatrix RS)).mulVecLin) = 1 := by
  let allOnes : LinearMap.ker
      (Matrix.transpose (incidenceMatrix RS)).mulVecLin :=
    ⟨fun _ => 1,
      (mem_ker_transpose_incidenceMatrix_iff_constant
        RS hconnected _).2 (fun _ _ => rfl)⟩
  let root : V := Classical.choice hconnected.nonempty
  apply finrank_eq_one allOnes
  · intro hzero
    have hvalue := congrFun (congrArg Subtype.val hzero) root
    change (1 : F2) = 0 at hvalue
    exact one_ne_zero hvalue
  · intro potential
    refine ⟨potential.1 root, ?_⟩
    apply Subtype.ext
    funext vertex
    have hconstant :=
      (mem_ker_transpose_incidenceMatrix_iff_constant
        RS hconnected potential.1).1 potential.2
    change potential.1 root * 1 = potential.1 vertex
    rw [mul_one]
    exact hconstant root vertex

/-- The scalar cycle space of the literal rotation multigraph. -/
def cycleSpace (RS : RotationSystem V E) : Submodule F2 (E → F2) :=
  LinearMap.ker (incidenceMatrix RS).mulVecLin

/-- Its dimension is `E - (V - 1)`, including every parallel edge as a
separate column. -/
theorem finrank_cycleSpace_eq
    (RS : RotationSystem V E)
    (hconnected : (rotationPrimalGraph RS).Connected) :
    Module.finrank F2 (cycleSpace RS) =
      Fintype.card E - (Fintype.card V - 1) := by
  have hrankNullity :=
    (Matrix.transpose (incidenceMatrix RS)).mulVecLin
      |>.finrank_range_add_finrank_ker
  rw [finrank_ker_transpose_incidenceMatrix_eq_one RS hconnected,
    Module.finrank_pi] at hrankNullity
  have htransposeRank :
      (Matrix.transpose (incidenceMatrix RS)).rank =
        Fintype.card V - 1 := by
    unfold Matrix.rank
    omega
  rw [Matrix.rank_transpose] at htransposeRank
  have hrankNullity' := (incidenceMatrix RS).mulVecLin.finrank_range_add_finrank_ker
  have hrange :
      Module.finrank F2 (LinearMap.range (incidenceMatrix RS).mulVecLin) =
        Fintype.card V - 1 := htransposeRank
  rw [hrange, Module.finrank_pi] at hrankNullity'
  apply Nat.eq_sub_of_add_eq
  rw [add_comm]
  exact hrankNullity'

/-- The scalar indicator of one quotient facial boundary on the literal edge
carrier. -/
def faceBoundaryIndicator (RS : RotationSystem V E)
    (face : OrbitFace RS) : E → F2 :=
  fun edge => if edge ∈ orbitFaceBoundary RS face then 1 else 0

/-- A two-sided quotient facial boundary is a multigraph cycle. -/
theorem faceBoundaryIndicator_mem_cycleSpace
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (face : OrbitFace RS) :
    faceBoundaryIndicator RS face ∈ cycleSpace RS := by
  rw [cycleSpace, LinearMap.mem_ker]
  funext vertex
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    incidenceMatrix, faceBoundaryIndicator]
  change (∑ edge : E,
    (if edge ∈ RS.incidentEdges vertex then 1 else 0) *
      (if edge ∈ orbitFaceBoundary RS face then 1 else 0)) = 0
  let incidentBoundary :=
    RS.incidentEdges vertex ∩ orbitFaceBoundary RS face
  calc
    (∑ edge : E,
      (if edge ∈ RS.incidentEdges vertex then 1 else 0) *
        (if edge ∈ orbitFaceBoundary RS face then 1 else 0)) =
        ∑ edge : E,
          if edge ∈ RS.incidentEdges vertex ∧
            edge ∈ orbitFaceBoundary RS face then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro edge _
      by_cases hvertex : edge ∈ RS.incidentEdges vertex <;>
        by_cases hface : edge ∈ orbitFaceBoundary RS face <;>
        simp [hvertex, hface]
    _ = (incidentBoundary.card : F2) := by
      rw [show incidentBoundary =
          Finset.univ.filter fun edge : E =>
            edge ∈ RS.incidentEdges vertex ∧
              edge ∈ orbitFaceBoundary RS face by
        ext edge
        simp [incidentBoundary]]
      exact Finset.sum_boole _ _
    _ = 0 :=
      (incidentEdges_inter_orbitFaceBoundary_card_even
        RS htwoSided face vertex).natCast_zmod_two

/-- Every facial-boundary combination lies in the literal multigraph cycle
space. -/
theorem range_faceBoundaryLinearMap_le_cycleSpace
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS) :
    LinearMap.range (orbitFaceBoundaryLinearMap RS) ≤ cycleSpace RS := by
  rintro vector ⟨coefficients, rfl⟩
  have hsum :
      orbitFaceBoundaryLinearMap RS coefficients =
        ∑ face : OrbitFace RS,
          coefficients face • faceBoundaryIndicator RS face := by
    funext edge
    simp only [orbitFaceBoundaryLinearMap_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, faceBoundaryIndicator]
    apply Finset.sum_congr rfl
    intro face _
    split_ifs <;> simp
  rw [hsum]
  exact Submodule.sum_mem _ fun face _ =>
    Submodule.smul_mem _ _
      (faceBoundaryIndicator_mem_cycleSpace RS htwoSided face)

/-- On a connected spherical rotation multigraph, facial boundaries span the
entire literal cycle space. -/
theorem range_faceBoundaryLinearMap_eq_cycleSpace
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (hdual : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Connected)
    (hconnected : (rotationPrimalGraph RS).Connected)
    (heuler :
      (Fintype.card V : Int) - Fintype.card E +
        Fintype.card (OrbitFace RS) = 2) :
    LinearMap.range (orbitFaceBoundaryLinearMap RS) = cycleSpace RS := by
  apply Submodule.eq_of_le_of_finrank_eq
    (range_faceBoundaryLinearMap_le_cycleSpace RS htwoSided)
  rw [finrank_range_orbitFaceBoundaryLinearMap RS htwoSided hdual,
    finrank_cycleSpace_eq RS hconnected]
  have hvertices : 0 < Fintype.card V :=
    Fintype.card_pos_iff.mpr hconnected.nonempty
  omega

end

end GoertzelV24RotationCycleSpace

end Mettapedia.GraphTheory.FourColor
