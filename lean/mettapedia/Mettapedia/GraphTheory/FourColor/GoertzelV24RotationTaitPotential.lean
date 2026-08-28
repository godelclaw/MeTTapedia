import Mettapedia.GraphTheory.FourColor.GoertzelV24DualRotationSystem
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationWalkCycleParity
import Mettapedia.GraphTheory.FourColor.GoertzelV24TaitReductionPotential

/-!
# Tait integration on a rotation-system multigraph

This is the source's Klein-potential argument without a simple-graph edge
carrier.  A proper nonzero edge colouring of the facial dual sums to zero at
every dual vertex.  Those vertices are the primal faces, so the colouring
vanishes on every facial boundary and hence, by the spherical cycle-space
theorem, on every literal multigraph cycle.  Integrating along lifted primal
walks then gives a proper four-colouring of the primal vertex graph.

Parallel edges are kept distinct throughout.  This is essential for stellar
subdivision at a face that revisits an old vertex.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RotationTaitPotential

open GoertzelV24DualRotationSystem
open GoertzelV24FaceBoundaryLinearAlgebra
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationCycleSpace
open GoertzelV24RotationWalkCycleParity
open GoertzelV24TaitReductionPotential
open SimpleGraph
open scoped BigOperators

noncomputable section

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- At a facial-dual vertex, the incident literal edges are exactly the
boundary edges of the corresponding primal face. -/
theorem dual_incidentEdges_eq_orbitFaceBoundary
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (face : OrbitFace RS) :
    (rotationSystem RS htwoSided).incidentEdges face =
      orbitFaceBoundary RS face := by
  ext edge
  constructor
  · intro hedge
    rcases ((rotationSystem RS htwoSided).mem_incidentEdges_iff).1 hedge with
      ⟨dart, hdartEdge, hdartFace⟩
    exact (mem_orbitFaceBoundary_iff RS face edge).2
      ⟨dart, (mem_orbitFaceDarts_iff RS face dart).2 hdartFace, hdartEdge⟩
  · intro hedge
    rcases (mem_orbitFaceBoundary_iff RS face edge).1 hedge with
      ⟨dart, hdartFace, hdartEdge⟩
    exact ((rotationSystem RS htwoSided).mem_incidentEdges_iff).2
      ⟨dart, hdartEdge, (mem_orbitFaceDarts_iff RS face dart).1 hdartFace⟩

/-- Connectedness of the literal facial-dual primal graph implies
connectedness of the equivalent full face-incidence graph used by the rank
calculation. -/
theorem interiorDual_connected_of_dualPrimalConnected
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (hdualConnected :
      (rotationPrimalGraph (rotationSystem RS htwoSided)).Connected) :
    (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Connected := by
  let inclusion :
      rotationPrimalGraph (rotationSystem RS htwoSided) →g
        interiorDualGraph (orbitFaceBoundary RS)
          (Finset.univ : Finset (OrbitFace RS)) :=
    { toFun := fun face => ⟨face, Finset.mem_univ face⟩
      map_rel' := by
        intro left right hadj
        rcases (rotationPrimalGraph_adj_iff
          (rotationSystem RS htwoSided)).1 hadj with
          ⟨dart, hleft, hright⟩
        apply
          interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
            (orbitFaceBoundary RS)
            (Finset.univ : Finset (OrbitFace RS))
            (orbitFace_incidence_le_two RS)
            (by
              show left ≠ right
              intro hlr
              apply htwoSided dart
              have hleft' : dartOrbitFace RS dart = left := by
                simpa using hleft
              have hright' :
                  dartOrbitFace RS (RS.alpha dart) = right := by
                simpa using hright
              exact hleft'.trans (hlr.trans hright'.symm))
        · change RS.edgeOf dart ∈ orbitFaceBoundary RS left
          rw [← hleft]
          exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS dart
        · change RS.edgeOf dart ∈ orbitFaceBoundary RS right
          rw [← hright]
          simpa [RS.edge_alpha] using
            edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS (RS.alpha dart) }
  apply hdualConnected.map inclusion
  intro face
  exact ⟨face.1, Subtype.ext rfl⟩

/-- A Tait colouring of the facial dual sums to zero on every primal facial
boundary. -/
theorem sum_orbitFaceBoundary_eq_zero_of_dualTait
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (hdualCubic : (rotationSystem RS htwoSided).IsCubic)
    (colouring : (rotationSystem RS htwoSided).EdgeColoring Color)
    (hTait : (rotationSystem RS htwoSided).IsTaitEdgeColoring colouring)
    (face : OrbitFace RS) :
    ∑ edge ∈ orbitFaceBoundary RS face, colouring edge = 0 := by
  have hsum :=
    (rotationSystem RS htwoSided).vertexColorSum_eq_zero_of_isCubic_of_isTaitEdgeColoring
      hdualCubic colouring hTait face
  rw [RotationSystem.vertexColorSum,
    dual_incidentEdges_eq_orbitFaceBoundary] at hsum
  exact hsum

/-- Summation of a literal edge chain with values in the Klein group. -/
def edgeSum (omega : E → Color) : (E → F2) →ₗ[F2] Color where
  toFun weights := ∑ edge : E, weights edge • omega edge
  map_add' := by
    intro left right
    simp only [Pi.add_apply, add_smul]
    exact Finset.sum_add_distrib
  map_smul' := by
    intro scalar weights
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply]
    exact (Finset.smul_sum).symm

omit [DecidableEq E] in
@[simp] theorem edgeSum_apply (omega : E → Color) (weights : E → F2) :
    edgeSum omega weights = ∑ edge : E, weights edge • omega edge := rfl

theorem edgeSum_indicator (omega : E → Color) (edges : Finset E) :
    edgeSum omega (fun edge => if edge ∈ edges then 1 else 0) =
      ∑ edge ∈ edges, omega edge := by
  classical
  simp only [edgeSum_apply, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

theorem edgeSum_faceBoundaryIndicator_eq_zero
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (hdualCubic : (rotationSystem RS htwoSided).IsCubic)
    (colouring : (rotationSystem RS htwoSided).EdgeColoring Color)
    (hTait : (rotationSystem RS htwoSided).IsTaitEdgeColoring colouring)
    (face : OrbitFace RS) :
    edgeSum (fun edge => colouring edge)
      (faceBoundaryIndicator RS face) = 0 := by
  rw [show faceBoundaryIndicator RS face =
      fun edge => if edge ∈ orbitFaceBoundary RS face then 1 else 0 by rfl,
    edgeSum_indicator]
  exact sum_orbitFaceBoundary_eq_zero_of_dualTait
    RS htwoSided hdualCubic colouring hTait face

/-- The dual Tait colouring vanishes on every literal primal cycle. -/
theorem edgeSum_eq_zero_of_mem_cycleSpace
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (hdualConnected : (rotationPrimalGraph
      (rotationSystem RS htwoSided)).Connected)
    (hconnected : (rotationPrimalGraph RS).Connected)
    (heuler :
      (Fintype.card V : Int) - Fintype.card E +
        Fintype.card (OrbitFace RS) = 2)
    (hdualCubic : (rotationSystem RS htwoSided).IsCubic)
    (colouring : (rotationSystem RS htwoSided).EdgeColoring Color)
    (hTait : (rotationSystem RS htwoSided).IsTaitEdgeColoring colouring)
    {weights : E → F2} (hweights : weights ∈ cycleSpace RS) :
    edgeSum (fun edge => colouring edge) weights = 0 := by
  have hfacialDual :
      (interiorDualGraph (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS))).Connected := by
    exact interiorDual_connected_of_dualPrimalConnected
      RS htwoSided hdualConnected
  rw [← range_faceBoundaryLinearMap_eq_cycleSpace
    RS htwoSided hfacialDual hconnected heuler] at hweights
  obtain ⟨coefficients, rfl⟩ := hweights
  have hexpand :
      orbitFaceBoundaryLinearMap RS coefficients =
        ∑ face : OrbitFace RS,
          coefficients face • faceBoundaryIndicator RS face := by
    funext edge
    simp only [orbitFaceBoundaryLinearMap_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, faceBoundaryIndicator]
    apply Finset.sum_congr rfl
    intro face _
    split_ifs <;> simp
  rw [hexpand, map_sum]
  refine Finset.sum_eq_zero fun face _ => ?_
  rw [map_smul,
    edgeSum_faceBoundaryIndicator_eq_zero
      RS htwoSided hdualCubic colouring hTait face,
    smul_zero]

theorem edgeSum_single (omega : E → Color) (edge : E) :
    edgeSum omega (Pi.single edge 1) = omega edge := by
  classical
  simp only [edgeSum_apply, Pi.single_apply, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_eq' Finset.univ edge omega]
  simp

/-- Integrate the literal edge colouring along one chosen lifted walk from a
fixed root. -/
def potential (RS : RotationSystem V E) (colouring : E → Color)
    (hconnected : (rotationPrimalGraph RS).Connected)
    (root vertex : V) : Color :=
  edgeSum colouring
    (walkEdgeParity RS (hconnected.preconnected root vertex).some)

/-- The potentials at the two ends of an adjacency differ by the nonzero
colour on the chosen literal edge witnessing that step. -/
theorem potential_add_potential_eq_adjacencyEdge
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (hdualConnected : (rotationPrimalGraph
      (rotationSystem RS htwoSided)).Connected)
    (hconnected : (rotationPrimalGraph RS).Connected)
    (heuler :
      (Fintype.card V : Int) - Fintype.card E +
        Fintype.card (OrbitFace RS) = 2)
    (hdualCubic : (rotationSystem RS htwoSided).IsCubic)
    (colouring : (rotationSystem RS htwoSided).EdgeColoring Color)
    (hTait : (rotationSystem RS htwoSided).IsTaitEdgeColoring colouring)
    (root : V) {first second : V}
    (hadj : (rotationPrimalGraph RS).Adj first second) :
    potential RS (fun edge => colouring edge) hconnected root first +
        potential RS (fun edge => colouring edge) hconnected root second =
      colouring (adjacencyEdge RS hadj) := by
  let firstWalk := (hconnected.preconnected root first).some
  let secondWalk := (hconnected.preconnected root second).some
  let edge := adjacencyEdge RS hadj
  let combination : E → F2 :=
    walkEdgeParity RS firstWalk + walkEdgeParity RS secondWalk +
      Pi.single edge 1
  have hboundary : combination ∈ cycleSpace RS := by
    rw [cycleSpace, LinearMap.mem_ker]
    rw [show combination =
        walkEdgeParity RS firstWalk + walkEdgeParity RS secondWalk +
          Pi.single edge 1 by rfl,
      map_add, map_add,
      incidenceMatrix_mulVec_walkEdgeParity,
      incidenceMatrix_mulVec_walkEdgeParity,
      show edge = adjacencyEdge RS hadj by rfl,
      incidenceMatrix_mulVec_single_adjacencyEdge]
    funext vertex
    simp only [Pi.add_apply, Pi.zero_apply]
    let rootValue : F2 := (Pi.single root (1 : F2) : V → F2) vertex
    let firstValue : F2 := (Pi.single first (1 : F2) : V → F2) vertex
    let secondValue : F2 := (Pi.single second (1 : F2) : V → F2) vertex
    change rootValue + firstValue + (rootValue + secondValue) +
        (firstValue + secondValue) = 0
    calc
      rootValue + firstValue + (rootValue + secondValue) +
          (firstValue + secondValue) =
          (rootValue + rootValue) + (firstValue + firstValue) +
            (secondValue + secondValue) := by abel
      _ = 0 := by simp
  have hzero := edgeSum_eq_zero_of_mem_cycleSpace RS htwoSided
    hdualConnected hconnected heuler hdualCubic colouring hTait hboundary
  rw [show combination =
      walkEdgeParity RS firstWalk + walkEdgeParity RS secondWalk +
        Pi.single edge 1 by rfl,
    map_add, map_add, edgeSum_single] at hzero
  change
    potential RS (fun current => colouring current) hconnected root first +
        potential RS (fun current => colouring current) hconnected root second +
          colouring edge = 0 at hzero
  have hchar : ∀ left right : Color,
      left + right = 0 → left = right := by
    intro left right hsum
    exact (add_eq_zero_iff_eq left right).1 hsum
  exact hchar _ _ hzero

/-- The integrated potential is a proper four-colouring of the computed
primal graph. -/
theorem colorable_four_of_dualTaitColoring
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (hdualConnected : (rotationPrimalGraph
      (rotationSystem RS htwoSided)).Connected)
    (hconnected : (rotationPrimalGraph RS).Connected)
    (heuler :
      (Fintype.card V : Int) - Fintype.card E +
        Fintype.card (OrbitFace RS) = 2)
    (hdualCubic : (rotationSystem RS htwoSided).IsCubic)
    (colouring : (rotationSystem RS htwoSided).EdgeColoring Color)
    (hTait : (rotationSystem RS htwoSided).IsTaitEdgeColoring colouring) :
    (rotationPrimalGraph RS).Colorable 4 := by
  obtain ⟨root⟩ := hconnected.nonempty
  let vertexColouring : (rotationPrimalGraph RS).Coloring Color :=
    SimpleGraph.Coloring.mk
      (potential RS (fun edge => colouring edge) hconnected root)
      (fun {first second} hadj => by
        intro hequal
        have hsum := potential_add_potential_eq_adjacencyEdge
          RS htwoSided hdualConnected hconnected heuler hdualCubic
          colouring hTait root hadj
        rw [hequal, color_add_self] at hsum
        exact hTait _ hsum.symm)
  have hcard : Fintype.card Color = 4 := by decide
  have hcolorable := vertexColouring.colorable
  rwa [hcard] at hcolorable

end

end GoertzelV24RotationTaitPotential

end Mettapedia.GraphTheory.FourColor
