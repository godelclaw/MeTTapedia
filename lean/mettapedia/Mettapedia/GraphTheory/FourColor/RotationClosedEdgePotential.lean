import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationTaitPotential

/-!
# Integration of closed edge fields on spherical rotation multigraphs

An arbitrary Klein-valued field that sums to zero on every facial boundary
vanishes on every literal cycle. Integrating it along lifted walks recovers
its value on every actual edge, including each distinct parallel edge.
No dual cubicity or supplied vertex colouring is needed.
-/

namespace Mettapedia.GraphTheory.FourColor.RotationClosedEdgePotential

open GoertzelV24FaceBoundaryLinearAlgebra GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationCycleSpace GoertzelV24RotationWalkCycleParity
open GoertzelV24RotationTaitPotential
open scoped BigOperators

noncomputable section

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- Facial closedness implies closedness on every literal cycle, using the
already established spherical cycle-space theorem. -/
theorem edgeSum_eq_zero_of_faces
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (hdual : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Connected)
    (hconnected : (rotationPrimalGraph RS).Connected)
    (heuler : (Fintype.card V : Int) - Fintype.card E +
      Fintype.card (OrbitFace RS) = 2)
    (omega : E → Color)
    (hfaces : ∀ face, ∑ edge ∈ orbitFaceBoundary RS face, omega edge = 0)
    {weights : E → F2} (hweights : weights ∈ cycleSpace RS) :
    edgeSum omega weights = 0 := by
  rw [← range_faceBoundaryLinearMap_eq_cycleSpace
    RS htwoSided hdual hconnected heuler] at hweights
  obtain ⟨coefficients, rfl⟩ := hweights
  have hexpand : orbitFaceBoundaryLinearMap RS coefficients =
      ∑ face : OrbitFace RS, coefficients face • faceBoundaryIndicator RS face := by
    funext edge
    simp only [orbitFaceBoundaryLinearMap_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, faceBoundaryIndicator]
    apply Finset.sum_congr rfl
    intro face _
    split_ifs <;> simp
  rw [hexpand, map_sum]
  refine Finset.sum_eq_zero fun face _ => ?_
  rw [map_smul, show faceBoundaryIndicator RS face =
      fun edge => if edge ∈ orbitFaceBoundary RS face then 1 else 0 by rfl,
    edgeSum_indicator, hfaces face, smul_zero]

/-- Integrating a cycle-closed field recovers every literal edge value.
The chosen walks may use a different parallel edge; the cycle equation
proves that the requested edge has the same endpoint difference. -/
theorem potential_difference_of_cycle_vanishing
    (RS : RotationSystem V E) (omega : E → Color)
    (hconnected : (rotationPrimalGraph RS).Connected)
    (hcycles : ∀ weights ∈ cycleSpace RS, edgeSum omega weights = 0)
    (root : V) (dart : RS.D) :
    potential RS omega hconnected root (RS.vertOf dart) +
      potential RS omega hconnected root (RS.vertOf (RS.alpha dart)) =
        omega (RS.edgeOf dart) := by
  let firstWalk := (hconnected.preconnected root (RS.vertOf dart)).some
  let secondWalk := (hconnected.preconnected root (RS.vertOf (RS.alpha dart))).some
  let combination : E → F2 :=
    walkEdgeParity RS firstWalk + walkEdgeParity RS secondWalk +
      Pi.single (RS.edgeOf dart) 1
  have hboundary : combination ∈ cycleSpace RS := by
    rw [cycleSpace, LinearMap.mem_ker]
    rw [show combination = walkEdgeParity RS firstWalk +
        walkEdgeParity RS secondWalk + Pi.single (RS.edgeOf dart) 1 by rfl,
      map_add, map_add, incidenceMatrix_mulVec_walkEdgeParity,
      incidenceMatrix_mulVec_walkEdgeParity, incidenceMatrix_mulVec_single_edge]
    funext vertex
    simp only [Pi.add_apply, Pi.zero_apply]
    let a : F2 := (Pi.single root (1 : F2) : V → F2) vertex
    let b : F2 := (Pi.single (RS.vertOf dart) (1 : F2) : V → F2) vertex
    let c : F2 := (Pi.single (RS.vertOf (RS.alpha dart)) (1 : F2) : V → F2) vertex
    change a + b + (a + c) + (b + c) = 0
    calc
      a + b + (a + c) + (b + c) = (a+a) + (b+b) + (c+c) := by abel
      _ = 0 := by simp
  have hzero := hcycles combination hboundary
  rw [show combination = walkEdgeParity RS firstWalk +
      walkEdgeParity RS secondWalk + Pi.single (RS.edgeOf dart) 1 by rfl,
    map_add, map_add, edgeSum_single] at hzero
  change potential RS omega hconnected root (RS.vertOf dart) +
    potential RS omega hconnected root (RS.vertOf (RS.alpha dart)) +
      omega (RS.edgeOf dart) = 0 at hzero
  exact (add_eq_zero_iff_eq _ _).1 hzero

/-- Facial closedness on the actual spherical rotation suffices for exact
integration on all its edges. -/
theorem potential_difference
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (hdual : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Connected)
    (hconnected : (rotationPrimalGraph RS).Connected)
    (heuler : (Fintype.card V : Int) - Fintype.card E +
      Fintype.card (OrbitFace RS) = 2)
    (omega : E → Color)
    (hfaces : ∀ face, ∑ edge ∈ orbitFaceBoundary RS face, omega edge = 0)
    (root : V) (dart : RS.D) :
    potential RS omega hconnected root (RS.vertOf dart) +
      potential RS omega hconnected root (RS.vertOf (RS.alpha dart)) =
        omega (RS.edgeOf dart) :=
  potential_difference_of_cycle_vanishing RS omega hconnected
    (fun _ hw => edgeSum_eq_zero_of_faces
      RS htwoSided hdual hconnected heuler omega hfaces hw) root dart

end
end Mettapedia.GraphTheory.FourColor.RotationClosedEdgePotential
