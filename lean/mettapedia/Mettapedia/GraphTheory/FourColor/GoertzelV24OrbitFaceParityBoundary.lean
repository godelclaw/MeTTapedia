import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceBoundaryLinearAlgebra
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceCycleSpace
import Mettapedia.GraphTheory.FourColor.GoertzelV24PrimalCycleSpace
import Mettapedia.GraphTheory.FourColor.RotationSystemEdgeColoring

/-!
# Facial boundaries with dart multiplicity

The existing quotient-face boundary map records edge support, so it requires
every edge to have two distinct incident faces.  A framed annular tangle has
degree-one boundary edges whose two darts lie on the same hole face.  Such a
bridge must occur twice and cancel over `F2`, not occur once.

This module defines the multiplicity-correct boundary map by summing the face
coefficient over the two darts above each edge.  It agrees with the existing
map in the two-sided case and remains correct on bridge edges.  This is the
linear-algebra interface needed to separate the faces along closed radial and
chord walls without pretending that the annular stub edges are two-sided.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OrbitFaceParityBoundary

open GoertzelV24FaceBoundaryLinearAlgebra
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceCycleSpace
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24PrimalCycleSpace
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The `F2` facial boundary map with dart multiplicity.  At each edge it
sums the labels of the two dart-side faces; if both darts belong to the same
face, that coefficient occurs twice and cancels. -/
def orbitFaceParityBoundaryLinearMap (RS : RotationSystem V E) :
    (OrbitFace RS → F2) →ₗ[F2] (E → F2) where
  toFun coefficients edge :=
    ∑ dart ∈ RS.dartsOn edge,
      coefficients (dartOrbitFace RS dart)
  map_add' := by
    intro left right
    funext edge
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
  map_smul' := by
    intro scalar coefficients
    funext edge
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]

@[simp] theorem orbitFaceParityBoundaryLinearMap_apply
    (RS : RotationSystem V E) (coefficients : OrbitFace RS → F2)
    (edge : E) :
    orbitFaceParityBoundaryLinearMap RS coefficients edge =
      ∑ dart ∈ RS.dartsOn edge,
        coefficients (dartOrbitFace RS dart) :=
  rfl

/-- The multiplicity-correct edge coordinate is the sum of the two dart-side
face labels, without a two-sidedness hypothesis. -/
theorem orbitFaceParityBoundaryLinearMap_apply_edgeOf
    (RS : RotationSystem V E) (coefficients : OrbitFace RS → F2)
    (dart : RS.D) :
    orbitFaceParityBoundaryLinearMap RS coefficients (RS.edgeOf dart) =
      coefficients (dartOrbitFace RS dart) +
        coefficients (dartOrbitFace RS (RS.alpha dart)) := by
  rw [orbitFaceParityBoundaryLinearMap_apply]
  have hdart : dart ∈ RS.dartsOn (RS.edgeOf dart) :=
    (RS.mem_dartsOn).2 rfl
  rw [RS.dartsOn_eq_pair_of_mem hdart]
  have hnotmem : dart ∉ ({RS.alpha dart} : Finset RS.D) := by
    simpa using (RS.alpha_fixfree dart).symm
  rw [Finset.sum_insert hnotmem, Finset.sum_singleton]

/-- A one-sided edge contributes zero: its repeated face coefficient cancels
over `F2`. -/
theorem orbitFaceParityBoundaryLinearMap_apply_edgeOf_eq_zero_of_sameFace
    (RS : RotationSystem V E) (coefficients : OrbitFace RS → F2)
    (dart : RS.D)
    (hsame : dartOrbitFace RS dart =
      dartOrbitFace RS (RS.alpha dart)) :
    orbitFaceParityBoundaryLinearMap RS coefficients (RS.edgeOf dart) = 0 := by
  rw [orbitFaceParityBoundaryLinearMap_apply_edgeOf, hsame]
  exact zmod2_add_self _

/-- On a two-sided rotation system, dart multiplicity and ordinary facial
support define the same boundary map. -/
theorem orbitFaceParityBoundaryLinearMap_eq_orbitFaceBoundaryLinearMap
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS) :
    orbitFaceParityBoundaryLinearMap RS =
      orbitFaceBoundaryLinearMap RS := by
  apply LinearMap.ext
  intro coefficients
  funext edge
  rcases RS.dartsOn_nonempty edge with ⟨dart, hdart⟩
  have hedge : RS.edgeOf dart = edge := (RS.mem_dartsOn).1 hdart
  rw [← hedge,
    orbitFaceParityBoundaryLinearMap_apply_edgeOf,
    orbitFaceBoundaryLinearMap_apply_edgeOf RS htwoSided]

/-- At every vertex, the sum of all multiplicity-correct facial-boundary
coordinates is zero.  Around the vertex, the second dart-side face of each
edge is the first dart-side face after one vertex-rotation step, so the two
finite sums cancel over `F2`. -/
theorem sum_incidentEdges_orbitFaceParityBoundaryLinearMap_eq_zero
    (RS : RotationSystem V E) (coefficients : OrbitFace RS → F2)
    (vertex : V) :
    ∑ edge ∈ RS.incidentEdges vertex,
        orbitFaceParityBoundaryLinearMap RS coefficients edge = 0 := by
  rw [RS.incidentEdges_eq_image_dartsAt vertex]
  rw [Finset.sum_image (RS.edgeOf_injOn_dartsAt vertex)]
  simp_rw [orbitFaceParityBoundaryLinearMap_apply_edgeOf]
  rw [Finset.sum_add_distrib]
  simp_rw [dartOrbitFace_alpha_eq_dartOrbitFace_rho]
  have hrhoImage :
      (RS.dartsAt vertex).image RS.rho = RS.dartsAt vertex := by
    ext dart
    constructor
    · intro hdart
      rcases Finset.mem_image.1 hdart with ⟨before, hbefore, rfl⟩
      simp only [RotationSystem.dartsAt, Finset.mem_filter,
        Finset.mem_univ, true_and] at hbefore ⊢
      exact (RS.vert_rho before).trans hbefore
    · intro hdart
      refine Finset.mem_image.2 ⟨RS.rho.symm dart, ?_, by simp⟩
      simp only [RotationSystem.dartsAt, Finset.mem_filter,
        Finset.mem_univ, true_and] at hdart ⊢
      calc
        RS.vertOf (RS.rho.symm dart) =
            RS.vertOf (RS.rho (RS.rho.symm dart)) :=
          (RS.vert_rho (RS.rho.symm dart)).symm
        _ = RS.vertOf dart := by simp
        _ = vertex := hdart
  have hrhoInjective : Set.InjOn RS.rho (RS.dartsAt vertex : Set RS.D) :=
    RS.rho.injective.injOn
  have hsumRotation :
      (∑ dart ∈ RS.dartsAt vertex,
          coefficients (dartOrbitFace RS (RS.rho dart))) =
        ∑ dart ∈ RS.dartsAt vertex,
          coefficients (dartOrbitFace RS dart) := by
    calc
      _ = ∑ dart ∈ (RS.dartsAt vertex).image RS.rho,
          coefficients (dartOrbitFace RS dart) :=
        (Finset.sum_image
          (f := fun dart => coefficients (dartOrbitFace RS dart))
          hrhoInjective).symm
      _ = _ := by rw [hrhoImage]
  rw [hsumRotation]
  exact zmod2_add_self _

private theorem f2_add_eq_zero_iff_eq (left right : F2) :
    left + right = 0 ↔ left = right := by
  constructor
  · intro hzero
    calc
      left = left + 0 := by simp
      _ = left + (right + right) := by rw [zmod2_add_self]
      _ = (left + right) + right := by rw [add_assoc]
      _ = right := by rw [hzero]; simp
  · rintro rfl
    exact zmod2_add_self _

/-- For a connected full facial dual, the kernel of the multiplicity-correct
boundary map consists exactly of constant face labels.  This needs no global
two-sidedness: a dual adjacency already supplies two distinct incident faces,
while a same-face bridge contributes zero automatically. -/
theorem mem_ker_orbitFaceParityBoundaryLinearMap_iff_constant
    (RS : RotationSystem V E)
    (hdual : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Connected)
    (coefficients : OrbitFace RS → F2) :
    coefficients ∈ LinearMap.ker
        (orbitFaceParityBoundaryLinearMap RS) ↔
      ∀ left right, coefficients left = coefficients right := by
  constructor
  · intro hkernel
    have hzero : orbitFaceParityBoundaryLinearMap RS coefficients = 0 :=
      (LinearMap.mem_ker).1 hkernel
    have hadjacent : ∀ {left right :
        AmbientFace (Finset.univ : Finset (OrbitFace RS))},
        (interiorDualGraph (orbitFaceBoundary RS)
          (Finset.univ : Finset (OrbitFace RS))).Adj left right →
          coefficients left.1 = coefficients right.1 := by
      intro left right hadj
      rcases (interiorDualGraph_adj_iff (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS))).1 hadj with
          ⟨hfaces, edge, _hedgeInterior, hedgeLeft, hedgeRight⟩
      rcases (mem_orbitFaceBoundary_iff RS left.1 edge).1 hedgeLeft with
        ⟨leftDart, hleftDart, hleftEdge⟩
      rcases (mem_orbitFaceBoundary_iff RS right.1 edge).1 hedgeRight with
        ⟨rightDart, hrightDart, hrightEdge⟩
      have hleftFace : dartOrbitFace RS leftDart = left.1 :=
        (mem_orbitFaceDarts_iff RS left.1 leftDart).1 hleftDart
      have hrightFace : dartOrbitFace RS rightDart = right.1 :=
        (mem_orbitFaceDarts_iff RS right.1 rightDart).1 hrightDart
      have hrightDartEq : rightDart = RS.alpha leftDart := by
        rcases RS.edge_fiber_two_cases hleftEdge hrightEdge with heq | heq
        · exfalso
          apply hfaces
          rw [← hleftFace, ← hrightFace, heq]
        · exact heq
      have hedgeZero := congrFun hzero (RS.edgeOf leftDart)
      rw [Pi.zero_apply,
        orbitFaceParityBoundaryLinearMap_apply_edgeOf] at hedgeZero
      apply (f2_add_eq_zero_iff_eq _ _).1 at hedgeZero
      have halphaFace :
          dartOrbitFace RS (RS.alpha leftDart) = right.1 := by
        rw [← hrightDartEq]
        exact hrightFace
      rwa [hleftFace, halphaFace] at hedgeZero
    intro left right
    let leftFace : AmbientFace (Finset.univ : Finset (OrbitFace RS)) :=
      ⟨left, Finset.mem_univ left⟩
    let rightFace : AmbientFace (Finset.univ : Finset (OrbitFace RS)) :=
      ⟨right, Finset.mem_univ right⟩
    change coefficients leftFace.1 = coefficients rightFace.1
    rcases hdual leftFace rightFace with ⟨walk⟩
    have hwalk : ∀ {start finish :
        AmbientFace (Finset.univ : Finset (OrbitFace RS))},
        (path : (interiorDualGraph (orbitFaceBoundary RS)
          (Finset.univ : Finset (OrbitFace RS))).Walk start finish) →
          coefficients start.1 = coefficients finish.1 := by
      intro start finish path
      induction path with
      | nil => rfl
      | @cons first second last hadj tail ih =>
          exact (hadjacent hadj).trans ih
    exact hwalk walk
  · intro hconstant
    rw [LinearMap.mem_ker]
    funext edge
    rcases RS.dartsOn_nonempty edge with ⟨dart, hdart⟩
    have hedge : RS.edgeOf dart = edge := (RS.mem_dartsOn).1 hdart
    rw [← hedge, orbitFaceParityBoundaryLinearMap_apply_edgeOf]
    rw [hconstant (dartOrbitFace RS (RS.alpha dart))
      (dartOrbitFace RS dart)]
    exact zmod2_add_self _

/-- The multiplicity-correct all-face boundary map has rank `F - 1` when the
full facial dual is connected. -/
theorem finrank_range_orbitFaceParityBoundaryLinearMap
    (RS : RotationSystem V E)
    (hdual : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Connected) :
    Module.finrank F2
        (LinearMap.range (orbitFaceParityBoundaryLinearMap RS)) =
      Fintype.card (OrbitFace RS) - 1 := by
  have hkernel : Module.finrank F2
      (LinearMap.ker (orbitFaceParityBoundaryLinearMap RS)) = 1 := by
    let allOnes : LinearMap.ker
        (orbitFaceParityBoundaryLinearMap RS) :=
      ⟨fun _ => 1,
        (mem_ker_orbitFaceParityBoundaryLinearMap_iff_constant
          RS hdual _).2 (fun _ _ => rfl)⟩
    apply finrank_eq_one allOnes
    · intro hzero
      have hvalue := congrFun (congrArg Subtype.val hzero)
        (dartOrbitFace RS RS.outer)
      change (1 : F2) = 0 at hvalue
      exact one_ne_zero hvalue
    · intro coefficients
      refine ⟨coefficients.1 (dartOrbitFace RS RS.outer), ?_⟩
      apply Subtype.ext
      funext face
      have hconstant :=
        (mem_ker_orbitFaceParityBoundaryLinearMap_iff_constant
          RS hdual coefficients.1).1 coefficients.2
      change coefficients.1 (dartOrbitFace RS RS.outer) * 1 =
        coefficients.1 face
      rw [mul_one]
      exact hconstant (dartOrbitFace RS RS.outer) face
  have hrankNullity :=
    (orbitFaceParityBoundaryLinearMap RS).finrank_range_add_finrank_ker
  rw [hkernel, Module.finrank_pi] at hrankNullity
  omega

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- For a graph-backed rotation, every multiplicity-correct facial-boundary
combination is a genuine graph cycle over `F2`, including when some edges have
the same quotient face on both dart sides. -/
theorem orbitFaceParityBoundaryLinearMap_mem_f2CycleSpace
    (data : Data G)
    (coefficients : OrbitFace data.toRotationSystem → F2) :
    orbitFaceParityBoundaryLinearMap data.toRotationSystem coefficients ∈
      f2CycleSpace G := by
  rw [f2CycleSpace, LinearMap.mem_ker]
  funext vertex
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    f2IncidenceMatrix]
  change (∑ edge : G.edgeSet,
    (if vertex ∈ (edge.1 : Sym2 V) then 1 else 0) *
      orbitFaceParityBoundaryLinearMap data.toRotationSystem coefficients edge) = 0
  calc
    _ = ∑ edge : G.edgeSet,
        if vertex ∈ (edge.1 : Sym2 V)
        then orbitFaceParityBoundaryLinearMap
          data.toRotationSystem coefficients edge else 0 := by
      apply Finset.sum_congr rfl
      intro edge _
      by_cases hvertex : vertex ∈ (edge.1 : Sym2 V) <;>
        simp [hvertex]
    _ = ∑ edge ∈ data.toRotationSystem.incidentEdges vertex,
        orbitFaceParityBoundaryLinearMap
          data.toRotationSystem coefficients edge := by
      rw [← Finset.sum_filter]
      congr 1
      ext edge
      simp [mem_toRotationSystem_incidentEdges_iff data]
    _ = 0 :=
      sum_incidentEdges_orbitFaceParityBoundaryLinearMap_eq_zero
        data.toRotationSystem coefficients vertex

/-- The range of the multiplicity-correct facial-boundary map lies in the
primal graph cycle space without a two-sidedness hypothesis. -/
theorem range_orbitFaceParityBoundaryLinearMap_le_f2CycleSpace
    (data : Data G) :
    LinearMap.range
        (orbitFaceParityBoundaryLinearMap data.toRotationSystem) ≤
      f2CycleSpace G := by
  rintro vector ⟨coefficients, rfl⟩
  exact orbitFaceParityBoundaryLinearMap_mem_f2CycleSpace data coefficients

/-- Euler's sphere equation alone identifies the multiplicity-correct facial
boundary rank with the connected graph cycle-space rank; cubicity is not used. -/
theorem orbitSphere_faceRank_eq_cycleRank_of_euler
    (data : Data G) (hconnected : G.Connected)
    (heuler : (Fintype.card V : Int) - Fintype.card G.edgeSet +
      Fintype.card (OrbitFace data.toRotationSystem) = 2) :
    Fintype.card (OrbitFace data.toRotationSystem) - 1 =
      Fintype.card G.edgeSet - (Fintype.card V - 1) := by
  have hvertices : 0 < Fintype.card V :=
    Fintype.card_pos_iff.mpr hconnected.nonempty
  omega

/-- On a connected cellular sphere graph with connected full facial dual,
the multiplicity-correct quotient facial boundaries span the entire `F2`
cycle space, even in the presence of bridge edges. -/
theorem range_orbitFaceParityBoundaryLinearMap_eq_f2CycleSpace
    (data : Data G)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (heuler : (Fintype.card V : Int) - Fintype.card G.edgeSet +
      Fintype.card (OrbitFace data.toRotationSystem) = 2) :
    LinearMap.range
        (orbitFaceParityBoundaryLinearMap data.toRotationSystem) =
      f2CycleSpace G := by
  apply Submodule.eq_of_le_of_finrank_eq
    (range_orbitFaceParityBoundaryLinearMap_le_f2CycleSpace data)
  rw [finrank_range_orbitFaceParityBoundaryLinearMap
      data.toRotationSystem hdual,
    finrank_f2CycleSpace_eq G hconnected]
  exact orbitSphere_faceRank_eq_cycleRank_of_euler
    data hconnected heuler

end

end GoertzelV24OrbitFaceParityBoundary

end Mettapedia.GraphTheory.FourColor
