import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mettapedia.GraphTheory.FourColor.ColorAlgebra
import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceDualConnectedness
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceTwoSided

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FaceBoundaryLinearAlgebra

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceTwoSided

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The `F2` boundary map from quotient-face coefficients to primal-edge
coefficients. A face contributes its coefficient exactly on its boundary. -/
def orbitFaceBoundaryLinearMap (RS : RotationSystem V E) :
    (OrbitFace RS → F2) →ₗ[F2] (E → F2) where
  toFun coefficients edge :=
    ∑ face : OrbitFace RS,
      if edge ∈ orbitFaceBoundary RS face then coefficients face else 0
  map_add' := by
    intro left right
    funext edge
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro face _
    split_ifs <;> simp
  map_smul' := by
    intro scalar coefficients
    funext edge
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro face _
    split_ifs <;> simp

@[simp]
theorem orbitFaceBoundaryLinearMap_apply
    (RS : RotationSystem V E) (coefficients : OrbitFace RS → F2)
    (edge : E) :
    orbitFaceBoundaryLinearMap RS coefficients edge =
      ∑ face : OrbitFace RS,
        if edge ∈ orbitFaceBoundary RS face then coefficients face else 0 :=
  rfl

/-- On a two-sided map, an edge coordinate is the sum of the coefficients of
its two dart-side quotient faces. -/
theorem orbitFaceBoundaryLinearMap_apply_edgeOf
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (coefficients : OrbitFace RS → F2) (dart : RS.D) :
    orbitFaceBoundaryLinearMap RS coefficients (RS.edgeOf dart) =
      coefficients (dartOrbitFace RS dart) +
        coefficients (dartOrbitFace RS (RS.alpha dart)) := by
  rw [orbitFaceBoundaryLinearMap_apply]
  calc
    (∑ face : OrbitFace RS,
        if RS.edgeOf dart ∈ orbitFaceBoundary RS face
        then coefficients face else 0) =
        ∑ face ∈ (Finset.univ.filter fun face : OrbitFace RS =>
          RS.edgeOf dart ∈ orbitFaceBoundary RS face), coefficients face := by
      rw [Finset.sum_filter]
    _ = ∑ face ∈
        ({dartOrbitFace RS dart,
          dartOrbitFace RS (RS.alpha dart)} : Finset (OrbitFace RS)),
          coefficients face := by
      rw [orbitFace_incidentFaces_eq_dartSide_pair RS htwoSided dart]
    _ = coefficients (dartOrbitFace RS dart) +
        coefficients (dartOrbitFace RS (RS.alpha dart)) := by
      simp [htwoSided dart]

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

/-- The only relation among all quotient facial boundaries of a connected
two-sided facial dual is the constant coefficient relation. -/
theorem mem_ker_orbitFaceBoundaryLinearMap_iff_constant
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (hdual : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Connected)
    (coefficients : OrbitFace RS → F2) :
    coefficients ∈ LinearMap.ker (orbitFaceBoundaryLinearMap RS) ↔
      ∀ left right, coefficients left = coefficients right := by
  constructor
  · intro hkernel
    have hzero : orbitFaceBoundaryLinearMap RS coefficients = 0 :=
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
        orbitFaceBoundaryLinearMap_apply_edgeOf RS htwoSided] at hedgeZero
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
    rw [← hedge, orbitFaceBoundaryLinearMap_apply_edgeOf RS htwoSided]
    rw [hconstant (dartOrbitFace RS (RS.alpha dart))
      (dartOrbitFace RS dart)]
    exact zmod2_add_self _

/-- For a connected two-sided facial dual, the kernel of the all-face
boundary map has dimension one. -/
theorem finrank_ker_orbitFaceBoundaryLinearMap_eq_one
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (hdual : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Connected) :
    Module.finrank F2 (LinearMap.ker (orbitFaceBoundaryLinearMap RS)) = 1 := by
  let allOnes : LinearMap.ker (orbitFaceBoundaryLinearMap RS) :=
    ⟨fun _ => 1, (mem_ker_orbitFaceBoundaryLinearMap_iff_constant
      RS htwoSided hdual _).2 (fun _ _ => rfl)⟩
  apply finrank_eq_one allOnes
  · intro hzero
    have hvalue := congrFun (congrArg Subtype.val hzero)
      (dartOrbitFace RS RS.outer)
    simpa [allOnes] using hvalue
  · intro coefficients
    refine ⟨coefficients.1 (dartOrbitFace RS RS.outer), ?_⟩
    apply Subtype.ext
    funext face
    have hconstant :=
      (mem_ker_orbitFaceBoundaryLinearMap_iff_constant
        RS htwoSided hdual coefficients.1).1 coefficients.2
    change coefficients.1 (dartOrbitFace RS RS.outer) * 1 =
      coefficients.1 face
    rw [mul_one]
    exact hconstant (dartOrbitFace RS RS.outer) face

/-- Connected two-sided quotient facial boundaries span an `(F - 1)`-
dimensional subspace of the primal edge space. -/
theorem finrank_range_orbitFaceBoundaryLinearMap
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (hdual : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Connected) :
    Module.finrank F2 (LinearMap.range (orbitFaceBoundaryLinearMap RS)) =
      Fintype.card (OrbitFace RS) - 1 := by
  have hrankNullity :=
    (orbitFaceBoundaryLinearMap RS).finrank_range_add_finrank_ker
  rw [finrank_ker_orbitFaceBoundaryLinearMap_eq_one RS htwoSided hdual,
    Module.finrank_pi] at hrankNullity
  omega

end

end GoertzelV24FaceBoundaryLinearAlgebra

end Mettapedia.GraphTheory.FourColor
