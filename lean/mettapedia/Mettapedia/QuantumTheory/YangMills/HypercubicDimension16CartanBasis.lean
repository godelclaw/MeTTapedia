import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanStabilizers

/-!
# Exact basis and conditioning at canonical dimension sixteen

The sparse census certificate yields seventeen signed orbit indicators on the
1,287-element unpadded Cartan carrier.  This module proves their covariance,
identity representative-dual matrix, reconstruction, independence, and exact
coefficient-sup conditioning constant one.

The norm is stated explicitly on this finite coefficient chart.  It is not an
unstated transfer from a Wilson analytic norm, and no value from a padded or
lower-dimensional carrier is reused.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16CartanCensus

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus
open SU2LatticeFDCensusNoGo

/-! ## Finite representative checks -/

/-- The seventeen representatives lie in pairwise distinct unsigned orbits. -/
theorem octic_representative_orbits_disjoint :
    ∀ left right : Fin 17,
      InSignedOcticOrbit (octicRepresentative left)
          (octicRepresentative right) →
        left = right := by
  simp only [InSignedOcticOrbit]
  intro left right htransport
  obtain ⟨h, hh⟩ := htransport
  have unsignedCheck : ∀ left right : Fin 17,
      ∀ permutation : Equiv.Perm Axis,
        (octicRepresentative left).act
            (unsignedHypercubic permutation) = octicRepresentative right →
          left = right := by
    set_option maxRecDepth 100000 in decide
  apply unsignedCheck left right h.perm
  exact (OcticMonomial.act_eq_unsigned h
    (octicRepresentative left)).symm.trans hh

theorem OcticMonomial.tensorSign_eq_one_or_neg_one
    (h : Hypercubic4) (monomial : OcticMonomial) :
    monomial.tensorSign h = 1 ∨ monomial.tensorSign h = -1 := by
  unfold OcticMonomial.tensorSign
  induction (monomial : Multiset OrientedPlane) using Multiset.induction_on with
  | empty => simp
  | cons plane planes ih =>
      rcases planeTensorSign_eq_one_or_neg_one h plane with hp | hp <;>
        rcases ih with hs | hs <;> simp [hp, hs]

/-! ## Signed transport and orbit indicators -/

theorem octic_transport_sign_unique (coordinate : Fin 17)
    (left right : Hypercubic4) (target : OcticMonomial)
    (hleft : (octicRepresentative coordinate).act left = target)
    (hright : (octicRepresentative coordinate).act right = target) :
    (octicRepresentative coordinate).tensorSign left =
      (octicRepresentative coordinate).tensorSign right := by
  let undo := Hypercubic4.inverse right
  have hleftStabilizes :
      (octicRepresentative coordinate).act
          (Hypercubic4.compose undo left) =
        octicRepresentative coordinate := by
    rw [← OcticMonomial.act_compose]
    rw [hleft, ← hright]
    rw [OcticMonomial.act_compose]
    simp [undo]
  have hleftSign := octic_representative_stabilizer_positive coordinate
    (Hypercubic4.compose undo left) hleftStabilizes
  have hrightSign :
      (octicRepresentative coordinate).tensorSign right *
          target.tensorSign undo = 1 := by
    rw [← hright]
    rw [← OcticMonomial.tensorSign_compose]
    simp [undo]
  have hleftProduct :
      (octicRepresentative coordinate).tensorSign left *
          target.tensorSign undo = 1 := by
    rw [← hleft]
    rw [← OcticMonomial.tensorSign_compose]
    exact hleftSign
  have hundoNonzero : target.tensorSign undo ≠ 0 := by
    rcases target.tensorSign_eq_one_or_neg_one undo with hsign | hsign <;>
      simp [hsign]
  exact mul_right_cancel₀ hundoNonzero
    (hleftProduct.trans hrightSign.symm)

theorem octic_orbit_act_iff (coordinate : Fin 17)
    (monomial : OcticMonomial) (h : Hypercubic4) :
    InSignedOcticOrbit (octicRepresentative coordinate) (monomial.act h) ↔
      InSignedOcticOrbit (octicRepresentative coordinate) monomial := by
  constructor
  · rintro ⟨transport, htransport⟩
    refine ⟨Hypercubic4.compose (Hypercubic4.inverse h) transport, ?_⟩
    rw [← OcticMonomial.act_compose, htransport]
    rw [OcticMonomial.act_compose]
    simp
  · rintro ⟨transport, htransport⟩
    refine ⟨Hypercubic4.compose h transport, ?_⟩
    rw [← OcticMonomial.act_compose, htransport]

theorem octic_common_orbit_coordinate_unique
    (left right : Fin 17) (monomial : OcticMonomial)
    (hleft : InSignedOcticOrbit (octicRepresentative left) monomial)
    (hright : InSignedOcticOrbit (octicRepresentative right) monomial) :
    left = right := by
  obtain ⟨leftTransport, hleftTransport⟩ := hleft
  obtain ⟨rightTransport, hrightTransport⟩ := hright
  apply octic_representative_orbits_disjoint left right
  refine ⟨Hypercubic4.compose (Hypercubic4.inverse rightTransport)
    leftTransport, ?_⟩
  rw [← OcticMonomial.act_compose, hleftTransport,
    ← hrightTransport]
  rw [OcticMonomial.act_compose]
  simp

/-- Signed orbit indicator.  Stabilizer positivity proves independence from
the chosen transporter. -/
noncomputable def octicOrbitBasis (coordinate : Fin 17)
    (monomial : OcticMonomial) : ℚ := by
  classical
  exact
    if horbit : InSignedOcticOrbit
        (octicRepresentative coordinate) monomial then
      ((octicRepresentative coordinate).tensorSign
        (Classical.choose horbit) : ℚ)
    else 0

theorem octicOrbitBasis_of_transport (coordinate : Fin 17)
    (monomial : OcticMonomial) (transport : Hypercubic4)
    (htransport :
      (octicRepresentative coordinate).act transport = monomial) :
    octicOrbitBasis coordinate monomial =
      ((octicRepresentative coordinate).tensorSign transport : ℚ) := by
  classical
  let horbit : InSignedOcticOrbit
      (octicRepresentative coordinate) monomial :=
    ⟨transport, htransport⟩
  rw [octicOrbitBasis, dif_pos horbit]
  norm_cast
  apply octic_transport_sign_unique coordinate
      (Classical.choose horbit) transport monomial
  · exact Classical.choose_spec horbit
  · exact htransport

theorem octicOrbitBasis_eq_zero_of_not_orbit (coordinate : Fin 17)
    (monomial : OcticMonomial)
    (hnot : ¬ InSignedOcticOrbit
      (octicRepresentative coordinate) monomial) :
    octicOrbitBasis coordinate monomial = 0 := by
  classical
  simp [octicOrbitBasis, hnot]

theorem octicOrbitBasis_invariant (coordinate : Fin 17) :
    IsHypercubicOcticCoefficient (octicOrbitBasis coordinate) := by
  intro h monomial
  by_cases horbit :
      InSignedOcticOrbit (octicRepresentative coordinate) monomial
  · obtain ⟨transport, htransport⟩ := horbit
    rw [octicOrbitBasis_of_transport coordinate monomial transport htransport]
    have hcomposed :
        (octicRepresentative coordinate).act
            (Hypercubic4.compose h transport) = monomial.act h := by
      rw [← OcticMonomial.act_compose, htransport]
    rw [octicOrbitBasis_of_transport coordinate (monomial.act h)
      (Hypercubic4.compose h transport) hcomposed]
    rw [OcticMonomial.tensorSign_compose, htransport]
    norm_cast
    ring
  · have hnotAct :
        ¬ InSignedOcticOrbit
          (octicRepresentative coordinate) (monomial.act h) := by
      simpa [octic_orbit_act_iff] using horbit
    rw [octicOrbitBasis_eq_zero_of_not_orbit coordinate monomial horbit,
      octicOrbitBasis_eq_zero_of_not_orbit coordinate (monomial.act h) hnotAct]
    ring

theorem octicOrbitBasis_at_representative (left right : Fin 17) :
    octicOrbitBasis left (octicRepresentative right) =
      if left = right then 1 else 0 := by
  split_ifs with heq
  · subst right
    simpa using
      (octicOrbitBasis_of_transport left (octicRepresentative left)
        Hypercubic4.one (by simp))
  · apply octicOrbitBasis_eq_zero_of_not_orbit
    intro horbit
    exact heq (octic_representative_orbits_disjoint left right horbit)

/-! ## Reconstruction and dual coordinates -/

theorem octic_invariant_zero_of_negative_stabilizer
    (coefficients : OcticMonomial → ℚ)
    (hinvariant : IsHypercubicOcticCoefficient coefficients)
    (monomial : OcticMonomial)
    (hkilled : HasNegativeOcticStabilizer monomial) :
    coefficients monomial = 0 := by
  obtain ⟨h, hfix, hnegative⟩ := hkilled
  have hcovariant := hinvariant h monomial
  rw [hfix, hnegative] at hcovariant
  norm_num at hcovariant ⊢
  linarith

theorem octic_invariant_of_transport
    (coefficients : OcticMonomial → ℚ)
    (hinvariant : IsHypercubicOcticCoefficient coefficients)
    (coordinate : Fin 17) (monomial : OcticMonomial)
    (transport : Hypercubic4)
    (htransport :
      (octicRepresentative coordinate).act transport = monomial) :
    coefficients monomial =
      ((octicRepresentative coordinate).tensorSign transport : ℚ) *
        coefficients (octicRepresentative coordinate) := by
  simpa [htransport] using
    (hinvariant transport (octicRepresentative coordinate))

theorem octicOrbitBasis_eq_zero_of_other_orbit
    (basisCoordinate orbitCoordinate : Fin 17)
    (monomial : OcticMonomial)
    (horbit : InSignedOcticOrbit
      (octicRepresentative orbitCoordinate) monomial)
    (hne : basisCoordinate ≠ orbitCoordinate) :
    octicOrbitBasis basisCoordinate monomial = 0 := by
  apply octicOrbitBasis_eq_zero_of_not_orbit
  intro hbasisOrbit
  exact hne (octic_common_orbit_coordinate_unique
    basisCoordinate orbitCoordinate monomial hbasisOrbit horbit)

theorem octic_hypercubic_reconstruction
    (coefficients : OcticMonomial → ℚ)
    (hinvariant : IsHypercubicOcticCoefficient coefficients)
    (monomial : OcticMonomial) :
    coefficients monomial =
      ∑ coordinate : Fin 17,
        coefficients (octicRepresentative coordinate) *
          octicOrbitBasis coordinate monomial := by
  classical
  rcases octic_signedOrbit_classification monomial with horbit | hkilled
  · obtain ⟨coordinate, transport, htransport⟩ := horbit
    rw [octic_invariant_of_transport coefficients hinvariant coordinate
      monomial transport htransport]
    rw [Finset.sum_eq_single coordinate]
    · rw [octicOrbitBasis_of_transport coordinate monomial transport htransport]
      ring
    · intro other _ hother
      rw [octicOrbitBasis_eq_zero_of_other_orbit other coordinate monomial
        ⟨transport, htransport⟩ hother]
      ring
    · simp
  · rw [octic_invariant_zero_of_negative_stabilizer coefficients hinvariant
      monomial hkilled]
    symm
    apply Finset.sum_eq_zero
    intro coordinate _
    rw [octic_invariant_zero_of_negative_stabilizer
      (octicOrbitBasis coordinate) (octicOrbitBasis_invariant coordinate)
      monomial hkilled]
    ring

def octicDual (coordinate : Fin 17)
    (coefficients : OcticMonomial → ℚ) : ℚ :=
  coefficients (octicRepresentative coordinate)

theorem octicDual_basis (dualCoordinate basisCoordinate : Fin 17) :
    octicDual dualCoordinate (octicOrbitBasis basisCoordinate) =
      if basisCoordinate = dualCoordinate then 1 else 0 :=
  octicOrbitBasis_at_representative basisCoordinate dualCoordinate

/-- The newly derived `17 × 17` conditioning matrix is the identity. -/
theorem octic_conditioning_matrix_identity :
    (fun dualCoordinate basisCoordinate : Fin 17 =>
      octicDual dualCoordinate (octicOrbitBasis basisCoordinate)) =
      fun dualCoordinate basisCoordinate =>
        if basisCoordinate = dualCoordinate then 1 else 0 := by
  funext dualCoordinate basisCoordinate
  exact octicDual_basis dualCoordinate basisCoordinate

theorem octicOrbitBasis_coordinate_independent
    (coordinates : Fin 17 → ℚ)
    (hzero : ∀ monomial : OcticMonomial,
      (∑ coordinate : Fin 17,
        coordinates coordinate * octicOrbitBasis coordinate monomial) = 0) :
    ∀ coordinate, coordinates coordinate = 0 := by
  classical
  intro coordinate
  have hatRepresentative := hzero (octicRepresentative coordinate)
  simp only [octicOrbitBasis_at_representative] at hatRepresentative
  rw [Finset.sum_eq_single coordinate] at hatRepresentative
  · simpa using hatRepresentative
  · intro other _ hother
    simp [hother]
  · simp

/-! ## Exact coefficient-sup conditioning -/

def octicSynthesis (coordinates : Fin 17 → ℚ) : OcticMonomial → ℚ :=
  fun monomial => ∑ coordinate : Fin 17,
    coordinates coordinate * octicOrbitBasis coordinate monomial

def HasOcticCoordinateSupBound
    (coordinates : Fin 17 → ℚ) (C : ℚ) : Prop :=
  ∀ coordinate, |coordinates coordinate| ≤ C

def HasOcticCoefficientSupBound
    (coefficients : OcticMonomial → ℚ) (C : ℚ) : Prop :=
  ∀ monomial, |coefficients monomial| ≤ C

def octicConditioningConstant : ℚ := 1

theorem octicSynthesis_coefficientSup_le
    (coordinates : Fin 17 → ℚ) {C : ℚ}
    (hC : 0 ≤ C)
    (hbound : HasOcticCoordinateSupBound coordinates C) :
    HasOcticCoefficientSupBound (octicSynthesis coordinates)
      (octicConditioningConstant * C) := by
  classical
  intro monomial
  rcases octic_signedOrbit_classification monomial with horbit | hkilled
  · obtain ⟨coordinate, transport, htransport⟩ := horbit
    have hvalue : octicSynthesis coordinates monomial =
        coordinates coordinate *
          ((octicRepresentative coordinate).tensorSign transport : ℚ) := by
      unfold octicSynthesis
      rw [Finset.sum_eq_single coordinate]
      · rw [octicOrbitBasis_of_transport coordinate monomial transport htransport]
      · intro other _ hother
        rw [octicOrbitBasis_eq_zero_of_other_orbit other coordinate monomial
          ⟨transport, htransport⟩ hother]
        ring
      · simp
    rw [hvalue, abs_mul]
    rcases (octicRepresentative coordinate).tensorSign_eq_one_or_neg_one
        transport with hsign | hsign <;>
      simp [hsign, octicConditioningConstant, hbound coordinate]
  · have hbasis (coordinate : Fin 17) :
        octicOrbitBasis coordinate monomial = 0 :=
      octic_invariant_zero_of_negative_stabilizer
        (octicOrbitBasis coordinate) (octicOrbitBasis_invariant coordinate)
        monomial hkilled
    simp [octicSynthesis, hbasis, octicConditioningConstant, hC]

theorem octicDual_coefficientSup_le
    (coefficients : OcticMonomial → ℚ) {C : ℚ}
    (hbound : HasOcticCoefficientSupBound coefficients C) :
    HasOcticCoordinateSupBound
      (fun coordinate => octicDual coordinate coefficients)
      (octicConditioningConstant * C) := by
  intro coordinate
  simpa [octicDual, octicConditioningConstant] using
    hbound (octicRepresentative coordinate)

def octicUnitCoordinate : Fin 17 → ℚ :=
  fun coordinate => if coordinate = 0 then 1 else 0

theorem octicConditioningConstant_sharp :
    HasOcticCoordinateSupBound octicUnitCoordinate 1 ∧
      |octicSynthesis octicUnitCoordinate (octicRepresentative 0)| = 1 := by
  constructor
  · intro coordinate
    by_cases hcoordinate : coordinate = 0 <;>
      simp [octicUnitCoordinate, hcoordinate]
  · simp [octicSynthesis, octicUnitCoordinate,
      octicOrbitBasis_at_representative]

/-- Complete finite packet for the canonical-dimension-sixteen Cartan rung. -/
theorem dimension16CartanCensus_packet :
    Fintype.card OcticMonomial = 1287 ∧
    (∀ monomial : OcticMonomial,
      (∃ coordinate : Fin 17,
        InSignedOcticOrbit (octicRepresentative coordinate) monomial) ∨
        HasNegativeOcticStabilizer monomial) ∧
    (∀ coordinate : Fin 17,
      IsHypercubicOcticCoefficient (octicOrbitBasis coordinate)) ∧
    ((fun dualCoordinate basisCoordinate : Fin 17 =>
      octicDual dualCoordinate (octicOrbitBasis basisCoordinate)) =
        fun dualCoordinate basisCoordinate =>
          if basisCoordinate = dualCoordinate then 1 else 0) ∧
    octicConditioningConstant = 1 := by
  exact ⟨card_octicMonomial, octic_signedOrbit_classification,
    octicOrbitBasis_invariant, octic_conditioning_matrix_identity, rfl⟩

end HypercubicDimension16CartanCensus
end YangMills
end QuantumTheory
end Mettapedia
