import Mettapedia.QuantumTheory.YangMills.V14HypercubicQuarticCensusCertificate

/-!
# Exact basis and coordinate duals for the hypercubic quartic census

This module turns the signed-orbit classification into four explicit orbit
averages.  It proves their action law, their Kronecker evaluation matrix at
the four admissible representatives, and reconstruction of every invariant
rational coefficient function.

The result is the exact basis theorem for the derivative-free Cartan quartic
restriction.  It does not promote that restriction to the full
noncommutative `SU(2)` `F,D` quotient.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace V14HypercubicQuarticCensus

open SU2LatticeFDCensusNoGo
open V14HypercubicFDCensus

/-! ## Signed action cocycles -/

theorem permutationCode_injective : Function.Injective permutationCode := by
  decide

theorem permutationCode_bijective : Function.Bijective permutationCode := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨permutationCode_injective, ?_⟩
  rw [Fintype.card_perm]
  decide

theorem planeActionPerm_compose_codes :
    ∀ left right : Fin 24, ∀ plane : OrientedPlane,
      planeActionPerm ((permutationCode right).trans
          (permutationCode left)) plane =
        planeActionPerm (permutationCode left)
          (planeActionPerm (permutationCode right) plane) := by
  decide

theorem planeActionPerm_compose :
    ∀ left right : Equiv.Perm Axis, ∀ plane : OrientedPlane,
      planeActionPerm (right.trans left) plane =
        planeActionPerm left (planeActionPerm right plane) := by
  intro left right plane
  obtain ⟨leftCode, rfl⟩ := permutationCode_bijective.2 left
  obtain ⟨rightCode, rfl⟩ := permutationCode_bijective.2 right
  exact planeActionPerm_compose_codes leftCode rightCode plane

theorem planeAction_compose (left right : Hypercubic4)
    (plane : OrientedPlane) :
    planeAction (Hypercubic4.compose left right) plane =
      planeAction left (planeAction right plane) :=
  planeActionPerm_compose left.perm right.perm plane

theorem planeEquiv_compose (left right : Hypercubic4) :
    planeEquiv (Hypercubic4.compose left right) =
      (planeEquiv right).trans (planeEquiv left) := by
  apply Equiv.ext
  intro plane
  exact planeAction_compose left right plane

theorem QuarticMonomial.act_compose (left right : Hypercubic4)
    (monomial : QuarticMonomial) :
    (monomial.act right).act left =
      monomial.act (Hypercubic4.compose left right) := by
  apply Sym.ext
  simp [QuarticMonomial.act, Sym.map, planeEquiv_compose,
    Multiset.map_map]

@[simp] theorem QuarticMonomial.act_one (monomial : QuarticMonomial) :
    monomial.act Hypercubic4.one = monomial := by
  apply Sym.ext
  simp [QuarticMonomial.act, Sym.map, planeEquiv, planeAction_one]

theorem QuarticMonomial.act_injective (h : Hypercubic4) :
    Function.Injective (QuarticMonomial.act h) := by
  intro left right heq
  have hinverse := congrArg
    (QuarticMonomial.act (Hypercubic4.inverse h)) heq
  simpa [QuarticMonomial.act_compose] using hinverse

/-- Integer sign of a reflected source axis. -/
def axisTensorSign (reflected : Axis → Bool) (axis : Axis) : ℤ :=
  if reflected axis then -1 else 1

theorem axisTensorSign_xor (left right : Bool) :
    axisTensorSign (fun _ => left ^^ right) 0 =
      axisTensorSign (fun _ => left) 0 * axisTensorSign (fun _ => right) 0 := by
  cases left <;> cases right <;> decide

theorem axisTensorSign_compose (left right : Hypercubic4) (axis : Axis) :
    axisTensorSign (Hypercubic4.compose left right).reflected axis =
      axisTensorSign right.reflected axis *
        axisTensorSign left.reflected (right.perm axis) := by
  cases hright : right.reflected axis <;>
    cases hleft : left.reflected (right.perm axis) <;>
    simp [axisTensorSign, Hypercubic4.compose, hright, hleft]

theorem axisTensorSign_sortedProduct :
    ∀ reflected : Axis → Bool, ∀ permutation : Equiv.Perm Axis,
      ∀ plane : OrientedPlane,
        axisTensorSign reflected
            (planeActionPerm permutation plane).first *
          axisTensorSign reflected
            (planeActionPerm permutation plane).second =
        axisTensorSign reflected (permutation plane.first) *
          axisTensorSign reflected (permutation plane.second) := by
  set_option maxRecDepth 10000 in
    decide

theorem planeReorderSign_compose :
    ∀ left right : Equiv.Perm Axis, ∀ plane : OrientedPlane,
      planeReorderSign
          (Hypercubic4.compose (unsignedHypercubic left)
            (unsignedHypercubic right)) plane =
        planeReorderSign (unsignedHypercubic right) plane *
          planeReorderSign (unsignedHypercubic left)
            (planeActionPerm right plane) := by
  set_option maxRecDepth 10000 in
    decide

theorem planeTensorSign_compose (left right : Hypercubic4)
    (plane : OrientedPlane) :
    planeTensorSign (Hypercubic4.compose left right) plane =
      planeTensorSign right plane *
        planeTensorSign left (planeAction right plane) := by
  change
    (axisTensorSign (Hypercubic4.compose left right).reflected plane.first *
        axisTensorSign (Hypercubic4.compose left right).reflected plane.second) *
        planeReorderSign (Hypercubic4.compose left right) plane = _
  rw [axisTensorSign_compose, axisTensorSign_compose]
  have hsorted := axisTensorSign_sortedProduct left.reflected right.perm plane
  have hreorder := planeReorderSign_compose left.perm right.perm plane
  change planeReorderSign (Hypercubic4.compose left right) plane = _ at hreorder
  rw [hreorder]
  change
    ((axisTensorSign right.reflected plane.first *
        axisTensorSign left.reflected (right.perm plane.first)) *
      (axisTensorSign right.reflected plane.second *
        axisTensorSign left.reflected (right.perm plane.second))) *
      (planeReorderSign right plane *
        planeReorderSign left (planeAction right plane)) =
      ((axisTensorSign right.reflected plane.first *
          axisTensorSign right.reflected plane.second) *
        planeReorderSign right plane) *
      ((axisTensorSign left.reflected
            (planeActionPerm right.perm plane).first *
          axisTensorSign left.reflected
            (planeActionPerm right.perm plane).second) *
        planeReorderSign left (planeAction right plane))
  rw [hsorted]
  ring

theorem multiset_tensorSign_compose (left right : Hypercubic4)
    (planes : Multiset OrientedPlane) :
    (planes.map (planeTensorSign (Hypercubic4.compose left right))).prod =
      (planes.map (planeTensorSign right)).prod *
        ((planes.map (planeAction right)).map
          (planeTensorSign left)).prod := by
  induction planes using Multiset.induction_on with
  | empty => simp
  | cons plane planes ih =>
      simp [planeTensorSign_compose]
      ring

theorem QuarticMonomial.tensorSign_compose (left right : Hypercubic4)
    (monomial : QuarticMonomial) :
    monomial.tensorSign (Hypercubic4.compose left right) =
      monomial.tensorSign right * (monomial.act right).tensorSign left := by
  exact multiset_tensorSign_compose left right monomial

@[simp] theorem QuarticMonomial.tensorSign_one
    (monomial : QuarticMonomial) :
    monomial.tensorSign Hypercubic4.one = 1 := by
  unfold QuarticMonomial.tensorSign
  have hplane (plane : OrientedPlane) :
      planeTensorSign Hypercubic4.one plane = 1 := by
    simp [planeTensorSign, planeReorderSign, OrientedPlane.ordered]
  simp [hplane]

theorem quartic_transport_sign_unique (coordinate : Fin 4)
    (left right : Hypercubic4) (target : QuarticMonomial)
    (hleft : (quarticRepresentative coordinate).act left = target)
    (hright : (quarticRepresentative coordinate).act right = target) :
    (quarticRepresentative coordinate).tensorSign left =
      (quarticRepresentative coordinate).tensorSign right := by
  let undo := Hypercubic4.inverse right
  have hleftStabilizes :
      (quarticRepresentative coordinate).act
          (Hypercubic4.compose undo left) =
        quarticRepresentative coordinate := by
    rw [← QuarticMonomial.act_compose]
    rw [hleft, ← hright]
    rw [QuarticMonomial.act_compose]
    simp [undo]
  have hleftSign := quartic_representative_stabilizer_positive coordinate
    (Hypercubic4.compose undo left) hleftStabilizes
  have hrightSign :
      (quarticRepresentative coordinate).tensorSign right *
          target.tensorSign undo = 1 := by
    rw [← hright]
    rw [← QuarticMonomial.tensorSign_compose]
    simp [undo]
  have hleftProduct :
      (quarticRepresentative coordinate).tensorSign left *
          target.tensorSign undo = 1 := by
    rw [← hleft]
    rw [← QuarticMonomial.tensorSign_compose]
    exact hleftSign
  have hundoNonzero : target.tensorSign undo ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hrightSign
    norm_num at hrightSign
  exact mul_right_cancel₀ hundoNonzero (hleftProduct.trans hrightSign.symm)

theorem quartic_orbit_act_iff (coordinate : Fin 4)
    (monomial : QuarticMonomial) (h : Hypercubic4) :
    InSignedOrbit (quarticRepresentative coordinate) (monomial.act h) ↔
      InSignedOrbit (quarticRepresentative coordinate) monomial := by
  constructor
  · rintro ⟨transport, htransport⟩
    refine ⟨Hypercubic4.compose (Hypercubic4.inverse h) transport, ?_⟩
    rw [← QuarticMonomial.act_compose, htransport]
    rw [QuarticMonomial.act_compose]
    simp
  · rintro ⟨transport, htransport⟩
    refine ⟨Hypercubic4.compose h transport, ?_⟩
    rw [← QuarticMonomial.act_compose, htransport]

theorem quartic_common_orbit_coordinate_unique
    (left right : Fin 4) (monomial : QuarticMonomial)
    (hleft : InSignedOrbit (quarticRepresentative left) monomial)
    (hright : InSignedOrbit (quarticRepresentative right) monomial) :
    left = right := by
  obtain ⟨leftTransport, hleftTransport⟩ := hleft
  obtain ⟨rightTransport, hrightTransport⟩ := hright
  apply quartic_representative_orbits_disjoint left right
  refine ⟨Hypercubic4.compose (Hypercubic4.inverse rightTransport)
    leftTransport, ?_⟩
  rw [← QuarticMonomial.act_compose, hleftTransport,
    ← hrightTransport]
  rw [QuarticMonomial.act_compose]
  simp

/-! ## Four explicit signed-orbit basis functions -/

/-- The signed orbit indicator.  On an admissible orbit the stabilizer theorem
makes the sign independent of the chosen transport; off that orbit it is
zero.  The use of finite choice is representational only, and its independence
is proved by `quartic_transport_sign_unique`. -/
noncomputable def quarticOrbitBasis (coordinate : Fin 4)
    (monomial : QuarticMonomial) : ℚ := by
  classical
  exact
    if horbit : InSignedOrbit (quarticRepresentative coordinate) monomial then
      ((quarticRepresentative coordinate).tensorSign
        (Classical.choose horbit) : ℚ)
    else 0

theorem quarticOrbitBasis_of_transport (coordinate : Fin 4)
    (monomial : QuarticMonomial) (transport : Hypercubic4)
    (htransport :
      (quarticRepresentative coordinate).act transport = monomial) :
    quarticOrbitBasis coordinate monomial =
      ((quarticRepresentative coordinate).tensorSign transport : ℚ) := by
  classical
  let horbit : InSignedOrbit (quarticRepresentative coordinate) monomial :=
    ⟨transport, htransport⟩
  rw [quarticOrbitBasis, dif_pos horbit]
  norm_cast
  apply quartic_transport_sign_unique coordinate
      (Classical.choose horbit) transport monomial
  · exact Classical.choose_spec horbit
  · exact htransport

theorem quarticOrbitBasis_eq_zero_of_not_orbit (coordinate : Fin 4)
    (monomial : QuarticMonomial)
    (hnot : ¬ InSignedOrbit (quarticRepresentative coordinate) monomial) :
    quarticOrbitBasis coordinate monomial = 0 := by
  classical
  simp [quarticOrbitBasis, hnot]

theorem quarticOrbitBasis_invariant (coordinate : Fin 4) :
    IsHypercubicQuarticCoefficient (quarticOrbitBasis coordinate) := by
  intro h monomial
  by_cases horbit :
      InSignedOrbit (quarticRepresentative coordinate) monomial
  · obtain ⟨transport, htransport⟩ := horbit
    rw [quarticOrbitBasis_of_transport coordinate monomial transport htransport]
    have hcomposed :
        (quarticRepresentative coordinate).act
            (Hypercubic4.compose h transport) = monomial.act h := by
      rw [← QuarticMonomial.act_compose, htransport]
    rw [quarticOrbitBasis_of_transport coordinate (monomial.act h)
      (Hypercubic4.compose h transport) hcomposed]
    rw [QuarticMonomial.tensorSign_compose, htransport]
    norm_cast
    ring
  · have hnotAct :
        ¬ InSignedOrbit (quarticRepresentative coordinate) (monomial.act h) := by
      simpa [quartic_orbit_act_iff] using horbit
    rw [quarticOrbitBasis_eq_zero_of_not_orbit coordinate monomial horbit,
      quarticOrbitBasis_eq_zero_of_not_orbit coordinate (monomial.act h) hnotAct]
    ring

theorem quarticOrbitBasis_at_representative (left right : Fin 4) :
    quarticOrbitBasis left (quarticRepresentative right) =
      if left = right then 1 else 0 := by
  split_ifs with heq
  · subst right
    simpa using
      (quarticOrbitBasis_of_transport left (quarticRepresentative left)
        Hypercubic4.one (by simp))
  · apply quarticOrbitBasis_eq_zero_of_not_orbit
    intro horbit
    exact heq (quartic_representative_orbits_disjoint left right horbit)

/-! ## Duals, reconstruction, and exact dimension -/

theorem quartic_invariant_zero_of_negative_stabilizer
    (coefficients : QuarticMonomial → ℚ)
    (hinvariant : IsHypercubicQuarticCoefficient coefficients)
    (monomial : QuarticMonomial)
    (hkilled : HasNegativeStabilizer monomial) :
    coefficients monomial = 0 := by
  obtain ⟨h, hfix, hnegative⟩ := hkilled
  have hcovariant := hinvariant h monomial
  rw [hfix, hnegative] at hcovariant
  norm_num at hcovariant ⊢
  linarith

theorem quartic_invariant_of_transport
    (coefficients : QuarticMonomial → ℚ)
    (hinvariant : IsHypercubicQuarticCoefficient coefficients)
    (coordinate : Fin 4) (monomial : QuarticMonomial)
    (transport : Hypercubic4)
    (htransport :
      (quarticRepresentative coordinate).act transport = monomial) :
    coefficients monomial =
      ((quarticRepresentative coordinate).tensorSign transport : ℚ) *
        coefficients (quarticRepresentative coordinate) := by
  simpa [htransport] using
    (hinvariant transport (quarticRepresentative coordinate))

theorem quarticOrbitBasis_eq_zero_of_other_orbit
    (basisCoordinate orbitCoordinate : Fin 4)
    (monomial : QuarticMonomial)
    (horbit : InSignedOrbit
      (quarticRepresentative orbitCoordinate) monomial)
    (hne : basisCoordinate ≠ orbitCoordinate) :
    quarticOrbitBasis basisCoordinate monomial = 0 := by
  apply quarticOrbitBasis_eq_zero_of_not_orbit
  intro hbasisOrbit
  exact hne (quartic_common_orbit_coordinate_unique
    basisCoordinate orbitCoordinate monomial hbasisOrbit horbit)

/-- Every invariant rational quartic coefficient function is reconstructed
from its four representative values.  Together with the identity evaluation
matrix below, this is the exact four-dimensional basis theorem. -/
theorem quartic_hypercubic_reconstruction
    (coefficients : QuarticMonomial → ℚ)
    (hinvariant : IsHypercubicQuarticCoefficient coefficients)
    (monomial : QuarticMonomial) :
    coefficients monomial =
      ∑ coordinate : Fin 4,
        coefficients (quarticRepresentative coordinate) *
          quarticOrbitBasis coordinate monomial := by
  classical
  rcases quartic_signedOrbit_classification monomial with horbit | hkilled
  · obtain ⟨coordinate, transport, htransport⟩ := horbit
    rw [quartic_invariant_of_transport coefficients hinvariant coordinate
      monomial transport htransport]
    rw [Finset.sum_eq_single coordinate]
    · rw [quarticOrbitBasis_of_transport coordinate monomial transport htransport]
      ring
    · intro other _ hother
      rw [quarticOrbitBasis_eq_zero_of_other_orbit other coordinate monomial
        ⟨transport, htransport⟩ hother]
      ring
    · simp
  · rw [quartic_invariant_zero_of_negative_stabilizer coefficients hinvariant
      monomial hkilled]
    symm
    apply Finset.sum_eq_zero
    intro coordinate _
    rw [quartic_invariant_zero_of_negative_stabilizer
      (quarticOrbitBasis coordinate)
      (quarticOrbitBasis_invariant coordinate) monomial hkilled]
    ring

/-- Evaluation at an admissible orbit representative: the certified dual
coordinate functional for the quartic basis. -/
def quarticDual (coordinate : Fin 4)
    (coefficients : QuarticMonomial → ℚ) : ℚ :=
  coefficients (quarticRepresentative coordinate)

theorem quarticDual_basis (dualCoordinate basisCoordinate : Fin 4) :
    quarticDual dualCoordinate (quarticOrbitBasis basisCoordinate) =
      if basisCoordinate = dualCoordinate then 1 else 0 := by
  exact quarticOrbitBasis_at_representative basisCoordinate dualCoordinate

/-- The basis-to-dual conditioning matrix is literally the `4 × 4` identity;
there is no imported numerical conditioning constant at dimension eight. -/
theorem quartic_conditioning_matrix_identity :
    (fun dualCoordinate basisCoordinate : Fin 4 =>
      quarticDual dualCoordinate (quarticOrbitBasis basisCoordinate)) =
      fun dualCoordinate basisCoordinate =>
        if basisCoordinate = dualCoordinate then 1 else 0 := by
  funext dualCoordinate basisCoordinate
  exact quarticDual_basis dualCoordinate basisCoordinate

theorem quartic_hypercubic_invariant_ext
    (left right : QuarticMonomial → ℚ)
    (hleft : IsHypercubicQuarticCoefficient left)
    (hright : IsHypercubicQuarticCoefficient right)
    (hcoordinates : ∀ coordinate : Fin 4,
      quarticDual coordinate left = quarticDual coordinate right) :
    left = right := by
  funext monomial
  rw [quartic_hypercubic_reconstruction left hleft monomial,
    quartic_hypercubic_reconstruction right hright monomial]
  apply Finset.sum_congr rfl
  intro coordinate _
  change quarticDual coordinate left * quarticOrbitBasis coordinate monomial =
    quarticDual coordinate right * quarticOrbitBasis coordinate monomial
  rw [hcoordinates coordinate]

/-- The four orbit basis functions are coordinate-independent: a vanishing
linear combination has four vanishing coefficients. -/
theorem quarticOrbitBasis_coordinate_independent
    (coordinates : Fin 4 → ℚ)
    (hzero : ∀ monomial : QuarticMonomial,
      (∑ coordinate : Fin 4,
        coordinates coordinate * quarticOrbitBasis coordinate monomial) = 0) :
    ∀ coordinate, coordinates coordinate = 0 := by
  classical
  intro coordinate
  have hatRepresentative := hzero (quarticRepresentative coordinate)
  simp only [quarticOrbitBasis_at_representative] at hatRepresentative
  rw [Finset.sum_eq_single coordinate] at hatRepresentative
  · simpa using hatRepresentative
  · intro other _ hother
    simp [hother]
  · simp

end V14HypercubicQuarticCensus
end YangMills
end QuantumTheory
end Mettapedia
