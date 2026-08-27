import Mettapedia.GraphTheory.FourColor.GoertzelV24SeamExchange
import Mettapedia.GraphTheory.FourColor.GoertzelV24CompositeSeamMultigraph
import Mettapedia.GraphTheory.FourColor.GoertzelV24StellarEuler

/-!
# Sphericity of the composed rotation system

The last field of the target map class.  Two closed sides that are discs, glued
by an orientation-reversing matching of `k` ports, compose to a spherical map.

The exchanged permutation of the seam exchange lives on the joint carrier of
both closed sides.  Reassociating that carrier into real darts and hub darts,
it is the disjoint sum of the composite's own face permutation and a *dipole*:
`k` parallel edges between the two hubs, whose face permutation is a fixed-point
free involution and so has exactly `k` orbits when the matching reverses
orientation.  Hence

    F(comp) + k = F(L̂) + F(R̂),

and with each closed side spherical the Euler count of the composite is `2`.
Edges are counted as orbits of the pairing throughout, and the two counts are
identified through the two-element fibres of a fixed-point free involution.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24CompositeSphericity

open Equiv Equiv.Perm
open GoertzelV24PermutationOrbitSurgery
open GoertzelV24OrbitCountCongr
open GoertzelV24SeamExchange
open GoertzelV24OpenTangleComposition
open GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24CompositeSeamMultigraph
open GoertzelV24RotationSpliceConstructor
open GoertzelV24FaceOrbitIncidence
open GoertzelV24StellarEuler

/-! ## Orbits of a fixed-point free involution -/

section Involution

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Powers of an involution are the identity or the involution. -/
theorem pow_apply_of_involutive {σ : Perm D} (hinv : ∀ x, σ (σ x) = x) (n : ℕ) (x : D) :
    (σ ^ n) x = x ∨ (σ ^ n) x = σ x := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
      rw [pow_succ', Perm.mul_apply]
      rcases ih with h | h
      · exact Or.inr (by rw [h])
      · exact Or.inl (by rw [h, hinv])

/-- **A fixed-point free involution has orbits of size two**, so the carrier is
twice the orbit count. -/
theorem card_eq_two_mul_orbitCount_of_involutive {σ : Perm D}
    (hinv : ∀ x, σ (σ x) = x) (hfree : ∀ x, σ x ≠ x) :
    Fintype.card D = 2 * orbitCount σ := by
  refine card_eq_mul_orbitCount (fun d => {d, σ d}) ?_ ?_
  · intro d x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl)
      · exact SameCycle.refl _ _
      · exact sameCycle_apply_left.2 (SameCycle.refl _ _)
    · intro h
      obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
      rcases pow_apply_of_involutive hinv n x with h' | h'
      · exact Or.inl (by rw [← hn, h'])
      · exact Or.inr (by rw [← hn, h', hinv])
  · intro d
    rw [Finset.card_insert_of_notMem (by simpa using (hfree d).symm), Finset.card_singleton]

end Involution

/-! ## The dipole -/

section Dipole

variable {L R : Type*} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
  (matching : L ≃ R) (ρL : Perm L) (ρR : Perm R)

/-- The face permutation of the hub dipole: rotate at the hubs, cross via the
matching. -/
def dipolePhi : Perm (L ⊕ R) :=
  Equiv.sumCongr ρL ρR * MatchedSeam.seamSwap matching

theorem dipolePhi_inl (b : L) : dipolePhi matching ρL ρR (Sum.inl b) = Sum.inr (ρR (matching b)) := by
  simp [dipolePhi, Perm.mul_apply]

theorem dipolePhi_inr (c : R) :
    dipolePhi matching ρL ρR (Sum.inr c) = Sum.inl (ρL (matching.symm c)) := by
  simp [dipolePhi, Perm.mul_apply]

/-- Under orientation reversal the dipole face permutation is an involution. -/
theorem dipolePhi_involutive (hrev : OrientationReversing matching ρL ρR) (x : L ⊕ R) :
    dipolePhi matching ρL ρR (dipolePhi matching ρL ρR x) = x := by
  rcases x with b | c
  · rw [dipolePhi_inl, dipolePhi_inr, hrev, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  · rw [dipolePhi_inr, dipolePhi_inl, hrev, Equiv.symm_apply_apply, Equiv.apply_symm_apply]

theorem dipolePhi_fixfree (x : L ⊕ R) : dipolePhi matching ρL ρR x ≠ x := by
  rcases x with b | c
  · rw [dipolePhi_inl]; exact Sum.inr_ne_inl
  · rw [dipolePhi_inr]; exact Sum.inl_ne_inr

/-- **The dipole has `k` faces.** -/
theorem orbitCount_dipolePhi (hrev : OrientationReversing matching ρL ρR) :
    orbitCount (dipolePhi matching ρL ρR) = Fintype.card L := by
  have h := card_eq_two_mul_orbitCount_of_involutive
    (dipolePhi_involutive matching ρL ρR hrev) (dipolePhi_fixfree matching ρL ρR)
  rw [Fintype.card_sum, Fintype.card_congr matching.symm] at h
  omega

end Dipole

/-! ## Reassociating the joint carrier -/

section Assembly

variable {V W I L J R : Type*}
  [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
  (left : OpenTangleData V I L) (right : OpenTangleData W J R)
  (matching : L ≃ R) (ρL : Perm L) (ρR : Perm R)

/-- Real darts first, hub darts second. -/
def reJoint : Joint I L J R ≃ ((I ⊕ L) ⊕ (J ⊕ R)) ⊕ (L ⊕ R) where
  toFun
    | Sum.inl (Sum.inl d) => Sum.inl (Sum.inl d)
    | Sum.inl (Sum.inr b) => Sum.inr (Sum.inl b)
    | Sum.inr (Sum.inl d) => Sum.inl (Sum.inr d)
    | Sum.inr (Sum.inr c) => Sum.inr (Sum.inr c)
  invFun
    | Sum.inl (Sum.inl d) => Sum.inl (Sum.inl d)
    | Sum.inl (Sum.inr d) => Sum.inr (Sum.inl d)
    | Sum.inr (Sum.inl b) => Sum.inl (Sum.inr b)
    | Sum.inr (Sum.inr c) => Sum.inr (Sum.inr c)
  left_inv := by rintro ((d | b) | (d | c)) <;> rfl
  right_inv := by rintro ((d | d) | (b | c)) <;> rfl

/-- The composite's face permutation, on its own dart carrier. -/
noncomputable def compositePhi : Perm (MatchedSeam.Dart (I ⊕ J) L R) :=
  (compositeDarts left right matching).rho * (compositeDarts left right matching).alpha

/-- It is the face permutation of the composed rotation system, so its orbits
are the quotient faces. -/
theorem orbitCount_compositePhi :
    orbitCount (compositePhi left right matching) =
      Fintype.card (OrbitFace (compositeRS left right matching)) :=
  Fintype.card_congr (Equiv.refl _)

/-- The composite's face permutation, read on the real-dart carrier. -/
noncomputable def realPhi : Perm ((I ⊕ L) ⊕ (J ⊕ R)) :=
  ((composeDartEquiv (I := I) (L := L) (J := J) (R := R)).trans
    (compositePhi left right matching)).trans
      (composeDartEquiv (I := I) (L := L) (J := J) (R := R)).symm

@[simp] theorem composeDartEquiv_symm_left_interior (i : I) :
    (composeDartEquiv (I := I) (L := L) (J := J) (R := R)).symm (Sum.inl (Sum.inl i)) =
      Sum.inl (Sum.inl i) := rfl

@[simp] theorem composeDartEquiv_symm_right_interior (j : J) :
    (composeDartEquiv (I := I) (L := L) (J := J) (R := R)).symm (Sum.inl (Sum.inr j)) =
      Sum.inr (Sum.inl j) := rfl

@[simp] theorem composeDartEquiv_symm_left_boundary (b : L) :
    (composeDartEquiv (I := I) (L := L) (J := J) (R := R)).symm (Sum.inr (Sum.inl b)) =
      Sum.inl (Sum.inr b) := rfl

@[simp] theorem composeDartEquiv_symm_right_boundary (c : R) :
    (composeDartEquiv (I := I) (L := L) (J := J) (R := R)).symm (Sum.inr (Sum.inr c)) =
      Sum.inr (Sum.inr c) := rfl

/-- Conjugation in the other direction preserves orbit counts too. -/
theorem orbitCount_conjEquiv' {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (σ : Perm β) :
    orbitCount ((e.trans σ).trans e.symm) = orbitCount σ := by
  have := orbitCount_conjEquiv e.symm σ
  simpa using this

/-- **The exchanged permutation is composite faces plus the dipole.** -/
theorem reJoint_phiS_univ :
    ((reJoint (I := I) (L := L) (J := J) (R := R)).symm.trans
        (phiS left right matching ρL ρR Finset.univ)).trans reJoint =
      Equiv.sumCongr (realPhi left right matching) (dipolePhi matching ρL ρR) := by
  ext x
  rcases x with ((i | b) | (j | c)) | (b | c) <;>
    simp [reJoint, phiS, jointRho, alphaFun, realPhi, dipolePhi, compositePhi, compositeDarts,
      MatchedSeam.Data.toRewiredDartSystem, composeData, Perm.mul_apply, Equiv.trans_apply]

/-- Orbit counts of the face permutation and of the quotient faces agree. -/
theorem orbitCount_phi_eq_card_orbitFace {V' E' : Type*} [Fintype V'] [DecidableEq V']
    [Fintype E'] [DecidableEq E'] (RS : RotationSystem V' E') :
    orbitCount RS.phi = Fintype.card (OrbitFace RS) :=
  Fintype.card_congr (Equiv.refl _)

/-- **The face count of the glue**: `F(comp) + k = F(L̂) + F(R̂)`. -/
theorem card_orbitFace_composite_add
    (hL : HubFacesDistinct left ρL) (hR : HubFacesDistinct right ρR)
    (hrev : OrientationReversing matching ρL ρR) :
    Fintype.card (OrbitFace (compositeRS left right matching)) + Fintype.card L =
      orbitCount (hubPhi left ρL) + orbitCount (hubPhi right ρR) := by
  rw [← orbitCount_phiS_univ left right matching ρL ρR hL hR hrev,
    ← orbitCount_conjEquiv (reJoint (I := I) (L := L) (J := J) (R := R)),
    reJoint_phiS_univ, orbitCount_sumCongr, orbitCount_dipolePhi matching ρL ρR hrev,
    realPhi, orbitCount_conjEquiv', orbitCount_compositePhi]

/-! ## Edge counts -/

/-- Every edge carries two darts, so darts are twice the edges. -/
theorem two_mul_card_edge {V' E' : Type*} [Fintype V'] [DecidableEq V']
    [Fintype E'] [DecidableEq E'] (RS : RotationSystem V' E') :
    2 * Fintype.card E' = Fintype.card RS.D := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset RS.D)) (t := (Finset.univ : Finset E')) (f := RS.edgeOf)
    (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_univ] at h
  rw [h]
  simp only [RS.edge_fiber_two, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  ring

/-- Darts are twice the pairing orbits. -/
theorem two_mul_orbitCount_alpha {V' E' : Type*} [Fintype V'] [DecidableEq V']
    [Fintype E'] [DecidableEq E'] (RS : RotationSystem V' E') :
    2 * orbitCount RS.alpha = Fintype.card RS.D :=
  (card_eq_two_mul_orbitCount_of_involutive RS.alpha_involutive RS.alpha_fixfree).symm

/-- Hub pairing orbits, counted on the closed side's carrier. -/
theorem two_mul_orbitCount_hubAlpha {V' I' B' : Type*} [Fintype I'] [DecidableEq I']
    [Fintype B'] [DecidableEq B'] (T : OpenTangleData V' I' B') :
    2 * orbitCount (hubAlpha T) = Fintype.card I' + 2 * Fintype.card B' := by
  have h := card_eq_two_mul_orbitCount_of_involutive (σ := hubAlpha T)
    (hubAlphaFun_involutive T) (by
      rintro ((i | b) | b)
      · simpa [hubAlphaFun] using T.interiorAlpha_fixfree i
      · simp [hubAlphaFun]
      · simp [hubAlphaFun])
  simp only [Fintype.card_sum] at h
  omega

/-! ## Sphericity -/

/-- **A closed side is spherical**: Euler's count on the hub closure, with the
hub as one extra vertex and edges counted as orbits of the pairing. -/
def ClosedSideSpherical {V' I' B' : Type*} [Fintype V'] [Fintype I'] [DecidableEq I']
    [Fintype B'] [DecidableEq B'] (T : OpenTangleData V' I' B') (ρ : Perm B') : Prop :=
  Fintype.card V' + 1 + orbitCount (hubPhi T ρ) = orbitCount (hubAlpha T) + 2

/-- **The composed rotation system is spherical.**  Two disc sides glued by an
orientation-reversing matching satisfy Euler's count `V − E + F = 2`, stated
without subtraction as `V + F = E + 2`. -/
theorem composite_euler
    (hL : HubFacesDistinct left ρL) (hR : HubFacesDistinct right ρR)
    (hrev : OrientationReversing matching ρL ρR)
    (hEL : ClosedSideSpherical left ρL) (hER : ClosedSideSpherical right ρR) :
    Fintype.card (V ⊕ W) + Fintype.card (OrbitFace (compositeRS left right matching)) =
      Fintype.card (compositeDarts left right matching).Edge + 2 := by
  have hF := card_orbitFace_composite_add left right matching ρL ρR hL hR hrev
  have hEc := two_mul_card_edge (compositeRS left right matching)
  have hDc : Fintype.card (compositeRS left right matching).D =
      Fintype.card I + Fintype.card J + 2 * Fintype.card L := by
    change Fintype.card (MatchedSeam.Dart (I ⊕ J) L R) = _
    simp only [MatchedSeam.Dart, Fintype.card_sum, Fintype.card_congr matching.symm]
    omega
  have hoL := two_mul_orbitCount_hubAlpha left
  have hoR := two_mul_orbitCount_hubAlpha right
  have hR' : Fintype.card R = Fintype.card L := Fintype.card_congr matching.symm
  unfold ClosedSideSpherical at hEL hER
  rw [Fintype.card_sum]
  omega

end Assembly

end GoertzelV24CompositeSphericity

end Mettapedia.GraphTheory.FourColor
