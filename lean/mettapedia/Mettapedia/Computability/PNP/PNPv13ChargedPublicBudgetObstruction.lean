import Mettapedia.Computability.PNP.PNPv13NeutralSyntaxCouplingObstruction

/-!
# PNP v13: charged-public budget obstruction

This module studies the direct repair of the D.31/Definition-7 conflict in
which the complete public catalog is partitioned into pair-neutral primitives
and primitives with charged expansions.  It keeps D.48's exact opposite-phase
marginals, full public observability, and public-fiber target rigidity.

For each target coordinate, exact phase marginals put coupling probability one
on target-mismatched pairs.  Pair-neutral primitives cannot distinguish a
positive-mass pair.  If the charged primitives also failed to distinguish it,
the complete catalog would agree, hence the public instance and target would
agree.  Therefore the coupling mass of charged public disagreement is exactly
one at every target coordinate, and its coordinate sum is exactly the target
set cardinality.  Sharing or localizing a charged primitive between target
coordinates does not change this coordinate-summed identity.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

universe u v

/-- A charged public disagreement is witnessed by a charged catalog atom whose
Boolean values differ at the two coupling endpoints. -/
def V13ChargedPublicDisagreement
    {Omega : Type u} {Atom : Type v}
    (value : Atom -> Omega -> Bool) (charged : Atom -> Prop)
    (omega0 omega1 : Omega) : Prop :=
  exists atom, charged atom ∧ value atom omega0 ≠ value atom omega1

namespace V13FiniteCoupling

variable {Omega : Type u} [Fintype Omega]

/-- An event has probability one when every positive coupling atom belongs to
it.  This support form is the converse companion to
`event_of_probability_one_of_mass_pos`. -/
theorem probability_eq_one_of_mass_pos_imp
    (Gamma : V13FiniteCoupling Omega) (event : Omega -> Omega -> Prop)
    (hEvent : forall omega0 omega1,
      0 < Gamma.mass omega0 omega1 -> event omega0 omega1) :
    Gamma.probability event = 1 := by
  classical
  have hcomplement :
      Gamma.probability (fun omega0 omega1 => ¬ event omega0 omega1) = 0 := by
    rw [probability]
    apply Finset.sum_eq_zero
    intro omega0 _
    apply Finset.sum_eq_zero
    intro omega1 hmem
    have hnot : ¬ event omega0 omega1 := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hmem
    have hnotpos : ¬ 0 < Gamma.mass omega0 omega1 := by
      intro hpos
      exact hnot (hEvent omega0 omega1 hpos)
    exact le_antisymm (not_lt.mp hnotpos)
      (Gamma.mass_nonnegative omega0 omega1)
  have hpartition := Gamma.probability_add_probability_not event
  rw [hcomplement] at hpartition
  linarith

/-- Finite coupling core of the charged-public obstruction.  Exact
left-false/right-true marginals, support-wide neutrality of the uncharged
catalog, and extensional target determination force charged disagreement with
probability one. -/
theorem chargedPublicDisagreement_probability_one_of_opposite_phase_marginals
    {Atom : Type v}
    (Gamma : V13FiniteCoupling Omega) (target : Omega -> Bool)
    (value : Atom -> Omega -> Bool)
    (neutral charged : Atom -> Prop)
    (classified : forall atom, neutral atom ∨ charged atom)
    (neutral_eq_on_support : forall atom omega0 omega1,
      neutral atom -> 0 < Gamma.mass omega0 omega1 ->
        value atom omega0 = value atom omega1)
    (target_ext : forall omega0 omega1,
      (forall atom, value atom omega0 = value atom omega1) ->
        target omega0 = target omega1)
    (hleftTrue : Gamma.leftProbability (fun omega => target omega = true) = 0)
    (hrightFalse : Gamma.rightProbability (fun omega => target omega = false) = 0) :
    Gamma.probability
      (V13ChargedPublicDisagreement value charged) = 1 := by
  have hmismatch :=
    Gamma.target_mismatch_probability_one_of_opposite_phase_marginals
      target hleftTrue hrightFalse
  apply Gamma.probability_eq_one_of_mass_pos_imp
  intro omega0 omega1 hmass
  have htarget_ne := Gamma.event_of_probability_one_of_mass_pos hmismatch hmass
  by_cases hcharged :
      V13ChargedPublicDisagreement value charged omega0 omega1
  · exact hcharged
  · exfalso
    apply htarget_ne
    apply target_ext
    intro atom
    rcases classified atom with hneutral | hchargedAtom
    · exact neutral_eq_on_support atom omega0 omega1 hneutral hmass
    · by_contra hneq
      exact hcharged ⟨atom, hchargedAtom, hneq⟩

end V13FiniteCoupling

/-- Charged disagreement inside the exact complete public catalog of the v13
ensemble. -/
def V13D48ChargedPublicDisagreement
    (E : V13QuantitativeEnsemble)
    (theta : E.Parameter) (m t : Nat)
    (omega0 omega1 : E.World theta m t) : Prop :=
  exists primitive : E.PublicPrimitive theta m t,
    primitive ∈ E.fullPublicSyntax theta m t ∧
      E.chargedPrimitiveExpansion primitive ∧
        E.primitiveValue primitive omega0 ≠
          E.primitiveValue primitive omega1

/-- D.48 coupling mass carried by pairs distinguished by at least one charged
primitive in the complete public catalog. -/
noncomputable def V13D48ChargedPublicDisagreementMass
    {E : V13QuantitativeEnsemble} {G : V13M4LayeredGeometry E}
    {C : V13M4LocalComponents E G}
    (D48 : V13D48CompatibleCouplings E G C)
    (theta : E.Parameter) (m t : Nat)
    (j : E.TargetCoord theta m t) : Real :=
  let Gamma := D48.coupling theta m t j
  @V13FiniteCoupling.probability (E.World theta m t)
    (E.worldFintype theta m t) Gamma
    (V13D48ChargedPublicDisagreement E theta m t)

/-- The charged-public repair pays unit coupling mass at each target.  The
premises are existing v13 objects: exact D.48 marginals, full-catalog
neutral-or-charged coverage, Definition 7 support neutrality, extensional full
public observability, and public-fiber target rigidity. -/
theorem v13D48_chargedPublicDisagreementMass_eq_one
    {E : V13QuantitativeEnsemble} {G : V13M4LayeredGeometry E}
    {C : V13M4LocalComponents E G}
    (D48 : V13D48CompatibleCouplings E G C)
    (coverage : V13FullPublicSyntaxCoverage E)
    (fullSyntax : V13FullPublicSyntaxObservability E)
    (neutralCoherence : V13Definition7NeutralPairCoherence E G C D48)
    (theta : E.Parameter) (m t : Nat) (j : E.TargetCoord theta m t)
    (targetRigidOnPublicFiber : forall omega0 omega1 : E.World theta m t,
      E.publicInput omega0 = E.publicInput omega1 ->
        E.targetBit omega0 j = E.targetBit omega1 j) :
    V13D48ChargedPublicDisagreementMass D48 theta m t j = 1 := by
  letI := E.worldFintype theta m t
  let Gamma := D48.coupling theta m t j
  let Atom := {primitive : E.PublicPrimitive theta m t //
    primitive ∈ E.fullPublicSyntax theta m t}
  let target := fun omega : E.World theta m t => E.targetBit omega j
  let value := fun atom : Atom => E.primitiveValue atom.1
  let neutral := fun atom : Atom => E.declaredNeutralPrimitive atom.1
  let charged := fun atom : Atom => E.chargedPrimitiveExpansion atom.1
  have hclassified : forall atom : Atom, neutral atom ∨ charged atom := by
    intro atom
    exact coverage.every_primitive_classified theta m t atom.1 atom.2
  have hneutral : forall (atom : Atom)
      (omega0 omega1 : E.World theta m t),
      neutral atom -> 0 < Gamma.mass omega0 omega1 ->
        value atom omega0 = value atom omega1 := by
    intro atom omega0 omega1 hneutralAtom hmass
    exact neutralCoherence.pair_neutral_on_coupling_support
      theta m t j atom.1 atom.2 hneutralAtom omega0 omega1 hmass
  have htarget_ext : forall omega0 omega1 : E.World theta m t,
      (forall atom : Atom, value atom omega0 = value atom omega1) ->
        target omega0 = target omega1 := by
    intro omega0 omega1 hall
    apply targetRigidOnPublicFiber
    apply fullSyntax.publicInput_ext theta m t
    intro primitive hprimitive
    exact hall ⟨primitive, hprimitive⟩
  have hleftTrue :
      Gamma.leftProbability (fun omega => target omega = true) = 0 := by
    have h := D48.left_phase_marginal theta m t j
      (fun omega => E.targetBit omega j = true)
    simpa [Gamma, target, V13QuantitativeEnsemble.conditionalProbabilityAt,
      V13FiniteLaw.conditionalProbability, V13FiniteLaw.probability] using h
  have hrightFalse :
      Gamma.rightProbability (fun omega => target omega = false) = 0 := by
    have h := D48.right_phase_marginal theta m t j
      (fun omega => E.targetBit omega j = false)
    simpa [Gamma, target, V13QuantitativeEnsemble.conditionalProbabilityAt,
      V13FiniteLaw.conditionalProbability, V13FiniteLaw.probability] using h
  have hmass :=
    Gamma.chargedPublicDisagreement_probability_one_of_opposite_phase_marginals
      target value neutral charged hclassified hneutral htarget_ext
      hleftTrue hrightFalse
  have hevent :
      V13ChargedPublicDisagreement value charged =
        V13D48ChargedPublicDisagreement E theta m t := by
    funext omega0 omega1
    apply propext
    constructor
    · rintro ⟨atom, hchargedAtom, hneq⟩
      exact ⟨atom.1, atom.2, hchargedAtom, hneq⟩
    · rintro ⟨primitive, hprimitive, hchargedPrimitive, hneq⟩
      exact ⟨⟨primitive, hprimitive⟩, hchargedPrimitive, hneq⟩
  change Gamma.probability
    (V13D48ChargedPublicDisagreement E theta m t) = 1
  rw [← hevent]
  exact hmass

/-- Coordinate-summed charged-public disagreement mass on a finite target set. -/
noncomputable def V13D48ChargedPublicDisagreementTotal
    {E : V13QuantitativeEnsemble} {G : V13M4LayeredGeometry E}
    {C : V13M4LocalComponents E G}
    (D48 : V13D48CompatibleCouplings E G C)
    (theta : E.Parameter) (m t : Nat)
    (S : Finset (E.TargetCoord theta m t)) : Real :=
  S.sum fun j => V13D48ChargedPublicDisagreementMass D48 theta m t j

/-- Exact coefficient-one verdict for the charged-public budget fork. -/
theorem v13D48_chargedPublicDisagreementTotal_eq_card
    {E : V13QuantitativeEnsemble} {G : V13M4LayeredGeometry E}
    {C : V13M4LocalComponents E G}
    (D48 : V13D48CompatibleCouplings E G C)
    (coverage : V13FullPublicSyntaxCoverage E)
    (fullSyntax : V13FullPublicSyntaxObservability E)
    (neutralCoherence : V13Definition7NeutralPairCoherence E G C D48)
    (theta : E.Parameter) (m t : Nat)
    (S : Finset (E.TargetCoord theta m t))
    (targetRigidOnPublicFiber : forall
      (j : E.TargetCoord theta m t) (omega0 omega1 : E.World theta m t),
      E.publicInput omega0 = E.publicInput omega1 ->
        E.targetBit omega0 j = E.targetBit omega1 j) :
    V13D48ChargedPublicDisagreementTotal D48 theta m t S =
      (S.card : Real) := by
  rw [V13D48ChargedPublicDisagreementTotal]
  calc
    (∑ j ∈ S, V13D48ChargedPublicDisagreementMass D48 theta m t j) =
        ∑ _j ∈ S, (1 : Real) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact v13D48_chargedPublicDisagreementMass_eq_one
        D48 coverage fullSyntax neutralCoherence theta m t j
        (targetRigidOnPublicFiber j)
    _ = (S.card : Real) := by simp

/-- No strict subunit multiple of target cardinality can upper-bound the
charged-public disagreement total on a nonempty target set. -/
theorem v13D48_chargedPublicDisagreementTotal_not_subunit
    {E : V13QuantitativeEnsemble} {G : V13M4LayeredGeometry E}
    {C : V13M4LocalComponents E G}
    (D48 : V13D48CompatibleCouplings E G C)
    (coverage : V13FullPublicSyntaxCoverage E)
    (fullSyntax : V13FullPublicSyntaxObservability E)
    (neutralCoherence : V13Definition7NeutralPairCoherence E G C D48)
    (theta : E.Parameter) (m t : Nat)
    (S : Finset (E.TargetCoord theta m t)) (hS : S.Nonempty)
    (targetRigidOnPublicFiber : forall
      (j : E.TargetCoord theta m t) (omega0 omega1 : E.World theta m t),
      E.publicInput omega0 = E.publicInput omega1 ->
        E.targetBit omega0 j = E.targetBit omega1 j)
    {c : Real} (hc : c < 1) :
    ¬ V13D48ChargedPublicDisagreementTotal D48 theta m t S <=
        c * (S.card : Real) := by
  rw [v13D48_chargedPublicDisagreementTotal_eq_card
    D48 coverage fullSyntax neutralCoherence theta m t S
    targetRigidOnPublicFiber]
  have hcardNat : 0 < S.card := Finset.card_pos.mpr hS
  have hcard : 0 < (S.card : Real) := by exact_mod_cast hcardNat
  nlinarith

end Mettapedia.Computability.PNP
