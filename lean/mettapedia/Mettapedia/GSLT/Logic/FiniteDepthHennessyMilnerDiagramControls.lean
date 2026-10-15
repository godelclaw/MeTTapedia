import Mettapedia.GSLT.Logic.FiniteDepthHennessyMilnerDiagram

/-!
# Genuine observation refinement and dependent witness controls

An infinite branching system separates a branch from a stopped state at
depth one. Restriction identifies their depth-zero classes and therefore
has no inverse recovering every deeper class. A nonconstant family over
the atomic reading retains a supplied certificate at every greater depth.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.HennessyMilner.FiniteDepth.DiagramControls

open BehavioralCoverControls

theorem shallower_restriction_loses_a_real_distinction :
    restriction system 0 1 (by decide) (⟦State.branch false⟧ : Approximation system 1) =
      restriction system 0 1 (by decide) ⟦State.terminal 0⟧ ∧
      (⟦State.branch false⟧ : Approximation system 1) ≠ ⟦State.terminal 0⟧ :=
  QuotientControls.one_additional_round_separates_the_classes

theorem no_reconstruction_of_every_deeper_class :
    ¬ ∃ decoder : Approximation system 0 → Approximation system 1,
      ∀ value : Approximation system 1,
        decoder (restriction system 0 1 (by decide) value) = value := by
  rintro ⟨decoder, recovers⟩
  have same := congrArg decoder shallower_restriction_loses_a_real_distinction.1
  have impossible : (⟦State.branch false⟧ : Approximation system 1) = ⟦State.terminal 0⟧ :=
    (recovers ⟦State.branch false⟧).symm.trans (same.trans (recovers ⟦State.terminal 0⟧))
  exact shallower_restriction_loses_a_real_distinction.2 impossible

noncomputable def parityFamily (value : Approximation system 0) : Type := by
  classical
  exact if formulaPredicate system 0 (.atom .odd) (by decide) value then Fin 3 else Fin 1

theorem parity_family_really_varies :
    parityFamily ⟦State.terminal 1⟧ = Fin 3 ∧ parityFamily ⟦State.terminal 0⟧ = Fin 1 := by
  classical
  constructor
  · change (if observes .odd (.terminal 1) then Fin 3 else Fin 1) = Fin 3
    simp [observes]
  · change (if observes .odd (.terminal 0) then Fin 3 else Fin 1) = Fin 1
    simp [observes]

noncomputable def suppliedCertificate : parityFamily ⟦State.terminal 1⟧ :=
  cast parity_family_really_varies.1.symm (⟨2, by decide⟩ : Fin 3)

def certificateReadout (certificate : parityFamily ⟦State.terminal 1⟧) : Nat :=
  (cast parity_family_really_varies.1 certificate).val

theorem certificate_readout_is_supplied_value : certificateReadout suppliedCertificate = 2 := by
  simp [certificateReadout, suppliedCertificate]

theorem every_deeper_reading_recovers_supplied_certificate (depth : Nat) :
    certificateReadout
      (suppliedWitnessComparison system (Nat.zero_le depth) parityFamily (State.terminal 1)
        ((suppliedWitnessComparison system (Nat.zero_le depth) parityFamily (State.terminal 1)).symm
          suppliedCertificate)) = 2 := by
  exact (congrArg certificateReadout
    ((suppliedWitnessComparison system (Nat.zero_le depth) parityFamily
      (State.terminal 1)).apply_symm_apply suppliedCertificate)).trans
        certificate_readout_is_supplied_value

end Mettapedia.GSLT.HennessyMilner.FiniteDepth.DiagramControls
