import Mettapedia.Logic.GovernanceReasoning.Core

/-!
# Controls for the Deontic Traditional Scheme

Every theorem of `GovernanceReasoning.Core.DTS` holds of an arbitrary scheme `d : DTS P`.
This file gives a scheme with all three deontic statuses: over pairs of Booleans, `p` is
obligatory when both components are `true`, and negation flips the first component.
So `(true, true)` is obligatory, `(false, true)` is forbidden (its negation is
obligatory), and `(true, false)` is optional.

Positive: each theorem of `DTS` applies to this scheme, at the proposition of the status
it is about (`ob_implies_pe_tt`, …, `classify_optional_tf`).

Negative: obligation in this scheme is not trivial: `(true, false)` is not obligatory and
`(true, true)` is not optional (`not_ob_tf`, `not_op_tt`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.GovernanceReasoning.DTSControls

open Mettapedia.Logic.GovernanceReasoning.Core

/-- Obligation is truth of both components; negation flips the first one. -/
def sampleDTS : DTS (Bool × Bool) where
  ob p := p.1 = true ∧ p.2 = true
  neg p := (!p.1, p.2)
  neg_neg p := by simp
  consistent := by decide

theorem ob_tt : sampleDTS.ob (true, true) := ⟨rfl, rfl⟩

theorem ob_neg_ft : sampleDTS.ob (sampleDTS.neg (false, true)) := ⟨rfl, rfl⟩

theorem not_ob_ft : ¬ sampleDTS.ob (false, true) := fun h => Bool.false_ne_true h.1

/-- **Negative control.** The optional proposition is not obligatory. -/
theorem not_ob_tf : ¬ sampleDTS.ob (true, false) := fun h => Bool.false_ne_true h.2

theorem not_ob_neg_tf : ¬ sampleDTS.ob (sampleDTS.neg (true, false)) := fun h =>
  Bool.false_ne_true h.2

theorem op_tf : sampleDTS.op (true, false) := ⟨not_ob_tf, not_ob_neg_tf⟩

theorem not_pe_ft : ¬ sampleDTS.pe (false, true) := fun h => h ob_neg_ft

/-! ## Each theorem of `DTS`, applied -/

theorem ob_implies_pe_tt : sampleDTS.pe (true, true) :=
  DTS.ob_implies_pe sampleDTS (true, true) ob_tt

theorem pe_iff_not_ob_neg_tt : type_of% (DTS.pe_iff_not_ob_neg sampleDTS (true, true)) :=
  DTS.pe_iff_not_ob_neg sampleDTS (true, true)

theorem op_iff_tf : type_of% (DTS.op_iff sampleDTS (true, false)) :=
  DTS.op_iff sampleDTS (true, false)

theorem not_pe_implies_ob_neg_ft : sampleDTS.ob (sampleDTS.neg (false, true)) :=
  DTS.not_pe_implies_ob_neg sampleDTS (false, true) not_pe_ft

theorem not_op_iff_tt : type_of% (DTS.not_op_iff sampleDTS (true, true)) :=
  DTS.not_op_iff sampleDTS (true, true)

theorem pe_and_pe_neg_iff_op_tf : type_of% (DTS.pe_and_pe_neg_iff_op sampleDTS (true, false)) :=
  DTS.pe_and_pe_neg_iff_op sampleDTS (true, false)

/-- **Negative control.** The obligatory proposition is not optional. -/
theorem not_op_tt : ¬ sampleDTS.op (true, true) :=
  DTS.ob_implies_not_op sampleDTS (true, true) ob_tt

theorem pe_of_op_tf : sampleDTS.pe (true, false) :=
  DTS.pe_of_op sampleDTS (true, false) op_tf

theorem pe_neg_of_op_tf : sampleDTS.pe (sampleDTS.neg (true, false)) :=
  DTS.pe_neg_of_op sampleDTS (true, false) op_tf

theorem dts_trichotomy_tf : type_of% (DTS.dts_trichotomy sampleDTS (true, false)) :=
  DTS.dts_trichotomy sampleDTS (true, false)

theorem dts_exclusive_tf : type_of% (DTS.dts_exclusive sampleDTS (true, false)) :=
  DTS.dts_exclusive sampleDTS (true, false)

theorem ob_neg_implies_not_pe_ft : ¬ sampleDTS.pe (false, true) :=
  DTS.ob_neg_implies_not_pe sampleDTS (false, true) ob_neg_ft

theorem classify_obligatory_tt :
    type_of% (DTS.classify_obligatory sampleDTS (true, true) ob_tt) :=
  DTS.classify_obligatory sampleDTS (true, true) ob_tt

theorem classify_forbidden_ft :
    type_of% (DTS.classify_forbidden sampleDTS (false, true) not_ob_ft ob_neg_ft) :=
  DTS.classify_forbidden sampleDTS (false, true) not_ob_ft ob_neg_ft

theorem classify_optional_tf :
    type_of% (DTS.classify_optional sampleDTS (true, false) not_ob_tf not_ob_neg_tf) :=
  DTS.classify_optional sampleDTS (true, false) not_ob_tf not_ob_neg_tf

#print axioms classify_optional_tf
#print axioms not_op_tt
#print axioms dts_trichotomy_tf

end Mettapedia.Logic.GovernanceReasoning.DTSControls
