import Mettapedia.OSLF.Framework.RhoScopedInstrumentAdmission
import Mettapedia.OSLF.Framework.RhoScopedFundedInspection

/-!
# Actual funded modal questions in the binding observer logic

Closed fixed-point-free questions are compiled into original proper
interaction formulas, retaining their ambient variable context. The
independent original transition relation and the binding-base action agree
through their earned quotient cover. Boxes use the classical Boolean
dual, and no structural instrument is added by this compilation.

Every finite greatest-fixed-point assay stage therefore has the same
meaning in the original operational system and in every binding instrument
kit. This comparison does not turn finite confirmation into a certificate
of the full greatest fixed point.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.RhoScopedInstrumentQuestionTranslation

open Mettapedia.OSLF.Binding RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open ScopedEncoding ScopedInstruments RhoScopedInstrumentProperBase RhoScopedFundedInspection
open Mettapedia.Logic.ModalMuCalculus

abbrev InstrumentFormula (context : Ctx sig) :=
  ScopedInstruments.Formula sig Empty ProperLabel (context, Srt.pr)

def truth (context : Ctx sig) : InstrumentFormula context :=
  @SortedInstrumentCongruence.Formula.top (signature sig) Empty ProperLabel (context, Srt.pr)

def translate {context : Ctx sig} (formula : Formula (Process context) 0)
    (finite : formula.isHML = true) : InstrumentFormula context :=
  match formula with
  | .tt => truth context
  | .ff => .neg (truth context)
  | .neg inner => .neg (translate inner finite)
  | .conj first second => .conj (fun flag : Bool =>
      if flag then translate second (Bool.and_eq_true_iff.mp finite).2
      else translate first (Bool.and_eq_true_iff.mp finite).1)
  | .disj first second => .neg (.conj (fun flag : Bool =>
      if flag then .neg (translate second (Bool.and_eq_true_iff.mp finite).2)
      else .neg (translate first (Bool.and_eq_true_iff.mp finite).1)))
  | .diamond label inner => .proper ⟨context, label⟩ (context, Srt.pr) (translate inner finite)
  | .box label inner => .neg (.proper ⟨context, label⟩ (context, Srt.pr) (.neg (translate inner finite)))
  | .mu _ => False.elim (Bool.false_ne_true finite)
  | .nu _ => False.elim (Bool.false_ne_true finite)
  | .var impossible => impossible.elim0

theorem proper_exists_iff (admitted : RhoScopedParallelEvents.SourceRule → Prop)
    {context : Ctx sig} (label : Process context) (before : Term sig context Srt.pr)
    (predicate : Process context → Prop) :
    (∃ after : Term sig context Srt.pr,
      (base admitted).act (source := (context, Srt.pr)) (target := (context, Srt.pr))
        ⟨context, label⟩ before after ∧ predicate (project after)) ↔
      ∃ after : Process context, (originalLTS admitted context).trans (project before) label after ∧
        predicate after := by
  constructor
  · rintro ⟨after, fired, postcondition⟩
    exact ⟨project after, (proper_iff_original admitted label before after).mp fired, postcondition⟩
  · rintro ⟨after, fired, postcondition⟩
    refine ⟨Quotient.out after, ?_, ?_⟩
    · apply (proper_iff_original admitted label before _).mpr
      simpa only [project, originalLTS, Quotient.out_eq] using fired
    · simpa only [project, Quotient.out_eq] using postcondition

theorem translation_allowed {context : Ctx sig} (formula : Formula (Process context) 0)
    (finite : formula.isHML = true) (opened : Constructor sig → Prop) :
    SortedInstrumentCongruence.Formula.Allowed opened (translate formula finite) := by
  cases formula <;> simp only [translate, SortedInstrumentCongruence.Formula.Allowed]
  case tt => exact fun impossible => impossible.elim
  case ff => exact fun impossible => impossible.elim
  case neg inner => exact translation_allowed inner finite opened
  case conj first second =>
      intro flag
      cases flag
      · exact translation_allowed first (Bool.and_eq_true_iff.mp finite).1 opened
      · exact translation_allowed second (Bool.and_eq_true_iff.mp finite).2 opened
  case disj first second =>
      intro flag
      cases flag
      · exact translation_allowed first (Bool.and_eq_true_iff.mp finite).1 opened
      · exact translation_allowed second (Bool.and_eq_true_iff.mp finite).2 opened
  case diamond label inner => exact translation_allowed inner finite opened
  case box label inner => exact translation_allowed inner finite opened
  case mu inner => exact False.elim (Bool.false_ne_true finite)
  case nu inner => exact False.elim (Bool.false_ne_true finite)
  case var impossible => exact impossible.elim0

theorem translation_truth (admitted : RhoScopedParallelEvents.SourceRule → Prop)
    {context : Ctx sig} (formula : Formula (Process context) 0) (finite : formula.isHML = true)
    (value : Term sig context Srt.pr) :
    ScopedInstruments.Holds (base admitted) (translate formula finite) value ↔
      satisfies (originalLTS admitted context) Env.empty formula (project value) := by
  classical
  cases formula <;> simp only [translate, ScopedInstruments.Holds]
  case tt => simp [truth, SortedInstrumentCongruence.Formula.top, ScopedInstruments.Holds, satisfies]
  case ff => simp [truth, SortedInstrumentCongruence.Formula.top, ScopedInstruments.Holds, satisfies]
  case neg inner => exact not_congr (translation_truth admitted inner finite value)
  case conj first second =>
      change (∀ flag : Bool, ScopedInstruments.Holds (base admitted)
        (if flag then translate second (Bool.and_eq_true_iff.mp finite).2
         else translate first (Bool.and_eq_true_iff.mp finite).1) value) ↔ _
      rw [Bool.forall_bool]
      exact and_congr (translation_truth admitted first (Bool.and_eq_true_iff.mp finite).1 value)
        (translation_truth admitted second (Bool.and_eq_true_iff.mp finite).2 value)
  case disj first second =>
      change (¬ ∀ flag : Bool, ScopedInstruments.Holds (base admitted)
        (if flag then .neg (translate second (Bool.and_eq_true_iff.mp finite).2)
         else .neg (translate first (Bool.and_eq_true_iff.mp finite).1)) value) ↔ _
      rw [Bool.forall_bool]
      change (¬ (¬ ScopedInstruments.Holds (base admitted) (translate first (Bool.and_eq_true_iff.mp finite).1) value ∧
        ¬ ScopedInstruments.Holds (base admitted) (translate second (Bool.and_eq_true_iff.mp finite).2) value)) ↔ _
      rw [not_and_or, not_not, not_not]
      exact or_congr (translation_truth admitted first (Bool.and_eq_true_iff.mp finite).1 value)
        (translation_truth admitted second (Bool.and_eq_true_iff.mp finite).2 value)
  case diamond label inner =>
      change (∃ after : Term sig context Srt.pr,
        (base admitted).act (source := (context, Srt.pr)) (target := (context, Srt.pr))
          ⟨context, label⟩ value after ∧ ScopedInstruments.Holds (base admitted) (translate inner finite) after) ↔ _
      exact (exists_congr (fun after => and_congr_right (fun _ =>
        translation_truth admitted inner finite after))).trans
          (proper_exists_iff admitted label value _)
  case box label inner =>
      change (¬ ∃ after : Term sig context Srt.pr,
        (base admitted).act (source := (context, Srt.pr)) (target := (context, Srt.pr))
          ⟨context, label⟩ value after ∧ ¬ ScopedInstruments.Holds (base admitted) (translate inner finite) after) ↔ _
      have comparison :
          (∃ after : Term sig context Srt.pr,
            (base admitted).act (source := (context, Srt.pr)) (target := (context, Srt.pr))
              ⟨context, label⟩ value after ∧ ¬ ScopedInstruments.Holds (base admitted) (translate inner finite) after) ↔
          ∃ after : Process context, (originalLTS admitted context).trans (project value) label after ∧
            ¬ satisfies (originalLTS admitted context) Env.empty inner after :=
        (exists_congr (fun after => and_congr_right (fun _ =>
        not_congr (translation_truth admitted inner finite after)))).trans
          (proper_exists_iff admitted label value
            (fun after => ¬ satisfies (originalLTS admitted context) Env.empty inner after))
      simpa only [not_exists, not_and, not_not, satisfies, LTS.successors, Set.mem_ofPred_eq] using not_congr comparison
  case mu inner => exact False.elim (Bool.false_ne_true finite)
  case nu inner => exact False.elim (Bool.false_ne_true finite)
  case var impossible => exact impossible.elim0

def stage {context : Ctx sig} (question : Question context) : InstrumentFormula context :=
  translate (question.1.atStage question.2) (question.1.stage_admitted question.2)

theorem stage_truth (admitted : RhoScopedParallelEvents.SourceRule → Prop)
    {context : Ctx sig} (question : Question context) (value : Term sig context Srt.pr) :
    ScopedInstruments.Holds (base admitted) (stage question) value ↔
      StageCertificate admitted question Mettapedia.GSLT.Causality.ComplementaryAssay.Verdict.confirm
        (project value) :=
  translation_truth admitted _ _ value

end Mettapedia.OSLF.Framework.RhoScopedInstrumentQuestionTranslation
