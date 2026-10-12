import Mettapedia.OSLF.Syntax.RhoPayloadAdmittedReflection
import Mettapedia.GSLT.Core.IndexedOperational

/-!
# The admitted authored runtime in the payload rho theory

The target relation is independently interpreted from the payload COMM and
parallel-congruence rules. Every admitted source state has a total translation;
equations are preserved and reflected, and every target step from a translated
state lifts to an admitted authored firing. Coverage concerns the image of the
translation, without asserting that every payload term is admitted source code.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.RhoPayloadParameterizedRuntime

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.RhoPayloadPresentation
open Mettapedia.OSLF.MeTTaIL.Syntax (rhoReflectivePresentation)
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical (canonicalize)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
open Mettapedia.GSLT Mettapedia.GSLT.Ultrainfinite Mettapedia.GSLT.IndexedOperational

/-- The target's one-step relation uses its own rule interpretation and
equation classes, independently of the source executor. -/
def classStep (before after : Cls [] Srt.pr) : Prop :=
  Steps strictRules (Quotient.out before) (Quotient.out after)

theorem classStep_cls (before after : Term sig [] Srt.pr) :
    classStep (cls before) (cls after) ↔ Steps strictRules before after := by
  have beforeEq : EqClosure equations (Quotient.out (cls before)) before :=
    cls_eq_iff.mp (Quotient.out_eq _)
  have afterEq : EqClosure equations (Quotient.out (cls after)) after :=
    cls_eq_iff.mp (Quotient.out_eq _)
  exact ⟨steps_of_equiv beforeEq.symm afterEq,
    steps_of_equiv beforeEq afterEq.symm⟩

def targetTheory : GSLT where
  Term := Cls [] Srt.pr
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := classStep
  rewrites_resp_left := by
    intro first second final equal step
    cases equal
    exact ⟨final, step, rfl⟩
  rewrites_resp_right := by
    intro first second final step equal
    cases equal
    exact step

variable {free : FreeSortContext}
variable (namesOnly : ∀ x, free x ≠ some rhoReflectivePresentation.processSort)

def decode (process : ParameterizedRewriteSystem.Process free) : Term sig [] Srt.pr :=
  Classical.choose (closed_admitted_translates namesOnly
    ((ParameterizedRewriteSystem.process_iff _ _).mp process.2).1
    ((ParameterizedRewriteSystem.process_iff _ _).mp process.2).2)

theorem decode_spec (process : ParameterizedRewriteSystem.Process free) :
    tProc (Env.empty []) process.1 = some (decode namesOnly process) :=
  Classical.choose_spec (closed_admitted_translates namesOnly
    ((ParameterizedRewriteSystem.process_iff _ _).mp process.2).1
    ((ParameterizedRewriteSystem.process_iff _ _).mp process.2).2)

def mapClass (process : ParameterizedRewriteSystem.Process free) : targetTheory.Term :=
  cls (decode namesOnly process)

theorem class_of_translation (process : ParameterizedRewriteSystem.Process free)
    {term : Term sig [] Srt.pr} (translated : tProc (Env.empty []) process.1 = some term) :
    cls term = mapClass namesOnly process := by
  have equal := (decode_spec namesOnly process).symm.trans translated
  cases Option.some.inj equal
  rfl

/-- Equation agreement is exactly agreement of the independently translated
payload classes, including quotation and parallel equations. -/
theorem mapClass_eq_iff (before after : ParameterizedRewriteSystem.Process free) :
    mapClass namesOnly before = mapClass namesOnly after ↔
      (ParameterizedRewriteSystem.equations free).r before after := by
  constructor
  · intro equal
    apply (ParameterizedRewriteSystem.equations_iff_structuralCongruence before after).mpr
    have first := readback_translate.2.1 (Env.empty []) before.1
      (decode namesOnly before) VarEnv.empty (decode_spec namesOnly before)
    have second := readback_translate.2.1 (Env.empty []) after.1
      (decode namesOnly after) VarEnv.empty (decode_spec namesOnly after)
    exact first.symm _ _ |>.trans _ _ _
      ((readback_sc (cls_eq_iff.mp equal)).trans _ _ _ second)
  · intro equal
    obtain ⟨first, firstTr, firstEq⟩ := translate_canonicalize.2.1 (Env.empty []) before.1
      (decode namesOnly before) (decode_spec namesOnly before)
    obtain ⟨second, secondTr, secondEq⟩ := translate_canonicalize.2.1 (Env.empty []) after.1
      (decode namesOnly after) (decode_spec namesOnly after)
    change canonicalize before.1 = canonicalize after.1 at equal
    rw [equal] at firstTr
    have termsEqual := Option.some.inj (firstTr.symm.trans secondTr)
    exact cls_eq (firstEq.symm.trans (termsEqual ▸ secondEq))

theorem raw_step {before after : ParameterizedRewriteSystem.Process free}
    (step : DerivedContextualStep.RhoStep before.1 after.1) :
    targetTheory.Step (mapClass namesOnly before) (mapClass namesOnly after) := by
  apply (classStep_cls _ _).mpr
  obtain ⟨term, translated, step'⟩ := rhoStep_simulation
    ((ParameterizedRewriteSystem.process_iff _ _).mp before.2).1
    step (decode_spec namesOnly before)
  have equal := Option.some.inj (translated.symm.trans (decode_spec namesOnly after))
  exact equal ▸ step'

theorem forward_step {before after : ParameterizedRewriteSystem.Process free}
    (step : (ParameterizedRewriteSystem.theory free).Step before after) :
    targetTheory.Step (mapClass namesOnly before) (mapClass namesOnly after) := by
  obtain ⟨redex, contractum, beforeEq, firing, afterEq⟩ :=
    ParameterizedRewriteSystem.step_iff.mp step
  have mapped := raw_step namesOnly firing
  rw [← (mapClass_eq_iff namesOnly before redex).mpr beforeEq,
    (mapClass_eq_iff namesOnly contractum after).mpr afterEq] at mapped
  exact mapped

/-- Every target step, including a target represented in a different normal
form, has an admitted source reduct with exactly that target class. -/
theorem lift_step {before : ParameterizedRewriteSystem.Process free} {after : targetTheory.Term}
    (step : targetTheory.Step (mapClass namesOnly before) after) :
    ∃ result : ParameterizedRewriteSystem.Process free,
      (ParameterizedRewriteSystem.theory free).Step before result ∧
        mapClass namesOnly result = after := by
  have represented : Steps strictRules (decode namesOnly before) (Quotient.out after) := by
    have firstEq : EqClosure equations (decode namesOnly before)
        (Quotient.out (mapClass namesOnly before)) :=
      cls_eq_iff.mp (Quotient.out_eq _).symm
    exact steps_of_equiv firstEq (.refl _) step
  obtain ⟨redex, contractum, beforeEq, firing, term, translated, equal⟩ :=
    strict_reflection_admitted
      ((ParameterizedRewriteSystem.process_iff _ _).mp before.2).1
      ((ParameterizedRewriteSystem.process_iff _ _).mp before.2).2
      (decode_spec namesOnly before) represented
  refine ⟨contractum, ParameterizedRewriteSystem.step_iff.mpr
    ⟨redex, contractum,
      (ParameterizedRewriteSystem.equations_iff_structuralCongruence before redex).mpr beforeEq,
      firing, rfl⟩, ?_⟩
  exact (class_of_translation namesOnly contractum translated).symm.trans
    (equal.trans (Quotient.out_eq after))

def covered : CoveredTranslation (ParameterizedRewriteSystem.theory free) targetTheory where
  mapTerm := mapClass namesOnly
  mapEquiv := fun {before after} equal => (mapClass_eq_iff namesOnly before after).mpr equal
  cover := ⟨forward_step namesOnly, lift_step namesOnly⟩

theorem step_iff (before after : ParameterizedRewriteSystem.Process free) :
    (ParameterizedRewriteSystem.theory free).Step before after ↔
      targetTheory.Step (mapClass namesOnly before) (mapClass namesOnly after) := by
  refine ⟨forward_step namesOnly, ?_⟩
  intro step
  obtain ⟨result, firing, equal⟩ := lift_step namesOnly step
  exact (ParameterizedRewriteSystem.theory free).rewrites_resp_right firing
    ((mapClass_eq_iff namesOnly result after).mp equal)

theorem bisimilar_iff (before after : ParameterizedRewriteSystem.Process free) :
    (ParameterizedRewriteSystem.theory free).Bisimilar before after ↔
      targetTheory.Bisimilar (mapClass namesOnly before) (mapClass namesOnly after) := by
  refine ⟨(covered namesOnly).cover.preservesBisimilar, ?_⟩
  rintro ⟨relation, ⟨forward, backward⟩, related⟩
  refine ⟨fun left right => relation (mapClass namesOnly left) (mapClass namesOnly right),
    ⟨?_, ?_⟩, related⟩
  · intro left right same next firing
    obtain ⟨target, targetStep, targetRelated⟩ := forward same (forward_step namesOnly firing)
    obtain ⟨result, resultStep, equal⟩ := lift_step namesOnly targetStep
    refine ⟨result, resultStep, ?_⟩
    change relation (mapClass namesOnly next) (mapClass namesOnly result)
    rw [equal]
    exact targetRelated
  · intro left right same next firing
    obtain ⟨target, targetStep, targetRelated⟩ := backward same (forward_step namesOnly firing)
    obtain ⟨result, resultStep, equal⟩ := lift_step namesOnly targetStep
    refine ⟨result, resultStep, ?_⟩
    change relation (mapClass namesOnly result) (mapClass namesOnly next)
    rw [equal]
    exact targetRelated

end Mettapedia.OSLF.Binding.RhoPayloadParameterizedRuntime
