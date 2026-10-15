import Mettapedia.OSLF.Framework.RhoScopeCanonicalSizeBound

/-!
# Terminating generated-scope decisions on actual intrinsic rho names

Decidable atomic satisfaction and the complete finite decomposition catalogue
give a decision at every finite depth. The earned canonical-size bound makes
one such finite decision complete for the least generated scope, including
negative answers. Equivalent raw spellings share the verdict because the
algorithm reads the actual source equation class. This is a static scope
guard; execution scheduling and assay funding are separate constructions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoGeneratedScopeDecision

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoEquationGeneratedScope RhoScopeBoundedDecision RhoScopeCanonicalSizeBound

def generatedDecision {context : Ctx sig} (left right : Process context → Prop)
    [DecidablePred left] [DecidablePred right] (name : Name context) :
    Decidable (generated left right name) := by
  letI := boundedDecision left right (canonicalSize name) name
  exact decidable_of_iff' _ (generated_iff_size_bounded left right name)

def guard {context : Ctx sig} (left right : Process context → Prop)
    [DecidablePred left] [DecidablePred right] (name : Name context) : Bool :=
  @decide (generated left right name) (generatedDecision left right name)

theorem guard_true_iff {context : Ctx sig} (left right : Process context → Prop)
    [DecidablePred left] [DecidablePred right] (name : Name context) :
    guard left right name = true ↔ generated left right name :=
  Iff.of_eq (@decide_eq_true_eq _ (generatedDecision left right name))

theorem guard_false_iff {context : Ctx sig} (left right : Process context → Prop)
    [DecidablePred left] [DecidablePred right] (name : Name context) :
    guard left right name = false ↔ ¬ generated left right name :=
  @decide_eq_false_iff_not _ (generatedDecision left right name)

theorem guard_is_complete_bounded_test {context : Ctx sig}
    (left right : Process context → Prop) [DecidablePred left] [DecidablePred right]
    (name : Name context) :
    guard left right name = boundedTest left right (canonicalSize name) name := by
  have agreement : guard left right name = true ↔
      boundedTest left right (canonicalSize name) name = true := by
    rw [guard_true_iff, boundedTest_true_iff]
    exact generated_iff_size_bounded left right name
  exact Bool.eq_iff_iff.mpr agreement

theorem admitted_guard_has_size_bounded_witness {context : Ctx sig}
    (left right : Process context → Prop) [DecidablePred left] [DecidablePred right]
    (name : Name context) (accepted : guard left right name = true) :
    ∃ certificate : Certificate left right name, certificate.depth ≤ canonicalSize name :=
  (generated_iff_size_bounded left right name).mp ((guard_true_iff left right name).mp accepted)

def rawGuard {context : Ctx sig} (left right : Process context → Prop)
    [DecidablePred left] [DecidablePred right] (term : Term sig context Srt.nm) : Bool :=
  guard left right (project term)

theorem raw_guard_equation {context : Ctx sig} (left right : Process context → Prop)
    [DecidablePred left] [DecidablePred right] {first second : Term sig context Srt.nm}
    (equation : EqClosure rhoSourceE first second) :
    rawGuard left right first = rawGuard left right second :=
  congrArg (guard left right) (Quotient.sound equation)

theorem complementary_equivalent_guards_do_not_overlap {context : Ctx sig}
    (left right : Process context → Prop) [DecidablePred left] [DecidablePred right]
    {first second : Term sig context Srt.nm} (equation : EqClosure rhoSourceE first second) :
    ¬ (rawGuard left right first = true ∧ (!rawGuard left right second) = true) := by
  rw [raw_guard_equation left right equation]
  cases rawGuard left right second <;> simp

end Mettapedia.OSLF.Framework.RhoGeneratedScopeDecision
