import Mettapedia.OSLF.Framework.RhoSeededScopeControls

/-!
# Equation-invariant Boolean guards for an actual generated scope

Canonical scope recognition supplies a computable Boolean guard on source
name classes. A raw source spelling is first projected to its equation class.
Equivalent spellings therefore have the same verdict, and one cannot satisfy
the guard while an equivalent spelling satisfies its complement. This is the
static coherence obligation for later guarded assays; execution scheduling,
permissions and exact assay funding are additional contracts.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoSeededScopeGuard

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoSchema.IntrinsicEncoding
open RhoSeededScopeParser RhoSeededScopeInterpretation

def guard (name : Name []) : Bool := (depth (encodeEquationClass name)).isSome

theorem guard_true_iff (env : RhoScopeExpression.Environment []) (name : Name []) :
    guard name = true ↔
      RhoScopeExpression.denote RhoScopeSeedReadings.atoms RhoScopeSeedReadings.seeded env name :=
  depth_actual_scope_iff env name

theorem guard_false_iff (env : RhoScopeExpression.Environment []) (name : Name []) :
    guard name = false ↔
      ¬ RhoScopeExpression.denote RhoScopeSeedReadings.atoms RhoScopeSeedReadings.seeded env name := by
  rw [← guard_true_iff]
  cases guard name <;> simp

def rawGuard (term : Term sig [] Srt.nm) : Bool := guard (project term)

theorem raw_guard_equation {first second : Term sig [] Srt.nm}
    (equation : EqClosure rhoSourceE first second) : rawGuard first = rawGuard second :=
  congrArg guard (Quotient.sound equation)

theorem complementary_equivalent_guards_do_not_overlap {first second : Term sig [] Srt.nm}
    (equation : EqClosure rhoSourceE first second) :
    ¬ (rawGuard first = true ∧ (!rawGuard second) = true) := by
  rw [raw_guard_equation equation]
  cases rawGuard second <;> simp

theorem native_guard_receipt_readout (name : Name []) :
    (RhoSeededScopeReceipts.receipt? name).isSome = guard name :=
  RhoSeededScopeReceipts.receipt?_isSome name

end Mettapedia.OSLF.Framework.RhoSeededScopeGuard
