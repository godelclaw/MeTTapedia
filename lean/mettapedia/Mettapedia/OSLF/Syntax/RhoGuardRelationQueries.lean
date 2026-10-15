import Mettapedia.OSLF.Syntax.RhoIntrinsicReadbackConstructors
import Mettapedia.OSLF.Syntax.RhoIntrinsicReadbackRoundtrip
import Mettapedia.OSLF.MeTTaIL.RelationQueryAdmission
import Mettapedia.GSLT.Causality.ComplementaryAssay

/-!
# Payload-sensitive complementary rho relation queries

The actual relation engine receives the already-bound output payload. Its
sorted readback determines the quoted name on which an independently
supplied class guard is evaluated. Each branch supplies either one echo
row or none. The complete query then preserves the actual input bindings
or fails; it cannot manufacture a new assignment or a second branch.

Every encoded intrinsic closed payload is admitted, including equivalent
spellings. Malformed or open payloads rejected by the closed readback
enable neither branch. These are explicit relation-interpreter semantics,
not an implementation of a guard in the unextended rho COMM rule.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoGuardRelationQueries

open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoSchema.IntrinsicEncoding RhoIntrinsicReadback
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.RelationQueryAdmission
open Mettapedia.GSLT.Causality.ComplementaryAssay (Verdict)

noncomputable section

def payloadGuard (guard : Name [] → Bool) (payload : Pattern) : Option Bool :=
  (readProcessClass [] payload).map (fun process => guard (quote process))

theorem payloadGuard_encoded (guard : Name [] → Bool) (payload : Term sig [] Srt.pr) :
    payloadGuard guard (encodeTerm payload) = some (guard (quote (project payload))) := by
  obtain ⟨decoded, readout, represented⟩ := read_encoded_class payload
  change readProcess [] (encodeTerm payload) = some decoded at readout
  simp only [payloadGuard, readProcessClass, readout, Option.map_some, represented]

theorem payloadGuard_equations (guard : Name [] → Bool)
    {first second : Term sig [] Srt.pr} (related : EqClosure rhoSourceE first second) :
    payloadGuard guard (encodeTerm first) = payloadGuard guard (encodeTerm second) := by
  rw [payloadGuard_encoded, payloadGuard_encoded]
  exact congrArg (fun process : Process [] => some (guard (quote process)))
    (Quotient.sound related)

def enabled (guard : Name [] → Bool) (branch : Verdict) (payload : Pattern) : Bool :=
  match payloadGuard guard payload with
  | none => false
  | some bit => bit == branch.bit

theorem encoded_enabled_iff (guard : Name [] → Bool) (branch : Verdict)
    (payload : Term sig [] Srt.pr) :
    enabled guard branch (encodeTerm payload) = true ↔
      guard (quote (project payload)) = branch.bit := by
  simp only [enabled, payloadGuard_encoded, beq_iff_eq]

theorem enabled_unique (guard : Name [] → Bool) (payload : Pattern)
    {first last : Verdict} (firstEnabled : enabled guard first payload = true)
    (lastEnabled : enabled guard last payload = true) : first = last := by
  cases reading : payloadGuard guard payload with
  | none => simp [enabled, reading] at firstEnabled
  | some bit =>
    have firstBit : bit = first.bit := by simpa [enabled, reading] using firstEnabled
    have lastBit : bit = last.bit := by simpa [enabled, reading] using lastEnabled
    exact Mettapedia.GSLT.Causality.ComplementaryAssay.verdict_eq_of_bit
      (firstBit.symm.trans lastBit)

theorem encoded_has_one_branch (guard : Name [] → Bool) (payload : Term sig [] Srt.pr) :
    ∃ branch : Verdict, enabled guard branch (encodeTerm payload) = true ∧
      ∀ other, enabled guard other (encodeTerm payload) = true → other = branch := by
  let branch := Mettapedia.GSLT.Causality.ComplementaryAssay.verdictOf
    (guard (quote (project payload)))
  have admitted : enabled guard branch (encodeTerm payload) = true :=
    (encoded_enabled_iff guard branch payload).mpr
      (Mettapedia.GSLT.Causality.ComplementaryAssay.verdictOf_bit _).symm
  exact ⟨branch, admitted, fun _ enabledOther => enabled_unique guard _ enabledOther admitted⟩

theorem malformed_enables_neither (guard : Name [] → Bool) (payload : Pattern)
    (rejected : readProcessClass [] payload = none) :
    enabled guard .confirm payload = false ∧ enabled guard .refute payload = false := by
  simp [enabled, payloadGuard, rejected]

def relationName : Verdict → String
  | .confirm => "scopeConfirm"
  | .refute => "scopeRefute"

def rows (guard : Name [] → Bool) (branch : Verdict) : List Pattern → List (List Pattern)
  | [payload] => if enabled guard branch payload then [[payload]] else []
  | _ => []

def environment (guard : Name [] → Bool) : RelationEnv where
  tuples := fun relation arguments =>
    if relation = relationName .confirm then rows guard .confirm arguments
    else if relation = relationName .refute then rows guard .refute arguments
    else []

theorem environment_branch (guard : Name [] → Bool) (branch : Verdict)
    (arguments : List Pattern) :
    (environment guard).tuples (relationName branch) arguments = rows guard branch arguments := by
  cases branch <;> simp [environment, relationName]

theorem branch_has_no_builtin (language : LanguageDef) (branch : Verdict)
    (arguments : List Pattern) :
    builtinRelationTuples language (relationName branch) arguments = [] := by
  cases branch <;> rfl

theorem bound_query_exact (guard : Name [] → Bool) (branch : Verdict)
    (language : LanguageDef) {bindings : Bindings} {slotName : String} {payload : Pattern}
    (found : bindings.lookup slotName = some payload) :
    relationQueryStep (environment guard) language bindings (relationName branch)
      [.fvar slotName] = if enabled guard branch payload then [bindings] else [] := by
  exact relationQueryStep_boundVariables_echo_eq
    (List.Forall₂.cons found .nil) (branch_has_no_builtin language branch [payload])
    (by rw [environment_branch]; rfl)

theorem bound_query_present_iff (guard : Name [] → Bool) (branch : Verdict)
    (language : LanguageDef) {bindings : Bindings} {slotName : String} {payload : Pattern}
    (found : bindings.lookup slotName = some payload) :
    bindings ∈ relationQueryStep (environment guard) language bindings (relationName branch)
      [.fvar slotName] ↔ enabled guard branch payload = true := by
  rw [bound_query_exact guard branch language found]
  by_cases admitted : enabled guard branch payload = true <;> simp [admitted]

theorem bound_queries_do_not_race (guard : Name [] → Bool) (language : LanguageDef)
    {bindings : Bindings} {slotName : String} {payload : Pattern}
    (found : bindings.lookup slotName = some payload) :
    ¬ (bindings ∈ relationQueryStep (environment guard) language bindings (relationName .confirm)
        [.fvar slotName] ∧
      bindings ∈ relationQueryStep (environment guard) language bindings (relationName .refute)
        [.fvar slotName]) := by
  rintro ⟨first, last⟩
  have impossible : Verdict.confirm = Verdict.refute := enabled_unique guard payload
    ((bound_query_present_iff guard .confirm language found).mp first)
    ((bound_query_present_iff guard .refute language found).mp last)
  cases impossible

end

end Mettapedia.OSLF.Binding.RhoGuardRelationQueries
