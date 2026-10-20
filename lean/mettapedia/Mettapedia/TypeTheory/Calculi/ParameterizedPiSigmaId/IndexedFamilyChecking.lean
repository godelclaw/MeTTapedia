import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedFamilyDeclaration
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.SchemaTableConversionCode
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveCheckingOSLF
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveHeadMap

/-!
# Selected inductive computation and checked typed instantiation

Existing iota schemas provide the telescope, displayed type and retained
computation witness. Their ordered table feeds the common finite root decoder.
A selected calculus keeps the original head, universe and constant policies,
and uses just the selected schema instances as its additional roots.

Its derivations include into the original declaration calculus. This does not
establish preservation, normalization or conservativity in the reverse
direction. Typed replay separately checks a substitution against the original
calculus and reconstructs the complete existing iota receipt. Neither path
derives an eliminator or makes an informative candidate authorized.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace Declaration.IndexedFamily.Checking

open AlgebraicSchema ComputationAuthority

variable {Head : Type} {base : Rules Head} {signature : Signature Head}
    {computation : ProofRelevantRootComputation Head}

/-- A view of typed canonical schemas, retaining each original receipt. -/
abbrev Schemas (base : Rules Head) (signature : Signature Head)
    (computation : ProofRelevantRootComputation Head) :=
  List (Σ arity : Nat, IotaSchema base signature computation arity)

abbrev table (schemas : Schemas base signature computation) : SchemaTable Head :=
  schemas.map fun row => ⟨row.1, row.2.left, row.2.right⟩

/-- The table address also retrieves its exact telescope, type and evidence;
equal endpoints do not replace one row's receipt with another. -/
def receiptAt (schemas : Schemas base signature computation)
    (index : Fin (table schemas).length) :
    Σ context : Ctx Head ((table schemas).get index).1,
      Σ type : Tm Head ((table schemas).get index).1,
        ProofRelevantStepReceipt base signature computation context
          ((table schemas).get index).2.1 ((table schemas).get index).2.2 type :=
  match schemas with
  | [] => Fin.elim0 index
  | row :: rest =>
      Fin.cases ⟨row.2.context, row.2.type, row.2.receipt⟩
        (fun prior => receiptAt rest prior) index

/-- Reconstruct the exact original root evidence of a selected row instance. -/
def realizeEvidence (schemas : Schemas base signature computation)
    {enabled : Fin (table schemas).length → Bool} {n : Nat} {left right : Tm Head n}
    (evidence : SchemaTableConversionCode.Evidence (table schemas) enabled left right) :
    computation.Evidence left right := by
  cases evidence with
  | instantiate index _ substitution =>
      exact computation.substitute substitution (receiptAt schemas index).2.2.evidence

/-- A genuine root restriction; it changes no universe or constant policy.
The surrounding structural beta and congruence rules remain unchanged. -/
def rules (schemas : Schemas base signature computation)
    (enabled : Fin (table schemas).length → Bool) : Rules Head :=
  { extendRules base signature with computation := SchemaTableConversionCode.root (table schemas) enabled }

def rootDecoder (schemas : Schemas base signature computation)
    (enabled : Fin (table schemas).length → Bool) :
    StructuralConversionCode.RootDecoder (rules schemas enabled).computation :=
  SchemaTableConversionCode.rootDecoder (table schemas) enabled

/-- The selected rules are included in the actual declaration calculus,
using its independently supplied support equation. -/
theorem inclusion (schemas : Schemas base signature computation)
    (support : signature.computation = computation.support)
    (enabled : Fin (table schemas).length → Bool) :
    (rules schemas enabled).Morphism (extendRules base signature) (fun head => head) where
  headTyping := fun known => known
  isUniverse := fun known => known
  join := fun known => known
  cumulative := fun known => known
  headEq := fun known => known
  constantType := by
    intro name type known
    simpa only [rules, Tm.mapHead_id] using known
  computation := by
    intro n left right step
    obtain ⟨evidence⟩ := step
    have original : signature.computation.step left right := by
      rw [support]
      exact ⟨realizeEvidence schemas evidence⟩
    change RootStep base signature n (left.mapHead fun head => head)
      (right.mapHead fun head => head)
    simpa only [Tm.mapHead_id] using RootStep.declared (base := base) original

/-- Inclusion preserves the full formation-sensitive judgment, including
the original context and displayed result type. No reverse claim is made. -/
theorem judgment_inclusion (schemas : Schemas base signature computation)
    (support : signature.computation = computation.support)
    (enabled : Fin (table schemas).length → Bool)
    {n : Nat} {context : Ctx Head n} {term type : Tm Head n}
    (derived : FormationSensitive.Judgment (rules schemas enabled) context term type) :
    FormationSensitive.Judgment (extendRules base signature) context term type := by
  simpa only [Ctx.mapHead_id, Tm.mapHead_id] using
    derived.mapHead (inclusion schemas support enabled)

/-- The same constructed inclusion is an operational route for the declared
conversion observation. It preserves steps; target coverage is not asserted. -/
def conversionRoute (schemas : Schemas base signature computation)
    (support : signature.computation = computation.support)
    (enabled : Fin (table schemas).length → Bool) (n : Nat) :
    Mettapedia.GSLT.IndexedOperational.OperationalTranslation
      (FormationSensitiveCheckingOSLF.theory (rules schemas enabled) n)
      (FormationSensitiveCheckingOSLF.theory (extendRules base signature) n) where
  mapTerm := id
  mapEquiv := fun equal => equal
  mapStep := by
    intro left right edge
    have transfer {left right : Tm Head n}
        (step : Step (rules schemas enabled).headEq left right (rules schemas enabled).computation) :
        Step (extendRules base signature).headEq left right (extendRules base signature).computation := by
      simpa only [Tm.mapHead_id] using step.mapHead (fun head => head)
        (inclusion schemas support enabled).headEq (inclusion schemas support enabled).computation
    exact edge.elim (fun step => .inl (transfer step)) (fun step => .inr (transfer step))

/-- Existing family candidates expose their listed computation schemas in
the same order, without reconstructing constructors or eliminators. -/
def candidateSchemas (candidate : Candidate base) :
    Schemas base candidate.signature candidate.computation :=
  candidate.iotaRules.map fun rule => ⟨rule.arity, rule.schema⟩

section TypedReplay

variable (schemas : Schemas base signature computation)
variable (decoder : StructuralConversionCode.RootDecoder (extendRules base signature).computation)
variable [DecidableEq Head] [DecidableRel base.headTyping] [DecidablePred base.isUniverse]
    [∀ u v w, Decidable (base.join u v w)] [DecidableRel base.cumulative]
    [DecidableRel base.headEq]

local instance : DecidableRel (extendRules base signature).headTyping :=
  fun h u => inferInstanceAs (Decidable (base.headTyping h u))
local instance : DecidablePred (extendRules base signature).isUniverse :=
  fun h => inferInstanceAs (Decidable (base.isUniverse h))
local instance : ∀ u v w, Decidable ((extendRules base signature).join u v w) :=
  fun u v w => inferInstanceAs (Decidable (base.join u v w))
local instance : DecidableRel (extendRules base signature).cumulative :=
  fun u v => inferInstanceAs (Decidable (base.cumulative u v))
local instance : DecidableRel (extendRules base signature).headEq :=
  fun h u => inferInstanceAs (Decidable (base.headEq h u))

/-- Evidence contains the existing finite substitution checker; it does not
take a typing or preservation theorem as an executable argument. -/
structure InstanceRequest {n : Nat} (context : Ctx Head n) where
  index : Fin (table schemas).length
  substitution : Sub Head ((table schemas).get index).1 n
  arguments : FormationSensitiveChecking.SubstitutionRequest decoder
    (receiptAt schemas index).1 context substitution

def InstanceRequest.source {n : Nat} {context : Ctx Head n}
    (request : InstanceRequest schemas decoder context) : Tm Head n :=
  subst request.substitution ((table schemas).get request.index).2.1

def InstanceRequest.target {n : Nat} {context : Ctx Head n}
    (request : InstanceRequest schemas decoder context) : Tm Head n :=
  subst request.substitution ((table schemas).get request.index).2.2

def InstanceRequest.type {n : Nat} {context : Ctx Head n}
    (request : InstanceRequest schemas decoder context) : Tm Head n :=
  subst request.substitution (receiptAt schemas request.index).2.1

/-- Export the cited row and explicit finite arguments to common raw replay.
Typing evidence remains a separate part of the request. -/
def InstanceRequest.rootCode {n : Nat} {context : Ctx Head n}
    (request : InstanceRequest schemas decoder context) :
    SchemaTableConversionCode.Code Head n :=
  SchemaTableConversionCode.encode (table schemas) request.index request.substitution

def InstanceRequest.check {n : Nat} {context : Ctx Head n}
    (request : InstanceRequest schemas decoder context)
    (enabled : Fin (table schemas).length → Bool) (left right displayed : Tm Head n) : Bool :=
  enabled request.index && (request.arguments.check decoder &&
    decide (request.source schemas decoder = left ∧
      request.target schemas decoder = right ∧ request.type schemas decoder = displayed))

/-- Exact certificate coverage for a fixed row and assignment. Raw endpoint
replay does not supply the independent formed context and typed substitution.
The result is existence of finite evidence, not inference of an assignment. -/
theorem InstanceRequest.checked_arguments_iff {n : Nat} {context : Ctx Head n}
    (index : Fin (table schemas).length)
    (substitution : Sub Head ((table schemas).get index).1 n)
    (enabled : Fin (table schemas).length → Bool) (left right displayed : Tm Head n) :
    (∃ arguments : FormationSensitiveChecking.SubstitutionRequest decoder
        (receiptAt schemas index).1 context substitution,
      (InstanceRequest.mk index substitution arguments).check schemas decoder enabled
        left right displayed = true) ↔
      enabled index = true ∧
      FormationSensitive.ContextFormation (extendRules base signature) context ∧
      FormationSensitive.CtxMor (extendRules base signature)
        (receiptAt schemas index).1 context substitution ∧
      subst substitution ((table schemas).get index).2.1 = left ∧
      subst substitution ((table schemas).get index).2.2 = right ∧
      subst substitution (receiptAt schemas index).2.1 = displayed := by
  constructor
  · rintro ⟨arguments, accepted⟩
    simp only [InstanceRequest.check, Bool.and_eq_true, decide_eq_true_eq] at accepted
    have checked := arguments.sound decoder accepted.2.1
    exact ⟨accepted.1, checked.1, checked.2, accepted.2.2⟩
  · rintro ⟨permitted, formed, typed, endpoints⟩
    obtain ⟨arguments, accepted⟩ :=
      FormationSensitiveChecking.SubstitutionRequest.complete decoder formed typed
    refine ⟨arguments, ?_⟩
    simp only [InstanceRequest.check, permitted, accepted, Bool.true_and]
    exact decide_eq_true endpoints

/-- Checked instantiation retains both endpoint typings and the original
computation witness at the exact requested context and displayed type. -/
def InstanceRequest.replay {n : Nat} {context : Ctx Head n}
    (request : InstanceRequest schemas decoder context)
    (enabled : Fin (table schemas).length → Bool) (left right displayed : Tm Head n)
    (accepted : request.check schemas decoder enabled left right displayed = true) :
    ProofRelevantStepReceipt base signature computation context left right displayed := by
  simp only [InstanceRequest.check, Bool.and_eq_true, decide_eq_true_eq] at accepted
  have typed := (request.arguments.sound decoder accepted.2.1).2.toRaw
  have receipt := (receiptAt schemas request.index).2.2.substitute request.substitution typed
  have endpoints := accepted.2.2
  change subst request.substitution ((table schemas).get request.index).2.1 = left ∧
    subst request.substitution ((table schemas).get request.index).2.2 = right ∧
    subst request.substitution (receiptAt schemas request.index).2.1 = displayed at endpoints
  rw [endpoints.1, endpoints.2.1, endpoints.2.2] at receipt
  exact receipt

theorem InstanceRequest.formed {n : Nat} {context : Ctx Head n}
    (request : InstanceRequest schemas decoder context)
    (enabled : Fin (table schemas).length → Bool) (left right displayed : Tm Head n)
    (accepted : request.check schemas decoder enabled left right displayed = true) :
    FormationSensitive.ContextFormation (extendRules base signature) context := by
  simp only [InstanceRequest.check, Bool.and_eq_true, decide_eq_true_eq] at accepted
  exact (request.arguments.sound decoder accepted.2.1).1

/-- Typed publication also yields the selected raw computation certificate.
The converse would discard the independent argument-typing checks. -/
theorem InstanceRequest.rootCode_accepted {n : Nat} {context : Ctx Head n}
    (request : InstanceRequest schemas decoder context)
    (enabled : Fin (table schemas).length → Bool) (left right displayed : Tm Head n)
    (accepted : request.check schemas decoder enabled left right displayed = true) :
    SchemaTableConversionCode.decode (table schemas) enabled
      (request.rootCode schemas decoder) = some (left, right) := by
  simp only [InstanceRequest.check, Bool.and_eq_true, decide_eq_true_eq] at accepted
  have decoded := SchemaTableConversionCode.decode_encode (table schemas) enabled
    request.index accepted.1 request.substitution
  change SchemaTableConversionCode.decode (table schemas) enabled
    (request.rootCode schemas decoder) =
      some (request.source schemas decoder, request.target schemas decoder) at decoded
  simpa only [accepted.2.2.1, accepted.2.2.2.1] using decoded

end TypedReplay
end Declaration.IndexedFamily.Checking
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
