import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalEqualityCode

/-!
# Certificate-directed contextual HOL equality interpretation

The interpreter follows incoming annotated derivation nodes. It covers the
natural rows, beta, equivalence, application, abstraction and product
congruence. Type-only equality/subtyping adjustments retain the interpreted
endpoints. The complete source checker and context checker run separately
before the result is admitted. Other source rules remain outside this reader.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
namespace AnnotatedConversion.CertificateInterpretation

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Annotated NativeNaturalVectorFamilies Programs.Annotated

universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v} [DecidableEq Base]

/-- Nat's evidence and root table instantiate the shared contextual traversal. -/
def readEquality? (operations : Operations Base Const) (profile : Programs.ComputationProfiles.Selection)
    (certificate : JudgmentReplay.Certificate profile) (Γ : HOL.Ctx Base)
    (context : CCtx Tower.Head Γ.length) (source target type : CTm Tower.Head Γ.length) :
    Option (EqualityReading operations Γ source target) :=
  AnnotatedPredicateReading.Interpreter.readEquality? (evidenceOps operations)
    (EqualityCode.natural? operations profile) certificate Γ context source target type

structure CheckedEquality (operations : Operations Base Const) (profile : Programs.ComputationProfiles.Selection)
    (Γ : HOL.Ctx Base) (context : CCtx Tower.Head Γ.length) (source target type : CTm Tower.Head Γ.length) where
  contextFormed : CCtxFormed (church profile) context
  sourceEqual : CEqual (church profile) context source target type
  reading : EqualityReading operations Γ source target

/-- Admit the interpreted proof only after the complete source judgment and
its actual binder context have passed their independent finite checks. -/
def check? (operations : Operations Base Const) (profile : Programs.ComputationProfiles.Selection)
    (Γ : HOL.Ctx Base) (context : CCtx Tower.Head Γ.length) (source target type : CTm Tower.Head Γ.length)
    (contextCertificate : JudgmentReplay.ContextCertificate profile Γ.length)
    (certificate : JudgmentReplay.Certificate profile) :
    Option (CheckedEquality operations profile Γ context source target type) :=
  (AnnotatedPredicateReading.Interpreter.check? (church profile) (JudgmentReplay.decoder profile)
    (evidenceOps operations) (EqualityCode.natural? operations profile) Γ context source target type
    contextCertificate certificate).map fun received =>
      ⟨received.contextFormed, received.sourceEqual, ⟨received.carrier, received.evidence⟩⟩

namespace CheckedEquality

variable {operations : Operations Base Const} {profile : Programs.ComputationProfiles.Selection}
    {Γ : HOL.Ctx Base} {context : CCtx Tower.Head Γ.length} {source target type : CTm Tower.Head Γ.length}

def sourceState (received : CheckedEquality operations profile Γ context source target type) :
    State operations profile ⟨Γ, context, type, received.reading.1⟩ where
  contextFormed := received.contextFormed
  term := source
  typed := (CEqual.typed (Programs.Annotated.levelModel profile) received.sourceEqual received.contextFormed).1
  code := received.reading.2.left
  reading := received.reading.2.leftRead

def targetState (received : CheckedEquality operations profile Γ context source target type) :
    State operations profile ⟨Γ, context, type, received.reading.1⟩ where
  contextFormed := received.contextFormed
  term := target
  typed := (CEqual.typed (Programs.Annotated.levelModel profile) received.sourceEqual received.contextFormed).2
  code := received.reading.2.right
  reading := received.reading.2.rightRead

/-- The received proof inhabits the existing root-equality interface at its
constructed typed endpoint states. No endpoint equality premise is supplied. -/
def rootProof (received : CheckedEquality operations profile Γ context source target type) :
    (holEquality operations profile).Eq received.sourceState received.targetState :=
  received.reading.2.proof

omit [DecidableEq Base] in
theorem rootProof_free (received : CheckedEquality operations profile Γ context source target type) :
    received.rootProof.FunctionExtensionalityFree := received.reading.2.free

end CheckedEquality

theorem check?_refuses_source {operations : Operations Base Const} {profile : Programs.ComputationProfiles.Selection}
    {Γ : HOL.Ctx Base} {context : CCtx Tower.Head Γ.length} {source target type : CTm Tower.Head Γ.length}
    (contextCertificate : JudgmentReplay.ContextCertificate profile Γ.length)
    (certificate : JudgmentReplay.Certificate profile)
    (refused : JudgmentReplay.check profile certificate (.equality context source target type) = false) :
    check? operations profile Γ context source target type contextCertificate certificate = none := by
  have rejected := AnnotatedPredicateReading.Interpreter.check?_refuses_source
    (church profile) (JudgmentReplay.decoder profile) (evidenceOps operations)
    (EqualityCode.natural? operations profile) Γ context source target type contextCertificate certificate refused
  simp only [check?, rejected, Option.map_none]

#print axioms readEquality?
#print axioms check?
#print axioms CheckedEquality.sourceState
#print axioms CheckedEquality.targetState
#print axioms CheckedEquality.rootProof

end AnnotatedConversion.CertificateInterpretation
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
