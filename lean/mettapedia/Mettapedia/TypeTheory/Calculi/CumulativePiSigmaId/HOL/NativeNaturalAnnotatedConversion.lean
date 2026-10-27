import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalAnnotatedTransport
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorAnnotatedChecking
import Mettapedia.TypeTheory.BubbleElaboration

/-!
# Interpreted typed natural computation instances

The original annotated natural/vector declaration profile supplies the source
contexts, types and computation rows. Represented typed caller substitutions
instantiate its two natural rows. Their HOL proofs retain selection and
recursion as explicit hypotheses of the selected root theory.

The states retain source typing and the actual annotated reading. Literal
agreement of their codes follows from reading coherence, rather than being a
new premise of proof composition. The result carrier remains fixed by the
natural predicate interpretation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
namespace AnnotatedConversion

open Mettapedia.Logic
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Annotated NativeNaturalVectorFamilies
open FormationSensitiveHOLInterface (variableIndex)

universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v}

/-- Both contexts and the displayed source type are part of the fibre. -/
structure Index (Base : Type u) where
  targetContext : HOL.Ctx Base
  sourceContext : CCtx Tower.Head targetContext.length
  sourceType : CTm Tower.Head targetContext.length
  targetType : HOL.Ty Base

structure State (operations : Operations Base Const)
    (profile : Programs.ComputationProfiles.Selection) (index : Index Base) where
  contextFormed : CCtxFormed (Programs.Annotated.church profile) index.sourceContext
  term : CTm Tower.Head index.targetContext.length
  typed : CTyped (Programs.Annotated.church profile) index.sourceContext term index.sourceType
  code : HOL.Term Const index.targetContext index.targetType
  reading : AnnotatedReads operations term code

def assumptions (operations : Operations Base Const) (Γ : HOL.Ctx Base) :
    List (HOL.Formula Const Γ) :=
  [HOL.SelectionProofs.principle (HOL.weakenCtx Γ operations.selection),
   HOL.NaturalRecursionProofs.statement (HOL.weakenCtx Γ operations.zero)
     (HOL.weakenCtx Γ operations.successor) operations.result]

theorem assumptions_substitute (operations : Operations Base Const)
    {Γ Ξ : HOL.Ctx Base} (substitution : HOL.Subst Const Γ Ξ) :
    (assumptions operations Γ).map (HOL.subst substitution) = assumptions operations Ξ := by
  simp only [assumptions, List.map_cons, List.map_nil]
  congr 1
  · simp [HOL.SelectionProofs.principle, HOL.SelectionProofs.instanceFormula,
      HOL.subst, HOL.subst_weaken, HOL.subst_weakenCtx, HOL.Subst.lift]
  · congr 1
    simp [HOL.NaturalRecursionProofs.statement, HOL.NaturalRecursionProofs.subst_body,
      HOL.subst, HOL.subst_weaken, HOL.subst_weakenCtx, HOL.Subst.lift, HOL.Rename.weaken]

/-- The Nat instance retains its two actual closed source premises. -/
def closedAssumptions (operations : Operations Base Const) : List (HOL.ClosedFormula Const) :=
  [HOL.SelectionProofs.principle operations.selection,
   HOL.NaturalRecursionProofs.statement operations.zero operations.successor operations.result]

theorem assumptions_eq_closed (operations : Operations Base Const) (Γ : HOL.Ctx Base) :
    assumptions operations Γ = AnnotatedPredicateReading.assumptions (closedAssumptions operations) Γ := by
  let rho : HOL.Subst Const [] Γ := fun index => nomatch index
  calc
    assumptions operations Γ = (assumptions operations []).map (HOL.subst rho) :=
      (assumptions_substitute operations rho).symm
    _ = AnnotatedPredicateReading.assumptions (closedAssumptions operations) Γ := by
      change (closedAssumptions operations).map (HOL.subst rho) =
        (closedAssumptions operations).map (HOL.weakenCtx Γ)
      apply List.map_congr_left
      intro formula _
      exact HOL.subst_weakenCtx rho formula

#print axioms assumptions_eq_closed

inductive Row where
  | zero
  | successor
  deriving DecidableEq

namespace Row

def address : Row → Programs.Annotated.Row
  | .zero => ⟨0, by decide⟩
  | .successor => ⟨1, by decide⟩

def parameters (operations : Operations Base Const) : Row → HOL.Ctx Base
  | .zero => operations.parameters
  | .successor => operations.successorParameters

def context (operations : Operations Base Const) (row : Row) :
    CCtx Tower.Head (row.parameters operations).length :=
  match row with
  | .zero => Programs.Annotated.context ⟨0, by decide⟩
  | .successor => Programs.Annotated.context ⟨1, by decide⟩

def type (operations : Operations Base Const) (row : Row) :
    CTm Tower.Head (row.parameters operations).length :=
  match row with
  | .zero => Programs.Annotated.resultType ⟨0, by decide⟩
  | .successor => Programs.Annotated.resultType ⟨1, by decide⟩

def left (operations : Operations Base Const) (row : Row) :
    CTm Tower.Head (row.parameters operations).length :=
  match row with
  | .zero => liftTm natZeroIotaLeft
  | .successor => liftTm natSuccIotaLeft

def right (operations : Operations Base Const) (row : Row) :
    CTm Tower.Head (row.parameters operations).length :=
  match row with
  | .zero => liftTm natZeroIotaRight
  | .successor => liftTm natSuccIotaRight

def leftCode (operations : Operations Base Const) (row : Row) :
    HOL.Term Const (row.parameters operations) operations.result :=
  match row with
  | .zero => operations.zeroLeft
  | .successor => operations.successorLeft

def rightCode (operations : Operations Base Const) (row : Row) :
    HOL.Term Const (row.parameters operations) operations.result :=
  match row with
  | .zero => operations.zeroRight
  | .successor => operations.successorRight

theorem left_reads (operations : Operations Base Const) (row : Row) :
    AnnotatedReads operations (row.left operations) (row.leftCode operations) := by
  cases row with
  | zero => exact AnnotatedReads.of_lamFree operations.zeroLeft_reads (by rfl)
  | successor => exact AnnotatedReads.of_lamFree operations.successorLeft_reads (by rfl)

theorem right_reads (operations : Operations Base Const) (row : Row) :
    AnnotatedReads operations (row.right operations) (row.rightCode operations) := by
  cases row with
  | zero => exact AnnotatedReads.of_lamFree operations.zeroRight_reads (by rfl)
  | successor => exact AnnotatedReads.of_lamFree operations.successorRight_reads (by rfl)

theorem typed (operations : Operations Base Const)
    (profile : Programs.ComputationProfiles.Selection) (row : Row) :
    CTyped (Programs.Annotated.church profile) (row.context operations)
      (row.left operations) (row.type operations) ∧
    CTyped (Programs.Annotated.church profile) (row.context operations)
      (row.right operations) (row.type operations) := by
  cases row with
  | zero => exact Programs.Annotated.endpoints_typed profile ⟨0, by decide⟩
  | successor => exact Programs.Annotated.endpoints_typed profile ⟨1, by decide⟩

def proof (operations : Operations Base Const) (row : Row) :
    HOL.ProofSyntax Const (assumptions operations (row.parameters operations))
      (.eq (row.leftCode operations) (row.rightCode operations)) := by
  cases row with
  | zero =>
      exact operations.zero_row_proof
        (.hyp ⟨0, by simp [assumptions]⟩) (.hyp ⟨1, by simp [assumptions]⟩)
  | successor =>
      exact operations.successor_row_proof
        (.hyp ⟨0, by simp [assumptions]⟩) (.hyp ⟨1, by simp [assumptions]⟩)

theorem proof_free (operations : Operations Base Const) (row : Row) :
    (row.proof operations).FunctionExtensionalityFree := by
  cases row <;>
    simp [proof, Operations.zero_row_proof, Operations.successor_row_proof,
      Operations.zeroIota_free, Operations.successorIota_free,
      HOL.ProofSyntax.FunctionExtensionalityFree]

end Row

/-- The source caller is independently typed. Its target assignments read
each actual annotated component; no row-equality proof is an input. -/
structure Instance (operations : Operations Base Const)
    (profile : Programs.ComputationProfiles.Selection) (row : Row)
    (Γ : HOL.Ctx Base) (context : CCtx Tower.Head Γ.length) where
  contextFormed : CCtxFormed (Programs.Annotated.church profile) context
  sourceSubstitution : CSub Tower.Head (row.parameters operations).length Γ.length
  targetSubstitution : HOL.Subst Const (row.parameters operations) Γ
  typed : CSubstMor (Programs.Annotated.church profile) (row.context operations)
    context sourceSubstitution
  represented : ∀ {type} (index : HOL.Var (row.parameters operations) type),
    AnnotatedReads operations (sourceSubstitution (variableIndex index)) (targetSubstitution index)

namespace Instance

variable {operations : Operations Base Const} {profile : Programs.ComputationProfiles.Selection}
    {row : Row} {Γ : HOL.Ctx Base} {context : CCtx Tower.Head Γ.length}

def index (inst : Instance operations profile row Γ context) : Index Base :=
  ⟨Γ, context, (row.type operations).subst inst.sourceSubstitution, operations.result⟩

def source (inst : Instance operations profile row Γ context) :
    State operations profile inst.index where
  contextFormed := inst.contextFormed
  term := (row.left operations).subst inst.sourceSubstitution
  typed := (row.typed operations profile).1.substitute inst.typed
  code := HOL.subst inst.targetSubstitution (row.leftCode operations)
  reading := (row.left_reads operations).substitute
    inst.targetSubstitution inst.sourceSubstitution inst.represented

def target (inst : Instance operations profile row Γ context) :
    State operations profile inst.index where
  contextFormed := inst.contextFormed
  term := (row.right operations).subst inst.sourceSubstitution
  typed := (row.typed operations profile).2.substitute inst.typed
  code := HOL.subst inst.targetSubstitution (row.rightCode operations)
  reading := (row.right_reads operations).substitute
    inst.targetSubstitution inst.sourceSubstitution inst.represented

theorem source_equal (inst : Instance operations profile row Γ context)
    (permitted : profile row.address = true) :
    CEqual (Programs.Annotated.church profile) context inst.source.term inst.target.term
      inst.index.sourceType := by
  cases row with
  | zero => exact Programs.Annotated.instantiated_equal profile ⟨0, by decide⟩ permitted inst.typed
  | successor => exact Programs.Annotated.instantiated_equal profile ⟨1, by decide⟩ permitted inst.typed

/-- Substitute the retained open schematic proof; the endpoints are the
computed readings of the original source inst. -/
def proof (inst : Instance operations profile row Γ context) :
    HOL.ProofSyntax Const (assumptions operations Γ)
      (.eq inst.source.code inst.target.code) :=
  HOL.ProofSyntax.castIndices (assumptions_substitute operations inst.targetSubstitution) rfl
    (HOL.ProofSyntax.subst inst.targetSubstitution (row.proof operations))

theorem proof_free (inst : Instance operations profile row Γ context) :
    inst.proof.FunctionExtensionalityFree := by
  simpa only [proof, HOL.ProofSyntax.functionExtensionalityFree_castIndices,
    HOL.ProofSyntax.functionExtensionalityFree_subst] using row.proof_free operations

end Instance

/-- The ordinary annotated beta rule retains the actual source typing premises
and the represented domain, body and argument. -/
structure BetaInstance (operations : Operations Base Const)
    (profile : Programs.ComputationProfiles.Selection)
    (Γ : HOL.Ctx Base) (context : CCtx Tower.Head Γ.length) where
  contextFormed : CCtxFormed (Programs.Annotated.church profile) context
  domain : CTm Tower.Head Γ.length
  body : CTm Tower.Head (Γ.length + 1)
  argument : CTm Tower.Head Γ.length
  family : CTm Tower.Head (Γ.length + 1)
  domainLevel : Tower.Head
  productLevel : Tower.Head
  domainUniverse : (Programs.ComputationProfiles.rules profile).isUniverse domainLevel
  productUniverse : (Programs.ComputationProfiles.rules profile).isUniverse productLevel
  domainTyped : CTyped (Programs.Annotated.church profile) context domain (.head domainLevel)
  productTyped : CTyped (Programs.Annotated.church profile) context (.pi domain family) (.head productLevel)
  bodyTyped : CTyped (Programs.Annotated.church profile) (.snoc context domain) body family
  argumentTyped : CTyped (Programs.Annotated.church profile) context argument domain
  domainCarrier : HOL.Ty Base
  resultCarrier : HOL.Ty Base
  domainCode : HOL.Term Const Γ (.arr domainCarrier .prop)
  bodyCode : HOL.Term Const (domainCarrier :: Γ) resultCarrier
  argumentCode : HOL.Term Const Γ domainCarrier
  domainReading : AnnotatedReads operations domain domainCode
  bodyReading : AnnotatedReads operations (Γ := domainCarrier :: Γ) body bodyCode
  argumentReading : AnnotatedReads operations argument argumentCode

namespace BetaInstance

variable {operations : Operations Base Const} {profile : Programs.ComputationProfiles.Selection}
    {Γ : HOL.Ctx Base} {context : CCtx Tower.Head Γ.length}

def index (inst : BetaInstance operations profile Γ context) : Index Base :=
  ⟨Γ, context, CTm.inst0 inst.argument inst.family, inst.resultCarrier⟩

def source (inst : BetaInstance operations profile Γ context) :
    State operations profile inst.index where
  contextFormed := inst.contextFormed
  term := .app (.lam inst.domain inst.body) inst.argument
  typed := .appElim
    (.lamIntro inst.domainTyped inst.domainUniverse inst.productTyped inst.productUniverse inst.bodyTyped)
    inst.argumentTyped
  code := .app (.lam inst.bodyCode) inst.argumentCode
  reading := .application (.abstraction inst.domainReading inst.bodyReading) inst.argumentReading

def target (inst : BetaInstance operations profile Γ context) :
    State operations profile inst.index where
  contextFormed := inst.contextFormed
  term := CTm.inst0 inst.argument inst.body
  typed := inst.bodyTyped.substitute (CSubstMor.single inst.argumentTyped)
  code := HOL.instantiate inst.argumentCode inst.bodyCode
  reading := inst.bodyReading.instantiate inst.argumentReading

theorem source_equal (inst : BetaInstance operations profile Γ context) :
    CEqual (Programs.Annotated.church profile) context inst.source.term inst.target.term
      inst.index.sourceType :=
  .betaPi inst.productTyped inst.productUniverse inst.bodyTyped inst.argumentTyped

def proof (inst : BetaInstance operations profile Γ context) :
    HOL.ProofSyntax Const (assumptions operations Γ) (.eq inst.source.code inst.target.code) :=
  .beta inst.argumentCode inst.bodyCode

end BetaInstance

/-- The original row address remains in the step. Beta is always available;
each natural row also requires its source profile and bubble permissions. -/
inductive Step (operations : Operations Base Const)
    (profile enabled : Programs.ComputationProfiles.Selection) :
    {index : Index Base} → State operations profile index → State operations profile index → Type (max u v) where
  | row {row : Row} {Γ : HOL.Ctx Base} {context : CCtx Tower.Head Γ.length}
      (inst : Instance operations profile row Γ context)
      (inProfile : profile row.address = true) (permitted : enabled row.address = true) :
      Step operations profile enabled inst.source inst.target
  | beta {Γ : HOL.Ctx Base} {context : CCtx Tower.Head Γ.length}
      (inst : BetaInstance operations profile Γ context) :
      Step operations profile enabled inst.source inst.target

def bubbles (operations : Operations Base Const) (profile : Programs.ComputationProfiles.Selection) :
    BubbleConversion.Bubbles (Index Base) where
  State := State operations profile
  Bubble := Programs.ComputationProfiles.Selection
  Step := Step operations profile

def holEquality (operations : Operations Base Const) (profile : Programs.ComputationProfiles.Selection) :
    (bubbles operations profile).GlobalEquality where
  Eq {index} source target := HOL.ProofSyntax Const (assumptions operations index.targetContext)
    (.eq source.code target.code)
  refl source := .eqRefl source.code
  symm proof := .eqSymm proof
  trans first second := .eqTrans first second

def sourceEquality (operations : Operations Base Const) (profile : Programs.ComputationProfiles.Selection) :
    (bubbles operations profile).GlobalEquality where
  Eq {index} source target := PLift (CEqual (Programs.Annotated.church profile)
    index.sourceContext source.term target.term index.sourceType)
  refl source := ⟨.refl source.typed⟩
  symm proof := ⟨.symm proof.down⟩
  trans first second := ⟨.trans first.down second.down⟩

namespace Step

variable {operations : Operations Base Const} {profile enabled : Programs.ComputationProfiles.Selection}

def proof : {index : Index Base} → {source target : State operations profile index} →
    Step operations profile enabled source target → (holEquality operations profile).Eq source target
  | _, _, _, .row inst _ _ => inst.proof
  | _, _, _, .beta inst => inst.proof

def sourceProof : {index : Index Base} → {source target : State operations profile index} →
    Step operations profile enabled source target → (sourceEquality operations profile).Eq source target
  | _, _, _, .row inst inProfile _ => ⟨inst.source_equal inProfile⟩
  | _, _, _, .beta inst => ⟨inst.source_equal⟩

theorem proof_free {index : Index Base} {source target : State operations profile index}
    (step : Step operations profile enabled source target) : step.proof.FunctionExtensionalityFree := by
  cases step with
  | row inst _ _ => exact inst.proof_free
  | beta inst => trivial

end Step

variable {operations : Operations Base Const} {profile enabled : Programs.ComputationProfiles.Selection}
    {index : Index Base} {source target : State operations profile index}

/-- Actual retained HOL equality for every typed beta/natural-row tree. -/
def elaborate (path : (bubbles operations profile).Conv enabled source target) :
    HOL.ProofSyntax Const (assumptions operations index.targetContext) (.eq source.code target.code) :=
  (bubbles operations profile).sound (holEquality operations profile) Step.proof path

/-- The same tree is a typed equality in the original annotated declaration
profile. Source and target interpretations do not replace that judgment. -/
theorem source_equal (path : (bubbles operations profile).Conv enabled source target) :
    CEqual (Programs.Annotated.church profile) index.sourceContext source.term target.term index.sourceType :=
  ((bubbles operations profile).sound (sourceEquality operations profile) Step.sourceProof path).down

theorem elaborate_free (path : (bubbles operations profile).Conv enabled source target) :
    (elaborate path).FunctionExtensionalityFree := by
  induction path using @JudgmentalEquality.ConversionEvidence.rec (Index Base)
      (FreeConversion.computation (bubbles operations profile).State
        ((bubbles operations profile).Step enabled)) index with
  | step step =>
      simpa only [elaborate, BubbleElaboration.sound_step] using step.proof_free
  | refl state =>
      simp only [elaborate, BubbleElaboration.sound_refl, holEquality,
        HOL.ProofSyntax.FunctionExtensionalityFree]
  | symm path ih =>
      simpa only [elaborate, BubbleElaboration.sound_symm, holEquality,
        HOL.ProofSyntax.FunctionExtensionalityFree] using ih
  | trans first second ihFirst ihSecond =>
      simpa only [elaborate, BubbleElaboration.sound_trans, holEquality,
        HOL.ProofSyntax.FunctionExtensionalityFree] using And.intro ihFirst ihSecond

theorem Step.disabled_source_is_beta {source target : State operations profile index}
    (step : Step operations profile (fun _ => false) source target) :
    ∃ domain body argument, source.term = CTm.app (CTm.lam domain body) argument := by
  cases step with
  | row _ _ permitted => cases permitted
  | beta inst => exact ⟨inst.domain, inst.body, inst.argument, rfl⟩

/-- At one judgement index, the actual annotated source determines its target
code and hence the complete interpreted state. -/
theorem State.ext [DecidableEq Base] (first second : State operations profile index)
    (same : first.term = second.term) : first = second := by
  cases first with
  | mk formedFirst first typedFirst codeFirst readingFirst =>
    cases second with
    | mk formedSecond second typedSecond codeSecond readingSecond =>
      dsimp only at same
      subst second
      have codeSame := AnnotatedReading.term_unique readingFirst readingSecond
      subst codeSecond
      rfl

def Step.widen {large : Programs.ComputationProfiles.Selection}
    (included : ∀ row, enabled row = true → large row = true) :
    {index : Index Base} → {source target : State operations profile index} →
      Step operations profile enabled source target → Step operations profile large source target
  | _, _, _, .row inst inProfile permitted => .row inst inProfile (included _ permitted)
  | _, _, _, .beta inst => .beta inst

theorem Step.proof_widen {large : Programs.ComputationProfiles.Selection}
    (included : ∀ row, enabled row = true → large row = true)
    {source target : State operations profile index} (step : Step operations profile enabled source target) :
    (step.widen included).proof = step.proof := by
  cases step <;> rfl

/-- Widening permissions preserves the retained proof tree literally. -/
theorem elaborate_widen {large : Programs.ComputationProfiles.Selection}
    (included : ∀ row, enabled row = true → large row = true)
    (path : (bubbles operations profile).Conv enabled source target) :
    elaborate ((bubbles operations profile).widen (Step.widen included) path) = elaborate path :=
  BubbleElaboration.sound_widen (bubbles operations profile) (holEquality operations profile)
    (Step.widen included) Step.proof Step.proof (Step.proof_widen included) path

#print axioms assumptions_substitute
#print axioms Instance.source_equal
#print axioms Instance.proof
#print axioms elaborate
#print axioms source_equal
#print axioms State.ext
#print axioms elaborate_widen
#print axioms elaborate_free

end AnnotatedConversion
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
