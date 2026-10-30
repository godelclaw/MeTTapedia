import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalGuardedContexts
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalPredicateControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.AnnotatedCertificateProducer

/-!
# Actual source telescopes and dependent guard controls

The two original Nat contexts pass formation replay and the independent
guard reader. Their instantiated universe heads, predicate carriers and
ordered dependent guards are retained. A separate open predicate/value
telescope constructs an identity function and guarded closing substitutions;
a carrier-correct assignment into the empty predicate is refuted semantically.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading.GuardedContexts.Controls
open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Annotated NativeNaturalVectorFamilies
open HOL.PredicateContexts
local infixr:60 " ⇒ " => HOL.Ty.arr

def operations := NativeNaturalPredicateReading.Controls.operations
abbrev Const := HOL.NaturalRecursionProofControls.Const
def profile : Programs.ComputationProfiles.Selection := fun _ => true

def certificate : (row : AnnotatedConversion.Row) →
    Programs.Annotated.JudgmentReplay.ContextCertificate profile (row.parameters operations).length
  | .zero => by annotated_context_certificate 5000 (Programs.Annotated.Evidence.context_0 profile)
  | .successor => by annotated_context_certificate 5000 (Programs.Annotated.Evidence.context_1 profile)

def received (row : AnnotatedConversion.Row) :=
  AnnotatedPredicateReading.Reader.admitContext? (Programs.Annotated.church profile) (lexical operations)
    (Programs.Annotated.JudgmentReplay.decoder profile) (row.parameters operations) (row.context operations)
    (certificate row)

theorem zero_admitted : (received .zero).isSome = true := by decide +kernel
theorem successor_admitted : (received .successor).isSome = true := by decide +kernel

theorem guard_counts : (received .zero).map (fun context => context.code.hypotheses.length) = some 3 ∧
    (received .successor).map (fun context => context.code.hypotheses.length) = some 4 := by decide +kernel

def sourceWeakening : (contextCode operations .zero).Realizes (HOL.Subst.ofRename HOL.Rename.weaken)
    (contextCode operations .successor).hypotheses :=
  AnnotatedPredicateReading.ContextReads.renamingRealizer (context_reads operations .zero)
    (context_reads operations .successor) HOL.Rename.weaken wk (fun _ => rfl)
    (CCtxRen.wk (AnnotatedConversion.Row.zero.context operations) (.const natName))

theorem source_weakening_retained : Nonempty
    (HOL.ProofSyntax Const (contextCode operations .successor).hypotheses
      (HOL.subst (HOL.Subst.ofRename HOL.Rename.weaken) ((contextCode operations .zero).guard HOL.Var.vz))) :=
  ⟨sourceWeakening HOL.Var.vz⟩

theorem result_from_guards_free : (resultTyping operations).FunctionExtensionalityFree := resultTyping_free operations

theorem old_level_table_refused :
    (AnnotatedPredicateReading.Reader.readContext? (lexicalReading operations) operations.parameters
      (AnnotatedConversion.Row.zero.context operations)).isNone = true := by decide +kernel

def malformedCertificate : Programs.Annotated.JudgmentReplay.ContextCertificate profile 3 :=
  match certificate .zero with
  | .snoc prior _ evidence => .snoc prior .legacyGround evidence

theorem malformed_formation_refused :
    (AnnotatedPredicateReading.Reader.admitContext? (Programs.Annotated.church profile) (lexical operations)
      (Programs.Annotated.JudgmentReplay.decoder profile) operations.parameters
      (AnnotatedConversion.Row.zero.context operations) malformedCertificate).isNone = true := by decide +kernel

theorem wrong_carrier_refused :
    (AnnotatedPredicateReading.Reader.readContext? (lexical operations) [operations.number ⇒ operations.number]
      (.snoc .nil (.const natName))).isNone = true := by decide +kernel

theorem non_predicate_refused :
    (AnnotatedPredicateReading.Reader.readContext? (lexical operations) [operations.number]
      (.snoc .nil (.const zeroName))).isNone = true := by decide +kernel

abbrev predicateType : HOL.Ty Unit := .prop ⇒ .prop
def predicateContext : Telescope Const [predicateType] :=
  .snoc .nil (HOL.PredicateProducts.full predicateType)
def dependentContext : Telescope Const [.prop, predicateType] :=
  .snoc predicateContext (.var .vz)

def sourcePredicate : CCtx Tower.Head 1 := .snoc .nil (.head (levelMap (.sort motiveLevel)))
def sourceDependent : CCtx Tower.Head 2 := .snoc sourcePredicate (.var 0)

theorem dependent_context_reads :
    AnnotatedPredicateReading.ContextReads (lexical operations) (Γ := [.prop, predicateType])
      sourceDependent dependentContext := by
  exact AnnotatedPredicateReading.ContextReads.snoc
    (Γ := [predicateType]) (type := HOL.Ty.prop) (context := sourcePredicate)
    (code := predicateContext) (domain := .var 0) (predicate := .var .vz)
    (AnnotatedPredicateReading.ContextReads.snoc (Γ := []) (type := predicateType)
      (context := CCtx.nil) (code := Telescope.nil)
      (domain := .head (levelMap (.sort motiveLevel)))
      (predicate := HOL.PredicateProducts.full predicateType) .nil
      (.head (by simp [lexical, operations, NativeNaturalPredicateReading.Controls.operations, HOL.PredicateProducts.full])))
    (.var .vz)

def dependentIdentity : HOL.ProofSyntax Const predicateContext.hypotheses
    (.app (HOL.PredicateProducts.pi (.var .vz) (HOL.weaken (.var .vz)))
      (.lam (.var (.vz : HOL.Var [.prop, predicateType] .prop)))) :=
  predicateContext.lambdaMember (.var .vz) (HOL.weaken (.var .vz)) (.var .vz)
    (dependentContext.variableProof .vz)

theorem dependent_identity_free : dependentIdentity.FunctionExtensionalityFree := by
  apply Telescope.lambdaMember_free
  simp [Telescope.variableProof, HOL.ProofSyntax.FunctionExtensionalityFree]

def fullPredicate : HOL.ClosedTerm Const predicateType := .lam .top
def emptyPredicate : HOL.ClosedTerm Const predicateType := .lam .bot

def predicateAssignment : predicateContext.Realizes (HOL.Subst.single fullPredicate) [] := by
  intro type index
  cases index with
  | vz => exact .impE (.eqPropER (.beta fullPredicate .top)) .topI
  | vs impossible => cases impossible

def valueContext : Telescope Const [.prop] := .snoc .nil fullPredicate
def valueAssignment : valueContext.Realizes (HOL.Subst.single (.top : HOL.ClosedTerm Const .prop)) [] := by
  intro type index
  cases index with
  | vz => exact .impE (.eqPropER (.beta .top .top)) .topI
  | vs impossible => cases impossible

def dependentAssignment : HOL.Subst Const [.prop, predicateType] [] :=
  HOL.Subst.comp (HOL.Subst.single (.top : HOL.ClosedTerm Const .prop))
    (HOL.Subst.lift (HOL.Subst.single fullPredicate))

def liftedAssignment : dependentContext.Realizes (HOL.Subst.lift (HOL.Subst.single fullPredicate))
    valueContext.hypotheses :=
  Telescope.Realizes.lift (target := Telescope.nil) predicateAssignment (.var .vz)

def dependentRealizer : dependentContext.Realizes dependentAssignment [] :=
  Telescope.Realizes.comp (target := valueContext) liftedAssignment valueAssignment

def transportedVariable := dependentRealizer.transport (dependentContext.variableProof .vz)

theorem guard_transport_retained : Nonempty
    (HOL.ProofSyntax Const [] (HOL.subst dependentAssignment (dependentContext.guard HOL.Var.vz))) :=
  ⟨transportedVariable⟩

def wrongAssignment : HOL.Subst Const [.prop, predicateType] [] :=
  HOL.Subst.comp (HOL.Subst.single (.top : HOL.ClosedTerm Const .prop))
    (HOL.Subst.lift (HOL.Subst.single emptyPredicate))

noncomputable def model := HOL.NaturalRecursionProofControls.model
def emptyValues : model.Valuation [] := fun index => nomatch index

noncomputable def motiveValues : model.Valuation [operations.motiveType] :=
  model.extend emptyValues (model.denote HOL.NaturalRecursionProofControls.family emptyValues)
noncomputable def baseValues : model.Valuation [operations.result, operations.motiveType] :=
  model.extend motiveValues (model.denote HOL.NaturalRecursionProofControls.base emptyValues)
noncomputable def parameterValues : model.Valuation operations.parameters :=
  model.extend baseValues (model.denote NativeNaturalPredicateReading.Controls.method emptyValues)

theorem parameter_guards_hold : (parameters operations).Satisfies model parameterValues := by
  change (Telescope.snoc _ operations.stepCode).Satisfies model (model.extend baseValues _)
  rw [Telescope.satisfies_snoc]
  constructor
  · change (Telescope.snoc _ operations.zeroCode).Satisfies model (model.extend motiveValues _)
    rw [Telescope.satisfies_snoc]
    constructor
    · change (Telescope.snoc Telescope.nil operations.motiveCode).Satisfies model (model.extend emptyValues _)
      rw [Telescope.satisfies_snoc]
      constructor
      · intro formula member
        cases member
      · intro index admitted present
        trivial
    · exact HOL.NaturalRecursionProofControls.base_fits
  · exact NativeNaturalPredicateReading.Controls.method_guard_holds

theorem typing_background_holds : HOL.Soundness.SatisfiesHyps model parameterValues (typingAssumptions operations) := by
  intro formula member
  rcases List.mem_append.mp member with root | guarded
  · simp only [rootAssumptions, List.mem_cons, List.not_mem_nil, or_false] at root
    rcases root with rfl | rfl | rfl
    · exact HOL.NaturalRecursionProofControls.selection_holds
    · exact HOL.NaturalRecursionProofControls.recursion_holds
    · exact HOL.NaturalRecursionProofControls.induction_holds
  · exact parameter_guards_hold formula guarded

theorem wrong_assignment_not_realizable : ¬ Nonempty (dependentContext.Realizes wrongAssignment []) := by
  rintro ⟨realizer⟩
  have contextHolds := realizer.satisfies_subst model
    (model.functionsRespectEqv_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _))
    emptyValues (fun index => nomatch index) (fun _ member => nomatch member)
  have impossible := dependentContext.satisfies_variable model _ contextHolds HOL.Var.vz
  exact impossible

theorem exact_context_recovered :
    AnnotatedPredicateReading.Reader.readContext? (lexical operations) [.prop, predicateType] sourceDependent =
      some ⟨dependentContext, dependent_context_reads⟩ :=
  AnnotatedPredicateReading.Reader.readContext_complete dependent_context_reads

theorem actual_context_map :
    AnnotatedPredicateReading.ContextReads (lexical operations) (Γ := operations.parameters)
      (AnnotatedConversion.Row.zero.context operations) (parameters operations) := by
  rw [zero_context_mapped]
  exact AnnotatedPredicateReading.ContextReads.mapLexical (lexical_map operations) (original_reads operations)

theorem actual_admission_available :
    ∃ evidence, AnnotatedPredicateReading.Reader.admitContext? (Programs.Annotated.church profile)
      (lexical operations) (Programs.Annotated.JudgmentReplay.decoder profile) operations.parameters
      (AnnotatedConversion.Row.zero.context operations) evidence = some (admitted operations profile .zero) :=
  AnnotatedPredicateReading.Reader.admitContext_complete (Programs.Annotated.church profile)
    (Programs.Annotated.JudgmentReplay.decoder profile) (admitted operations profile .zero)

#print axioms zero_admitted
#print axioms successor_admitted
#print axioms dependent_identity_free
#print axioms guard_transport_retained
#print axioms wrong_assignment_not_realizable
#print axioms exact_context_recovered
#print axioms source_weakening_retained
#print axioms result_from_guards_free
#print axioms parameter_guards_hold
#print axioms typing_background_holds
#print axioms actual_context_map
#print axioms actual_admission_available
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading.GuardedContexts.Controls
