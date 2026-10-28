import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateRealizability
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalVectorProfileControls

/-!
# Open predicate variables, retained functions and genuine substitutions

The source context contains a type variable and a value in that type. Its
reading uses an arbitrary predicate on the selected natural carrier. Identity
abstraction and application retain the predicate guard. Typed substitution
extends, composes and lifts this actual evidence. Models separate these open
guards from a uniform closed value or an unrealizable empty predicate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeGuardedRealizability.Controls
open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Annotated NativeNaturalVectorFamilies
open AnnotatedPredicateReading
local infixr:60 " ⇒ " => HOL.Ty.arr

abbrev BaseSort := NativeNaturalVectorProfile.Controls.BaseSort
abbrev Const := NativeNaturalVectorProfile.Controls.Const
def raw := NativeNaturalVectorProfile.Controls.raw
def vectorInterface := NativeNaturalVectorProfile.Controls.vectorInterface
def naturalSelection := NativeNaturalVectorProfile.Controls.naturalSelection
def profile := NativeNaturalVectorProfile.Controls.profile
def lex := NativeNaturalVectorProfile.Controls.lex
def roots := NativeNaturalVectorProfile.closedAssumptions raw vectorInterface naturalSelection
abbrev number := raw.number
abbrev predicateType := number ⇒ HOL.Ty.prop

def universeHead : Tower.Head := NativeVectorComputationRows.GuardedFamily.motiveHead
def nextHead : Tower.Head := .sort (.succ (.max elementLevel motiveLevel))

def baseContext : GuardedContext (Programs.Annotated.church profile) lex [predicateType] where
  source := .snoc .nil (.head universeHead)
  telescope := .snoc .nil (HOL.PredicateProducts.full predicateType)
  formed := .snoc .nil ⟨nextHead, by decide +kernel, .headType (by decide +kernel)⟩
  reading := .snoc .nil (.head (by decide +kernel))

def domain : CTm Tower.Head 1 := .var 0
def predicate : HOL.Term Const [predicateType] (number ⇒ .prop) := .var .vz

theorem domain_read : Reads lex (Γ := [predicateType]) domain predicate :=
  Reads.var (lex := lex) (Γ := [predicateType]) (.vz : HOL.Var [predicateType] predicateType)

theorem domain_formed : CIsType (Programs.Annotated.church profile) baseContext.source domain :=
  ⟨universeHead, by decide +kernel, .var 0⟩

def valueContext := baseContext.snoc predicate domain_read domain_formed

theorem family_formed : CIsType (Programs.Annotated.church profile) valueContext.source (.var 1) :=
  ⟨universeHead, by decide +kernel, .var 1⟩

def variableValue := GuardedRealizer.ofVariable roots valueContext (.vz : HOL.Var [number, predicateType] number)

def identityValue := GuardedRealizer.abstraction (Programs.Annotated.levelModel profile)
  predicate domain_read domain_formed family_formed variableValue

def weakening := GuardedSubstitution.weakening roots baseContext predicate domain_read domain_formed

def weakenedIdentity := identityValue.substitute weakening

def appliedIdentity := GuardedRealizer.application weakenedIdentity variableValue

def supplied := GuardedSubstitution.cons weakening predicate domain_read domain_formed appliedIdentity

def composed := supplied.comp supplied

def lifted := supplied.lift variableValue.predicate variableValue.typeRead
  (valueContext.formed.lookup (0 : Fin 2))

theorem variable_free : variableValue.Free := GuardedRealizer.ofVariable_free roots valueContext _

theorem identity_free : identityValue.Free :=
  GuardedRealizer.abstraction_free _ _ _ _ _ _ variable_free

theorem weakening_free : weakening.Free :=
  GuardedSubstitution.ofRenaming_free roots baseContext valueContext wk HOL.Rename.weaken (fun _ => rfl)
    (CCtxRen.wk baseContext.source domain)

theorem application_free : appliedIdentity.Free :=
  GuardedRealizer.application_free weakenedIdentity variableValue
    (GuardedRealizer.substitute_free identityValue weakening identity_free weakening_free) variable_free

theorem supplied_free : supplied.Free :=
  GuardedSubstitution.cons_free weakening predicate domain_read domain_formed appliedIdentity weakening_free application_free

theorem composed_free : composed.Free := GuardedSubstitution.comp_free supplied supplied supplied_free supplied_free

theorem lifted_free : lifted.Free :=
  GuardedSubstitution.lift_free supplied variableValue.predicate variableValue.typeRead
    (valueContext.formed.lookup (0 : Fin 2)) supplied_free

theorem application_source_typed : CTyped (Programs.Annotated.church profile) valueContext.source
    (.app (.lam (.var 1) (.var 0)) (.var 0)) (.var 1) := appliedIdentity.typed


def expandedType : CTm Tower.Head 2 := .app (.lam (.var 1) (.var 2)) (.var 0)

theorem source_type_expansion : CTypeEq (Programs.Annotated.church profile) valueContext.source (.var 1) expandedType := by
  have Aformed : CIsType (Programs.Annotated.church profile) valueContext.source (.var 1) := family_formed
  have universeFormed : CIsType (Programs.Annotated.church profile) (.snoc valueContext.source (.var 1)) (.head universeHead) :=
    ⟨nextHead, by decide +kernel, .headType (by decide +kernel)⟩
  obtain ⟨level, allowed, formed⟩ := CIsType.pi (Programs.Annotated.levelModel profile) Aformed universeFormed
  have body : CTyped (Programs.Annotated.church profile) (.snoc valueContext.source (.var 1)) (.var 2) (.head universeHead) := .var 2
  have beta := CDerivable.betaPi formed allowed body variableValue.typed
  exact ⟨universeHead, by decide +kernel, .symm beta⟩

def semanticTypeExpansion : EqualityAt lex roots [number, predicateType] (.var 1) expandedType (number ⇒ .prop) :=
  EqualityAt.symm (EqualityAt.beta
    (Reads.var (lex := lex) (Γ := [number, predicateType]) (.vs .vz : HOL.Var [number, predicateType] predicateType))
    (Reads.var (lex := lex) (Γ := [number, number, predicateType]) (.vs (.vs .vz) : HOL.Var [number, number, predicateType] predicateType))
    (Reads.var (lex := lex) (Γ := [number, predicateType]) (.vz : HOL.Var [number, predicateType] number)))

def convertedValue := variableValue.convert source_type_expansion semanticTypeExpansion

theorem converted_free : convertedValue.Free := by
  apply GuardedRealizer.convert_free _ _ _ variable_free
  simp [semanticTypeExpansion, EqualityAt.symm, EqualityAt.beta, HOL.ProofSyntax.FunctionExtensionalityFree]

theorem wrong_expected_carrier_refused :
    (Reader.readTyped? lex [number, predicateType] (.var 1) number).isNone = true := by decide +kernel

def contextCertificate : Programs.Annotated.JudgmentReplay.ContextCertificate profile 2 := by
  annotated_context_certificate 8000 valueContext.formed

def applicationCertificate : Programs.Annotated.JudgmentReplay.Certificate profile := by
  annotated_certificate 8000 application_source_typed

def conversionCertificate : Programs.Annotated.JudgmentReplay.Certificate profile := by
  annotated_certificate 8000 convertedValue.typed

theorem context_checked : Programs.Annotated.JudgmentReplay.checkContext profile valueContext.source contextCertificate = true := by
  decide +kernel

theorem application_checked : Programs.Annotated.JudgmentReplay.check profile applicationCertificate
    (.typing valueContext.source (.app (.lam (.var 1) (.var 0)) (.var 0)) (.var 1)) = true := by decide +kernel

theorem conversion_checked : Programs.Annotated.JudgmentReplay.check profile conversionCertificate
    (.typing valueContext.source (.var 0) expandedType) = true := by decide +kernel

theorem changed_source_type_refused : Programs.Annotated.JudgmentReplay.check profile applicationCertificate
    (.typing valueContext.source (.app (.lam (.var 1) (.var 0)) (.var 0)) (.const natName)) = false := by decide +kernel

noncomputable def model := NativeNaturalVectorProfile.Controls.model
def emptyValues : model.Valuation [] := fun index => nomatch index
noncomputable def predicateValues (chosen : Nat) : model.Valuation [predicateType] :=
  model.extend (σ := predicateType) emptyValues (fun value => ULift.up (value.down = chosen))
noncomputable def values (chosen : Nat) : model.Valuation [number, predicateType] :=
  model.extend (σ := number) (predicateValues chosen) (ULift.up chosen)

theorem guards_hold (chosen : Nat) : valueContext.telescope.Satisfies model (values chosen) := by
  change (HOL.PredicateContexts.Telescope.snoc baseContext.telescope predicate).Satisfies model
    (model.extend (σ := number) (predicateValues chosen) (ULift.up chosen))
  rw [HOL.PredicateContexts.Telescope.satisfies_snoc]
  constructor
  · change (HOL.PredicateContexts.Telescope.snoc .nil (HOL.PredicateProducts.full predicateType)).Satisfies model
      (model.extend (σ := predicateType) emptyValues (fun value => ULift.up (value.down = chosen)))
    rw [HOL.PredicateContexts.Telescope.satisfies_snoc]
    exact ⟨(fun _ absent => nomatch absent), True.intro⟩
  · rfl

theorem background_holds (chosen : Nat) : HOL.Soundness.SatisfiesHyps model (values chosen) (valueContext.hypotheses roots) := by
  intro formula present
  change formula ∈ assumptions roots [number, predicateType] ++ valueContext.telescope.hypotheses at present
  rcases List.mem_append.mp present with root | guard
  · change formula ∈ roots.map (HOL.weakenCtx [number, predicateType]) at root
    obtain ⟨closed, inside, rfl⟩ := List.mem_map.mp root
    change (model.denote (HOL.weakenCtx _ closed) (values chosen)).down
    rw [model.denote_weakenCtx]
    exact NativeNaturalVectorProfile.Controls.root_background_realizable closed inside
  · exact guards_hold chosen formula guard

theorem application_valid (chosen : Nat) :
    (model.denote (.app appliedIdentity.predicate appliedIdentity.term) (values chosen)).down :=
  appliedIdentity.satisfies model
    (model.functionsRespectEqv_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _))
    (values chosen) (fun _ => trivial) (background_holds chosen)

def suppliedCode : HOL.Subst Const [number, predicateType] [number, predicateType] :=
  HOL.Subst.cons appliedIdentity.term (HOL.Subst.ofRename HOL.Rename.weaken)

theorem composed_preserves_guards (chosen : Nat) :
    HOL.Soundness.SatisfiesHyps model
      (HOL.Soundness.substVal model (HOL.Subst.comp suppliedCode suppliedCode) (values chosen))
      (valueContext.hypotheses roots) :=
  composed.satisfies model
    (model.functionsRespectEqv_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _))
    (values chosen) (fun _ => trivial) (background_holds chosen)

theorem application_at_two :
    (model.denote (.app appliedIdentity.predicate appliedIdentity.term) (values 2)).down :=
  GuardedRealizer.satisfies appliedIdentity model
    (model.functionsRespectEqv_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _))
    (values 2) (fun _ => trivial) (background_holds 2)

theorem composed_at_two :
    HOL.Soundness.SatisfiesHyps model
      (HOL.Soundness.substVal model (HOL.Subst.comp suppliedCode suppliedCode) (values 2))
      (valueContext.hypotheses roots) :=
  GuardedSubstitution.satisfies composed model
    (model.functionsRespectEqv_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _))
    (values 2) (fun _ => trivial) (background_holds 2)

def emptyContext : GuardedContext (Programs.Annotated.church profile) lex [] := ⟨.nil, .nil, .nil, .nil⟩
def sourceVectorType : CTm Tower.Head 0 := liftTm (RussellTarski.substLevelsTm Programs.levels vecType)
abbrev vectorFamilyCarrier :=
  NativeNaturalVectorProfile.Controls.vectorOps.elementPredicate ⇒ number ⇒
    NativeNaturalVectorProfile.Controls.vectorOps.vector ⇒ HOL.Ty.prop

theorem vector_declaration_readable : (Reader.infer? lex [] sourceVectorType).isSome = true := by decide +kernel

theorem vector_former_value_type_refused :
    (Reader.readTyped? lex [] sourceVectorType (vectorFamilyCarrier ⇒ .prop)).isNone = true := by decide +kernel

/-- The fixed-carrier universe reading does not turn the Vec type former
itself into a value of its declared universe-valued function type. -/
theorem no_vector_former_value :
    ¬ Nonempty (GuardedRealizer roots emptyContext (.const vecName) sourceVectorType vectorFamilyCarrier) := by
  rintro ⟨value⟩
  have refused := vector_former_value_type_refused
  rw [Reader.readTyped?_complete value.typeRead] at refused
  cases refused

def emptyPredicate : HOL.ClosedTerm Const predicateType := .lam .bot
def emptyAssignment : HOL.Subst Const [] [] := fun index => nomatch index
def wrongCode : HOL.Subst Const [number, predicateType] [] :=
  HOL.Subst.cons raw.zero (HOL.Subst.cons emptyPredicate emptyAssignment)

theorem empty_background_holds : HOL.Soundness.SatisfiesHyps model emptyValues (emptyContext.hypotheses roots) := by
  intro formula present
  change formula ∈ roots.map (HOL.weakenCtx []) ++ [] at present
  rw [List.append_nil] at present
  obtain ⟨closed, inside, rfl⟩ := List.mem_map.mp present
  change (model.denote (HOL.weakenCtx [] closed) emptyValues).down
  rw [model.denote_weakenCtx]
  exact NativeNaturalVectorProfile.Controls.root_background_realizable closed inside

theorem empty_guard_refuses (rawAssignment : CSub Tower.Head 2 0) :
    ¬ Nonempty (GuardedSubstitution roots valueContext emptyContext rawAssignment wrongCode) := by
  rintro ⟨realizer⟩
  have impossible := HOL.Soundness.extDerivation_sound
    (realizer.guards (.vz : HOL.Var [number, predicateType] number)).erase
    (model.functionsRespectEqv_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _))
    (fun index => nomatch index) empty_background_holds
  change False at impossible
  exact impossible

/-- No fixed closed value can agree with this open variable at all the
realizing valuations. This makes no source-conversion completeness claim. -/
theorem no_uniform_closed_value (closed : HOL.ClosedTerm Const number) :
    ¬ (∀ chosen, model.denote variableValue.term (values chosen) = model.denote closed emptyValues) := by
  intro uniform
  have different := (uniform 2).trans (uniform 3).symm
  change (ULift.up 2 : ULift.{1} Nat) = ULift.up 3 at different
  have impossible : (2 : Nat) = 3 := congrArg ULift.down different
  omega

#print axioms baseContext
#print axioms application_free
#print axioms context_checked
#print axioms application_checked
#print axioms conversion_checked
#print axioms changed_source_type_refused
#print axioms converted_free
#print axioms wrong_expected_carrier_refused
#print axioms supplied_free
#print axioms composed_free
#print axioms lifted_free
#print axioms guards_hold
#print axioms application_valid
#print axioms no_uniform_closed_value
#print axioms composed_preserves_guards
#print axioms empty_guard_refuses
#print axioms no_vector_former_value
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeGuardedRealizability.Controls
