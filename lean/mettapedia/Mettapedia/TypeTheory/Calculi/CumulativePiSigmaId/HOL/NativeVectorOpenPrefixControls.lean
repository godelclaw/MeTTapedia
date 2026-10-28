import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorOpenPrefixConversion

/-!
# Realizing and separating the open vector prefix

Two valuations realize the original dependent context, with tails of lengths
zero and one. The motive asks for the actual vector length. The retained result
membership therefore separates the open computation from every one uniform
closed result. This is a statement about this interpretation, not arbitrary
source nonconvertibility.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorOpenPrefix
namespace Controls
open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Annotated AnnotatedPredicateReading NativeNaturalVectorFamilies
local infixr:60 " ⇒ " => HOL.Ty.arr

abbrev cacheContext : HOL.Ctx BaseSort := [.prop, .arr .prop .prop]

def cacheAssignment : HOL.Subst Const cacheContext []
  | _, .vz => .bot
  | _, .vs .vz => .lam (.var .vz)

def cacheTerm : HOL.Term Const cacheContext .prop := .app (.var (.vs .vz)) (.var .vz)
def cacheExpected : HOL.ClosedFormula Const := .app (.lam (.var .vz)) .bot

def cacheProof : HOL.ProofSyntax Const [] (.eq cacheTerm cacheTerm) := .eqRefl cacheTerm

def cachedProof := HOL.ProofSyntax.substCached cacheAssignment cacheProof

theorem cached_proof_exact : cachedProof = cacheProof.subst cacheAssignment :=
  HOL.ProofSyntax.substCached_eq cacheAssignment cacheProof

theorem cached_term_expected : HOL.subst (HOL.Subst.Table.ofSubst cacheAssignment).lookup cacheTerm = cacheExpected := rfl

theorem changed_cached_argument_refused :
    HOL.subst (HOL.Subst.Table.ofSubst cacheAssignment).lookup cacheTerm ≠
      (HOL.Term.app (.lam (.var .vz)) .top : HOL.ClosedFormula Const) := by
  intro same
  cases same

abbrev duplicateHypotheses : List (HOL.ClosedFormula Const) := [.top, .top]

def exchangedHypotheses : HOL.ProofSyntax.HypothesisSubstitution duplicateHypotheses duplicateHypotheses :=
  Fin.cases (.hyp (Δ := duplicateHypotheses) 1) (Fin.cases (.hyp (Δ := duplicateHypotheses) 0) (fun impossible => Fin.elim0 impossible))

def orderedHypothesesProof : HOL.ProofSyntax Const duplicateHypotheses (.and .top .top) :=
  .andI (.hyp (Δ := duplicateHypotheses) 0) (.hyp (Δ := duplicateHypotheses) 1)

def cachedHypothesesProof := HOL.ProofSyntax.substituteHypothesesCached exchangedHypotheses orderedHypothesesProof

theorem cached_hypotheses_exact : cachedHypothesesProof =
    HOL.ProofSyntax.substituteHypotheses exchangedHypotheses orderedHypothesesProof :=
  HOL.ProofSyntax.substituteHypothesesCached_eq exchangedHypotheses orderedHypothesesProof

theorem cached_hypotheses_order : cachedHypothesesProof = .andI (.hyp (Δ := duplicateHypotheses) 1) (.hyp (Δ := duplicateHypotheses) 0) := rfl

theorem wrong_hypothesis_order_refused : cachedHypothesesProof ≠ .andI (.hyp (Δ := duplicateHypotheses) 0) (.hyp (Δ := duplicateHypotheses) 1) := by
  intro same
  cases same

def binderProof : HOL.ProofSyntax Const (Γ := cacheContext) []
    (.all (σ := .prop) (.eq (.var (.vs (.vz : HOL.Var cacheContext .prop))) (.var (.vs (.vz : HOL.Var cacheContext .prop))))) :=
  .allI (.eqRefl (.var (.vs .vz)))

theorem shared_renaming_exact :
    HOL.ProofSyntax.renameShared (HOL.Rename.weaken (σ := HOL.Ty.prop)) binderProof =
      HOL.ProofSyntax.rename (HOL.Rename.weaken (σ := HOL.Ty.prop)) binderProof :=
  HOL.ProofSyntax.renameShared_eq (HOL.Rename.weaken (σ := HOL.Ty.prop)) binderProof

noncomputable def model := NativeNaturalVectorProfile.Controls.model

def emptyValues : model.Valuation [] := fun index => nomatch index

noncomputable def baseValues : model.Valuation baseParameters :=
  NativeVectorComputationRows.GuardedFamily.Controls.parameterValues
noncomputable def xValues : model.Valuation (operations.element :: baseParameters) := model.extend baseValues (σ := operations.element) (ULift.up false)
noncomputable def yValues : model.Valuation (operations.element :: operations.element :: baseParameters) := model.extend xValues (σ := operations.element) (ULift.up true)
noncomputable def indexValues (length : Nat) : model.Valuation (operations.number :: operations.element :: operations.element :: baseParameters) := model.extend yValues (σ := operations.number) (ULift.up length)

def elements : HOL.ClosedTerm Const operations.elementPredicate := HOL.PredicateProducts.full operations.element
def emptyTail : HOL.ClosedTerm Const operations.vector := .app operations.nilCode elements
def extraHead : HOL.ClosedTerm Const operations.element := .app operations.head emptyTail
def singletonTail : HOL.ClosedTerm Const operations.vector :=
  .app (.app (.app (.app operations.consCode elements) operations.zero) extraHead) emptyTail

def tailTerm (long : Bool) : HOL.ClosedTerm Const operations.vector := if long then singletonTail else emptyTail
def lengthTerm (long : Bool) : HOL.ClosedTerm Const operations.number :=
  if long then .app operations.successor operations.zero else operations.zero
def tailLength (long : Bool) : Nat := if long then 1 else 0

def tailMember (long : Bool) : HOL.ProofSyntax Const []
    (NativeVectorComputationRows.GuardedFamily.membership operations elements (lengthTerm long) (tailTerm long)) := by
  cases long
  · exact NativeVectorComputationRows.GuardedFamily.nil_member operations elements
  · exact NativeVectorComputationRows.GuardedFamily.cons_member operations elements operations.zero extraHead emptyTail
      (.impE (.eqPropER (.beta extraHead .top)) .topI)
      (NativeVectorComputationRows.GuardedFamily.nil_member operations elements)

noncomputable def values (long : Bool) : model.Valuation Conversion.parameters :=
  model.extend (indexValues (tailLength long)) (model.denote (tailTerm long) emptyValues)

theorem base_guards_equal : baseContext.telescope.hypotheses =
    NativeVectorComputationRows.GuardedFamily.Controls.originalGuards := by decide +kernel

theorem base_guards_hold : baseContext.telescope.Satisfies model baseValues := by
  unfold HOL.PredicateContexts.Telescope.Satisfies
  rw [base_guards_equal]
  exact NativeVectorComputationRows.GuardedFamily.Controls.original_guards_realizable

theorem x_guards_hold : xContext.telescope.Satisfies model xValues := by
  change (baseContext.telescope.snoc element4.predicate).Satisfies model (model.extend (σ := operations.element) baseValues (ULift.up false))
  rw [HOL.PredicateContexts.Telescope.satisfies_snoc]
  exact ⟨base_guards_hold, True.intro⟩

theorem y_guards_hold : yContext.telescope.Satisfies model yValues := by
  change (xContext.telescope.snoc element5.predicate).Satisfies model (model.extend (σ := operations.element) xValues (ULift.up true))
  rw [HOL.PredicateContexts.Telescope.satisfies_snoc]
  exact ⟨x_guards_hold, True.intro⟩

theorem index_guards_hold (length : Nat) : indexContext.telescope.Satisfies model (indexValues length) := by
  change (yContext.telescope.snoc number6.predicate).Satisfies model (model.extend (σ := operations.number) yValues (ULift.up length))
  rw [HOL.PredicateContexts.Telescope.satisfies_snoc]
  exact ⟨y_guards_hold, True.intro⟩

abbrev indexParameters : HOL.Ctx BaseSort := operations.number :: operations.element :: operations.element :: baseParameters

def family : HOL.ClosedTerm Const (operations.elementPredicate ⇒ operations.number ⇒ operations.vector ⇒ .prop) :=
  NativeVectorComputationRows.GuardedFamily.familyCode operations

def elementAtIndex : HOL.Term Const indexParameters operations.elementPredicate :=
  .var (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))

theorem vector_predicate_exact : vector7.predicate =
    .app (.app (HOL.weakenCtx indexParameters family) elementAtIndex) (.var .vz) := by decide +kernel

theorem family_denote {Γ : HOL.Ctx BaseSort} (A : HOL.Term Const Γ operations.elementPredicate)
    (n : HOL.Term Const Γ operations.number) (valuation : model.Valuation Γ) :
    model.denote (.app (.app (HOL.weakenCtx Γ family) A) n) valuation =
      model.denote family emptyValues (model.denote A valuation) (model.denote n valuation) := by
  have same := (model.denote_weakenCtx Γ family valuation).trans
    (model.denote_closed_valuation_eq family _ emptyValues)
  exact congrFun (congrFun same (model.denote A valuation)) (model.denote n valuation)


theorem guards_hold (long : Bool) : context.telescope.Satisfies model (values long) := by
  change (indexContext.telescope.snoc vector7.predicate).Satisfies model
    (model.extend (σ := operations.vector) (indexValues (tailLength long)) (model.denote (tailTerm long) emptyValues))
  rw [HOL.PredicateContexts.Telescope.satisfies_snoc]
  refine ⟨index_guards_hold _, ?_⟩
  have tailValid := HOL.Soundness.extDerivation_sound (tailMember long).erase
    (model.functionsRespectEqv_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _))
    (ρ := emptyValues) (fun _ => trivial) (fun _ absent => nomatch absent)
  rw [vector_predicate_exact, family_denote]
  change (model.denote family emptyValues (fun _ => ULift.up True) (ULift.up (tailLength long))
    (model.denote (tailTerm long) emptyValues)).down
  change (model.denote family emptyValues (model.denote elements emptyValues)
    (model.denote (lengthTerm long) emptyValues) (model.denote (tailTerm long) emptyValues)).down at tailValid
  cases long <;> exact tailValid

theorem background_holds (long : Bool) : HOL.Soundness.SatisfiesHyps model (values long) (context.hypotheses roots) := by
  intro formula present
  rcases List.mem_append.mp present with root | guard
  · obtain ⟨closed, inside, rfl⟩ := List.mem_map.mp root
    change (model.denote (HOL.weakenCtx _ closed) (values long)).down
    rw [model.denote_weakenCtx]
    exact NativeNaturalVectorProfile.Controls.root_background_realizable closed inside
  · exact guards_hold long formula guard

theorem source_value (long : Bool) :
    (model.denote realizedElimination.term (values long)).down = tailLength long + 2 := by
  have member := realizedElimination.satisfies model
    (model.functionsRespectEqv_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _))
    (values long) (fun _ => trivial) (background_holds long)
  exact member

theorem reduced_value (long : Bool) :
    (model.denote Conversion.reducedValue.term (values long)).down = tailLength long + 2 := by
  have member := Conversion.reducedValue.satisfies model
    (model.functionsRespectEqv_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _))
    (values long) (fun _ => trivial) (background_holds long)
  exact member

theorem reduced_at_empty :
    (model.denote Conversion.reducedValue.term (values false)).down = 2 :=
  GuardedRealizer.satisfies Conversion.reducedValue model
    (model.functionsRespectEqv_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _))
    (values false) (fun _ => trivial) (background_holds false)

theorem reduced_at_singleton :
    (model.denote Conversion.reducedValue.term (values true)).down = 3 :=
  GuardedRealizer.satisfies Conversion.reducedValue model
    (model.functionsRespectEqv_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _))
    (values true) (fun _ => trivial) (background_holds true)

theorem no_uniform_closed_value (closed : HOL.ClosedTerm Const operations.result) :
    ¬ ∀ long, model.denote Conversion.reducedValue.term (values long) = model.denote closed emptyValues := by
  intro same
  have atZero := congrArg ULift.down (same false)
  have atOne := congrArg ULift.down (same true)
  rw [reduced_value] at atZero atOne
  simp only [tailLength, Bool.false_eq_true, if_false, if_true] at atZero atOne
  omega

theorem no_uniform_closed_certificate (closed : HOL.ClosedTerm Const operations.result) :
    ¬ Nonempty (HOL.ProofSyntax Const (context.hypotheses roots)
      (.eq Conversion.reducedValue.term (HOL.weakenCtx Conversion.parameters closed))) := by
  rintro ⟨proof⟩
  apply no_uniform_closed_value closed
  intro long
  have valid := HOL.Soundness.extDerivation_sound proof.erase
    (model.functionsRespectEqv_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _))
    (ρ := values long) (fun _ => trivial) (background_holds long)
  have same : model.denote Conversion.reducedValue.term (values long) =
      model.denote (HOL.weakenCtx Conversion.parameters closed) (values long) :=
    (model.eqv_iff_eq_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _) _ _).mp valid
  exact same.trans ((model.denote_weakenCtx Conversion.parameters closed (values long)).trans
    (model.denote_closed_valuation_eq closed _ emptyValues))


#print axioms guards_hold
#print axioms source_value
end Controls
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorOpenPrefix
