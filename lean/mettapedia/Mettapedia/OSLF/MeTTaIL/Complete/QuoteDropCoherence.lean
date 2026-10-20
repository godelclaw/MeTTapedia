import Mettapedia.OSLF.MeTTaIL.Complete.DescentCoherence
import Mettapedia.OSLF.MeTTaIL.QuoteDropFiring

/-!
# The explorer is complete modulo the quote-drop equation

A reflective presentation declares the name equation `@(*n) = n`. The model of a plan with such a
presentation identifies terms related by that equation, in every context, besides the plan's
equations and its declared collection and scope-extrusion laws (`ModelEquation`). The equation
expands without bound from right to left, so the explorer never searches it: it commits the
quote-drop normal form of each target and then the canonical form of the collection laws
(`commit`). Together they are a canonical form for the model's law moves (`normalizer`): the
quote-drop normal form maps law-equal terms to law-equal terms.

Completeness transfers through the two stages. A firing at any presentation has a counterpart at
the quote-drop normal form (`QuoteDrop.primitive_normal`) and from there at the law-normal form
(`DescentCoherence.firingsNormalize_descent`). The invariant is well-sortedness of the quote-drop
normal form, which every law move keeps in both directions: a use of `@(*n) = n` from right to left
may leave the typed terms, but never changes the normal form.

- `explores_of_normalizer`: the explorer that commits a canonical form of any law-move relation is
  complete for the plan's steps modulo the equality those moves generate, when firings normalize;
- `presented_explores_quoteDrop`: the explorer that commits `commit` is complete for the plan's
  steps modulo the model with the quote-drop equation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Complete.QuoteDropCoherence

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission CanonicalBags Coherence
open Mettapedia.GSLT.LanguageDef.WellSorted QuoteDrop
open Relation (EqvGen)

variable (plan : Plan) (bound : List TypeExpr) (expected : TypeExpr)

/-! ## Explorers committing a canonical form -/

/-- The search modulo equations, committing a given form of each target. -/
def searchWith (form : Pattern → Pattern) :
    Mettapedia.Machines.ResumableSearchRunner.Search Pattern (Classes.State plan) GeneralOccurrenceSemantics.Receipt :=
  { Classes.search plan bound expected with target := fun receipt => form receipt.target }

theorem searchWith_lawful (form : Pattern → Pattern) : (searchWith plan bound expected form).Lawful where
  resume_run := (Classes.search_lawful plan bound expected).resume_run
  publication_prefix := (Classes.search_lawful plan bound expected).publication_prefix
  sound := (Classes.search_lawful plan bound expected).sound

variable {plan bound expected}

/-- Without equations, the normalized class of a state is the state. -/
theorem normalClass_eq (noEquations : ∀ left right, ¬ GeneralOccurrenceSemantics.Equation plan bound expected left right)
    {form : Pattern → Pattern} {state reached : Pattern}
    (inClass : NormalClass (GeneralOccurrenceSemantics.Equation plan bound expected) form state reached) :
    reached = state := by
  induction inClass with
  | refl => rfl
  | tail _ step _ =>
    obtain ⟨_, equation, _⟩ := step
    rcases equation with forward | backward
    · exact absurd forward (noEquations _ _)
    · exact absurd backward (noEquations _ _)

/-- **The explorer committing a canonical form is complete**: for a plan without equations, a
relation of law moves with a canonical form, and firings that normalize at every presentation
satisfying an invariant kept by every move and by committed firings, every state reachable from a
source satisfying it by finitely many steps modulo the equality of the moves is explored, up to
that equality. -/
theorem explores_of_normalizer (checked : Predecessors.equationsChecked plan = true)
    (noEquations : ∀ left right, ¬ GeneralOccurrenceSemantics.Equation plan bound expected left right)
    {moves : Pattern → Pattern → Prop} {form : Pattern → Pattern} (normalizer : Normalizer moves form)
    {good : Pattern → Prop}
    (stable : ∀ a b, (GeneralOccurrenceSemantics.Equation plan bound expected a b ∨ moves a b) → (good a ↔ good b))
    (committed : ∀ term (receipt : GeneralRuleJobs.Receipt), GeneralOccurrenceSemantics.Primitive plan bound expected term
      receipt → good (form receipt.target))
    (normalize : FiringsNormalizeOn (GeneralOccurrenceSemantics.Equation plan bound expected) moves form
      (GeneralOccurrenceSemantics.Primitive plan bound expected) GeneralRuleJobs.Receipt.target good)
    (source : Pattern) (holds : good (form source)) {target : Pattern}
    (reaches : (Mettapedia.OSLF.Framework.FiniteEquationCoverage.moduloGSLT
      (fun a b => GeneralOccurrenceSemantics.Equation plan bound expected a b ∨ moves a b)
      (GeneralOccurrenceSemantics.Primitive plan bound expected) GeneralRuleJobs.Receipt.target).MultiStep source target) :
    ∃ state, Explore.Explored (S := searchWith plan bound expected form) (form source) state ∧
      EqvGen (fun a b => GeneralOccurrenceSemantics.Equation plan bound expected a b ∨ moves a b) state target := by
  have lift : EquationsLift (GeneralOccurrenceSemantics.Equation plan bound expected) form := by
    intro left right equation
    rcases equation with forward | backward
    · exact absurd forward (noEquations _ _)
    · exact absurd backward (noEquations _ _)
  suffices along : ∀ first last, (Mettapedia.OSLF.Framework.FiniteEquationCoverage.moduloGSLT
      (fun a b => GeneralOccurrenceSemantics.Equation plan bound expected a b ∨ moves a b)
      (GeneralOccurrenceSemantics.Primitive plan bound expected) GeneralRuleJobs.Receipt.target).MultiStep first last →
      ∀ state, Explore.Explored (S := searchWith plan bound expected form) (form source) state →
      form state = state → good state →
      EqvGen (fun a b => GeneralOccurrenceSemantics.Equation plan bound expected a b ∨ moves a b) state first →
      ∃ reached, Explore.Explored (S := searchWith plan bound expected form) (form source) reached ∧
        EqvGen (fun a b => GeneralOccurrenceSemantics.Equation plan bound expected a b ∨ moves a b) reached last from
    along source target reaches _ (Explore.explored_source _) (normalizer.idempotent source) holds
      (.symm _ _ (normalizer.sound source |> Relation.EqvGen.mono (fun _ _ move => .inr move) _ _))
  intro first last reaches
  induction reaches with
  | refl term => intro state explored _ _ equal; exact ⟨state, explored, equal⟩
  | @step first middle last stepped _ ih =>
    intro state explored normal stateGood equal
    obtain ⟨representative, receipt, before, fired, after⟩ := stepped
    obtain ⟨reached, receipt', inClass, fired', sameTarget⟩ :=
      fire_in_normalClass_on normalizer lift stable normalize normal stateGood (.trans _ _ _ equal before) fired
    rw [normalClass_eq noEquations inClass] at fired'
    have step : (GeneralOccurrenceSemantics.gslt plan bound expected).Step state receipt'.target :=
      ⟨state, receipt', .refl _, fired', .refl _⟩
    obtain ⟨work, published, member, related⟩ := Classes.complete_in_limit plan bound expected state checked step
    have next := Explore.explored_target (searchWith_lawful plan bound expected form) explored (work := work) member
    have equalOf : ∀ a b, Relation.EqvGen (GeneralOccurrenceSemantics.Equation plan bound expected) a b → a = b := by
      intro a b equivalent
      induction equivalent with
      | rel _ _ equation => exact absurd equation (noEquations _ _)
      | refl => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ first second => exact first.trans second
    have publishedEq : published.target = receipt'.target := equalOf _ _ related
    refine ih _ next (normalizer.idempotent _) ?_ ?_
    · show good (form published.target)
      rw [publishedEq]; exact committed _ _ fired'
    · have toPublished : EqvGen (fun a b => GeneralOccurrenceSemantics.Equation plan bound expected a b ∨ moves a b)
          (form published.target) published.target :=
        .symm _ _ (Relation.EqvGen.mono (fun _ _ move => .inr move) _ _ (normalizer.sound published.target))
      have fromEquations : EqvGen (fun a b => GeneralOccurrenceSemantics.Equation plan bound expected a b ∨ moves a b)
          published.target receipt'.target :=
        Relation.EqvGen.mono (fun _ _ equation => .inl equation) _ _ related
      exact .trans _ _ _ toPublished (.trans _ _ _ fromEquations (.trans _ _ _ (.symm _ _ sameTarget) after))

/-! ## The model with the quote-drop equation -/

variable (plan bound expected) (declaration : ReflectivePresentationDecl)

/-- A law move of the model: a standard move of the declared collection and scope-extrusion laws,
or one use of `@(*n) = n`, left to right, in any context. -/
def LawMove (left right : Pattern) : Prop :=
  StandardStep (Normalized.laws plan) (Normalized.extrusions plan) left right ∨ QuoteDropStep declaration left right

/-- One generating equality of the model: an equation of the plan or a law move. -/
def ModelEquation (left right : Pattern) : Prop :=
  GeneralOccurrenceSemantics.Equation plan bound expected left right ∨ LawMove plan declaration left right

/-- **The plan's steps modulo the model with the quote-drop equation.** -/
def gslt : Mettapedia.GSLT.GSLT :=
  Mettapedia.OSLF.Framework.FiniteEquationCoverage.moduloGSLT (ModelEquation plan bound expected declaration)
    (GeneralOccurrenceSemantics.Primitive plan bound expected) GeneralRuleJobs.Receipt.target

/-- Equality in the model with the quote-drop equation. -/
abbrev ModelEquiv (left right : Pattern) : Prop :=
  EqvGen (ModelEquation plan bound expected declaration) left right

/-- The committed form: the quote-drop normal form, then the canonical form of the declared
collection laws. -/
def commit (pattern : Pattern) : Pattern := lawNormal (Normalized.laws plan) (normal declaration pattern)

/-- The search modulo equations, committing `commit`. -/
abbrev search := searchWith plan bound expected (commit plan declaration)

variable {plan bound expected declaration}

/-- Without declared extrusions, the runner's reflective commit is `commit`. -/
theorem commit_reflective (noExtrusions : Normalized.extrusions plan = []) (pattern : Pattern) :
    Normalized.commit plan (.reflective declaration) pattern = commit plan declaration pattern := by
  rw [Normalized.commit, Normalized.standard, noExtrusions, CollectionLaws.standardForm, CollectionLaws.extrude_nil,
    commit, lawNormal]

variable (plan bound expected declaration) in
/-- **Without declared extrusions, the runner's reflective search is this search.** -/
theorem search_reflective (noExtrusions : Normalized.extrusions plan = []) :
    Normalized.search plan bound expected (.reflective declaration) = search plan bound expected declaration := by
  have targets : (fun receipt : GeneralOccurrenceSemantics.Receipt =>
      Normalized.commit plan (.reflective declaration) receipt.target) =
      fun receipt => commit plan declaration receipt.target := by
    funext receipt
    exact commit_reflective noExtrusions receipt.target
  simp only [Normalized.search, search, searchWith, targets]

/-- Equality in the model without the quote-drop equation is equality in this model. -/
theorem modelEquiv_of_presented {left right : Pattern} (equal : Presented.ModelEquiv plan bound expected left right) :
    ModelEquiv plan bound expected declaration left right :=
  Relation.EqvGen.mono (fun _ _ step => step.imp_right Or.inl) _ _ equal

/-- **The committed form is a canonical form for the model's law moves**, for a plan without
declared extrusions whose quote and drop constructors are distinct. -/
theorem normalizer (noExtrusions : Normalized.extrusions plan = [])
    (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor) :
    Normalizer (LawMove plan declaration) (commit plan declaration) where
  sound term := by
    have toNormal : EqvGen (LawMove plan declaration) term (normal declaration term) :=
      Relation.EqvGen.mono (fun _ _ step => .inr step) _ _ (quoteDrop_sound term)
    have toLawNormal : EqvGen (LawMove plan declaration) (normal declaration term) (commit plan declaration term) := by
      have := (lawNormalizer (Normalized.laws plan)).sound (normal declaration term)
      rw [← noExtrusions] at this
      exact Relation.EqvGen.mono (fun _ _ step => .inl step) _ _ this
    exact .trans _ _ _ toNormal toLawNormal
  canonical left right := by
    rintro (moved | step)
    · rw [noExtrusions] at moved
      have lawSame : LawSame (Normalized.laws plan) (normal declaration left) (normal declaration right) :=
        normalizeReflective_lawSame declaration (.rel _ _ (lawStep_of_standardStep moved))
      exact (lawNormalizer (Normalized.laws plan)).eqvGen_eq
        (Relation.EqvGen.mono (fun _ _ move => StandardStep.law move) _ _ lawSame)
    · simp only [commit]
      rw [step.normalize_eq distinct]

/-- Law-equal terms are equally well-sorted. -/
theorem lawSame_sorted_iff (admissible : DescentCoherence.DescentAdmissible plan)
    (boundOk : ∀ entry ∈ bound, LawTypeOk (Normalized.laws plan) (GeneralPlanEnvironment.environment plan).language entry)
    (expectedOk : LawTypeOk (Normalized.laws plan) (GeneralPlanEnvironment.environment plan).language expected)
    {left right : Pattern} (same : LawSame (Normalized.laws plan) left right) :
    OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language plan.snapshot.free bound expected left ↔
      OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language plan.snapshot.free bound expected right :=
  ⟨LawSame.openPatternWellSorted admissible.typed same boundOk expectedOk,
    LawSame.openPatternWellSorted admissible.typed (.symm _ _ same) boundOk expectedOk⟩

/-- **Firings normalize** at every presentation whose quote-drop normal form is well-sorted: a
firing moves to the quote-drop normal form and from there to the law-normal form. -/
theorem firingsNormalize (canonical : CanonicalCoherence.RulesAdmissible plan)
    (admissible : DescentCoherence.DescentAdmissible plan)
    (boundOk : ∀ entry ∈ bound, LawTypeOk (Normalized.laws plan) (GeneralPlanEnvironment.environment plan).language entry)
    (expectedOk : LawTypeOk (Normalized.laws plan) (GeneralPlanEnvironment.environment plan).language expected)
    (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    (typedPresentation : QuoteDropTyped (GeneralPlanEnvironment.environment plan).language declaration)
    (quoteOpaque : QuoteOpaque plan.permissions.sites declaration) (fires : RulesFireAtNormal plan declaration) :
    FiringsNormalizeOn (GeneralOccurrenceSemantics.Equation plan bound expected) (LawMove plan declaration)
      (commit plan declaration) (GeneralOccurrenceSemantics.Primitive plan bound expected) GeneralRuleJobs.Receipt.target
      (fun term => OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language plan.snapshot.free bound
        expected (normal declaration term)) := by
  intro term receipt sorted fired
  obtain ⟨atNormal, firedNormal, forward⟩ := primitive_normal distinct typedPresentation quoteOpaque fires fired
  obtain ⟨atCommit, firedCommit, related⟩ :=
    DescentCoherence.firingsNormalize_descent canonical admissible boundOk expectedOk _ atNormal sorted firedNormal
  refine ⟨atCommit, firedCommit, .trans _ atNormal.target _ ?_ ?_⟩
  · exact Relation.EqvGen.mono (fun _ _ step => .inr (.inr step)) _ _ forward.same
  · exact Relation.EqvGen.mono (fun _ _ step => step.imp_right Or.inl) _ _ related

/-- **The explorer is complete modulo the quote-drop equation**: for a plan without equations or
declared extrusions whose laws and rules are admissible, whose reflective presentation is typed with
distinct quote and drop constructors, whose sites never pass under a quote and whose rules fire at
quote-drop normal forms, every state reachable from a well-sorted source by finitely many steps
modulo the model with the quote-drop equation is explored, up to that model. -/
theorem presented_explores_quoteDrop (checked : Predecessors.equationsChecked plan = true)
    (noEquations : ∀ left right, ¬ GeneralOccurrenceSemantics.Equation plan bound expected left right)
    (noExtrusions : Normalized.extrusions plan = [])
    (canonical : CanonicalCoherence.RulesAdmissible plan) (admissible : DescentCoherence.DescentAdmissible plan)
    (boundOk : ∀ entry ∈ bound, LawTypeOk (Normalized.laws plan) (GeneralPlanEnvironment.environment plan).language entry)
    (expectedOk : LawTypeOk (Normalized.laws plan) (GeneralPlanEnvironment.environment plan).language expected)
    (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    (typedPresentation : QuoteDropTyped (GeneralPlanEnvironment.environment plan).language declaration)
    (quoteOpaque : QuoteOpaque plan.permissions.sites declaration) (fires : RulesFireAtNormal plan declaration)
    (source : Pattern)
    (sorted : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language plan.snapshot.free bound expected source)
    {target : Pattern} (reaches : (gslt plan bound expected declaration).MultiStep source target) :
    ∃ state, Explore.Explored (S := search plan bound expected declaration) (commit plan declaration source) state ∧
      ModelEquiv plan bound expected declaration state target := by
  have committedSorted : ∀ term, OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
      plan.snapshot.free bound expected term →
      OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language plan.snapshot.free bound expected
        (normal declaration (commit plan declaration term)) := fun term sortedTerm =>
    openPatternWellSorted_normal typedPresentation (DescentCoherence.lawNormal_sorted admissible boundOk expectedOk
      (openPatternWellSorted_normal typedPresentation sortedTerm))
  refine explores_of_normalizer checked noEquations (normalizer noExtrusions distinct)
    (good := fun term => OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language plan.snapshot.free
      bound expected (normal declaration term))
    ?_ ?_ (firingsNormalize canonical admissible boundOk expectedOk distinct typedPresentation quoteOpaque fires)
    source (committedSorted source sorted) reaches
  · intro a b step
    rcases step with equation | moved | quoteDrop
    · exact absurd equation (noEquations _ _)
    · rw [noExtrusions] at moved
      exact lawSame_sorted_iff admissible boundOk expectedOk
        (normalizeReflective_lawSame declaration (.rel _ _ (lawStep_of_standardStep moved)))
    · simp only [quoteDrop.normalize_eq distinct]
  · intro term receipt fired
    exact committedSorted _ fired.2.2.2.2

end Mettapedia.OSLF.MeTTaIL.Complete.QuoteDropCoherence
