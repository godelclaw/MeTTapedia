import Mettapedia.OSLF.MeTTaIL.Complete.QuoteDropCoherence
import Mettapedia.OSLF.MeTTaIL.WrapperFiring
import Mettapedia.OSLF.MeTTaIL.ModelNormality
import Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrenceLocalReplacement

/-!
# The explorer is complete modulo the declared collection algebra

The model of a reflective plan with the wrapper laws identifies terms related by the parallel laws, the
quote-drop equation and the two wrapper laws (`ModelEquation`); its canonical form is
`Wrappers.modelCanon`. The explorer commits that form and is complete for steps modulo the model
(`presented_explores_wrappers`).

A firing reaches the canonical form in rounds. One round moves it to the law normal form
(`DescentCoherence`), to the wrapper normal form (`Wrappers.primitive_wrapper`), to the quote-drop normal
form (`QuoteDrop.primitive_normal`) and to the sorted form (`CanonicalCoherence.primitive_canon`). Each
round keeps the term or makes it lighter, and a round that keeps the weight ends at a term every normal
form keeps, a model normal form (`Wrappers.normal_of_fixed`). After as many rounds as the term weighs,
the firing sits at the canonical form (`iterate_eq`). The typing every stage needs comes from the firing
itself (`primitive_source_sorted`), so no invariant restricts the sources.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Complete.WrapperCoherence

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission CanonicalBags Coherence CollectionLaws
open Mettapedia.GSLT.LanguageDef.WellSorted QuoteDrop Wrappers
open Relation (EqvGen)

variable (plan : Plan) (bound : List TypeExpr) (expected : TypeExpr) (declaration : ReflectivePresentationDecl)

/-! ## The model -/

/-- One generating equality of the model: an equation of the plan or a law move of the declared
collection algebra with the quote-drop equation. -/
def ModelEquation (left right : Pattern) : Prop :=
  GeneralOccurrenceSemantics.Equation plan bound expected left right ∨
    ModelMove (Normalized.laws plan) declaration left right

/-- **The plan's steps modulo the declared collection algebra and the quote-drop equation.** -/
def gslt : Mettapedia.GSLT.GSLT :=
  Mettapedia.OSLF.Framework.FiniteEquationCoverage.moduloGSLT (ModelEquation plan bound expected declaration)
    (GeneralOccurrenceSemantics.Primitive plan bound expected) GeneralRuleJobs.Receipt.target

/-- Equality in the model. -/
abbrev ModelEquiv (left right : Pattern) : Prop :=
  EqvGen (ModelEquation plan bound expected declaration) left right

/-- The committed form: the model's canonical form. -/
def commit (pattern : Pattern) : Pattern := modelCanon (Normalized.laws plan) declaration pattern

/-- The search modulo equations, committing the model's canonical form. -/
abbrev search := QuoteDropCoherence.searchWith plan bound expected (commit plan declaration)

variable {plan bound expected declaration}

/-- **The committed form is a canonical form for the model's law moves.** -/
theorem normalizer (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor) :
    Normalizer (ModelMove (Normalized.laws plan) declaration) (commit plan declaration) where
  sound term := to_modelCanon term
  canonical _ _ move := ModelMove.modelCanon_eq distinct move

/-! ## Rounds -/

variable (plan declaration) in
/-- One round: the law normal form, the wrapper normal form, the quote-drop normal form, sorted. -/
def stage (pattern : Pattern) : Pattern :=
  canon (normal declaration (wrapperNormal (Normalized.laws plan) (lawNormal (Normalized.laws plan) pattern)))

variable (plan declaration) in
/-- Rounds while the term gets lighter. -/
def iterate : Nat → Pattern → Pattern
  | 0, pattern => pattern
  | fuel + 1, pattern =>
      if weight (stage plan declaration pattern) < weight pattern then iterate fuel (stage plan declaration pattern)
      else stage plan declaration pattern

theorem weight_pos : ∀ pattern : Pattern, 0 < weight pattern
  | .bvar _ => by rw [weight]; omega
  | .fvar _ => by rw [weight]; omega
  | .apply _ _ => by rw [weight_apply]; omega
  | .lambda _ _ => by rw [weight_lambda]; omega
  | .multiLambda _ _ _ => by rw [weight_multiLambda]; omega
  | .subst _ _ => by rw [weight_subst]; omega
  | .collection _ _ _ => by rw [weight_collection]; omega

theorem keeps_le {f : Pattern → Pattern} {pattern : Pattern}
    (step : f pattern = pattern ∨ weight (f pattern) < weight pattern) : weight (f pattern) ≤ weight pattern := by
  rcases step with same | lighter
  · rw [same]
  · exact lighter.le

theorem keeps_of_eq {f : Pattern → Pattern} {pattern : Pattern}
    (step : f pattern = pattern ∨ weight (f pattern) < weight pattern) (heavy : weight pattern ≤ weight (f pattern)) :
    f pattern = pattern := by
  rcases step with same | lighter
  · exact same
  · omega

theorem weight_lawNormal_le (laws : List Laws) (pattern : Pattern) :
    weight (lawNormal laws pattern) ≤ weight (normalize laws pattern) := by
  rw [lawNormal]; exact weight_canon_le _

/-- **A round keeps the term or makes it lighter.** -/
theorem stage_le (pattern : Pattern) : weight (stage plan declaration pattern) ≤ weight pattern := by
  have canonLe := weight_canon_le (normal declaration (wrapperNormal (Normalized.laws plan) (lawNormal (Normalized.laws plan) pattern)))
  have lawLe := keeps_le (normalize_keeps_or_lighter (Normalized.laws plan) pattern)
  have lawCanon := weight_lawNormal_le (Normalized.laws plan) pattern
  have wrapperLe := keeps_le (wrapperNormal_keeps_or_lighter (Normalized.laws plan) (lawNormal (Normalized.laws plan) pattern))
  have quoteLe := keeps_le (normal_keeps_or_lighter (declaration := declaration)
    (wrapperNormal (Normalized.laws plan) (lawNormal (Normalized.laws plan) pattern)))
  simp only [stage]
  omega

/-- **A round that keeps the weight ends at a model normal form**, sorted. -/
theorem stage_fixed (pattern : Pattern) (heavy : weight pattern ≤ weight (stage plan declaration pattern)) :
    Normal (Normalized.laws plan) declaration (stage plan declaration pattern) ∧
      canon (stage plan declaration pattern) = stage plan declaration pattern := by
  have lawStep := normalize_keeps_or_lighter (Normalized.laws plan) pattern
  have wrapperStep := wrapperNormal_keeps_or_lighter (Normalized.laws plan) (lawNormal (Normalized.laws plan) pattern)
  have quoteStep := normal_keeps_or_lighter (declaration := declaration)
    (wrapperNormal (Normalized.laws plan) (lawNormal (Normalized.laws plan) pattern))
  have lawLe := keeps_le lawStep
  have wrapperLe := keeps_le wrapperStep
  have quoteLe := keeps_le quoteStep
  have lawCanon := weight_lawNormal_le (Normalized.laws plan) pattern
  have canonLe := weight_canon_le (normal declaration (wrapperNormal (Normalized.laws plan) (lawNormal (Normalized.laws plan) pattern)))
  simp only [stage] at heavy
  have lawFixed : normalize (Normalized.laws plan) pattern = pattern := keeps_of_eq lawStep (by omega)
  have wrapperFixed := keeps_of_eq wrapperStep (by omega)
  rw [wrapperFixed] at quoteStep quoteLe heavy canonLe
  have quoteFixed := keeps_of_eq quoteStep (by omega)
  -- the round's result is the law-normal sorted form, which is itself law-normal
  have result : stage plan declaration pattern = lawNormal (Normalized.laws plan) pattern := by
    rw [stage, wrapperFixed, quoteFixed, lawNormal, canon_idempotent]
  have idempotent : lawNormal (Normalized.laws plan) (lawNormal (Normalized.laws plan) pattern) =
      lawNormal (Normalized.laws plan) pattern := (lawNormalizer (Normalized.laws plan)).idempotent pattern
  have lawNormalFixed : normalize (Normalized.laws plan) (lawNormal (Normalized.laws plan) pattern) =
      lawNormal (Normalized.laws plan) pattern := by
    apply keeps_of_eq (normalize_keeps_or_lighter (Normalized.laws plan) _)
    have same := congrArg weight idempotent
    have le := weight_lawNormal_le (Normalized.laws plan) (lawNormal (Normalized.laws plan) pattern)
    omega
  rw [result]
  refine ⟨normal_of_fixed (Normalized.laws plan) declaration _ lawNormalFixed wrapperFixed quoteFixed
    (by simp only [lawNormal, canon_idempotent]), ?_⟩
  simp only [lawNormal, canon_idempotent]

theorem wrapperForward_equiv {left right : Pattern} (forward : WrapperForward (Normalized.laws plan) left right) :
    EqvGen (ModelMove (Normalized.laws plan) declaration) left right := by
  induction forward with
  | refl => exact .refl _
  | tail _ step ih => exact .trans _ _ _ ih (.rel _ _ (.inr (.inr step)))

/-- Every round is a conversion of the model's law moves. -/
theorem stage_equiv (pattern : Pattern) :
    EqvGen (ModelMove (Normalized.laws plan) declaration) pattern (stage plan declaration pattern) := by
  have toLaw : EqvGen (ModelMove (Normalized.laws plan) declaration) pattern (lawNormal (Normalized.laws plan) pattern) :=
    Relation.EqvGen.mono (fun _ _ move => .inl (lawStep_of_standardStep move)) _ _
      ((lawNormalizer (Normalized.laws plan)).sound pattern)
  have toWrapper : EqvGen (ModelMove (Normalized.laws plan) declaration) (lawNormal (Normalized.laws plan) pattern)
      (wrapperNormal (Normalized.laws plan) (lawNormal (Normalized.laws plan) pattern)) :=
    wrapperForward_equiv (to_wrapperNormal _)
  have toQuote : EqvGen (ModelMove (Normalized.laws plan) declaration)
      (wrapperNormal (Normalized.laws plan) (lawNormal (Normalized.laws plan) pattern))
      (normal declaration (wrapperNormal (Normalized.laws plan) (lawNormal (Normalized.laws plan) pattern))) :=
    Relation.EqvGen.mono (fun _ _ step => .inr (.inl step)) _ _ (quoteDrop_sound _)
  have toCanon : ∀ term, EqvGen (ModelMove (Normalized.laws plan) declaration) term (canon term) := fun term =>
    Relation.EqvGen.mono (fun _ _ step => .inl (BagStep.lawStep _ step)) _ _ (to_canon term)
  exact .trans _ _ _ toLaw (.trans _ _ _ toWrapper (.trans _ _ _ toQuote (toCanon _)))

/-- **Enough rounds end at the canonical form.** -/
theorem iterate_eq (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor) :
    ∀ (fuel : Nat) (pattern : Pattern), weight pattern ≤ fuel →
      iterate plan declaration fuel pattern = commit plan declaration pattern
  | 0, pattern, light => absurd light (by have := weight_pos pattern; omega)
  | fuel + 1, pattern, light => by
    have sameClass : commit plan declaration (stage plan declaration pattern) = commit plan declaration pattern :=
      ((normalizer distinct).eqvGen_eq (stage_equiv pattern)).symm
    rw [iterate]
    split
    · rename_i lighter
      rw [iterate_eq distinct fuel (stage plan declaration pattern) (by omega), sameClass]
    · rename_i notLighter
      obtain ⟨normalForm, sorted⟩ := stage_fixed (plan := plan) (declaration := declaration) pattern (by omega)
      rw [← sameClass, commit, modelCanon, normalForm.fixed, sorted]

/-! ## Firings reach the canonical form -/

/-- **The source of a firing is well-sorted.** -/
theorem primitive_source_sorted {source : Pattern} {receipt : GeneralRuleJobs.Receipt}
    (fired : GeneralOccurrenceSemantics.Primitive plan bound expected source receipt) :
    OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language plan.snapshot.free bound expected source := by
  have localSource := (GeneralRuleJobs.receipt_root_readout fired).2.1
  have targetAdmitted := fired.2.2.2.2
  rw [fired.2.2.2.1] at targetAdmitted
  have sourceCore := Mettapedia.GSLT.LanguageDef.WellSorted.OneHoleContext.admissionCore_fill receipt.job.site.context
    localSource.2.1 localSource.2.2.1 targetAdmitted.2.1 targetAdmitted.2.2.1
  rw [fired.1.2.source_eq] at sourceCore
  have typed := fired.1.2.source_typed
  exact ⟨typed, sourceCore.1, sourceCore.2, typed.isWellScopedAt⟩

theorem qwForward_modelEquiv {left right : Pattern} (forward : QWForward (Normalized.laws plan) declaration left right) :
    ModelEquiv plan bound expected declaration left right := by
  induction forward with
  | refl => exact .refl _
  | tail _ step ih =>
    rcases step with quoteDrop | wrapped
    · exact .trans _ _ _ ih (.rel _ _ (.inr (.inr (.inl quoteDrop))))
    · exact .trans _ _ _ ih (.rel _ _ (.inr (.inr (.inr wrapped))))

/-- Every round moves a firing, with a result equal in the model. -/
theorem primitive_stage (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    (noExtrusions : Normalized.extrusions plan = [])
    (canonical : CanonicalCoherence.RulesAdmissible plan) (admissible : DescentCoherence.DescentAdmissible plan)
    (expectedLaw : LawTypeOk (Normalized.laws plan) (GeneralPlanEnvironment.environment plan).language expected)
    (wrappersTyped : WrappersTyped (Normalized.laws plan) (GeneralPlanEnvironment.environment plan).language)
    (typedPresentation : QuoteDropTyped (GeneralPlanEnvironment.environment plan).language declaration)
    (quoteOpaque : QuoteOpaque plan.permissions.sites declaration) (quoteFires : RulesFireAtNormal plan declaration)
    (noLambda : plan.permissions.sites.underLambda = false)
    (noMultiLambda : plan.permissions.sites.underMultiLambda = false)
    (expectedOk : NoLawCollections (Normalized.laws plan) expected)
    (wrapperFires : RulesFireAtWrapper (Normalized.laws plan) plan declaration)
    {source : Pattern} {receipt : GeneralRuleJobs.Receipt}
    (fired : GeneralOccurrenceSemantics.Primitive plan [] expected source receipt) :
    ∃ receipt', GeneralOccurrenceSemantics.Primitive plan [] expected (stage plan declaration source) receipt' ∧
      ModelEquiv plan [] expected declaration receipt.target receipt'.target := by
  obtain ⟨atLaw, firedLaw, lawRelated⟩ := DescentCoherence.firingsNormalize_descent canonical admissible
    (fun _ member => absurd member List.not_mem_nil) expectedLaw source receipt (primitive_source_sorted fired) fired
  obtain ⟨atWrapper, firedWrapper, wrapperForward⟩ := primitive_wrapper distinct wrappersTyped typedPresentation noLambda
    noMultiLambda expectedOk wrapperFires firedLaw
  obtain ⟨atQuote, firedQuote, quoteForward⟩ := primitive_normal distinct typedPresentation quoteOpaque quoteFires
    firedWrapper
  obtain ⟨atCanon, firedCanon, same⟩ := CanonicalCoherence.primitive_canon canonical firedQuote
  refine ⟨atCanon, firedCanon, ?_⟩
  have fromLaw : ModelEquiv plan [] expected declaration receipt.target atLaw.target := by
    refine Relation.EqvGen.mono (fun _ _ step => ?_) _ _ lawRelated
    rcases step with equation | standard
    · exact .inl equation
    · rw [noExtrusions] at standard
      exact .inr (.inl (lawStep_of_standardStep standard))
  have fromWrapper : ModelEquiv plan [] expected declaration atLaw.target atWrapper.target :=
    qwForward_modelEquiv wrapperForward
  have fromQuote : ModelEquiv plan [] expected declaration atWrapper.target atQuote.target :=
    Relation.EqvGen.mono (fun _ _ step => .inr (.inr (.inl step))) _ _ quoteForward.same
  have fromCanon : ModelEquiv plan [] expected declaration atQuote.target atCanon.target :=
    Relation.EqvGen.mono (fun _ _ step => .inr (.inl (BagStep.lawStep _ step))) _ _ ((same_iff _ _).mp same)
  exact .trans _ _ _ fromLaw (.trans _ _ _ fromWrapper (.trans _ _ _ fromQuote fromCanon))

/-- Rounds move a firing. -/
theorem primitive_iterate (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    (noExtrusions : Normalized.extrusions plan = [])
    (canonical : CanonicalCoherence.RulesAdmissible plan) (admissible : DescentCoherence.DescentAdmissible plan)
    (expectedLaw : LawTypeOk (Normalized.laws plan) (GeneralPlanEnvironment.environment plan).language expected)
    (wrappersTyped : WrappersTyped (Normalized.laws plan) (GeneralPlanEnvironment.environment plan).language)
    (typedPresentation : QuoteDropTyped (GeneralPlanEnvironment.environment plan).language declaration)
    (quoteOpaque : QuoteOpaque plan.permissions.sites declaration) (quoteFires : RulesFireAtNormal plan declaration)
    (noLambda : plan.permissions.sites.underLambda = false)
    (noMultiLambda : plan.permissions.sites.underMultiLambda = false)
    (expectedOk : NoLawCollections (Normalized.laws plan) expected)
    (wrapperFires : RulesFireAtWrapper (Normalized.laws plan) plan declaration) :
    ∀ (fuel : Nat) {source : Pattern} {receipt : GeneralRuleJobs.Receipt},
      GeneralOccurrenceSemantics.Primitive plan [] expected source receipt →
      ∃ receipt', GeneralOccurrenceSemantics.Primitive plan [] expected (iterate plan declaration fuel source) receipt' ∧
        ModelEquiv plan [] expected declaration receipt.target receipt'.target
  | 0, _, receipt, fired => ⟨receipt, fired, .refl _⟩
  | fuel + 1, _, _, fired => by
    obtain ⟨staged, firedStaged, related⟩ := primitive_stage distinct noExtrusions canonical admissible expectedLaw
      wrappersTyped typedPresentation quoteOpaque quoteFires noLambda noMultiLambda expectedOk wrapperFires fired
    rw [iterate]
    split
    · obtain ⟨final, firedFinal, finalRelated⟩ := primitive_iterate distinct noExtrusions canonical admissible
        expectedLaw wrappersTyped typedPresentation quoteOpaque quoteFires noLambda noMultiLambda expectedOk
        wrapperFires fuel firedStaged
      exact ⟨final, firedFinal, .trans _ _ _ related finalRelated⟩
    · exact ⟨staged, firedStaged, related⟩

/-- **Firings normalize at every presentation**: a firing has a counterpart at the model's canonical
form of its source, with a result equal in the model. -/
theorem firingsNormalize (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    (noExtrusions : Normalized.extrusions plan = [])
    (canonical : CanonicalCoherence.RulesAdmissible plan) (admissible : DescentCoherence.DescentAdmissible plan)
    (expectedLaw : LawTypeOk (Normalized.laws plan) (GeneralPlanEnvironment.environment plan).language expected)
    (wrappersTyped : WrappersTyped (Normalized.laws plan) (GeneralPlanEnvironment.environment plan).language)
    (typedPresentation : QuoteDropTyped (GeneralPlanEnvironment.environment plan).language declaration)
    (quoteOpaque : QuoteOpaque plan.permissions.sites declaration) (quoteFires : RulesFireAtNormal plan declaration)
    (noLambda : plan.permissions.sites.underLambda = false)
    (noMultiLambda : plan.permissions.sites.underMultiLambda = false)
    (expectedOk : NoLawCollections (Normalized.laws plan) expected)
    (wrapperFires : RulesFireAtWrapper (Normalized.laws plan) plan declaration) :
    FiringsNormalizeOn (GeneralOccurrenceSemantics.Equation plan [] expected) (ModelMove (Normalized.laws plan) declaration)
      (commit plan declaration) (GeneralOccurrenceSemantics.Primitive plan [] expected) GeneralRuleJobs.Receipt.target
      (fun _ => True) := by
  intro term receipt _ fired
  obtain ⟨final, firedFinal, related⟩ := primitive_iterate distinct noExtrusions canonical admissible expectedLaw
    wrappersTyped typedPresentation quoteOpaque quoteFires noLambda noMultiLambda expectedOk wrapperFires
    (weight term) fired
  rw [iterate_eq distinct (weight term) term le_rfl] at firedFinal
  exact ⟨final, firedFinal, related⟩

/-- **The explorer is complete modulo the declared collection algebra and the quote-drop equation**: for
a plan without equations or declared extrusions whose laws and rules are admissible, whose reflective
presentation and wrapper laws are typed, whose sites never pass under a quote or a binder and whose rules
fire at quote-drop and wrapper normal forms, every closed state reachable from any closed source by
finitely many steps modulo the model is explored from the source's canonical form, up to the model. -/
theorem presented_explores_wrappers (checked : Predecessors.equationsChecked plan = true)
    (noEquations : ∀ left right, ¬ GeneralOccurrenceSemantics.Equation plan [] expected left right)
    (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    (noExtrusions : Normalized.extrusions plan = [])
    (canonical : CanonicalCoherence.RulesAdmissible plan) (admissible : DescentCoherence.DescentAdmissible plan)
    (expectedLaw : LawTypeOk (Normalized.laws plan) (GeneralPlanEnvironment.environment plan).language expected)
    (wrappersTyped : WrappersTyped (Normalized.laws plan) (GeneralPlanEnvironment.environment plan).language)
    (typedPresentation : QuoteDropTyped (GeneralPlanEnvironment.environment plan).language declaration)
    (quoteOpaque : QuoteOpaque plan.permissions.sites declaration) (quoteFires : RulesFireAtNormal plan declaration)
    (noLambda : plan.permissions.sites.underLambda = false)
    (noMultiLambda : plan.permissions.sites.underMultiLambda = false)
    (expectedOk : NoLawCollections (Normalized.laws plan) expected)
    (wrapperFires : RulesFireAtWrapper (Normalized.laws plan) plan declaration)
    (source : Pattern) {target : Pattern} (reaches : (gslt plan [] expected declaration).MultiStep source target) :
    ∃ state, Explore.Explored (S := search plan [] expected declaration) (commit plan declaration source) state ∧
      ModelEquiv plan [] expected declaration state target :=
  QuoteDropCoherence.explores_of_normalizer checked noEquations (normalizer distinct) (good := fun _ => True)
    (fun _ _ _ => Iff.rfl) (fun _ _ _ => trivial)
    (firingsNormalize distinct noExtrusions canonical admissible expectedLaw wrappersTyped typedPresentation quoteOpaque
      quoteFires noLambda noMultiLambda expectedOk wrapperFires) source trivial reaches

/-! ## The runner's model commit -/

/-- Without declared extrusions, the runner's model commit is `commit`: a model normal form is already in
the standard form of the declared laws. -/
theorem commit_model (noExtrusions : Normalized.extrusions plan = []) (pattern : Pattern) :
    Normalized.commit plan (.model declaration) pattern = commit plan declaration pattern := by
  rw [Normalized.commit, Normalized.standard, noExtrusions, CollectionLaws.standardForm, CollectionLaws.extrude_nil,
    normalize_modelNormal, commit, modelCanon]

variable (plan bound expected declaration) in
/-- **Without declared extrusions, the runner's model search is this search.** -/
theorem search_model (noExtrusions : Normalized.extrusions plan = []) :
    Normalized.search plan bound expected (.model declaration) = search plan bound expected declaration := by
  have targets : (fun receipt : GeneralOccurrenceSemantics.Receipt =>
      Normalized.commit plan (.model declaration) receipt.target) =
      fun receipt => commit plan declaration receipt.target := by
    funext receipt
    exact commit_model noExtrusions receipt.target
  simp only [Normalized.search, search, QuoteDropCoherence.searchWith, targets]

end Mettapedia.OSLF.MeTTaIL.Complete.WrapperCoherence
