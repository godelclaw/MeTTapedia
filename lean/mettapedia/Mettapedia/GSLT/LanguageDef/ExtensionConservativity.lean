import Mettapedia.GSLT.LanguageDef.StructuralCoproductOperational
import Mettapedia.GSLT.LanguageDef.StructuralPatternBindingNaturality
import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.IdentityInterface
import Mettapedia.OSLF.NativeTypes.Instances.MeTTaFamily.EquationSite
import Mettapedia.Logic.Relation.Normalization

/-!
# Conservativity of extensions, per observation class

An observer of a language reads its step relation.  Two classes of
observation behave differently under extension.

* **May-observations**: some successor, or some reduct, satisfies a claim.
* **Must-observations**: every successor, or every reduct, satisfies a claim.
  Determinism, at most one successor at every reduct, is one of them.

`ExactEmbedding` is the shape of the operational transport of a structural
coproduct: the steps of an embedded term are exactly the images of the steps
of the term.  Every may- and every must-observation above is invariant under
exact embeddings (`TransportInvariant`).  A structural coproduct therefore
conserves both classes on each summand, in the sense of
`ExtensionLayer.Conserves` (`leftSummands_conserve`, `rightSummands_conserve`).
The only hypothesis beyond the coproduct itself is the premise-evaluator square
of `StructuralCoproductOperational` on the summand's own rules.

Normal forms are the must-observation of the empty claim, so exact embeddings
conserve them (`isNormal_transport`).  Conversion is no observation of a term
and its reducts alone: an exact embedding conserves it when the larger step
relation is confluent (`ExactEmbedding.eqvGen_iff`), and not otherwise, since
a term outside the image can fork into two embedded terms
(`fork_conversion_not_conserved`, `fork_not_confluent`).  A confluent entry
into the image is the positive control (`entry_conversion_conserved`).

An inclusion of rewrite rows, or an overlapping union, only adds steps.
May-observations grow with added steps (`GrowsWithSteps`), so they are
preserved; must-observations shrink.  Neither class is conserved: a rule added
on an old term creates a new answer and falsifies a vacuous must-claim
(`inclusions_do_not_conserve_may`, `inclusions_do_not_conserve_must`), and an
added equation keeps every successor while falsifying a must-claim and
determinism (`adding_equation_preserves_may_only`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ExtensionConservativity

open Relation
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Extension
open Mettapedia.GSLT.LanguageDef.StructuralCoproduct
open Mettapedia.GSLT.LanguageDef.StructuralCoproductOperational
open Mettapedia.Logic.Relation (IsNormal Confluent)

/-! ## Observation classes -/

/-- What an observer says of a term, given a step relation and a claim on
terms. -/
abbrev ObservationClass : Type 1 :=
  ∀ {Term : Type}, (Term → Term → Prop) → (Term → Prop) → Term → Prop

/-- Some successor satisfies the claim. -/
def May : ObservationClass := fun step claim term => ∃ next, step term next ∧ claim next

/-- Every successor satisfies the claim. -/
def Must : ObservationClass := fun step claim term => ∀ next, step term next → claim next

/-- Some reduct satisfies the claim. -/
def MayReach : ObservationClass := fun step claim term =>
  ∃ reduct, ReflTransGen step term reduct ∧ claim reduct

/-- Every reduct satisfies the claim. -/
def MustReach : ObservationClass := fun step claim term =>
  ∀ reduct, ReflTransGen step term reduct → claim reduct

/-- At most one successor. -/
def Functional {Term : Type} (step : Term → Term → Prop) (term : Term) : Prop :=
  ∀ first second, step term first → step term second → first = second

/-- Determinism: every reduct has at most one successor.  It reads no claim. -/
def Deterministic : ObservationClass := fun step _ term =>
  ∀ reduct, ReflTransGen step term reduct → Functional step reduct

/-! ## Exact embeddings -/

/-- An exact embedding of one step relation into another: the successors of an
embedded term are exactly the images of the successors of the term. -/
structure ExactEmbedding {Term Term' : Type} (step : Term → Term → Prop)
    (step' : Term' → Term' → Prop) where
  embed : Term → Term'
  injective : Function.Injective embed
  exact : ∀ term next', step' (embed term) next' ↔ ∃ next, step term next ∧ embed next = next'

/-- The image of a claim along an embedding. -/
def imageClaim {Term Term' : Type} (embed : Term → Term') (claim : Term → Prop) :
    Term' → Prop :=
  fun next' => ∃ next, embed next = next' ∧ claim next

/-- An observation class is transport-invariant when exact embeddings neither
create nor destroy its observations. -/
def TransportInvariant (observe : ObservationClass) : Prop :=
  ∀ {Term Term' : Type} {step : Term → Term → Prop} {step' : Term' → Term' → Prop}
    (embedding : ExactEmbedding step step') (claim : Term → Prop) (term : Term),
    observe step' (imageClaim embedding.embed claim) (embedding.embed term) ↔
      observe step claim term

/-- An observation class grows with steps when adding steps never destroys an
observation. -/
def GrowsWithSteps (observe : ObservationClass) : Prop :=
  ∀ {Term : Type} {step step' : Term → Term → Prop},
    (∀ source target, step source target → step' source target) →
      ∀ claim term, observe step claim term → observe step' claim term

namespace ExactEmbedding

variable {Term Term' : Type} {step : Term → Term → Prop} {step' : Term' → Term' → Prop}
  (embedding : ExactEmbedding step step')

/-- The reducts of an embedded term are exactly the images of its reducts. -/
theorem reach_iff (term : Term) (reduct' : Term') :
    ReflTransGen step' (embedding.embed term) reduct' ↔
      ∃ reduct, ReflTransGen step term reduct ∧ embedding.embed reduct = reduct' := by
  constructor
  · intro reaches
    induction reaches with
    | refl => exact ⟨term, ReflTransGen.refl, rfl⟩
    | tail _ stepped inductionHypothesis =>
        obtain ⟨reduct, reachesReduct, rfl⟩ := inductionHypothesis
        obtain ⟨next, stepNext, rfl⟩ := (embedding.exact reduct _).mp stepped
        exact ⟨next, reachesReduct.tail stepNext, rfl⟩
  · rintro ⟨reduct, reaches, rfl⟩
    induction reaches with
    | refl => exact ReflTransGen.refl
    | tail _ stepped inductionHypothesis =>
        exact inductionHypothesis.tail ((embedding.exact _ _).mpr ⟨_, stepped, rfl⟩)

theorem imageClaim_embed_iff (claim : Term → Prop) (term : Term) :
    imageClaim embedding.embed claim (embedding.embed term) ↔ claim term := by
  constructor
  · rintro ⟨other, same, holds⟩
    rwa [embedding.injective same] at holds
  · intro holds
    exact ⟨term, rfl, holds⟩

/-- An embedded term has at most one successor exactly when the term has. -/
theorem functional_iff (term : Term) :
    Functional step' (embedding.embed term) ↔ Functional step term := by
  constructor
  · intro functional first second stepFirst stepSecond
    exact embedding.injective (functional _ _
      ((embedding.exact _ _).mpr ⟨first, stepFirst, rfl⟩)
      ((embedding.exact _ _).mpr ⟨second, stepSecond, rfl⟩))
  · intro functional first' second' stepFirst' stepSecond'
    obtain ⟨first, firstStep, rfl⟩ := (embedding.exact _ _).mp stepFirst'
    obtain ⟨second, secondStep, rfl⟩ := (embedding.exact _ _).mp stepSecond'
    rw [functional first second firstStep secondStep]

end ExactEmbedding

theorem may_transportInvariant : TransportInvariant May := by
  intro Term Term' step step' embedding claim term
  constructor
  · rintro ⟨next', stepped, holds⟩
    obtain ⟨next, stepNext, rfl⟩ := (embedding.exact term next').mp stepped
    exact ⟨next, stepNext, (embedding.imageClaim_embed_iff claim next).mp holds⟩
  · rintro ⟨next, stepped, holds⟩
    exact ⟨embedding.embed next, (embedding.exact term _).mpr ⟨next, stepped, rfl⟩,
      next, rfl, holds⟩

theorem must_transportInvariant : TransportInvariant Must := by
  intro Term Term' step step' embedding claim term
  constructor
  · intro must next stepped
    exact (embedding.imageClaim_embed_iff claim next).mp
      (must _ ((embedding.exact term _).mpr ⟨next, stepped, rfl⟩))
  · intro must next' stepped
    obtain ⟨next, stepNext, rfl⟩ := (embedding.exact term next').mp stepped
    exact ⟨next, rfl, must next stepNext⟩

theorem mayReach_transportInvariant : TransportInvariant MayReach := by
  intro Term Term' step step' embedding claim term
  constructor
  · rintro ⟨reduct', reaches, holds⟩
    obtain ⟨reduct, reachesReduct, rfl⟩ := (embedding.reach_iff term reduct').mp reaches
    exact ⟨reduct, reachesReduct, (embedding.imageClaim_embed_iff claim reduct).mp holds⟩
  · rintro ⟨reduct, reaches, holds⟩
    exact ⟨embedding.embed reduct, (embedding.reach_iff term _).mpr ⟨reduct, reaches, rfl⟩,
      reduct, rfl, holds⟩

theorem mustReach_transportInvariant : TransportInvariant MustReach := by
  intro Term Term' step step' embedding claim term
  constructor
  · intro must reduct reaches
    exact (embedding.imageClaim_embed_iff claim reduct).mp
      (must _ ((embedding.reach_iff term _).mpr ⟨reduct, reaches, rfl⟩))
  · intro must reduct' reaches
    obtain ⟨reduct, reachesReduct, rfl⟩ := (embedding.reach_iff term reduct').mp reaches
    exact ⟨reduct, rfl, must reduct reachesReduct⟩

theorem deterministic_transportInvariant : TransportInvariant Deterministic := by
  intro Term Term' step step' embedding claim term
  constructor
  · intro deterministic reduct reaches
    exact (embedding.functional_iff reduct).mp
      (deterministic _ ((embedding.reach_iff term _).mpr ⟨reduct, reaches, rfl⟩))
  · intro deterministic reduct' reaches
    obtain ⟨reduct, reachesReduct, rfl⟩ := (embedding.reach_iff term reduct').mp reaches
    exact (embedding.functional_iff reduct).mpr (deterministic reduct reachesReduct)

theorem may_growsWithSteps : GrowsWithSteps May := by
  intro Term step step' included claim term
  rintro ⟨next, stepped, holds⟩
  exact ⟨next, included _ _ stepped, holds⟩

theorem mayReach_growsWithSteps : GrowsWithSteps MayReach := by
  intro Term step step' included claim term
  rintro ⟨reduct, reaches, holds⟩
  exact ⟨reduct, ReflTransGen.mono included term reduct reaches, holds⟩

/-! ## Normal forms and conversion along exact embeddings -/

/-- **Normal forms are conserved**: normality is the must-observation of the
empty claim. -/
theorem isNormal_transport {Term Term' : Type} {step : Term → Term → Prop}
    {step' : Term' → Term' → Prop} (embedding : ExactEmbedding step step') (term : Term) :
    IsNormal step' (embedding.embed term) ↔ IsNormal step term := by
  have observed := must_transportInvariant embedding (fun _ => False) term
  simp only [Must, imageClaim, and_false, exists_false] at observed
  exact observed

namespace ExactEmbedding

variable {Term Term' : Type} {step : Term → Term → Prop} {step' : Term' → Term' → Prop}
  (embedding : ExactEmbedding step step')

/-- Conversions of a term are conversions of its image. -/
theorem eqvGen_embed {term other : Term} (converted : EqvGen step term other) :
    EqvGen step' (embedding.embed term) (embedding.embed other) := by
  induction converted with
  | rel _ _ stepped => exact EqvGen.rel _ _ ((embedding.exact _ _).mpr ⟨_, stepped, rfl⟩)
  | refl => exact EqvGen.refl _
  | symm _ _ _ ih => exact EqvGen.symm _ _ ih
  | trans _ _ _ _ _ first second => exact EqvGen.trans _ _ _ first second

/-- **Conversion is conserved along an exact embedding into a confluent step
relation.** -/
theorem eqvGen_iff (confluent : Confluent step') (term other : Term) :
    EqvGen step' (embedding.embed term) (embedding.embed other) ↔ EqvGen step term other := by
  refine ⟨fun converted => ?_, embedding.eqvGen_embed⟩
  obtain ⟨common, fromTerm, fromOther⟩ := confluent.eqvGen_iff_join.mp converted
  obtain ⟨reduct, reaches, rfl⟩ := (embedding.reach_iff term common).mp fromTerm
  obtain ⟨reduct', reaches', same⟩ := (embedding.reach_iff other _).mp fromOther
  rw [embedding.injective same] at reaches'
  exact EqvGen.trans _ _ _ (EqvGen.reflTransGen_le_eqvGen step _ _ reaches)
    (EqvGen.symm _ _ (EqvGen.reflTransGen_le_eqvGen step _ _ reaches'))

end ExactEmbedding

/-- The empty step relation converts only equal terms. -/
private theorem eqvGen_empty {Term : Type} {term other : Term}
    (converted : EqvGen (fun (_ _ : Term) => False) term other) : term = other := by
  induction converted with
  | rel _ _ stepped => exact stepped.elim
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- A fork outside the image: the extra value steps to every embedded value. -/
def forkStep (source target : Option Bool) : Prop :=
  source = none ∧ target ≠ none

/-- The truth values embed exactly into the fork: no embedded value steps. -/
def forkEmbedding : ExactEmbedding (fun (_ _ : Bool) => False) forkStep where
  embed := some
  injective := Option.some_injective _
  exact := by
    intro term next'
    simp [forkStep]

/-- **Without confluence, conversion is not conserved**: the two embedded
values become convertible through the fork. -/
theorem fork_conversion_not_conserved :
    EqvGen forkStep (forkEmbedding.embed true) (forkEmbedding.embed false) ∧
      ¬ EqvGen (fun (_ _ : Bool) => False) true false :=
  ⟨EqvGen.trans _ none _ (EqvGen.symm _ _ (EqvGen.rel _ _ ⟨rfl, Option.some_ne_none _⟩))
      (EqvGen.rel _ _ ⟨rfl, Option.some_ne_none _⟩),
    fun converted => Bool.noConfusion (eqvGen_empty converted)⟩

/-- Confluence is exactly what the fork lacks. -/
theorem fork_not_confluent : ¬ Confluent forkStep := fun confluent =>
  fork_conversion_not_conserved.2
    ((forkEmbedding.eqvGen_iff confluent true false).mp fork_conversion_not_conserved.1)

/-- One step from outside the image into it. -/
def entryStep (source target : Option Bool) : Prop :=
  source = none ∧ target = some true

/-- The truth values embed exactly beside the entry step. -/
def entryEmbedding : ExactEmbedding (fun (_ _ : Bool) => False) entryStep where
  embed := some
  injective := Option.some_injective _
  exact := by
    intro term next'
    simp [entryStep]

theorem entryStep_confluent : Confluent entryStep := by
  have reach : ∀ source target, ReflTransGen entryStep source target →
      target = source ∨ target = some true := by
    intro source target reaches
    induction reaches with
    | refl => exact Or.inl rfl
    | tail _ stepped _ => exact Or.inr stepped.2
  intro source left right toLeft toRight
  rcases reach _ _ toLeft with sameLeft | entered
  · rcases reach _ _ toRight with sameRight | entered'
    · exact ⟨source, sameLeft ▸ ReflTransGen.refl, sameRight ▸ ReflTransGen.refl⟩
    · exact ⟨right, sameLeft ▸ toRight, ReflTransGen.refl⟩
  · rcases reach _ _ toRight with sameRight | entered'
    · exact ⟨left, ReflTransGen.refl, sameRight ▸ toLeft⟩
    · exact ⟨left, ReflTransGen.refl, entered ▸ entered' ▸ ReflTransGen.refl⟩

/-- **Positive control**: beside a confluent entry into the image, the two
embedded values stay apart. -/
theorem entry_conversion_conserved :
    ¬ EqvGen entryStep (entryEmbedding.embed true) (entryEmbedding.embed false) :=
  fun converted => Bool.noConfusion
    (eqvGen_empty ((entryEmbedding.eqvGen_iff entryStep_confluent true false).mp converted))

/-! ## Structural coproducts conserve both classes -/

/-- One step of the premise-aware contextual engine, read as a relation. -/
def answerStep (base : BasePremiseEvaluator) (language : LanguageDef) (fuel : Nat)
    (term next : Pattern) : Prop :=
  next ∈ rewriteAt base language fuel term

section Embeddings

variable {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
  {left right : ValidatedLanguageDef}
  (coproduct : Compatibility name leftSymbols rightSymbols left right)
  {sourceBase targetBase : BasePremiseEvaluator}

/-- The left summand embeds its contextual engine exactly, at every fuel,
whenever the premise evaluators commute on its rules. -/
def leftEmbedding
    (commutes : RulePremiseEvaluatorsCommute leftSymbols left.language
      coproduct.combinedLanguage.language sourceBase targetBase)
    (fuel : Nat) :
    ExactEmbedding (answerStep sourceBase left.language fuel)
      (answerStep targetBase coproduct.combinedLanguage.language fuel) where
  embed := mapPattern leftSymbols
  injective := mapPattern_injective_of_constructor_injective leftSymbols
    coproduct.leftSymbolsInjective.constructor
  exact term next' := by
    unfold answerStep
    rw [StructuralCoproductOperational.Compatibility.left_rewriteAt_exact_onRules
      coproduct sourceBase targetBase commutes fuel term, List.mem_map]

/-- The right summand embeds its contextual engine exactly. -/
def rightEmbedding
    (commutes : RulePremiseEvaluatorsCommute rightSymbols right.language
      coproduct.combinedLanguage.language sourceBase targetBase)
    (fuel : Nat) :
    ExactEmbedding (answerStep sourceBase right.language fuel)
      (answerStep targetBase coproduct.combinedLanguage.language fuel) where
  embed := mapPattern rightSymbols
  injective := mapPattern_injective_of_constructor_injective rightSymbols
    coproduct.rightSymbolsInjective.constructor
  exact term next' := by
    unfold answerStep
    rw [StructuralCoproductOperational.Compatibility.right_rewriteAt_exact_onRules
      coproduct sourceBase targetBase commutes fuel term, List.mem_map]

/-- Exactness includes multiplicity: an embedded term has as many answers as
the term, in the same order. -/
theorem left_answer_count
    (commutes : RulePremiseEvaluatorsCommute leftSymbols left.language
      coproduct.combinedLanguage.language sourceBase targetBase)
    (fuel : Nat) (term : Pattern) :
    (rewriteAt targetBase coproduct.combinedLanguage.language fuel
        (mapPattern leftSymbols term)).length =
      (rewriteAt sourceBase left.language fuel term).length := by
  rw [StructuralCoproductOperational.Compatibility.left_rewriteAt_exact_onRules
    coproduct sourceBase targetBase commutes fuel term, List.length_map]

end Embeddings

/-- A structural coproduct with a given core as its left summand, together with
a premise evaluator on the coproduct that commutes with the core's evaluator
on the core's own rules. -/
structure LeftSummand (sourceBase : BasePremiseEvaluator) (core : ValidatedLanguageDef) where
  name : String
  leftSymbols : LanguageDefSymbolMap
  rightSymbols : LanguageDefSymbolMap
  right : ValidatedLanguageDef
  coproduct : Compatibility name leftSymbols rightSymbols core right
  targetBase : BasePremiseEvaluator
  commutes : RulePremiseEvaluatorsCommute leftSymbols core.language
    coproduct.combinedLanguage.language sourceBase targetBase

/-- A structural coproduct with a given core as its right summand. -/
structure RightSummand (sourceBase : BasePremiseEvaluator) (core : ValidatedLanguageDef) where
  name : String
  leftSymbols : LanguageDefSymbolMap
  rightSymbols : LanguageDefSymbolMap
  left : ValidatedLanguageDef
  coproduct : Compatibility name leftSymbols rightSymbols left core
  targetBase : BasePremiseEvaluator
  commutes : RulePremiseEvaluatorsCommute rightSymbols core.language
    coproduct.combinedLanguage.language sourceBase targetBase

/-- Coproduct extensions of a core on its left, as an extension layer. -/
def leftSummands (sourceBase : BasePremiseEvaluator) : ExtensionLayer ValidatedLanguageDef where
  Fiber := LeftSummand sourceBase

/-- Coproduct extensions of a core on its right, as an extension layer. -/
def rightSummands (sourceBase : BasePremiseEvaluator) : ExtensionLayer ValidatedLanguageDef where
  Fiber := RightSummand sourceBase

/-- **A structural coproduct conserves every transport-invariant observation on
its left summand.**  The observation of a core term inside the coproduct, with
the claim carried along the injection, equals the observation inside the core.
`May`, `Must`, `MayReach`, `MustReach` and `Deterministic` are instances. -/
theorem leftSummands_conserve (sourceBase : BasePremiseEvaluator)
    (observe : ObservationClass) (invariant : TransportInvariant observe)
    (fuel : Nat) (claim : Pattern → Prop) (term : Pattern) :
    (leftSummands sourceBase).Conserves
      (fun core => observe (answerStep sourceBase core.language fuel) claim term)
      (fun attached =>
        let summand : LeftSummand sourceBase attached.1 := attached.2
        observe (answerStep summand.targetBase summand.coproduct.combinedLanguage.language fuel)
          (imageClaim (mapPattern summand.leftSymbols) claim)
          (mapPattern summand.leftSymbols term)) := by
  intro attached
  let summand : LeftSummand sourceBase attached.1 := attached.2
  exact propext (invariant (leftEmbedding summand.coproduct summand.commutes fuel) claim term)

/-- **A structural coproduct conserves every transport-invariant observation on
its right summand.** -/
theorem rightSummands_conserve (sourceBase : BasePremiseEvaluator)
    (observe : ObservationClass) (invariant : TransportInvariant observe)
    (fuel : Nat) (claim : Pattern → Prop) (term : Pattern) :
    (rightSummands sourceBase).Conserves
      (fun core => observe (answerStep sourceBase core.language fuel) claim term)
      (fun attached =>
        let summand : RightSummand sourceBase attached.1 := attached.2
        observe (answerStep summand.targetBase summand.coproduct.combinedLanguage.language fuel)
          (imageClaim (mapPattern summand.rightSymbols) claim)
          (mapPattern summand.rightSymbols term)) := by
  intro attached
  let summand : RightSummand sourceBase attached.1 := attached.2
  exact propext (invariant (rightEmbedding summand.coproduct summand.commutes fuel) claim term)

/-! ## Inclusions and overlapping unions preserve may-observations only -/

/-- One step of the premise-free root engine, read as a relation. -/
def rootStep (language : LanguageDef) (term next : Pattern) : Prop :=
  next ∈ rewriteStep language term

/-- Ordered inclusions of rewrite rows over a language, as an extension layer.
The extended language keeps every rule of the base in order and may add rules
anywhere, including rules over the base's own constructors. -/
def inclusions : ExtensionLayer LanguageDef where
  Fiber base := {extended : LanguageDef // base.rewrites.Sublist extended.rewrites}

/-- **Inclusions preserve every observation that grows with steps.**  May and
reachable-may observations survive every ordered inclusion of rewrite rows. -/
theorem inclusions_preserve (observe : ObservationClass) (grows : GrowsWithSteps observe)
    (claim : Pattern → Prop) (term : Pattern) (attached : inclusions.Total) :
    observe (rootStep attached.1) claim term →
      observe (rootStep (attached.2 : inclusions.Fiber attached.1).1) claim term :=
  grows (fun source _ stepped =>
    (ModuleAlgebra.IdentityInterface.ordered_rewrite_answers_preserved
      (attached.2 : inclusions.Fiber attached.1).2 source).subset stepped)
    claim term

/-- An overlapping union keeps both sides' rewrite rows in order.  Each side
is an ordered inclusion into it, so its may-observations survive. -/
theorem overlappingUnion_preserves (observe : ObservationClass) (grows : GrowsWithSteps observe)
    (union left right : LanguageDef) (rows : union.rewrites = left.rewrites ++ right.rewrites)
    (claim : Pattern → Prop) (term : Pattern) :
    (observe (rootStep left) claim term → observe (rootStep union) claim term) ∧
      (observe (rootStep right) claim term → observe (rootStep union) claim term) := by
  constructor
  · exact grows (fun source _ stepped =>
      (ModuleAlgebra.IdentityInterface.ordered_rewrite_answers_preserved
        (rows ▸ List.sublist_append_left left.rewrites right.rewrites) source).subset
        stepped) claim term
  · exact grows (fun source _ stepped =>
      (ModuleAlgebra.IdentityInterface.ordered_rewrite_answers_preserved
        (rows ▸ List.sublist_append_right left.rewrites right.rewrites) source).subset
        stepped) claim term

/-- **An inclusion can give an old term a new answer and falsify a vacuous
must-claim.**  The base language has no rule for `A`; the extended language
keeps the base rules and adds `A ↦ B`. -/
theorem inclusion_gains_answer_and_breaks_must :
    ∃ (base : LanguageDef) (extended : inclusions.Fiber base),
      ¬ May (rootStep base) (fun next => next = .apply "B" []) (.apply "A" []) ∧
        May (rootStep extended.1) (fun next => next = .apply "B" []) (.apply "A" []) ∧
        Must (rootStep base) (fun next => next = .apply "A" []) (.apply "A" []) ∧
        ¬ Must (rootStep extended.1) (fun next => next = .apply "A" []) (.apply "A" []) := by
  obtain ⟨silent, answers⟩ :=
    ModuleAlgebra.IdentityInterface.inclusion_does_not_imply_reflection
  refine ⟨_, ⟨_, ModuleAlgebra.IdentityInterface.extra_rules_include_source⟩, ?_, ?_, ?_, ?_⟩
  · rintro ⟨next, stepped, _⟩
    rw [rootStep, silent] at stepped
    cases stepped
  · exact ⟨.apply "B" [], by rw [rootStep, answers]; simp, rfl⟩
  · intro next stepped
    rw [rootStep, silent] at stepped
    cases stepped
  · intro must
    have answered := must (.apply "B" []) (by rw [rootStep, answers]; simp)
    simp at answered

/-- **Inclusions do not conserve may-observations.** -/
theorem inclusions_do_not_conserve_may :
    ¬ inclusions.Conserves
      (fun base => May (rootStep base) (fun next => next = .apply "B" []) (.apply "A" []))
      (fun attached =>
        May (rootStep (attached.2 : inclusions.Fiber attached.1).1)
          (fun next => next = .apply "B" []) (.apply "A" [])) := by
  intro conserves
  obtain ⟨base, extended, notBefore, after, _, _⟩ := inclusion_gains_answer_and_breaks_must
  have same := conserves ⟨base, extended⟩
  dsimp only [ExtensionLayer.erase] at same
  rw [same] at after
  exact notBefore after

/-- **Inclusions do not conserve must-observations.** -/
theorem inclusions_do_not_conserve_must :
    ¬ inclusions.Conserves
      (fun base => Must (rootStep base) (fun next => next = .apply "A" []) (.apply "A" []))
      (fun attached =>
        Must (rootStep (attached.2 : inclusions.Fiber attached.1).1)
          (fun next => next = .apply "A" []) (.apply "A" [])) := by
  intro conserves
  obtain ⟨base, extended, _, _, before, notAfter⟩ := inclusion_gains_answer_and_breaks_must
  have same := conserves ⟨base, extended⟩
  dsimp only [ExtensionLayer.erase] at same
  rw [← same] at before
  exact notAfter before

section AddedEquation

open Mettapedia.OSLF.Framework.TypeSynthesis (langReduces)
open Mettapedia.Languages.MeTTa.OSLFCore.Bridge.GroundData (schema)
open Mettapedia.OSLF.NativeTypes.Instances.MeTTaFamily
open Mettapedia.OSLF.NativeTypes.Instances.MeTTaFamily.EquationSite

/-- **Adding an equation preserves may-observations only.**  In the sample
MeTTa program read as rewrites, adding the third equation keeps every
successor of `(g a)`; it falsifies the must-claim that every successor is `b`
and it makes `(g a)` nondeterministic. -/
theorem adding_equation_preserves_may_only :
    (∀ claim, May (langReduces (programLanguage "metta-program" sampleProgramPrefix)) claim
        (schema (call "g" (.symbol "a"))) →
      May (langReduces program) claim (schema (call "g" (.symbol "a")))) ∧
    Must (langReduces (programLanguage "metta-program" sampleProgramPrefix))
      (fun next => next = schema (.symbol "b")) (schema (call "g" (.symbol "a"))) ∧
    ¬ Must (langReduces program) (fun next => next = schema (.symbol "b"))
      (schema (call "g" (.symbol "a"))) ∧
    Functional (langReduces (programLanguage "metta-program" sampleProgramPrefix))
      (schema (call "g" (.symbol "a"))) ∧
    ¬ Functional (langReduces program) (schema (call "g" (.symbol "a"))) := by
  obtain ⟨keeps, prefixMust, fullNotMust⟩ := adding_equation_breaks_must
  refine ⟨fun claim => ?_, prefixMust, fullNotMust, ?_, ?_⟩
  · rintro ⟨next, stepped, holds⟩
    exact ⟨next, keeps next stepped, holds⟩
  · intro first second stepFirst stepSecond
    rw [prefixMust first stepFirst, prefixMust second stepSecond]
  · intro functional
    have toB : langReduces program (schema (call "g" (.symbol "a"))) (schema (.symbol "b")) :=
      (steps_iff _ program_noncontextual _ _).mpr (by rw [call_successors]; simp)
    have toC : langReduces program (schema (call "g" (.symbol "a"))) (schema (.symbol "c")) :=
      (steps_iff _ program_noncontextual _ _).mpr (by rw [call_successors]; simp)
    have same := functional _ _ toB toC
    revert same
    decide +kernel

end AddedEquation

#print axioms leftSummands_conserve
#print axioms rightSummands_conserve
#print axioms deterministic_transportInvariant
#print axioms inclusions_preserve
#print axioms inclusion_gains_answer_and_breaks_must
#print axioms inclusions_do_not_conserve_may
#print axioms inclusions_do_not_conserve_must
#print axioms adding_equation_preserves_may_only
#print axioms isNormal_transport
#print axioms ExactEmbedding.eqvGen_iff
#print axioms fork_conversion_not_conserved
#print axioms fork_not_confluent
#print axioms entry_conversion_conserved

end Mettapedia.GSLT.LanguageDef.ExtensionConservativity
