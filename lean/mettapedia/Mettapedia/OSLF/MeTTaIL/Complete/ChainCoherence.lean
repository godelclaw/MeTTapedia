import Mettapedia.OSLF.MeTTaIL.Complete.QuoteDropCoherence

/-!
# The explorer is complete when firings normalize along chains

A canonical form may hold one redex several times. When composition distributes over a sum, the
canonical form is a sum of products, and a redex inside a shared factor occurs once in every product
that shares it: the firing at the factored presentation `P | (Q + R)` is two firings at the canonical
form `(P | Q) + (P | R)`, one in each product. A firing at a presentation is then matched, from the
canonical form of the presentation, by a chain of committed firings ending equal to its result
(`FiringsChainOn`), and the explorer committing that form still explores every reachable state, up to
the model's equality (`explores_of_chain`). A firing matched by one committed firing is the chain of
length one (`chainOn_of_normalizeOn`).

The canonical form need only be sound on the presentations of an invariant kept by the model's equality
(`NormalizerOn`): a sum of products is sound for processes whose sums are not empty, and those are the
presentations a well-formed process is equal to.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Complete.ChainCoherence

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission Coherence
open Relation (EqvGen ReflTransGen)

variable (plan : Plan) (bound : List TypeExpr) (expected : TypeExpr)

/-- One committed firing: a firing at a state, then the committed form of its result. -/
def CommittedFire (form : Pattern → Pattern) (state next : Pattern) : Prop :=
  ∃ receipt, GeneralOccurrenceSemantics.Primitive plan bound expected state receipt ∧ next = form receipt.target

/-- Every firing at a presentation satisfying an invariant is matched, from the committed form of the
presentation, by a chain of committed firings ending equal to its result in the model. -/
def FiringsChainOn (moves : Pattern → Pattern → Prop) (form : Pattern → Pattern) (good : Pattern → Prop) : Prop :=
  ∀ term (receipt : GeneralRuleJobs.Receipt), good term →
    GeneralOccurrenceSemantics.Primitive plan bound expected term receipt →
    ∃ last, ReflTransGen (CommittedFire plan bound expected form) (form term) last ∧
      EqvGen (fun a b => GeneralOccurrenceSemantics.Equation plan bound expected a b ∨ moves a b) receipt.target last

/-- A canonical form on the presentations satisfying an invariant: sound there, kept by every move,
and idempotent. -/
structure NormalizerOn (moves : Pattern → Pattern → Prop) (form : Pattern → Pattern) (good : Pattern → Prop) : Prop where
  sound : ∀ term, good term → EqvGen moves term (form term)
  canonical : ∀ left right, moves left right → form left = form right
  idempotent : ∀ term, form (form term) = form term

variable {plan bound expected}

/-- A canonical form sound everywhere is sound on every invariant. -/
theorem Normalizer.on {moves : Pattern → Pattern → Prop} {form : Pattern → Pattern} (normalizer : Normalizer moves form)
    (good : Pattern → Prop) : NormalizerOn moves form good :=
  ⟨fun term _ => normalizer.sound term, normalizer.canonical, normalizer.idempotent⟩

theorem NormalizerOn.eqvGen_eq {moves : Pattern → Pattern → Prop} {form : Pattern → Pattern} {good : Pattern → Prop}
    (normalizer : NormalizerOn moves form good) {left right : Pattern} (related : EqvGen moves left right) :
    form left = form right := by
  induction related with
  | rel _ _ move => exact normalizer.canonical _ _ move
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- **One committed firing is a chain of length one.** -/
theorem chainOn_of_normalizeOn {moves : Pattern → Pattern → Prop} {form : Pattern → Pattern}
    (normalizer : Normalizer moves form) {good : Pattern → Prop}
    (normalize : FiringsNormalizeOn (GeneralOccurrenceSemantics.Equation plan bound expected) moves form
      (GeneralOccurrenceSemantics.Primitive plan bound expected) GeneralRuleJobs.Receipt.target good) :
    FiringsChainOn plan bound expected moves form good := by
  intro term receipt holds fired
  obtain ⟨receipt', fired', same⟩ := normalize term receipt holds fired
  exact ⟨form receipt'.target, .single ⟨receipt', fired', rfl⟩,
    .trans _ _ _ same (Relation.EqvGen.mono (fun _ _ move => .inr move) _ _ (normalizer.sound _))⟩

/-- Without equations, equality modulo the plan's equations is identity. -/
theorem eq_of_equations (noEquations : ∀ left right, ¬ GeneralOccurrenceSemantics.Equation plan bound expected left right)
    {left right : Pattern} (related : EqvGen (GeneralOccurrenceSemantics.Equation plan bound expected) left right) :
    left = right := by
  induction related with
  | rel _ _ equation => exact absurd equation (noEquations _ _)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- **Committed firings stay explored**: every state a chain of committed firings reaches from an
explored state is explored. -/
theorem explored_along (checked : Predecessors.equationsChecked plan = true)
    (noEquations : ∀ left right, ¬ GeneralOccurrenceSemantics.Equation plan bound expected left right)
    {form : Pattern → Pattern} {start state last : Pattern}
    (explored : Explore.Explored (S := QuoteDropCoherence.searchWith plan bound expected form) start state)
    (chain : ReflTransGen (CommittedFire plan bound expected form) state last) :
    Explore.Explored (S := QuoteDropCoherence.searchWith plan bound expected form) start last := by
  induction chain with
  | refl => exact explored
  | @tail middle next _ step ih =>
    obtain ⟨receipt, fired, rfl⟩ := step
    have stepped : (GeneralOccurrenceSemantics.gslt plan bound expected).Step middle receipt.target :=
      ⟨middle, receipt, .refl _, fired, .refl _⟩
    obtain ⟨work, published, member, related⟩ := Classes.complete_in_limit plan bound expected middle checked stepped
    have reached := Explore.explored_target (QuoteDropCoherence.searchWith_lawful plan bound expected form) ih
      (work := work) member
    have same : published.target = receipt.target := eq_of_equations noEquations related
    rw [← same]
    exact reached

/-- Committed firings from good states stay good, when every committed firing from a good state does. -/
theorem chain_good {form : Pattern → Pattern} {good : Pattern → Prop}
    (committed : ∀ term (receipt : GeneralRuleJobs.Receipt), good term →
      GeneralOccurrenceSemantics.Primitive plan bound expected term receipt → good (form receipt.target))
    {state last : Pattern} (chain : ReflTransGen (CommittedFire plan bound expected form) state last)
    (holds : good state) : good last := by
  induction chain with
  | refl => exact holds
  | tail _ step ih =>
    obtain ⟨receipt, fired, rfl⟩ := step
    exact committed _ receipt ih fired

/-- The end of a chain of committed firings from a committed state is committed. -/
theorem chain_committed {form : Pattern → Pattern} (idempotent : ∀ term, form (form term) = form term)
    {state last : Pattern} (chain : ReflTransGen (CommittedFire plan bound expected form) state last)
    (normal : form state = state) : form last = last := by
  cases chain.cases_tail with
  | inl same => rw [same]; exact normal
  | inr step =>
    obtain ⟨_, _, receipt, _, rfl⟩ := step
    exact idempotent _

/-- **The explorer committing a canonical form is complete when firings normalize along chains**: for
a plan without equations, a relation of law moves with a canonical form sound on an invariant the moves
keep, committed firings keeping the invariant, and firings matched along chains of committed firings at
every presentation satisfying it, every state reachable from a source satisfying it by finitely many steps
modulo the equality of the moves is explored, up to that equality. -/
theorem explores_of_chain (checked : Predecessors.equationsChecked plan = true)
    (noEquations : ∀ left right, ¬ GeneralOccurrenceSemantics.Equation plan bound expected left right)
    {moves : Pattern → Pattern → Prop} {form : Pattern → Pattern} {good : Pattern → Prop}
    (normalizer : NormalizerOn moves form good)
    (stable : ∀ a b, (GeneralOccurrenceSemantics.Equation plan bound expected a b ∨ moves a b) → (good a ↔ good b))
    (committed : ∀ term (receipt : GeneralRuleJobs.Receipt), good term →
      GeneralOccurrenceSemantics.Primitive plan bound expected term receipt → good (form receipt.target))
    (chains : FiringsChainOn plan bound expected moves form good)
    (source : Pattern) (holds : good source) {target : Pattern}
    (reaches : (Mettapedia.OSLF.Framework.FiniteEquationCoverage.moduloGSLT
      (fun a b => GeneralOccurrenceSemantics.Equation plan bound expected a b ∨ moves a b)
      (GeneralOccurrenceSemantics.Primitive plan bound expected) GeneralRuleJobs.Receipt.target).MultiStep source target) :
    ∃ state, Explore.Explored (S := QuoteDropCoherence.searchWith plan bound expected form) (form source) state ∧
      EqvGen (fun a b => GeneralOccurrenceSemantics.Equation plan bound expected a b ∨ moves a b) state target := by
  have movesOnly : ∀ {a b : Pattern},
      EqvGen (fun a b => GeneralOccurrenceSemantics.Equation plan bound expected a b ∨ moves a b) a b →
      EqvGen moves a b := by
    intro a b related
    refine Relation.EqvGen.mono (fun x y step => ?_) _ _ related
    rcases step with equation | move
    · exact absurd equation (noEquations _ _)
    · exact move
  have toForm : EqvGen (fun a b => GeneralOccurrenceSemantics.Equation plan bound expected a b ∨ moves a b)
      source (form source) := Relation.EqvGen.mono (fun _ _ move => .inr move) _ _ (normalizer.sound source holds)
  suffices along : ∀ first last, (Mettapedia.OSLF.Framework.FiniteEquationCoverage.moduloGSLT
      (fun a b => GeneralOccurrenceSemantics.Equation plan bound expected a b ∨ moves a b)
      (GeneralOccurrenceSemantics.Primitive plan bound expected) GeneralRuleJobs.Receipt.target).MultiStep first last →
      ∀ state, Explore.Explored (S := QuoteDropCoherence.searchWith plan bound expected form) (form source) state →
      form state = state → good state →
      EqvGen (fun a b => GeneralOccurrenceSemantics.Equation plan bound expected a b ∨ moves a b) state first →
      ∃ reached, Explore.Explored (S := QuoteDropCoherence.searchWith plan bound expected form) (form source) reached ∧
        EqvGen (fun a b => GeneralOccurrenceSemantics.Equation plan bound expected a b ∨ moves a b) reached last from
    along source target reaches _ (Explore.explored_source _) (normalizer.idempotent source)
      (good_of_equiv stable toForm holds) (.symm _ _ toForm)
  intro first last reaches
  induction reaches with
  | refl term => intro state explored _ _ equal; exact ⟨state, explored, equal⟩
  | @step first middle last stepped _ ih =>
    intro state explored normal stateGood equal
    obtain ⟨representative, receipt, before, fired, after⟩ := stepped
    have related : EqvGen (fun a b => GeneralOccurrenceSemantics.Equation plan bound expected a b ∨ moves a b)
        state representative := .trans _ _ _ equal before
    have representativeGood : good representative := good_of_equiv stable related stateGood
    obtain ⟨final, chain, toFinal⟩ := chains representative receipt representativeGood fired
    have sameForm : form representative = state := by
      rw [← normalizer.eqvGen_eq (movesOnly related), normal]
    rw [sameForm] at chain
    exact ih final (explored_along checked noEquations explored chain)
      (chain_committed normalizer.idempotent chain normal) (chain_good committed chain stateGood)
      (.trans _ _ _ (.symm _ _ toFinal) after)

end Mettapedia.OSLF.MeTTaIL.Complete.ChainCoherence
