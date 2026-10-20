import Mettapedia.OSLF.MeTTaIL.Complete.Coherence
import Mettapedia.OSLF.MeTTaIL.CanonicalSites
import Mettapedia.OSLF.MeTTaIL.CanonicalFiring

/-!
# The canonical explorer is complete for the presented GSLT

An explorer that commits the canonical form of the declared collection laws (`lawNormal`)
visits one presentation per class of permutations, flattenings and unit removals. It is complete
for the presented GSLT, the plan's steps modulo equality in the model, whenever firings
normalize (`Coherence.FiringsNormalize`) and the plan has neither equations nor declared
extrusions (`presented_explores_canonical`).

Firings normalize for every plan without declared collection laws whose rules are admissible
at canonical forms: captures with increasing spines and no premises
(`firingsNormalize_of_admissible`). The proof transports a firing
at any presentation to the canonical form: a licensed site has a licensed counterpart
(`CanonicalBags.licensed_canon`), a match has a match with canonical captures
(`CanonicalBags.matches_canon`), and the reduct changes by a permutation
(`CanonicalBags.rootFiring_canon`).

- `primitive_canon`: every firing has a counterpart at the canonical form, with a
  permutation-equal result;
- `presented_explores_canonical`: every state reachable by finitely many presented steps is
  explored, up to equality in the model;
- `presented_explores_of_admissible`: the same, for plans without declared collection laws.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Complete.CanonicalCoherence

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission CanonicalBags Coherence
open Relation (EqvGen ReflTransGen SymmGen)

variable (plan : Plan) (bound : List TypeExpr) (expected : TypeExpr)

/-- No reduction context of the plan enters a set, and every rule fires at canonical forms. -/
def RulesAdmissible : Prop :=
  NoSetDescent plan.permissions.sites ∧
    ∀ declaration ordinal, (declaration, ordinal) ∈ plan.rules.zipIdx →
      CanonicalFiringAdmissible (GeneralPlanEnvironment.environment plan) ordinal

/-- The search modulo equations, committing canonical forms of the declared collection laws. -/
def search : Mettapedia.Machines.ResumableSearchRunner.Search Pattern (Classes.State plan)
    GeneralOccurrenceSemantics.Receipt :=
  { Classes.search plan bound expected with
    target := fun receipt => lawNormal (Normalized.laws plan) receipt.target }

theorem search_lawful : (search plan bound expected).Lawful where
  resume_run := (Classes.search_lawful plan bound expected).resume_run
  publication_prefix := (Classes.search_lawful plan bound expected).publication_prefix
  sound := (Classes.search_lawful plan bound expected).sound

variable {plan bound expected}

/-- **Every firing has a counterpart at the canonical form**, with a permutation-equal result. -/
theorem primitive_canon (admissible : RulesAdmissible plan) {source : Pattern} {receipt : GeneralRuleJobs.Receipt}
    (fired : GeneralOccurrenceSemantics.Primitive plan bound expected source receipt) :
    ∃ receipt', GeneralOccurrenceSemantics.Primitive plan bound expected (canon source) receipt' ∧
      Same receipt.target receipt'.target := by
  obtain ⟨⟨declared, licensed⟩, rooted, accepts, endpoint, sorted⟩ := fired
  obtain ⟨site', licensed', focus, focusBound, focusType, frames, context⟩ :=
    licensed_canon licensed (contextSetFree_of_noSetDescent admissible.1 licensed)
  obtain ⟨trace', localTarget', rooted', sameLocal⟩ :=
    rootFiring_canon rooted (admissible.2 _ _ declared)
  have sameTarget : Same receipt.target (site'.context.fill localTarget') := by
    rw [endpoint]; exact context.fill sameLocal
  refine ⟨⟨⟨receipt.job.ordinal, receipt.job.declaration, site'⟩, trace', canonAssignment receipt.captured,
    canonAssignment receipt.completed, receipt.premiseHistory, localTarget', site'.context.fill localTarget'⟩,
    ⟨⟨declared, licensed'⟩, ?_, ?_, rfl, ?_⟩, sameTarget⟩
  · simp only [focus, focusBound, focusType]
    exact rooted'
  · simp only [GeneralTypedSites.SiteData.acceptsReplacementRepresentation, frames]
    rw [← replacementRepresentations?_same context _ sameLocal]
    exact accepts
  · exact openPatternWellSorted_of_eqvGen ((same_iff _ _).mp sameTarget) sorted

theorem lawNormal_nil (pattern : Pattern) : lawNormal [] pattern = canon pattern := by
  rw [lawNormal, CollectionLaws.normalize_nil]

/-- Without scope extrusion, the canonical commit of the runner is `lawNormal`. -/
theorem commit_canonical (noExtrusions : Normalized.extrusions plan = []) (pattern : Pattern) :
    Normalized.commit plan .canonical pattern = lawNormal (Normalized.laws plan) pattern := by
  rw [Normalized.commit, Normalized.standard, noExtrusions, CollectionLaws.standardForm, CollectionLaws.extrude_nil,
    lawNormal]

/-- **Without scope extrusion, the runner's canonical search is this search.** -/
theorem search_canonical (plan : Plan) (bound : List TypeExpr) (expected : TypeExpr)
    (noExtrusions : Normalized.extrusions plan = []) :
    Normalized.search plan bound expected .canonical = search plan bound expected := by
  have targets : (fun receipt : GeneralOccurrenceSemantics.Receipt => Normalized.commit plan .canonical receipt.target) =
      fun receipt => lawNormal (Normalized.laws plan) receipt.target := by
    funext receipt
    exact commit_canonical noExtrusions receipt.target
  simp only [Normalized.search, search, targets]

/-- Permutation-equal terms are equal in the model. -/
theorem modelEquiv_of_same {left right : Pattern} (same : Same left right) :
    EqvGen (fun a b => GeneralOccurrenceSemantics.Equation plan bound expected a b ∨
      StandardStep (Normalized.laws plan) (Normalized.extrusions plan) a b) left right :=
  Relation.EqvGen.mono (fun _ _ step => .inr (.law (step.lawStep _))) _ _ ((same_iff _ _).mp same)

/-- **Firings normalize** for every plan without declared collection laws whose rules fire at
canonical forms. -/
theorem firingsNormalize_of_admissible (admissible : RulesAdmissible plan) (noLaws : Normalized.laws plan = []) :
    FiringsNormalize (GeneralOccurrenceSemantics.Equation plan bound expected)
      (StandardStep (Normalized.laws plan) (Normalized.extrusions plan)) (lawNormal (Normalized.laws plan))
      (GeneralOccurrenceSemantics.Primitive plan bound expected) GeneralRuleJobs.Receipt.target := by
  intro term receipt fired
  obtain ⟨receipt', fired', same⟩ := primitive_canon admissible fired
  refine ⟨receipt', ?_, modelEquiv_of_same same⟩
  rw [noLaws, lawNormal_nil]
  exact fired'

/-- Without equations, the normalized class of a state is the state. -/
theorem normalClass_eq (noEquations : ∀ left right, ¬ GeneralOccurrenceSemantics.Equation plan bound expected left right)
    {state reached : Pattern}
    (inClass : NormalClass (GeneralOccurrenceSemantics.Equation plan bound expected) (lawNormal (Normalized.laws plan))
      state reached) : reached = state := by
  induction inClass with
  | refl => rfl
  | tail _ step _ =>
    obtain ⟨_, equation, _⟩ := step
    rcases equation with forward | backward
    · exact absurd forward (noEquations _ _)
    · exact absurd backward (noEquations _ _)

/-- **The canonical explorer is complete for the presented GSLT, on an invariant**: for a plan
without equations or declared extrusions whose firings normalize at every presentation satisfying
an invariant kept by equality in the model and by committed firings, every state reachable from a
source satisfying it by finitely many presented steps is explored, up to equality in the model. -/
theorem presented_explores_canonical_on (checked : Predecessors.equationsChecked plan = true)
    (noEquations : ∀ left right, ¬ GeneralOccurrenceSemantics.Equation plan bound expected left right)
    (noExtrusions : Normalized.extrusions plan = []) {good : Pattern → Prop}
    (stable : ∀ a b, Presented.ModelEquation plan bound expected a b → (good a ↔ good b))
    (committed : ∀ term (receipt : GeneralRuleJobs.Receipt), GeneralOccurrenceSemantics.Primitive plan bound expected term
      receipt → good (lawNormal (Normalized.laws plan) receipt.target))
    (normalize : FiringsNormalizeOn (GeneralOccurrenceSemantics.Equation plan bound expected)
      (StandardStep (Normalized.laws plan) (Normalized.extrusions plan)) (lawNormal (Normalized.laws plan))
      (GeneralOccurrenceSemantics.Primitive plan bound expected) GeneralRuleJobs.Receipt.target good)
    (source : Pattern) (holds : good (lawNormal (Normalized.laws plan) source)) {target : Pattern}
    (reaches : (Presented.gslt plan bound expected).MultiStep source target) :
    ∃ state, Explore.Explored (S := search plan bound expected) (lawNormal (Normalized.laws plan) source) state ∧
      Presented.ModelEquiv plan bound expected state target := by
  have normalizer : Normalizer (StandardStep (Normalized.laws plan) (Normalized.extrusions plan))
      (lawNormal (Normalized.laws plan)) := by
    rw [noExtrusions]; exact lawNormalizer _
  have lift : EquationsLift (GeneralOccurrenceSemantics.Equation plan bound expected) (lawNormal (Normalized.laws plan)) := by
    intro left right equation
    rcases equation with forward | backward
    · exact absurd forward (noEquations _ _)
    · exact absurd backward (noEquations _ _)
  suffices along : ∀ first last, (Presented.gslt plan bound expected).MultiStep first last → ∀ state,
      Explore.Explored (S := search plan bound expected) (lawNormal (Normalized.laws plan) source) state →
      lawNormal (Normalized.laws plan) state = state → good state →
      Presented.ModelEquiv plan bound expected state first →
      ∃ reached, Explore.Explored (S := search plan bound expected) (lawNormal (Normalized.laws plan) source) reached ∧
        Presented.ModelEquiv plan bound expected reached last from
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
    have next := Explore.explored_target (search_lawful plan bound expected) explored (work := work) member
    have equalOf : ∀ a b, Relation.EqvGen (GeneralOccurrenceSemantics.Equation plan bound expected) a b → a = b := by
      intro a b equivalent
      induction equivalent with
      | rel _ _ equation => exact absurd equation (noEquations _ _)
      | refl => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ first second => exact first.trans second
    have publishedEq : published.target = receipt'.target := equalOf _ _ related
    refine ih _ next (normalizer.idempotent _) ?_ ?_
    · show good (lawNormal (Normalized.laws plan) published.target)
      rw [publishedEq]; exact committed _ _ fired'
    · have toPublished : Presented.ModelEquiv plan bound expected (lawNormal (Normalized.laws plan) published.target)
          published.target :=
        .symm _ _ (Relation.EqvGen.mono (fun _ _ move => .inr move) _ _ (normalizer.sound published.target))
      have fromEquations : Presented.ModelEquiv plan bound expected published.target receipt'.target :=
        Relation.EqvGen.mono (fun _ _ equation => .inl equation) _ _ related
      exact .trans _ _ _ toPublished (.trans _ _ _ fromEquations (.trans _ _ _ (.symm _ _ sameTarget) after))

/-- **The canonical explorer is complete for the presented GSLT**: for a plan without
equations or declared extrusions whose firings normalize, every state reachable from the
source by finitely many presented steps is explored, up to equality in the model. -/
theorem presented_explores_canonical (checked : Predecessors.equationsChecked plan = true)
    (noEquations : ∀ left right, ¬ GeneralOccurrenceSemantics.Equation plan bound expected left right)
    (noExtrusions : Normalized.extrusions plan = [])
    (normalize : FiringsNormalize (GeneralOccurrenceSemantics.Equation plan bound expected)
      (StandardStep (Normalized.laws plan) (Normalized.extrusions plan)) (lawNormal (Normalized.laws plan))
      (GeneralOccurrenceSemantics.Primitive plan bound expected) GeneralRuleJobs.Receipt.target)
    (source : Pattern) {target : Pattern}
    (reaches : (Presented.gslt plan bound expected).MultiStep source target) :
    ∃ state, Explore.Explored (S := search plan bound expected) (lawNormal (Normalized.laws plan) source) state ∧
      Presented.ModelEquiv plan bound expected state target :=
  presented_explores_canonical_on checked noEquations noExtrusions (good := fun _ => True) (fun _ _ _ => Iff.rfl)
    (fun _ _ _ => trivial) (fun term firing _ fired => normalize term firing fired) source trivial reaches

/-- **The canonical explorer is complete for the presented GSLT of every plan without
equations, declared collection laws or extrusions whose rules fire at canonical forms.** -/
theorem presented_explores_of_admissible (checked : Predecessors.equationsChecked plan = true)
    (noEquations : ∀ left right, ¬ GeneralOccurrenceSemantics.Equation plan bound expected left right)
    (noLaws : Normalized.laws plan = []) (noExtrusions : Normalized.extrusions plan = [])
    (admissible : RulesAdmissible plan) (source : Pattern) {target : Pattern}
    (reaches : (Presented.gslt plan bound expected).MultiStep source target) :
    ∃ state, Explore.Explored (S := search plan bound expected) (canon source) state ∧
      Presented.ModelEquiv plan bound expected state target := by
  have := presented_explores_canonical checked noEquations noExtrusions
    (firingsNormalize_of_admissible admissible noLaws) source reaches
  rwa [noLaws, lawNormal_nil] at this

end Mettapedia.OSLF.MeTTaIL.Complete.CanonicalCoherence
