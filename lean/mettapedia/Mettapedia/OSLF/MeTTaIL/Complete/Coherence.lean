import Mettapedia.OSLF.MeTTaIL.Complete.Presented
import Mettapedia.OSLF.MeTTaIL.Complete.Explore

/-!
# Completeness of the normalized explorer for the presented GSLT

The normalized explorer searches each state's class modulo the plan's equations and commits
standard forms. The presented GSLT steps modulo equality in the model, which also identifies
presentations related by the declared collection and scope-extrusion laws. The explorer is
complete for it exactly when firings are coherent with those laws: a firing at any model-equal
presentation of a state is matched, up to model equality of its result, by a firing at a
presentation equal to the state modulo the equations alone (`Coherent`).

- `step_of_presented`: under coherence, a presented step from any model-equal presentation is a
  step modulo the equations, up to model equality of its result;
- `presented_explores`: under coherence, every state reachable from the source by finitely many
  presented steps is explored, up to equality in the model.

Coherence follows from two local conditions (`coherent_of_local`): a law move and an
equation step from one presentation close with at most one equation step and law moves
(`LocalCommute`), and a firing survives one law move up to equality of its result
(`FiringInvariant`). The argument is a tiling of the conversion between the two presentations
(`split_equivalence`): every chain of equations and law moves rearranges into equations
followed by law moves. Both local conditions are properties of the plan's rules, equations and
laws: permutation by comparing repeated metavariables up to canonical form
(`CanonicalBags.matchAtWith_same`), flattening by rules that match collections with a rest.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Complete.Coherence

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission
open Relation (EqvGen ReflGen ReflTransGen SymmGen)

/-! ## Rearranging conversions -/

section Tiling

variable {α : Type} (E S : α → α → Prop)

/-- A law move and an equation step from one presentation close with at most one equation step
followed by law moves. -/
def LocalCommute : Prop :=
  ∀ a b c, SymmGen S a b → SymmGen E a c → ∃ d, ReflGen (SymmGen E) b d ∧ EqvGen S d c

variable {E S}

private theorem eqvGen_of_chain {R : α → α → Prop} {a b : α} (chain : ReflTransGen (SymmGen R) a b) :
    EqvGen R a b := by
  rw [← Relation.EqvGen.reflTransGen_symmGen]; exact chain

private theorem chain_of_eqvGen {R : α → α → Prop} {a b : α} (related : EqvGen R a b) :
    ReflTransGen (SymmGen R) a b := by
  rw [Relation.EqvGen.reflTransGen_symmGen]; exact related

private theorem eqvGen_of_reflGen {R : α → α → Prop} {a b : α} (related : ReflGen (SymmGen R) a b) :
    EqvGen R a b := by
  cases related with
  | refl => exact .refl _
  | single step =>
    rcases step with forward | backward
    · exact .rel _ _ forward
    · exact .symm _ _ (.rel _ _ backward)

/-- One equation step crosses a chain of law moves. -/
private theorem cross_moves (commute : LocalCommute E S) {a b c : α}
    (moves : ReflTransGen (SymmGen S) a b) (equation : SymmGen E a c) :
    ∃ d, ReflGen (SymmGen E) b d ∧ EqvGen S d c := by
  induction moves with
  | refl => exact ⟨c, .single equation, .refl _⟩
  | @tail middle last _ move ih =>
    obtain ⟨reached, step, back⟩ := ih
    cases step with
    | refl => exact ⟨last, .refl, .trans _ _ _ (eqvGen_of_reflGen (.single (Relation.SymmGen.symm move))) back⟩
    | single forward =>
      obtain ⟨d, next, toReached⟩ := commute middle last reached move forward
      exact ⟨d, next, .trans _ _ _ toReached back⟩

/-- A chain of equation steps crosses law moves. -/
private theorem cross_equations (commute : LocalCommute E S) {a b c : α}
    (moves : EqvGen S a b) (equations : ReflTransGen (SymmGen E) a c) :
    ∃ d, EqvGen E b d ∧ EqvGen S d c := by
  induction equations with
  | refl => exact ⟨b, .refl _, .symm _ _ moves⟩
  | @tail middle last _ equation ih =>
    obtain ⟨reached, toReached, back⟩ := ih
    obtain ⟨d, step, toD⟩ := cross_moves commute (chain_of_eqvGen (.symm _ _ back)) equation
    exact ⟨d, .trans _ _ _ toReached (eqvGen_of_reflGen step), toD⟩

/-- **Every conversion by equations and law moves rearranges into equations followed by law
moves**, when law moves commute locally with equation steps. -/
theorem split_equivalence (commute : LocalCommute E S) {x y : α}
    (related : EqvGen (fun a b => E a b ∨ S a b) x y) : ∃ z, EqvGen E x z ∧ EqvGen S z y := by
  induction related with
  | rel a b step =>
    rcases step with equation | move
    · exact ⟨b, .rel _ _ equation, .refl _⟩
    · exact ⟨a, .refl _, .rel _ _ move⟩
  | refl a => exact ⟨a, .refl _, .refl _⟩
  | symm a b _ ih =>
    obtain ⟨z, equations, moves⟩ := ih
    exact cross_equations commute moves (chain_of_eqvGen (.symm _ _ equations))
  | trans a b c _ _ first second =>
    obtain ⟨u, toU, fromU⟩ := first
    obtain ⟨v, toV, fromV⟩ := second
    obtain ⟨w, uToW, wToV⟩ := cross_equations commute (.symm _ _ fromU) (chain_of_eqvGen toV)
    exact ⟨w, .trans _ _ _ toU uToW, .trans _ _ _ wToV fromV⟩

end Tiling

/-! ## Normalized classes

When the law moves have a canonical form, a machine can keep every presentation it visits in
canonical form: an equation step, in either direction, followed by the canonical form of its
result (normalized rewriting). Coherence then needs only two one-sided conditions: equation
steps lift to canonical forms (`EquationsLift`), and a firing at any presentation has a
counterpart at its canonical form (`FiringsNormalize`). -/

section Normal

variable {α ρ : Type} (E S : α → α → Prop) (nf : α → α) (fire : α → ρ → Prop) (result : ρ → α)

/-- A canonical form for the law moves: equal to its source, and equal across one move. -/
structure Normalizer : Prop where
  sound : ∀ term, EqvGen S term (nf term)
  canonical : ∀ left right, S left right → nf left = nf right

/-- An equation step in either direction, then the canonical form. -/
def NormalStep (left right : α) : Prop := ∃ middle, SymmGen E left middle ∧ right = nf middle

/-- Presentations reached from a canonical one by normalized equation steps. -/
abbrev NormalClass (source : α) : α → Prop := ReflTransGen (NormalStep E nf) source

/-- Every equation step has a counterpart at the canonical form of its source, ending at the
same canonical form. -/
def EquationsLift : Prop :=
  ∀ left right, SymmGen E left right → ∃ reached, ReflGen (SymmGen E) (nf left) reached ∧ nf reached = nf right

/-- Every firing has a counterpart at the canonical form of its presentation, with an equal
result. -/
def FiringsNormalize : Prop :=
  ∀ term (firing : ρ), fire term firing →
    ∃ firing', fire (nf term) firing' ∧ EqvGen (fun a b => E a b ∨ S a b) (result firing) (result firing')

variable {E S nf fire result}

theorem Normalizer.eqvGen_eq (normalizer : Normalizer S nf) {left right : α} (related : EqvGen S left right) :
    nf left = nf right := by
  induction related with
  | rel _ _ move => exact normalizer.canonical _ _ move
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

theorem Normalizer.idempotent (normalizer : Normalizer S nf) (term : α) : nf (nf term) = nf term :=
  (normalizer.eqvGen_eq (normalizer.sound term)).symm

/-- Normalized steps stay in the model's equality. -/
theorem NormalStep.equiv (normalizer : Normalizer S nf) {left right : α} (step : NormalStep E nf left right) :
    EqvGen (fun a b => E a b ∨ S a b) left right := by
  obtain ⟨middle, equation, rfl⟩ := step
  have toMiddle : EqvGen (fun a b => E a b ∨ S a b) left middle := by
    rcases equation with forward | backward
    · exact .rel _ _ (.inl forward)
    · exact .symm _ _ (.rel _ _ (.inl backward))
  exact .trans _ _ _ toMiddle (Relation.EqvGen.mono (fun _ _ move => .inr move) _ _ (normalizer.sound middle))

theorem NormalClass.equiv (normalizer : Normalizer S nf) {source target : α}
    (reached : NormalClass E nf source target) : EqvGen (fun a b => E a b ∨ S a b) source target := by
  induction reached with
  | refl => exact .refl _
  | tail _ step ih => exact .trans _ _ _ ih (step.equiv normalizer)

/-- **Every presentation equal to a canonical one has its canonical form in the normalized
class**, when equation steps lift to canonical forms. -/
theorem normalClass_of_equiv (normalizer : Normalizer S nf) (lift : EquationsLift E nf) {source target : α}
    (normal : nf source = source) (related : EqvGen (fun a b => E a b ∨ S a b) source target) :
    NormalClass E nf source (nf target) := by
  have chain := chain_of_eqvGen related
  clear related
  induction chain with
  | refl => rw [normal]
  | @tail middle last _ step ih =>
    have fromSymm : SymmGen E middle last ∨ SymmGen S middle last := by
      rcases step with (forward | forward) | (backward | backward)
      · exact .inl (.inl forward)
      · exact .inr (.inl forward)
      · exact .inl (.inr backward)
      · exact .inr (.inr backward)
    rcases fromSymm with equation | move
    · obtain ⟨reached, lifted, same⟩ := lift middle last equation
      cases lifted with
      | refl => rw [← same, normalizer.idempotent]; exact ih
      | single forward => exact .tail ih ⟨reached, forward, same.symm⟩
    · have same : nf middle = nf last := by
        rcases move with forward | backward
        · exact normalizer.canonical _ _ forward
        · exact (normalizer.canonical _ _ backward).symm
      rw [← same]; exact ih

/-- **Normalized coherence**: a firing at any presentation equal to a canonical one has a
counterpart in the normalized class, with an equal result. -/
theorem fire_in_normalClass (normalizer : Normalizer S nf) (lift : EquationsLift E nf)
    (normalize : FiringsNormalize E S nf fire result) {source representative : α} {firing : ρ}
    (normal : nf source = source) (related : EqvGen (fun a b => E a b ∨ S a b) source representative)
    (fired : fire representative firing) :
    ∃ reached firing', NormalClass E nf source reached ∧ fire reached firing' ∧
      EqvGen (fun a b => E a b ∨ S a b) (result firing) (result firing') := by
  obtain ⟨firing', fired', same⟩ := normalize representative firing fired
  exact ⟨nf representative, firing', normalClass_of_equiv normalizer lift normal related, fired', same⟩

variable (E S nf fire result) in
/-- Firings normalize at every presentation satisfying an invariant. -/
def FiringsNormalizeOn (good : α → Prop) : Prop :=
  ∀ term (firing : ρ), good term → fire term firing →
    ∃ firing', fire (nf term) firing' ∧ EqvGen (fun a b => E a b ∨ S a b) (result firing) (result firing')

/-- An invariant holds along every conversion when every step keeps it. -/
theorem good_of_equiv {good : α → Prop}
    (stable : ∀ a b, (E a b ∨ S a b) → (good a ↔ good b)) {source target : α}
    (related : EqvGen (fun a b => E a b ∨ S a b) source target) (holds : good source) : good target := by
  have iff : good source ↔ good target := by
    clear holds
    induction related with
    | rel a b step => exact stable a b step
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ first second => exact first.trans second
  exact iff.mp holds

/-- **Normalized coherence on an invariant** kept by every step. -/
theorem fire_in_normalClass_on (normalizer : Normalizer S nf) (lift : EquationsLift E nf) {good : α → Prop}
    (stable : ∀ a b, (E a b ∨ S a b) → (good a ↔ good b))
    (normalize : FiringsNormalizeOn E S nf fire result good) {source representative : α} {firing : ρ}
    (normal : nf source = source) (holds : good source)
    (related : EqvGen (fun a b => E a b ∨ S a b) source representative) (fired : fire representative firing) :
    ∃ reached firing', NormalClass E nf source reached ∧ fire reached firing' ∧
      EqvGen (fun a b => E a b ∨ S a b) (result firing) (result firing') := by
  obtain ⟨firing', fired', same⟩ := normalize representative firing (good_of_equiv stable related holds) fired
  exact ⟨nf representative, firing', normalClass_of_equiv normalizer lift normal related, fired', same⟩

end Normal

variable (plan : Plan) (bound : List TypeExpr) (expected : TypeExpr)

/-- **Firing coherence** with the declared laws. -/
def Coherent : Prop :=
  ∀ (state representative : Pattern) (receipt : GeneralRuleJobs.Receipt),
    Presented.ModelEquiv plan bound expected state representative →
    GeneralOccurrenceSemantics.Primitive plan bound expected representative receipt →
    ∃ (representative' : Pattern) (receipt' : GeneralRuleJobs.Receipt),
      Relation.EqvGen (GeneralOccurrenceSemantics.Equation plan bound expected) state representative' ∧
      GeneralOccurrenceSemantics.Primitive plan bound expected representative' receipt' ∧
      Presented.ModelEquiv plan bound expected receipt.target receipt'.target

/-- **Firings survive a law move**, up to equality of their results in the model. -/
def FiringInvariant : Prop :=
  ∀ (left right : Pattern) (receipt : GeneralRuleJobs.Receipt),
    SymmGen (CanonicalBags.StandardStep (Normalized.laws plan) (Normalized.extrusions plan)) left right →
    GeneralOccurrenceSemantics.Primitive plan bound expected left receipt →
    ∃ receipt' : GeneralRuleJobs.Receipt,
      GeneralOccurrenceSemantics.Primitive plan bound expected right receipt' ∧
      Presented.ModelEquiv plan bound expected receipt.target receipt'.target

variable {plan bound expected}

/-- **Coherence from the local conditions.** -/
theorem coherent_of_local
    (commute : LocalCommute (GeneralOccurrenceSemantics.Equation plan bound expected)
      (CanonicalBags.StandardStep (Normalized.laws plan) (Normalized.extrusions plan)))
    (invariant : FiringInvariant plan bound expected) : Coherent plan bound expected := by
  intro state representative receipt equal firing
  obtain ⟨middle, equations, moves⟩ := split_equivalence commute equal
  suffices along : ∀ left right, ReflTransGen (SymmGen
      (CanonicalBags.StandardStep (Normalized.laws plan) (Normalized.extrusions plan))) left right →
      ∀ receipt : GeneralRuleJobs.Receipt, GeneralOccurrenceSemantics.Primitive plan bound expected left receipt →
      ∃ receipt' : GeneralRuleJobs.Receipt, GeneralOccurrenceSemantics.Primitive plan bound expected right receipt' ∧
        Presented.ModelEquiv plan bound expected receipt.target receipt'.target by
    obtain ⟨receipt', firing', sameTarget⟩ :=
      along representative middle (chain_of_eqvGen (.symm _ _ moves)) receipt firing
    exact ⟨middle, receipt', equations, firing', sameTarget⟩
  intro left right moves
  induction moves with
  | refl => intro receipt firing; exact ⟨receipt, firing, .refl _⟩
  | @tail middle last _ move ih =>
    intro receipt firing
    obtain ⟨reached, firingMiddle, first⟩ := ih receipt firing
    obtain ⟨final, firingLast, second⟩ := invariant middle last reached move firingMiddle
    exact ⟨final, firingLast, .trans _ _ _ first second⟩

/-- **Under coherence, a presented step is a step modulo the equations**, from any model-equal
presentation of its source, up to model equality of its result. -/
theorem step_of_presented (coherent : Coherent plan bound expected) {source target state : Pattern}
    (stepped : (Presented.gslt plan bound expected).Step source target)
    (equal : Presented.ModelEquiv plan bound expected state source) :
    ∃ reached, (GeneralOccurrenceSemantics.gslt plan bound expected).Step state reached ∧
      Presented.ModelEquiv plan bound expected reached target := by
  obtain ⟨representative, receipt, before, firing, after⟩ := stepped
  obtain ⟨representative', receipt', equations, firing', sameTarget⟩ :=
    coherent state representative receipt (.trans _ _ _ equal before) firing
  exact ⟨receipt'.target, ⟨representative', receipt', equations, firing', .refl _⟩,
    .trans _ _ _ (.symm _ _ sameTarget) after⟩

/-- **Every state reachable by finitely many presented steps is explored**, up to equality in the
model, for every plan with balanced equations, extrusions over unordered flattening kinds, and
coherent firings. -/
theorem presented_explores (coherent : Coherent plan bound expected)
    (checked : Predecessors.equationsChecked plan = true)
    (flatten : CanonicalBags.ExtrusionsFlatten (Normalized.laws plan) (Normalized.extrusions plan))
    (source : Pattern) {target : Pattern}
    (reaches : (Presented.gslt plan bound expected).MultiStep source target) :
    ∃ state, Explore.Explored (S := Normalized.search plan bound expected) (Normalized.standard plan source) state ∧
      Presented.ModelEquiv plan bound expected state target := by
  suffices along : ∀ first last, (Presented.gslt plan bound expected).MultiStep first last → ∀ state,
      Explore.Explored (S := Normalized.search plan bound expected) (Normalized.standard plan source) state →
      Presented.ModelEquiv plan bound expected state first →
      ∃ reached, Explore.Explored (S := Normalized.search plan bound expected) (Normalized.standard plan source) reached ∧
        Presented.ModelEquiv plan bound expected reached last from
    along source target reaches (Normalized.standard plan source) (Explore.explored_source _)
      (.symm _ _ (Presented.standard_equiv plan bound expected flatten source))
  intro first last reaches
  induction reaches with
  | refl term => intro state explored equal; exact ⟨state, explored, equal⟩
  | @step first middle last stepped _ ih =>
    intro state explored equal
    obtain ⟨reached, step, reachedEqual⟩ := step_of_presented coherent stepped equal
    obtain ⟨work, receipt, published, related⟩ :=
      Classes.complete_in_limit plan bound expected state checked step
    have next := Explore.explored_target (Normalized.search_lawful plan bound expected) explored
      (work := work) (receipt := receipt) published
    refine ih (Normalized.standard plan receipt.target) next ?_
    have toStandard := Presented.standard_equiv plan bound expected flatten receipt.target
    have fromEquations : Presented.ModelEquiv plan bound expected receipt.target reached :=
      Relation.EqvGen.mono (fun _ _ equation => .inl equation) _ _ related
    exact .trans _ _ _ (.symm _ _ toStandard) (.trans _ _ _ fromEquations reachedEqual)

/-! ## The canonical form of the declared collection laws -/

section Laws

open CanonicalBags CollectionLaws

/-- Without declared extrusions, a standard move is a law move. -/
theorem lawStep_of_standardStep {laws : List Laws} {left right : Pattern}
    (step : StandardStep laws [] left right) : LawStep laws left right := by
  induction step with
  | law move => exact move
  | extrude member => exact absurd member List.not_mem_nil
  | apply _ ih => exact .apply ih
  | lambda _ ih => exact .lambda ih
  | multiLambda _ ih => exact .multiLambda ih
  | substBody _ ih => exact .substBody ih
  | substReplacement _ ih => exact .substReplacement ih
  | element _ ih => exact .element ih

/-- **Permutation, flattening and unit removal have a canonical form**: `lawNormal`. -/
theorem lawNormalizer (laws : List Laws) : Normalizer (StandardStep laws []) (lawNormal laws) where
  sound term := Relation.EqvGen.mono (fun _ _ move => .law move) _ _ (to_lawNormal laws term)
  canonical _ _ move := LawStep.lawNormal_eq laws (lawStep_of_standardStep move)

/-- **Normalized coherence for a plan without declared extrusions**: a presented firing at any
presentation of a canonical state has a counterpart in the state's normalized class, with a
result equal in the model, when equation steps lift to canonical forms and firings normalize. -/
theorem presented_fire_in_normalClass (noExtrusions : Normalized.extrusions plan = [])
    (lift : EquationsLift (GeneralOccurrenceSemantics.Equation plan bound expected) (lawNormal (Normalized.laws plan)))
    (normalize : FiringsNormalize (GeneralOccurrenceSemantics.Equation plan bound expected)
      (StandardStep (Normalized.laws plan) (Normalized.extrusions plan)) (lawNormal (Normalized.laws plan))
      (GeneralOccurrenceSemantics.Primitive plan bound expected) GeneralRuleJobs.Receipt.target)
    {state representative : Pattern} {receipt : GeneralRuleJobs.Receipt}
    (normal : lawNormal (Normalized.laws plan) state = state)
    (equal : Presented.ModelEquiv plan bound expected state representative)
    (fired : GeneralOccurrenceSemantics.Primitive plan bound expected representative receipt) :
    ∃ reached receipt', NormalClass (GeneralOccurrenceSemantics.Equation plan bound expected)
        (lawNormal (Normalized.laws plan)) state reached ∧
      GeneralOccurrenceSemantics.Primitive plan bound expected reached receipt' ∧
      Presented.ModelEquiv plan bound expected receipt.target receipt'.target := by
  have normalizer : Normalizer (StandardStep (Normalized.laws plan) (Normalized.extrusions plan))
      (lawNormal (Normalized.laws plan)) := by
    rw [noExtrusions]; exact lawNormalizer _
  exact fire_in_normalClass normalizer lift normalize normal equal fired

end Laws

end Mettapedia.OSLF.MeTTaIL.Complete.Coherence
