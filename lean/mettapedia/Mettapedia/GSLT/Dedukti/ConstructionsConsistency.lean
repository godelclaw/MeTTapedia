import Mettapedia.GSLT.Dedukti.TypePreservation
import Mettapedia.GSLT.Dedukti.Confluence

/-!
# The calculus of constructions is consistent

No closed term of the calculus of constructions has the type `Π p : ∗. p`
(`constructions_consistent`), and so no system of the lambda cube proves it
(`consistent_of_subsumed`).  The proof is a proof-irrelevant model in the
metatheory's own impredicative propositions, in the style of the
set-theoretic model of B. Werner (*Sets in types, types in sets*) and of
A. Miquel and B. Werner (*The not so simple proof-irrelevant model of CC*):

* a kind denotes a set built from `Prop` by function spaces (`Skeleton`);
* a type denotes a proposition, and a type operator a function into
  propositions;
* a proof denotes nothing.

## The model is defined on raw terms

`eval env t` interprets every raw λΠ term.  Which of the three levels a
binder belongs to is read from the syntax: a domain denotes a kind exactly
when it has the shape `Π x₁ : A₁. … Π xₙ : Aₙ. ∗` (`kindSkeleton?`).  That
reading is right for typed terms: a typed term of that shape has type `□`
(`conv_kind_of_kindSkeleton`), a term of type `□` has that shape
(`kindSkeleton_isSome_of_kind`), and a type has not
(`kindSkeleton_eq_none_of_type`).

## Where the conversion rule is handled

The conversion rule compares types by untyped beta conversion, whose
intermediate terms need not be typed.  The model is invariant under steps of
typed terms only (`eval_step`), so conversion is reduced to steps through
confluence (`confluent_empty`) and type preservation (`typePreservation`):
two convertible typed terms have a common reduct, reached by steps through
typed terms.  The root case of `eval_step` needs that the value of a typed
term has the level its type gives (`shape_eval`): an argument of a kind has a
value of that kind's skeleton, a proof has none, and the body of a type
operator has a level that does not depend on the value of its variable.

## What the model refutes, and what it does not

`Π p : ∗. p` denotes `∀ p : Prop, p`, which is false; every closed inhabited
type denotes a true proposition (`sound`).  The model is proof-irrelevant, so
it says nothing about equality of proofs; and it does not give strong
normalization.

Controls: the polymorphic identity has a type the model makes true
(`polymorphicIdentity_sound`); the value changes under a step of an untyped
redex (`eval_untyped_step_changes`, `untyped_redex_not_typed`), which is why
conversion goes through typed steps.  The hypothesis that separates the
calculus of constructions from an inconsistent system is its axiom `∗ : □`:
with `∗ : ∗` the paradox of `TypeInTypeParadox` inhabits `Π p : ∗. p`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti.ConstructionsModel

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (Ctx ctxLookup lift subst subst0)
open Mettapedia.GSLT.LanguageDef.LFProfile (Profile ProductRule)
open Mettapedia.Logic.Relation (Confluent IsNormal)

/-! ## Skeletons of kinds -/

/-- The simple type underlying a kind: `∗` is a proposition, a product over a
kind is a function space, and a product over a type is dropped, proofs
carrying no information. -/
inductive Skeleton where
  | prop
  | arrow (domain codomain : Skeleton)
  deriving DecidableEq

/-- The set a skeleton denotes. -/
def Skeleton.den : Skeleton → Type
  | .prop => Prop
  | .arrow domain codomain => domain.den → codomain.den

/-- A chosen element of every denotation. -/
def Skeleton.default : (skeleton : Skeleton) → skeleton.den
  | .prop => True
  | .arrow _ codomain => fun _ => codomain.default

/-- The skeleton of a term of the shape `Π x₁ : A₁. … Π xₙ : Aₙ. ∗`, and
nothing for any other term. -/
def kindSkeleton? : Term → Option Skeleton
  | .srt .type => some .prop
  | .pi domain body =>
      (kindSkeleton? body).map fun codomain =>
        match kindSkeleton? domain with
        | some domainSkeleton => .arrow domainSkeleton codomain
        | none => codomain
  | _ => none

theorem kindSkeleton?_lift (term : Term) :
    ∀ amount cutoff : Nat, kindSkeleton? (lift amount cutoff term) = kindSkeleton? term := by
  induction term with
  | srt sort => intro amount cutoff; rfl
  | con name => intro amount cutoff; rfl
  | var index => intro amount cutoff; rfl
  | pi domain body ihDomain ihBody =>
      intro amount cutoff
      simp only [LFTyping.lift, kindSkeleton?, ihDomain, ihBody]
  | lam domain body _ _ => intro amount cutoff; rfl
  | app function argument _ _ => intro amount cutoff; rfl

/-- Substituting a term that is not of kind shape keeps the shape. -/
theorem kindSkeleton?_subst {replacement : Term} (notKind : kindSkeleton? replacement = none)
    (term : Term) :
    ∀ target : Nat, kindSkeleton? (subst target (lift target 0 replacement) term) =
      kindSkeleton? term := by
  induction term with
  | srt sort => intro target; rfl
  | con name => intro target; rfl
  | var index =>
      intro target
      simp only [LFTyping.subst]
      split
      · rw [kindSkeleton?_lift, notKind]; rfl
      · split <;> rfl
  | pi domain body ihDomain ihBody =>
      intro target
      have key : lift 1 0 (lift target 0 replacement) = lift (target + 1) 0 replacement := by
        rw [lift_lift_same, Nat.add_comm]
      simp only [LFTyping.subst, kindSkeleton?, key, ihDomain, ihBody]
  | lam domain body _ _ => intro target; rfl
  | app function argument _ _ => intro target; rfl

/-! ## Values -/

/-- The value of a term: an element of a skeleton's denotation for a type or
a type operator, and nothing for a proof. -/
abbrev Value : Type := Option (Σ skeleton : Skeleton, skeleton.den)

/-- The level a value has. -/
def shape (value : Value) : Option Skeleton := value.map Sigma.fst

/-- Read a value as a proposition. -/
def asProp : Value → Prop
  | some ⟨.prop, proposition⟩ => proposition
  | _ => True

@[simp] theorem asProp_prop (proposition : Prop) : asProp (some ⟨.prop, proposition⟩) = proposition := rfl

/-- Read a value at a skeleton. -/
def asDen (skeleton : Skeleton) : Value → skeleton.den
  | some ⟨found, value⟩ => if same : found = skeleton then same ▸ value else skeleton.default
  | none => skeleton.default

theorem asDen_of_shape {skeleton : Skeleton} {value : Value} (shaped : shape value = some skeleton) :
    some ⟨skeleton, asDen skeleton value⟩ = value := by
  rcases value with _ | ⟨found, inner⟩
  · cases shaped
  · simp only [shape, Option.map_some, Option.some.injEq] at shaped
    subst shaped
    simp [asDen]

theorem eq_none_of_shape {value : Value} (shaped : shape value = none) : value = none := by
  rcases value with _ | ⟨found, inner⟩
  · rfl
  · cases shaped

/-- **The interpretation of raw terms.**  A binder whose domain has kind shape
binds a value; any other binder binds a proof, which has no value. -/
def eval (env : List Value) : Term → Value
  | .srt _ => none
  | .con _ => none
  | .var index => (env[index]?).join
  | .pi domain body =>
      match kindSkeleton? domain with
      | some skeleton =>
          some ⟨.prop, ∀ value : skeleton.den, asProp (eval (some ⟨skeleton, value⟩ :: env) body)⟩
      | none => some ⟨.prop, asProp (eval env domain) → asProp (eval (none :: env) body)⟩
  | .lam domain body =>
      match kindSkeleton? domain with
      | some skeleton =>
          match shape (eval (some ⟨skeleton, skeleton.default⟩ :: env) body) with
          | some codomain =>
              some ⟨.arrow skeleton codomain,
                fun value => asDen codomain (eval (some ⟨skeleton, value⟩ :: env) body)⟩
          | none => none
      | none => eval (none :: env) body
  | .app function argument =>
      match eval env argument with
      | none => eval env function
      | some ⟨skeleton, value⟩ =>
          match eval env function with
          | some ⟨.arrow domain codomain, map⟩ =>
              if same : skeleton = domain then some ⟨codomain, map (same ▸ value)⟩ else none
          | _ => none

/-! ## Weakening and substitution in the model -/

theorem getElem?_join_insert (front middle back : List Value) (index : Nat) :
    ((front ++ middle ++ back)[if index < front.length then index else index + middle.length]?).join =
      ((front ++ back)[index]?).join := by
  by_cases below : index < front.length
  · rw [if_pos below, List.append_assoc, List.getElem?_append_left below,
      List.getElem?_append_left below]
  · obtain ⟨offset, rfl⟩ : ∃ offset, index = front.length + offset :=
      ⟨index - front.length, by omega⟩
    rw [if_neg below, List.append_assoc, show front.length + offset + middle.length =
      front.length + (middle.length + offset) by omega]
    simp [List.getElem?_append_right]

/-- **Weakening**: variables inserted in the middle of an environment are
not seen by a lifted term. -/
theorem eval_lift (term : Term) :
    ∀ front middle back : List Value,
      eval (front ++ middle ++ back) (lift middle.length front.length term) =
        eval (front ++ back) term := by
  induction term with
  | srt sort => intro front middle back; rfl
  | con name => intro front middle back; rfl
  | var index =>
      intro front middle back
      exact getElem?_join_insert front middle back index
  | pi domain body ihDomain ihBody =>
      intro front middle back
      have under : ∀ value : Value,
          eval (value :: (front ++ middle ++ back)) (lift middle.length (front.length + 1) body) =
            eval (value :: (front ++ back)) body := fun value => ihBody (value :: front) middle back
      simp only [eval, LFTyping.lift, kindSkeleton?_lift, under, ihDomain]
  | lam domain body ihDomain ihBody =>
      intro front middle back
      have under : ∀ value : Value,
          eval (value :: (front ++ middle ++ back)) (lift middle.length (front.length + 1) body) =
            eval (value :: (front ++ back)) body := fun value => ihBody (value :: front) middle back
      simp only [eval, LFTyping.lift, kindSkeleton?_lift, under]
  | app function argument ihFunction ihArgument =>
      intro front middle back
      simp only [eval, LFTyping.lift, ihFunction, ihArgument]

theorem eval_lift_front (term : Term) (front back : List Value) :
    eval (front ++ back) (lift front.length 0 term) = eval back term := by
  simpa using eval_lift term [] front back

theorem eval_lift_one (term : Term) (value : Value) (env : List Value) :
    eval (value :: env) (lift 1 0 term) = eval env term := by
  simpa using eval_lift_front term [value] env

/-- **Substitution**: substituting a term that is not of kind shape is
evaluating the body with the term's value. -/
theorem eval_subst {replacement : Term} (notKind : kindSkeleton? replacement = none)
    (back : List Value) (term : Term) :
    ∀ front : List Value,
      eval (front ++ back) (subst front.length (lift front.length 0 replacement) term) =
        eval (front ++ eval back replacement :: back) term := by
  induction term with
  | srt sort => intro front; rfl
  | con name => intro front; rfl
  | var index =>
      intro front
      simp only [eval, LFTyping.subst]
      by_cases same : index = front.length
      · subst same
        simp [eval_lift_front]
      · by_cases above : front.length < index
        · simp only [same, above, if_false, if_true, eval]
          rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
          obtain ⟨offset, rfl⟩ : ∃ offset, index = front.length + offset + 1 :=
            ⟨index - front.length - 1, by omega⟩
          simp [show front.length + offset + 1 - front.length = offset + 1 by omega]
        · have below : index < front.length := by omega
          simp only [same, above, if_false, eval]
          rw [List.getElem?_append_left below, List.getElem?_append_left below]
  | pi domain body ihDomain ihBody =>
      intro front
      have key : lift 1 0 (lift front.length 0 replacement) = lift (front.length + 1) 0 replacement := by
        rw [lift_lift_same, Nat.add_comm]
      have under : ∀ value : Value,
          eval (value :: (front ++ back)) (subst (front.length + 1) (lift (front.length + 1) 0 replacement) body) =
            eval (value :: (front ++ eval back replacement :: back)) body :=
        fun value => ihBody (value :: front)
      simp only [eval, LFTyping.subst, key, kindSkeleton?_subst notKind, under, ihDomain]
  | lam domain body ihDomain ihBody =>
      intro front
      have key : lift 1 0 (lift front.length 0 replacement) = lift (front.length + 1) 0 replacement := by
        rw [lift_lift_same, Nat.add_comm]
      have under : ∀ value : Value,
          eval (value :: (front ++ back)) (subst (front.length + 1) (lift (front.length + 1) 0 replacement) body) =
            eval (value :: (front ++ eval back replacement :: back)) body :=
        fun value => ihBody (value :: front)
      simp only [eval, LFTyping.subst, key, kindSkeleton?_subst notKind, under]
  | app function argument ihFunction ihArgument =>
      intro front
      simp only [eval, LFTyping.subst, ihFunction, ihArgument]

theorem eval_subst0 {argument : Term} (notKind : kindSkeleton? argument = none) (env : List Value)
    (body : Term) : eval env (subst0 argument body) = eval (eval env argument :: env) body := by
  simpa [LFTyping.subst0, lift_zero] using eval_subst notKind env body []

/-! ## A beta contraction in the model -/

/-- A contraction whose abstraction binds a value, with an argument of that
value's skeleton and a body whose level does not depend on the value. -/
theorem eval_beta_kind {env : List Value} {domain body argument : Term} {skeleton : Skeleton}
    {argumentValue : skeleton.den}
    (domainKind : kindSkeleton? domain = some skeleton) (notKind : kindSkeleton? argument = none)
    (argumentEval : eval env argument = some ⟨skeleton, argumentValue⟩)
    (bodyShape : ∀ value value' : skeleton.den,
      shape (eval (some ⟨skeleton, value⟩ :: env) body) =
        shape (eval (some ⟨skeleton, value'⟩ :: env) body)) :
    eval env (.app (.lam domain body) argument) = eval env (subst0 argument body) := by
  rw [eval_subst0 notKind, argumentEval]
  simp only [eval, domainKind, argumentEval]
  cases shaped : shape (eval (some ⟨skeleton, skeleton.default⟩ :: env) body) with
  | none =>
      simp only
      have := bodyShape argumentValue skeleton.default
      rw [shaped] at this
      exact (eq_none_of_shape this).symm
  | some codomain =>
      simp only [dite_true]
      have := bodyShape argumentValue skeleton.default
      rw [shaped] at this
      exact asDen_of_shape this

/-- A contraction whose abstraction binds a proof. -/
theorem eval_beta_proof {env : List Value} {domain body argument : Term}
    (domainType : kindSkeleton? domain = none) (notKind : kindSkeleton? argument = none)
    (argumentEval : eval env argument = none) :
    eval env (.app (.lam domain body) argument) = eval env (subst0 argument body) := by
  rw [eval_subst0 notKind, argumentEval]
  simp only [eval, domainType, argumentEval]


/-! ## The calculus of constructions -/

/-- Typing in the calculus of constructions, with beta conversion. -/
abbrev Typed : Ctx → Term → Term → Prop := HasType constructions Theory.empty

/-- A well-formed context of the calculus of constructions. -/
abbrev Formed : Ctx → Prop := WellFormedCtx constructions Theory.empty

theorem closedTypes : Theory.empty.ClosedTypes := fun _ _ declared => by cases declared

theorem formedSignature : Theory.empty.FormedSignature constructions :=
  fun _ _ declared => by cases declared

theorem typedBodies : Theory.empty.TypedBodies constructions := fun _ _ _ defined => by cases defined

theorem rulesPreserveTypes : Theory.empty.RulesPreserveTypes constructions :=
  fun _ _ _ _ member => member.elim

theorem functional : Functional constructions := by
  unfold Functional
  decide

/-- Every product rule of the calculus of constructions has the sort of its
codomain. -/
theorem result_eq_codomain : ∀ rule ∈ constructions.products, rule.result = rule.codomain := by
  decide

theorem sortAxiom_eq {source target : Srt} (axiomHolds : constructions.sortAxiom source = some target) :
    source = .type ∧ target = .kind := by
  cases source <;> cases target <;> simp_all [constructions, LFProfile.typeAxiom]

/-- Reduction keeps the type, in a well-formed context. -/
theorem typed_reduces {context : Ctx} {source target type : Term} (formed : Formed context)
    (typed : Typed context source type) (reduces : Reduces Theory.empty source target) :
    Typed context target type :=
  typePreservation_reduces confluent_empty Theory.empty_headed Theory.empty_closedBodies closedTypes
    formedSignature typedBodies rulesPreserveTypes formed typed reduces

theorem typed_step {context : Ctx} {source target type : Term} (formed : Formed context)
    (typed : Typed context source type) (step : Step Theory.empty source target) :
    Typed context target type :=
  typed_reduces formed typed (.single step)

theorem typed_correct {context : Ctx} {term type : Term} (formed : Formed context)
    (typed : Typed context term type) :
    type = .srt .kind ∨ ∃ sort, Typed context type (.srt sort) := by
  rcases HasType.correct Theory.empty_closedBodies closedTypes formedSignature formed typed with
    ⟨sort, rfl, noAxiom⟩ | formedType
  · cases sort
    · simp [constructions, LFProfile.typeAxiom] at noAxiom
    · exact Or.inl rfl
  · exact Or.inr formedType

theorem conv_srt_injective {first second : Srt}
    (convertible : Conv Theory.empty (.srt first) (.srt second)) : first = second :=
  Conv.srt_injective confluent_empty Theory.empty_headed convertible

/-- A sort is typed only as `∗ : □`. -/
theorem typed_srt_inv {context : Ctx} {sort : Srt} {type : Term} (typed : Typed context (.srt sort) type) :
    sort = .type ∧ Conv Theory.empty (.srt .kind) type := by
  obtain ⟨target, axiomHolds, convertible⟩ := typed.sort_inv
  obtain ⟨rfl, rfl⟩ := sortAxiom_eq axiomHolds
  exact ⟨rfl, convertible⟩

theorem not_typed_kind {context : Ctx} {type : Term} : ¬ Typed context (.srt .kind) type := by
  intro typed
  cases (typed_srt_inv typed).1

theorem not_typed_con {context : Ctx} {name : String} {type : Term} :
    ¬ Typed context (.con name) type := by
  intro typed
  obtain ⟨_, declared, _⟩ := typed.con_inv
  cases declared

/-- `∗` is not a type of sort `∗`. -/
theorem not_typed_type_type {context : Ctx} : ¬ Typed context (.srt .type) (.srt .type) := by
  intro typed
  cases conv_srt_injective (typed_srt_inv typed).2

/-- **No typed term is convertible to `□`.** -/
theorem not_conv_kind {context : Ctx} {term type : Term} (formed : Formed context)
    (typed : Typed context term type) (convertible : Conv Theory.empty term (.srt .kind)) : False := by
  obtain ⟨common, toCommon, kindToCommon⟩ := (conv_iff_joinable confluent_empty).mp convertible
  have same := (srt_normal Theory.empty_headed Srt.kind).reflTransGen_eq kindToCommon
  subst same
  exact not_typed_kind (typed_reduces formed typed toCommon)

/-- A product is not convertible to a sort. -/
theorem not_conv_pi_srt {domain body : Term} {sort : Srt} :
    ¬ Conv Theory.empty (.pi domain body) (.srt sort) := by
  intro convertible
  obtain ⟨common, piToCommon, srtToCommon⟩ := (conv_iff_joinable confluent_empty).mp convertible
  have same := (srt_normal Theory.empty_headed sort).reflTransGen_eq srtToCommon
  subst same
  obtain ⟨_, _, impossible, _, _⟩ := piToCommon.pi_inv Theory.empty_headed
  cases impossible

/-- Two convertible typed types have the same sort. -/
theorem sort_eq_of_conv {context : Ctx} {left right : Term} {leftSort rightSort : Srt}
    (formed : Formed context) (leftTyped : Typed context left (.srt leftSort))
    (rightTyped : Typed context right (.srt rightSort)) (convertible : Conv Theory.empty left right) :
    leftSort = rightSort := by
  obtain ⟨common, leftReduces, rightReduces⟩ := (conv_iff_joinable confluent_empty).mp convertible
  exact conv_srt_injective (HasType.unique functional confluent_empty Theory.empty_headed
    Theory.empty_closedBodies common (typed_reduces formed leftTyped leftReduces)
    (typed_reduces formed rightTyped rightReduces))

/-! ## The level of a term is read from its shape -/

/-- **A typed term of kind shape has type `□`.** -/
theorem conv_kind_of_kindSkeleton (term : Term) :
    ∀ {context : Ctx} {type : Term} {skeleton : Skeleton}, kindSkeleton? term = some skeleton →
      Typed context term type → Conv Theory.empty type (.srt .kind) := by
  induction term with
  | srt sort =>
      intro context type skeleton _ typed
      exact .symm _ _ (typed_srt_inv typed).2
  | pi domain body _ ihBody =>
      intro context type skeleton shaped typed
      obtain ⟨bodySkeleton, bodyShaped, _⟩ := Option.map_eq_some_iff.mp shaped
      obtain ⟨domainSort, codomainSort, resultSort, _, bodyTyped, rule, resultConv⟩ := typed.pi_inv
      have codomainKind := conv_srt_injective (ihBody bodyShaped bodyTyped)
      have resultKind : resultSort = .kind := (result_eq_codomain _ rule).trans codomainKind
      subst resultKind
      exact .symm _ _ resultConv
  | con name => intro context type skeleton shaped; cases shaped
  | var index => intro context type skeleton shaped; cases shaped
  | lam domain body _ _ => intro context type skeleton shaped; cases shaped
  | app function argument _ _ => intro context type skeleton shaped; cases shaped

/-- **A type is not of kind shape.** -/
theorem kindSkeleton_eq_none_of_type {context : Ctx} {term : Term}
    (typed : Typed context term (.srt .type)) : kindSkeleton? term = none := by
  cases shaped : kindSkeleton? term with
  | none => rfl
  | some skeleton => cases conv_srt_injective (conv_kind_of_kindSkeleton term shaped typed)

/-- **A term whose type is a type, or a kind, is not of kind shape.** -/
theorem kindSkeleton_eq_none_of_typed {context : Ctx} {term type : Term} {sort : Srt}
    (formed : Formed context) (typed : Typed context term type)
    (typeTyped : Typed context type (.srt sort)) : kindSkeleton? term = none := by
  cases shaped : kindSkeleton? term with
  | none => rfl
  | some skeleton =>
      exact (not_conv_kind formed typeTyped (conv_kind_of_kindSkeleton term shaped typed)).elim

/-- **A term of type `□` is of kind shape.** -/
theorem kindSkeleton_isSome_of_kind (term : Term) :
    ∀ {context : Ctx}, Formed context → Typed context term (.srt .kind) →
      (kindSkeleton? term).isSome := by
  induction term with
  | srt sort =>
      intro context _ typed
      obtain ⟨rfl, _⟩ := typed_srt_inv typed
      rfl
  | con name => intro context _ typed; exact (not_typed_con typed).elim
  | var index =>
      intro context formed typed
      obtain ⟨declared, found, convertible⟩ := typed.var_inv
      obtain ⟨sort, declaredTyped⟩ :=
        formed.lookup_formed Theory.empty_closedBodies closedTypes index declared found
      exact (not_conv_kind formed declaredTyped convertible).elim
  | pi domain body _ ihBody =>
      intro context formed typed
      obtain ⟨domainSort, codomainSort, resultSort, domainTyped, bodyTyped, rule, resultConv⟩ :=
        typed.pi_inv
      have resultKind := conv_srt_injective resultConv
      subst resultKind
      have codomainKind : codomainSort = .kind := (result_eq_codomain _ rule).symm
      subst codomainKind
      have bodySome := ihBody (formed.cons domainTyped) bodyTyped
      simp only [kindSkeleton?, Option.isSome_map]
      exact bodySome
  | lam domain body _ _ =>
      intro context _ typed
      obtain ⟨_, _, _, _, _, _, _, _, convertible⟩ := typed.lam_inv
      exact (not_conv_pi_srt convertible).elim
  | app function argument _ _ =>
      intro context formed typed
      obtain ⟨domain, bodyType, functionTyped, argumentTyped, convertible⟩ := typed.app_inv
      rcases typed_correct formed functionTyped with same | ⟨_, productTyped⟩
      · cases same
      obtain ⟨_, codomainSort, _, _, bodyTypeTyped, _, _⟩ := productTyped.pi_inv
      have substituted := HasType.subst0 Theory.empty_closedBodies closedTypes bodyTypeTyped argumentTyped
      exact (not_conv_kind formed substituted convertible).elim

/-- The two levels of a type: of sort `□` exactly when of kind shape. -/
theorem kindSkeleton_of_sort {context : Ctx} {term : Term} {sort : Srt} (formed : Formed context)
    (typed : Typed context term (.srt sort)) :
    (sort = .kind ∧ (kindSkeleton? term).isSome) ∨ (sort = .type ∧ kindSkeleton? term = none) := by
  cases sort with
  | type => exact Or.inr ⟨rfl, kindSkeleton_eq_none_of_type typed⟩
  | kind => exact Or.inl ⟨rfl, kindSkeleton_isSome_of_kind term formed typed⟩

/-! ## The skeleton of a kind is invariant -/

theorem kindSkeleton_step (term : Term) :
    ∀ {context : Ctx} {target : Term}, Formed context → Typed context term (.srt .kind) →
      Step Theory.empty term target → kindSkeleton? target = kindSkeleton? term := by
  induction term with
  | srt sort =>
      intro context target _ _ step
      exact (RootStep.not_srt Theory.empty_headed step.srt_inv).elim
  | pi domain body ihDomain ihBody =>
      intro context target formed typed step
      obtain ⟨domainSort, codomainSort, resultSort, domainTyped, bodyTyped, rule, resultConv⟩ :=
        typed.pi_inv
      have resultKind := conv_srt_injective resultConv
      subst resultKind
      have codomainKind : codomainSort = .kind := (result_eq_codomain _ rule).symm
      subst codomainKind
      rcases step.pi_inv with root | ⟨domain', inner, rfl⟩ | ⟨body', inner, rfl⟩
      · exact (RootStep.not_pi Theory.empty_headed root).elim
      · have same : kindSkeleton? domain' = kindSkeleton? domain := by
          cases domainSort with
          | kind => exact ihDomain formed domainTyped inner
          | type =>
              rw [kindSkeleton_eq_none_of_type domainTyped,
                kindSkeleton_eq_none_of_type (typed_step formed domainTyped inner)]
        simp only [kindSkeleton?, same]
      · simp only [kindSkeleton?, ihBody (formed.cons domainTyped) bodyTyped inner]
  | con name => intro context target _ typed; exact (not_typed_con typed).elim
  | var index =>
      intro context target formed typed
      have := kindSkeleton_isSome_of_kind (.var index) formed typed
      simp [kindSkeleton?] at this
  | lam domain body _ _ =>
      intro context target formed typed
      have := kindSkeleton_isSome_of_kind (.lam domain body) formed typed
      simp [kindSkeleton?] at this
  | app function argument _ _ =>
      intro context target formed typed
      have := kindSkeleton_isSome_of_kind (.app function argument) formed typed
      simp [kindSkeleton?] at this

theorem kindSkeleton_reduces {context : Ctx} {source target : Term} (formed : Formed context)
    (typed : Typed context source (.srt .kind)) (reduces : Reduces Theory.empty source target) :
    kindSkeleton? target = kindSkeleton? source := by
  induction reduces with
  | refl => rfl
  | tail earlier step ih =>
      rw [kindSkeleton_step _ formed (typed_reduces formed typed earlier) step, ih]

/-- **Convertible typed types have one skeleton.** -/
theorem kindSkeleton_conv {context : Ctx} {left right : Term} {leftSort rightSort : Srt}
    (formed : Formed context) (leftTyped : Typed context left (.srt leftSort))
    (rightTyped : Typed context right (.srt rightSort)) (convertible : Conv Theory.empty left right) :
    kindSkeleton? left = kindSkeleton? right := by
  have same := sort_eq_of_conv formed leftTyped rightTyped convertible
  subst same
  cases leftSort with
  | type => rw [kindSkeleton_eq_none_of_type leftTyped, kindSkeleton_eq_none_of_type rightTyped]
  | kind =>
      obtain ⟨common, leftReduces, rightReduces⟩ := (conv_iff_joinable confluent_empty).mp convertible
      rw [← kindSkeleton_reduces formed leftTyped leftReduces,
        ← kindSkeleton_reduces formed rightTyped rightReduces]

/-! ## Environments -/

/-- An environment whose values have the levels of the context's entries. -/
inductive Matches : Ctx → List Value → Prop where
  | nil : Matches [] []
  | cons {context : Ctx} {env : List Value} {entry : Term} {value : Value} :
      Matches context env → shape value = kindSkeleton? entry → Matches (entry :: context) (value :: env)

theorem Matches.lookup {context : Ctx} {env : List Value} (matching : Matches context env) :
    ∀ {index : Nat} {type : Term}, ctxLookup context index = some type →
      shape (eval env (.var index)) = kindSkeleton? type := by
  induction matching with
  | nil => intro index type found; simp [ctxLookup, LFTyping.ctxLookupAux] at found
  | @cons context env entry value _ shaped ih =>
      intro index type found
      cases index with
      | zero =>
          have same : type = lift 1 0 entry := by
            simpa [ctxLookup, LFTyping.ctxLookupAux] using found.symm
          subst same
          simpa [eval, kindSkeleton?_lift] using shaped
      | succ index =>
          rw [ctxLookup_cons_succ] at found
          obtain ⟨original, originalFound, rfl⟩ := Option.map_eq_some_iff.mp found
          simpa [eval, kindSkeleton?_lift] using ih originalFound

/-- **The value of a typed term has the level its type gives**: the
skeleton of its kind for a type operator, none for a proof. -/
theorem shape_eval {context : Ctx} {term type : Term} (typed : Typed context term type) :
    Formed context → ∀ env, Matches context env → ∀ sort, Typed context type (.srt sort) →
      shape (eval env term) = kindSkeleton? type := by
  induction typed with
  | @sort context source target axiomHolds =>
      intro _ env _ sort typeTyped
      obtain ⟨rfl, convertible⟩ := typed_srt_inv typeTyped
      cases (sortAxiom_eq axiomHolds).2
  | var found => intro _ env matching _ _; exact matching.lookup found
  | con declared => cases declared
  | @pi context domain body domainSort codomainSort resultSort _ _ _ _ _ =>
      intro _ env _ sort typeTyped
      obtain ⟨rfl, _⟩ := typed_srt_inv typeTyped
      simp only [eval, kindSkeleton?]
      split <;> rfl
  | @lam context domain body bodyType domainSort codomainSort resultSort domainTyped bodyTypeTyped _ _
      _ _ ihBody =>
      intro formed env matching _ _
      cases domainShape : kindSkeleton? domain with
      | some skeleton =>
          have inner := ihBody (formed.cons domainTyped) (some ⟨skeleton, skeleton.default⟩ :: env)
            (matching.cons (by simp [shape, domainShape])) codomainSort bodyTypeTyped
          simp only [eval, domainShape, kindSkeleton?, inner]
          cases kindSkeleton? bodyType <;> rfl
      | none =>
          have inner := ihBody (formed.cons domainTyped) (none :: env)
            (matching.cons (by simp [shape, domainShape])) codomainSort bodyTypeTyped
          simp only [eval, domainShape, kindSkeleton?, inner]
          cases kindSkeleton? bodyType <;> rfl
  | @app context function argument domain bodyType functionTyped argumentTyped ihFunction ihArgument =>
      intro formed env matching _ _
      rcases typed_correct formed functionTyped with same | ⟨productSort, productTyped⟩
      · cases same
      obtain ⟨domainSort, codomainSort, _, domainTyped, _, _, _⟩ := productTyped.pi_inv
      have argumentShape := ihArgument formed env matching domainSort domainTyped
      have functionShape := ihFunction formed env matching productSort productTyped
      have notKind := kindSkeleton_eq_none_of_typed formed argumentTyped domainTyped
      have substituted : kindSkeleton? (subst0 argument bodyType) = kindSkeleton? bodyType := by
        simpa [LFTyping.subst0, lift_zero] using kindSkeleton?_subst notKind bodyType 0
      rw [substituted]
      cases domainShape : kindSkeleton? domain with
      | some skeleton =>
          rw [domainShape] at argumentShape
          obtain ⟨argumentValue, argumentEval⟩ : ∃ argumentValue : skeleton.den,
              eval env argument = some ⟨skeleton, argumentValue⟩ :=
            ⟨_, (asDen_of_shape argumentShape).symm⟩
          simp only [kindSkeleton?, domainShape] at functionShape
          cases bodyShape : kindSkeleton? bodyType with
          | none =>
              rw [bodyShape] at functionShape
              simp only [eval, argumentEval, eq_none_of_shape functionShape, shape, Option.map_none]
          | some codomain =>
              rw [bodyShape] at functionShape
              obtain ⟨map, functionEval⟩ : ∃ map : (Skeleton.arrow skeleton codomain).den,
                  eval env function = some ⟨.arrow skeleton codomain, map⟩ :=
                ⟨_, (asDen_of_shape functionShape).symm⟩
              simp only [eval, argumentEval, functionEval, dite_true, shape, Option.map_some]
      | none =>
          rw [domainShape] at argumentShape
          simp only [kindSkeleton?, domainShape, Option.map_id'] at functionShape
          simp only [eval, eq_none_of_shape argumentShape, functionShape]
  | @conv context term source target sort sourceTyped convertible targetTyped ihSource _ =>
      intro formed env matching _ _
      rcases typed_correct formed sourceTyped with rfl | ⟨sourceSort, sourceFormed⟩
      · exact (not_conv_kind formed targetTyped (.symm _ _ convertible)).elim
      rw [ihSource formed env matching sourceSort sourceFormed,
        kindSkeleton_conv formed sourceFormed targetTyped convertible]

/-- A root contraction without rules or definitions is a beta contraction. -/
theorem rootStep_beta {source target : Term} (step : RootStep Theory.empty source target) :
    ∃ domain body argument, source = .app (.lam domain body) argument ∧ target = subst0 argument body := by
  cases step with
  | beta domain body argument => exact ⟨domain, body, argument, rfl, rfl⟩
  | delta defined => cases defined
  | rule _ member => exact member.elim

/-- **A step of a typed term keeps its value.** -/
theorem eval_step (term : Term) :
    ∀ {context : Ctx} {type target : Term} {env : List Value}, Formed context → Matches context env →
      Typed context term type → Step Theory.empty term target → eval env target = eval env term := by
  induction term with
  | srt sort =>
      intro context type target env _ _ _ step
      exact (RootStep.not_srt Theory.empty_headed step.srt_inv).elim
  | var index =>
      intro context type target env _ _ _ step
      exact (RootStep.not_var Theory.empty_headed step.var_inv).elim
  | con name => intro context type target env _ _ typed; exact (not_typed_con typed).elim
  | pi domain body ihDomain ihBody =>
      intro context type target env formed matching typed step
      obtain ⟨domainSort, codomainSort, _, domainTyped, bodyTyped, _, _⟩ := typed.pi_inv
      rcases step.pi_inv with root | ⟨domain', inner, rfl⟩ | ⟨body', inner, rfl⟩
      · exact (RootStep.not_pi Theory.empty_headed root).elim
      · have domain'Typed := typed_step formed domainTyped inner
        have sameShape : kindSkeleton? domain' = kindSkeleton? domain :=
          (kindSkeleton_conv formed domainTyped domain'Typed (.rel _ _ inner)).symm
        cases domainShape : kindSkeleton? domain with
        | some skeleton => simp only [eval, sameShape, domainShape]
        | none =>
            simp only [eval, sameShape, domainShape, ihDomain formed matching domainTyped inner]
      · cases domainShape : kindSkeleton? domain with
        | some skeleton =>
            have inner' : ∀ value : skeleton.den,
                eval (some ⟨skeleton, value⟩ :: env) body' = eval (some ⟨skeleton, value⟩ :: env) body :=
              fun value => ihBody (formed.cons domainTyped)
                (matching.cons (by simp [shape, domainShape])) bodyTyped inner
            simp only [eval, domainShape, inner']
        | none =>
            have inner' := ihBody (formed.cons domainTyped)
              (matching.cons (value := none) (by simp [shape, domainShape])) bodyTyped inner
            simp only [eval, domainShape, inner']
  | lam domain body ihDomain ihBody =>
      intro context type target env formed matching typed step
      obtain ⟨bodyType, domainSort, _, _, domainTyped, _, _, bodyTyped, _⟩ := typed.lam_inv
      rcases step.lam_inv with root | ⟨domain', inner, rfl⟩ | ⟨body', inner, rfl⟩
      · exact (RootStep.not_lam Theory.empty_headed root).elim
      · have sameShape : kindSkeleton? domain' = kindSkeleton? domain :=
          (kindSkeleton_conv formed domainTyped (typed_step formed domainTyped inner)
            (.rel _ _ inner)).symm
        simp only [eval, sameShape]
      · cases domainShape : kindSkeleton? domain with
        | some skeleton =>
            have inner' : ∀ value : skeleton.den,
                eval (some ⟨skeleton, value⟩ :: env) body' = eval (some ⟨skeleton, value⟩ :: env) body :=
              fun value => ihBody (formed.cons domainTyped)
                (matching.cons (by simp [shape, domainShape])) bodyTyped inner
            simp only [eval, domainShape, inner']
        | none =>
            have inner' := ihBody (formed.cons domainTyped)
              (matching.cons (value := none) (by simp [shape, domainShape])) bodyTyped inner
            simp only [eval, domainShape, inner']
  | app function argument ihFunction ihArgument =>
      intro context type target env formed matching typed step
      obtain ⟨domain, bodyType, functionTyped, argumentTyped, _⟩ := typed.app_inv
      rcases step.app_inv with root | ⟨function', inner, rfl⟩ | ⟨argument', inner, rfl⟩
      · obtain ⟨annotation, body, argument₀, same, rfl⟩ := rootStep_beta root
        cases same
        obtain ⟨bodyType₀, annotationSort, codomainSort, _, annotationTyped, bodyTypeTyped, _, bodyTyped,
          productConv⟩ := functionTyped.lam_inv
        have domains := (Conv.pi_injective confluent_empty Theory.empty_headed productConv).1
        have argumentTyped₀ : Typed context argument annotation :=
          .conv argumentTyped (.symm _ _ domains) annotationTyped
        have notKind := kindSkeleton_eq_none_of_typed formed argumentTyped₀ annotationTyped
        have argumentShape := shape_eval argumentTyped₀ formed env matching annotationSort annotationTyped
        cases annotationShape : kindSkeleton? annotation with
        | some skeleton =>
            rw [annotationShape] at argumentShape
            have bodyShape : ∀ value : skeleton.den,
                shape (eval (some ⟨skeleton, value⟩ :: env) body) = kindSkeleton? bodyType₀ :=
              fun value => shape_eval bodyTyped (formed.cons annotationTyped) _
                (matching.cons (by simp [shape, annotationShape])) codomainSort bodyTypeTyped
            exact (eval_beta_kind annotationShape notKind (asDen_of_shape argumentShape).symm
              fun value value' => (bodyShape value).trans (bodyShape value').symm).symm
        | none =>
            rw [annotationShape] at argumentShape
            exact (eval_beta_proof annotationShape notKind (eq_none_of_shape argumentShape)).symm
      · simp only [eval, ihFunction formed matching functionTyped inner]
      · simp only [eval, ihArgument formed matching argumentTyped inner]

theorem eval_reduces {context : Ctx} {source target type : Term} {env : List Value}
    (formed : Formed context) (matching : Matches context env) (typed : Typed context source type)
    (reduces : Reduces Theory.empty source target) : eval env target = eval env source := by
  induction reduces with
  | refl => rfl
  | tail earlier step ih =>
      rw [eval_step _ formed matching (typed_reduces formed typed earlier) step, ih]

/-- **Convertible typed terms have one value.** -/
theorem eval_conv {context : Ctx} {left right leftType rightType : Term} {env : List Value}
    (formed : Formed context) (matching : Matches context env) (leftTyped : Typed context left leftType)
    (rightTyped : Typed context right rightType) (convertible : Conv Theory.empty left right) :
    eval env left = eval env right := by
  obtain ⟨common, leftReduces, rightReduces⟩ := (conv_iff_joinable confluent_empty).mp convertible
  rw [← eval_reduces formed matching leftTyped leftReduces,
    ← eval_reduces formed matching rightTyped rightReduces]

/-! ## Soundness -/

/-- An environment that matching the context and makes every hypothesis
true. -/
inductive Satisfies : Ctx → List Value → Prop where
  | nil : Satisfies [] []
  | cons {context : Ctx} {env : List Value} {entry : Term} {value : Value} :
      Satisfies context env → shape value = kindSkeleton? entry →
      (kindSkeleton? entry = none → asProp (eval env entry)) →
      Satisfies (entry :: context) (value :: env)

theorem Satisfies.matching {context : Ctx} {env : List Value} (satisfies : Satisfies context env) :
    Matches context env := by
  induction satisfies with
  | nil => exact .nil
  | cons _ shaped _ ih => exact ih.cons shaped

theorem Satisfies.lookup {context : Ctx} {env : List Value} (satisfies : Satisfies context env) :
    ∀ {index : Nat} {type : Term}, ctxLookup context index = some type →
      kindSkeleton? type = none → asProp (eval env type) := by
  induction satisfies with
  | nil => intro index type found; simp [ctxLookup, LFTyping.ctxLookupAux] at found
  | @cons context env entry value _ _ holds ih =>
      intro index type found notKind
      cases index with
      | zero =>
          have same : type = lift 1 0 entry := by
            simpa [ctxLookup, LFTyping.ctxLookupAux] using found.symm
          subst same
          rw [eval_lift_one]
          exact holds (by simpa [kindSkeleton?_lift] using notKind)
      | succ index =>
          rw [ctxLookup_cons_succ] at found
          obtain ⟨original, originalFound, rfl⟩ := Option.map_eq_some_iff.mp found
          rw [eval_lift_one]
          exact ih originalFound (by simpa [kindSkeleton?_lift] using notKind)

/-- **Soundness**: the type of a typed term, when it is a type, is true in
every environment that makes the context true. -/
theorem sound {context : Ctx} {term type : Term} (typed : Typed context term type) :
    Formed context → ∀ env, Satisfies context env → Typed context type (.srt .type) →
      asProp (eval env type) := by
  induction typed with
  | sort _ =>
      intro _ env _ typeTyped
      cases conv_srt_injective (typed_srt_inv typeTyped).2
  | var found =>
      intro _ env satisfies typeTyped
      exact satisfies.lookup found (kindSkeleton_eq_none_of_type typeTyped)
  | con declared => cases declared
  | pi _ _ _ _ _ =>
      intro _ env _ typeTyped
      cases conv_srt_injective (typed_srt_inv typeTyped).2
  | @lam context domain body bodyType domainSort codomainSort resultSort domainTyped bodyTypeTyped rule
      _ _ _ ihBody =>
      intro formed env satisfies typeTyped
      have resultType := sort_eq_of_conv formed (.pi domainTyped bodyTypeTyped rule) typeTyped (.refl _)
      subst resultType
      have codomainType : codomainSort = .type := (result_eq_codomain _ rule).symm
      subst codomainType
      cases domainShape : kindSkeleton? domain with
      | some skeleton =>
          simp only [eval, domainShape, asProp_prop]
          intro value
          exact ihBody (formed.cons domainTyped) _
            (satisfies.cons (by simp [shape, domainShape]) (fun notKind => by rw [domainShape] at notKind; cases notKind))
            bodyTypeTyped
      | none =>
          simp only [eval, domainShape, asProp_prop]
          intro holds
          exact ihBody (formed.cons domainTyped) _
            (satisfies.cons (value := none) (by simp [shape, domainShape]) (fun _ => holds))
            bodyTypeTyped
  | @app context function argument domain bodyType functionTyped argumentTyped ihFunction ihArgument =>
      intro formed env satisfies typeTyped
      rcases typed_correct formed functionTyped with same | ⟨productSort, productTyped⟩
      · cases same
      obtain ⟨domainSort, codomainSort, resultSort, domainTyped, bodyTypeTyped, rule, _⟩ :=
        productTyped.pi_inv
      have substituted := HasType.subst0 Theory.empty_closedBodies closedTypes bodyTypeTyped argumentTyped
      have codomainType := sort_eq_of_conv formed substituted typeTyped (.refl _)
      subst codomainType
      have resultType : resultSort = .type := (result_eq_codomain _ rule)
      subst resultType
      have productType : Typed context (.pi domain bodyType) (.srt .type) := .pi domainTyped bodyTypeTyped rule
      have functionHolds := ihFunction formed env satisfies productType
      have notKind := kindSkeleton_eq_none_of_typed formed argumentTyped domainTyped
      have argumentShape := shape_eval argumentTyped formed env satisfies.matching domainSort domainTyped
      rw [eval_subst0 notKind]
      cases domainShape : kindSkeleton? domain with
      | some skeleton =>
          rw [domainShape] at argumentShape
          simp only [eval, domainShape, asProp_prop] at functionHolds
          rw [← asDen_of_shape argumentShape]
          exact functionHolds _
      | none =>
          rw [domainShape] at argumentShape
          simp only [eval, domainShape, asProp_prop] at functionHolds
          rw [eq_none_of_shape argumentShape]
          have domainType : domainSort = .type := by
            rcases kindSkeleton_of_sort formed domainTyped with ⟨_, isSome⟩ | ⟨same, _⟩
            · rw [domainShape] at isSome; cases isSome
            · exact same
          subst domainType
          exact functionHolds (ihArgument formed env satisfies domainTyped)
  | @conv context term source target sort sourceTyped convertible targetTyped ihSource _ =>
      intro formed env satisfies typeTyped
      rcases typed_correct formed sourceTyped with rfl | ⟨sourceSort, sourceFormed⟩
      · exact (not_conv_kind formed targetTyped (.symm _ _ convertible)).elim
      have sourceType := sort_eq_of_conv formed sourceFormed typeTyped convertible
      subst sourceType
      rw [← eval_conv formed satisfies.matching sourceFormed typeTyped convertible]
      exact ihSource formed env satisfies sourceFormed

/-! ## Consistency -/

/-- The type `Π p : ∗. p`. -/
def falsum : Term := .pi (.srt .type) (.var 0)

theorem falsum_typed : Typed [] falsum (.srt .type) :=
  .pi (domainSort := .kind) (codomainSort := .type) (.sort rfl) (.var rfl) (by decide)

/-- `Π p : ∗. p` denotes `∀ p : Prop, p`. -/
theorem eval_falsum : asProp (eval [] falsum) = ∀ proposition : Prop, proposition := rfl

/-- **The calculus of constructions is consistent**: no closed term has the
type `Π p : ∗. p`. -/
theorem constructions_consistent (term : Term) : ¬ Typed [] term falsum := by
  intro typed
  have holds := sound typed .nil [] .nil falsum_typed
  rw [eval_falsum] at holds
  exact holds False

/-- **Every system of the lambda cube is consistent.** -/
theorem consistent_of_subsumed {profile : Profile} (included : LFProfile.Subsumed profile constructions)
    (term : Term) : ¬ HasType profile Theory.empty [] term falsum :=
  fun typed => constructions_consistent term (typed.mono included (Theory.Extends.refl _))

/-- The same, for the sorted presentation: no closed derivation has a type
that erases to `Π p : ∗. p`. -/
theorem derives_consistent {profile : Profile} (included : LFProfile.Subsumed profile constructions)
    {term type : PTerm} {sort : Srt} (erased : type.erase = falsum) :
    ¬ Derives profile [] (.term term type sort) := by
  intro derivation
  have typed := derivation.erase
  simp only [Judgment.erased, erased] at typed
  exact consistent_of_subsumed included _ typed

/-! ## Controls -/

/-- **Positive**: the polymorphic identity's type denotes `∀ p : Prop, p → p`,
which holds. -/
theorem polymorphicIdentity_sound :
    asProp (eval [] Example.polymorphicIdentityType.erase) = ∀ proposition : Prop, proposition → proposition :=
  rfl

theorem polymorphicIdentity_typed_erased :
    Typed [] Example.polymorphicIdentity.erase Example.polymorphicIdentityType.erase :=
  Example.polymorphicIdentity_typed.erase

/-- **Negative**: the value is not invariant under an untyped step.  The
abstraction `λ x : ∗. x` applied to `∗`, which is not typed, is a type
operator, while its contraction `∗` has no value.  This is why the
conversion rule is reduced to steps of typed terms. -/
theorem eval_untyped_step_changes :
    eval [] (.app (.lam (.srt .type) (.var 0)) (.srt .type)) ≠ eval [] (subst0 (.srt .type) (.var 0)) := by
  simp [eval, kindSkeleton?, shape, LFTyping.subst0, LFTyping.subst]

theorem untyped_redex_not_typed {context : Ctx} {type : Term} :
    ¬ Typed context (.app (.lam (.srt .type) (.var 0)) (.srt .type)) type := by
  intro typed
  obtain ⟨domain, _, functionTyped, argumentTyped, _⟩ := typed.app_inv
  obtain ⟨_, _, _, _, _, _, _, _, productConv⟩ := functionTyped.lam_inv
  have domains := (Conv.pi_injective confluent_empty Theory.empty_headed productConv).1
  have kindConv := (typed_srt_inv argumentTyped).2
  cases conv_srt_injective (.trans _ _ _ domains (.symm _ _ kindConv))

#print axioms eval_subst0
#print axioms shape_eval
#print axioms eval_step
#print axioms sound
#print axioms constructions_consistent
#print axioms consistent_of_subsumed
#print axioms derives_consistent

end Mettapedia.GSLT.Dedukti.ConstructionsModel
