import Mettapedia.Languages.MeTTa.HE.HOLContract.Dependent

/-!
# The dependent route decides dependent typing

The dependent route of HE-style declarations, the binders `(: $x A)` of `he-prime`, types a
term as λΠ's application rule for declared constants prescribes, without conversion: a constant
has its declared type, and an application of a constant declared with a telescope to as many
arguments as it has binders has the telescope's result with the arguments substituted for its
variables, when each argument has its binder's type under the same substitution, up to syntactic
equality.

`dependentType?` is that computation.  It decides `DependentTyped`
(`dependentType?_eq_some_iff`, `dependentType?_eq_none_iff`): a term has at most one type
(`dependentTyped_unique`), the computation answers it when there is one, and answers nothing
exactly when the term has no type.  So a refutation by the route is a refutation of the
specification, and an answer is its only type.

On the dependent-binder programme the computation gives `(remember fact)` the type
`(WitnessOf fact)` and refutes `(useWitness fact otherWitness)`, as `Dependent` derives by hand
(`dependentType?_remember_fact`, `dependentType?_useWitness_fact`).

Hosted, the route hands each derivation to the LF kernel of the proof-kernel curriculum, which
executes this check; the kernel's own agreement with `DependentTyped` is not stated here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.HOLContract

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Spec.Type.RuntimeRefinement

variable (declarations : String → Option DependentDeclaration)

mutual

/-- The dependent route's answer for a term: the declared type of a constant, or, for an
application of a constant declared with a telescope, the substituted result when every argument
has its substituted binder type. -/
def dependentType? : Atom → Option Atom
  | .symbol name =>
      match declarations name with
      | some (.plain type) => some type
      | _ => none
  | .expression (.symbol name :: arguments) =>
      match declarations name with
      | some (.telescope binders result) =>
          if dependentArguments (argumentValuation binders arguments) binders arguments then
            some (applyTypeValuation (argumentValuation binders arguments) result)
          else none
      | _ => none
  | _ => none
termination_by structural atom => atom

/-- Binders and arguments pair up, and each argument's answer is its binder's type under the
valuation. -/
def dependentArguments (valuation : String → Atom) :
    List (String × Atom) → List Atom → Bool
  | [], [] => true
  | binder :: binders, argument :: arguments =>
      (dependentType? argument == some (applyTypeValuation valuation binder.2)) &&
        dependentArguments valuation binders arguments
  | _, _ => false
termination_by structural _ arguments => arguments

end

variable {declarations}

/-! ## A term has at most one type -/

/-- **Uniqueness.**  A constant has one declaration and an application one head, so dependent
typing is a partial function. -/
theorem dependentTyped_unique {term type other : Atom}
    (typed : DependentTyped declarations term type)
    (typedOther : DependentTyped declarations term other) : type = other := by
  cases typed with
  | constant found =>
      cases typedOther with
      | constant foundOther =>
          rw [found] at foundOther
          cases foundOther
          rfl
  | application found _ _ =>
      cases typedOther with
      | application foundOther _ _ =>
          rw [found] at foundOther
          cases foundOther
          rfl

/-! ## Soundness -/

private theorem dependentArguments_sound {valuation : String → Atom} :
    ∀ (binders : List (String × Atom)) (arguments : List Atom),
      (∀ argument ∈ arguments, ∀ type,
        dependentType? declarations argument = some type →
          DependentTyped declarations argument type) →
      dependentArguments declarations valuation binders arguments = true →
      binders.length = arguments.length ∧
        ∀ (index : Nat) (inBinders : index < binders.length)
          (inArguments : index < arguments.length),
          DependentTyped declarations arguments[index]
            (applyTypeValuation valuation binders[index].2)
  | [], [], _, _ => ⟨rfl, fun index inBinders => absurd inBinders (Nat.not_lt_zero index)⟩
  | [], _ :: _, _, checked => by simp [dependentArguments] at checked
  | _ :: _, [], _, checked => by simp [dependentArguments] at checked
  | binder :: binders, argument :: arguments, sound, checked => by
      simp only [dependentArguments, Bool.and_eq_true, beq_iff_eq] at checked
      have head := sound argument (List.mem_cons_self ..) _ checked.1
      have tail := dependentArguments_sound binders arguments
        (fun other member => sound other (List.mem_cons_of_mem _ member)) checked.2
      refine ⟨by simp [tail.1], ?_⟩
      intro index inBinders inArguments
      cases index with
      | zero => simpa using head
      | succ index =>
          simpa using tail.2 index (by simpa using inBinders) (by simpa using inArguments)

/-- **Soundness.**  The route's answer is a dependent typing. -/
theorem dependentType?_sound (term : Atom) :
    ∀ {type : Atom}, dependentType? declarations term = some type →
      DependentTyped declarations term type := by
  intro type answered
  match term, answered with
  | .symbol name, answered =>
      simp only [dependentType?] at answered
      split at answered
      · rename_i declared found
        cases answered
        exact .constant found
      · cases answered
  | .expression (.symbol name :: arguments), answered =>
      simp only [dependentType?] at answered
      split at answered
      · rename_i binders result found
        split at answered
        · rename_i checked
          cases answered
          have parts := dependentArguments_sound binders arguments
            (fun argument member _ answer => dependentType?_sound argument answer) checked
          exact .application found parts.1 parts.2
        · cases answered
      · cases answered
  | .var _, answered => simp [dependentType?] at answered
  | .grounded _, answered => simp [dependentType?] at answered
  | .expression [], answered => simp [dependentType?] at answered
  | .expression (.var _ :: _), answered => simp [dependentType?] at answered
  | .expression (.grounded _ :: _), answered => simp [dependentType?] at answered
  | .expression (.expression _ :: _), answered => simp [dependentType?] at answered
termination_by sizeOf term
decreasing_by
  all_goals
    simp_wf
    have := List.sizeOf_lt_of_mem ‹_ ∈ _›
    omega

/-! ## Completeness -/

private theorem dependentArguments_complete {valuation : String → Atom} :
    ∀ (binders : List (String × Atom)) (arguments : List Atom),
      binders.length = arguments.length →
      (∀ (index : Nat) (inBinders : index < binders.length)
          (inArguments : index < arguments.length),
          dependentType? declarations arguments[index] =
            some (applyTypeValuation valuation binders[index].2)) →
      dependentArguments declarations valuation binders arguments = true
  | [], [], _, _ => by simp [dependentArguments]
  | [], _ :: _, lengths, _ => by simp at lengths
  | _ :: _, [], lengths, _ => by simp at lengths
  | binder :: binders, argument :: arguments, lengths, answers => by
      simp only [dependentArguments, Bool.and_eq_true, beq_iff_eq]
      exact ⟨answers 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _),
        dependentArguments_complete binders arguments (by simpa using lengths)
          (fun index inBinders inArguments =>
            answers (index + 1) (Nat.succ_lt_succ inBinders) (Nat.succ_lt_succ inArguments))⟩

/-- **Completeness.**  A dependent typing is the route's answer. -/
theorem dependentType?_complete {term type : Atom}
    (typed : DependentTyped declarations term type) :
    dependentType? declarations term = some type := by
  induction typed with
  | constant found => simp [dependentType?, found]
  | @application name binders result arguments found lengths _ answers =>
      have checked := dependentArguments_complete (valuation := argumentValuation binders arguments)
        binders arguments lengths answers
      simp [dependentType?, found, checked]

/-! ## The route decides dependent typing -/

/-- **The route decides dependent typing**: its answer is exactly the type. -/
theorem dependentType?_eq_some_iff {term type : Atom} :
    dependentType? declarations term = some type ↔ DependentTyped declarations term type :=
  ⟨dependentType?_sound term, dependentType?_complete⟩

/-- **Refutations are earned**: the route answers nothing exactly when the term has no type. -/
theorem dependentType?_eq_none_iff {term : Atom} :
    dependentType? declarations term = none ↔ ∀ type, ¬DependentTyped declarations term type := by
  constructor
  · intro none type typed
    rw [dependentType?_complete typed] at none
    cases none
  · intro untyped
    cases answer : dependentType? declarations term with
    | none => rfl
    | some type => exact absurd (dependentType?_sound term answer) (untyped type)

/-! ## The dependent-binder programme, computed -/

private theorem binders_fact :
    bindersDeclarations "fact" = some (.plain (.symbol "Fact")) := rfl

private theorem binders_other :
    bindersDeclarations "other" = some (.plain (.symbol "Fact")) := rfl

private theorem binders_otherWitness :
    bindersDeclarations "otherWitness" =
      some (.plain (.expression [.symbol "WitnessOf", .symbol "other"])) := rfl

private theorem binders_remember :
    bindersDeclarations "remember" =
      some (.telescope [("p", .symbol "Fact")] (.expression [.symbol "WitnessOf", .var "p"])) :=
  rfl

private theorem binders_useWitness :
    bindersDeclarations "useWitness" =
      some (.telescope [("p", .symbol "Fact"), ("w", .expression [.symbol "WitnessOf", .var "p"])]
        (.expression [.symbol "Checked", .var "p", .var "w"])) := rfl

/-- `(remember fact)` computes `(WitnessOf fact)`. -/
theorem dependentType?_remember_fact :
    dependentType? bindersDeclarations (.expression [.symbol "remember", .symbol "fact"]) =
      some (.expression [.symbol "WitnessOf", .symbol "fact"]) := by
  simp [dependentType?, dependentArguments, binders_remember, binders_fact, argumentValuation,
    applyTypeValuation]

/-- `(useWitness other otherWitness)` computes `(Checked other otherWitness)`. -/
theorem dependentType?_useWitness_other :
    dependentType? bindersDeclarations
        (.expression [.symbol "useWitness", .symbol "other", .symbol "otherWitness"]) =
      some (.expression [.symbol "Checked", .symbol "other", .symbol "otherWitness"]) := by
  simp [dependentType?, dependentArguments, binders_useWitness, binders_other,
    binders_otherWitness, argumentValuation, applyTypeValuation]

/-- `(useWitness fact otherWitness)` computes nothing: the witness belongs to `other`. -/
theorem dependentType?_useWitness_fact :
    dependentType? bindersDeclarations
        (.expression [.symbol "useWitness", .symbol "fact", .symbol "otherWitness"]) = none := by
  simp [dependentType?, dependentArguments, binders_useWitness, binders_fact,
    binders_otherWitness, argumentValuation, applyTypeValuation]

/-- The refuted golden, now by computation: `(useWitness fact otherWitness)` has no type. -/
theorem not_dependentTyped_useWitness_fact_computed (type : Atom) :
    ¬DependentTyped bindersDeclarations
        (.expression [.symbol "useWitness", .symbol "fact", .symbol "otherWitness"]) type :=
  dependentType?_eq_none_iff.mp dependentType?_useWitness_fact type

/-- An application of another arity computes nothing. -/
theorem dependentType?_remember_two :
    dependentType? bindersDeclarations
        (.expression [.symbol "remember", .symbol "fact", .symbol "fact"]) = none := by
  simp [dependentType?, dependentArguments, binders_remember]

#print axioms dependentTyped_unique
#print axioms dependentType?_sound
#print axioms dependentType?_complete
#print axioms dependentType?_eq_some_iff
#print axioms dependentType?_eq_none_iff
#print axioms dependentType?_remember_fact
#print axioms dependentType?_useWitness_other
#print axioms dependentType?_useWitness_fact
#print axioms not_dependentTyped_useWitness_fact_computed
#print axioms dependentType?_remember_two

end Mettapedia.Languages.MeTTa.HE.HOLContract
