import Mettapedia.Languages.Megalodon.NaturalRecursion

/-!
# Meaning of the optional classical natural theory profile

The native source profile names three independent logical options: selection,
double-negation elimination and Dedekind infinity. This file states their
ordinary mathematical meaning and derives the selected zero, successor and
recursion laws. It does not add those options to the Egal kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.NaturalTheoryProfile

open NaturalRecursion

universe u v

def optionNames : List String :=
  ["niChoiceOption", "niClassicalOption", "niInfinityOption"]

def selectedRootNames : List String :=
  ["niSelectedZeroNotSuccessor", "niSelectedSuccessorInjective",
   "niSelectedSuccessorNotOnto", "niSelectedInfinity",
   "niSelectedNaturalZero", "niSelectedNaturalSuccessor",
   "niSelectedNaturalInduction", "niSelectedRecursion"]

def Selects {A : Type u} (choose : (A → Prop) → A) : Prop :=
  ∀ predicate : A → Prop, (∃ value, predicate value) → predicate (choose predicate)

def InfiniteFunction {N : Type u} (function : N → N) : Prop :=
  Function.Injective function ∧ ¬ Function.Surjective function

/-- The carrier options are separated by type. The native polymorphic selector
supplies these instances, but no parametricity or coherence law is assumed. -/
structure CarrierOptions (N : Type u) where
  classical : ∀ proposition : Prop, ¬¬proposition → proposition
  chooseNumber : (N → Prop) → N
  chooseFunction : ((N → N) → Prop) → (N → N)
  selectsNumber : Selects chooseNumber
  selectsFunction : Selects chooseFunction
  infinity : ∃ function : N → N, InfiniteFunction function

def successor {N : Type u} (options : CarrierOptions N) : N → N :=
  options.chooseFunction InfiniteFunction

def Omitted {N : Type u} (function : N → N) (missing : N) : Prop :=
  ∀ source, function source ≠ missing

theorem selected_infinite {N : Type u} (options : CarrierOptions N) :
    InfiniteFunction (successor options) :=
  options.selectsFunction InfiniteFunction options.infinity

theorem not_surjective_has_omitted {N : Type u} (options : CarrierOptions N)
    {function : N → N} (notOnto : ¬ Function.Surjective function) :
    ∃ missing, Omitted function missing := by
  apply options.classical
  intro noMissing
  apply notOnto
  intro target
  apply options.classical
  intro noPreimage
  apply noMissing
  exact ⟨target, fun source same => noPreimage ⟨source, same⟩⟩

def zero {N : Type u} (options : CarrierOptions N) : N :=
  options.chooseNumber (Omitted (successor options))

theorem zero_omitted {N : Type u} (options : CarrierOptions N) :
    Omitted (successor options) (zero options) :=
  options.selectsNumber _
    (not_surjective_has_omitted options (selected_infinite options).2)

theorem successor_ne_zero {N : Type u} (options : CarrierOptions N) (number : N) :
    successor options number ≠ zero options :=
  zero_omitted options number

theorem successor_injective {N : Type u} (options : CarrierOptions N) :
    Function.Injective (successor options) :=
  (selected_infinite options).1

def Generated {N : Type u} (options : CarrierOptions N) (number : N) : Prop :=
  ∀ predicate : N → Prop, predicate (zero options) →
    (∀ n, predicate n → predicate (successor options n)) → predicate number

theorem generated_zero {N : Type u} (options : CarrierOptions N) :
    Generated options (zero options) :=
  fun _ initial _ => initial

theorem generated_successor {N : Type u} (options : CarrierOptions N) {number : N}
    (generated : Generated options number) : Generated options (successor options number) :=
  fun predicate initial closed => closed number (generated predicate initial closed)

structure ResultSelection (A : Type v) where
  choose : (A → Prop) → A
  selects : Selects choose

def recursor {N : Type u} (options : CarrierOptions N) {A : Type v}
    (selection : ResultSelection A) (start : A) (step : N → A → A) (number : N) : A :=
  NaturalRecursion.selected selection.choose (zero options) (successor options) start step number

theorem recursor_graph {N : Type u} (options : CarrierOptions N) {A : Type v}
    (selection : ResultSelection A) (start : A) (step : N → A → A) {number : N}
    (generated : Generated options number) :
    Graph (zero options) (successor options) start step number
      (recursor options selection start step number) :=
  NaturalRecursion.selected_graph selection.choose selection.selects generated

theorem recursor_zero {N : Type u} (options : CarrierOptions N) {A : Type v}
    (selection : ResultSelection A) (start : A) (step : N → A → A) :
    recursor options selection start step (zero options) = start :=
  NaturalRecursion.selected_zero selection.choose selection.selects
    (successor_ne_zero options)

theorem recursor_successor {N : Type u} (options : CarrierOptions N) {A : Type v}
    (selection : ResultSelection A) (start : A) (step : N → A → A) {number : N}
    (generated : Generated options number) :
    recursor options selection start step (successor options number) =
      step number (recursor options selection start step number) :=
  NaturalRecursion.selected_successor selection.choose selection.selects
    (successor_ne_zero options) (successor_injective options) generated

theorem recursor_unique {N : Type u} (options : CarrierOptions N) {A : Type v}
    (selection : ResultSelection A) (start : A) (step : N → A → A)
    (candidate : N → A) (atZero : candidate (zero options) = start)
    (atSuccessor : ∀ number, Generated options number →
      candidate (successor options number) = step number (candidate number))
    {number : N} (generated : Generated options number) :
    recursor options selection start step number = candidate number :=
  NaturalRecursion.selected_unique selection.choose selection.selects candidate atZero
    (fun number generatedAtNumber => atSuccessor number generatedAtNumber) generated

/-- This is the ordinary meaning of the selected native recursion theorem.
Equations and uniqueness are deliberately restricted to the generated carrier. -/
theorem recursion {N : Type u} (options : CarrierOptions N) {A : Type v}
    (selection : ResultSelection A) (start : A) (step : N → A → A) :
    ∃ function : N → A,
      function (zero options) = start ∧
      (∀ number, Generated options number →
        function (successor options number) = step number (function number)) ∧
      ∀ candidate : N → A, candidate (zero options) = start →
        (∀ number, Generated options number →
          candidate (successor options number) = step number (candidate number)) →
        ∀ number, Generated options number → function number = candidate number := by
  refine ⟨recursor options selection start step, recursor_zero options selection start step,
    fun number generated => recursor_successor options selection start step generated, ?_⟩
  intro candidate atZero atSuccessor number generated
  exact recursor_unique options selection start step candidate atZero atSuccessor generated

/-- A finite singleton cannot satisfy the selected infinity option. -/
theorem unit_refuses_infinity :
    ¬ ∃ function : Unit → Unit, InfiniteFunction function := by
  rintro ⟨function, _, notOnto⟩
  apply notOnto
  intro target
  exact ⟨(), Subsingleton.elim _ _⟩

/-- A function of the selector's type can still violate its law. -/
theorem constant_false_refuses_selection :
    ¬ Selects (fun _ : Bool → Prop => false) := by
  intro selects
  exact Bool.false_ne_true (selects (fun value => value = true) ⟨true, rfl⟩)

def verdicts : List (String × Bool) := [
  ("Megalodon theory options are independently named", decide
    optionNames.Nodup),
  ("Megalodon selected options do not include HOTG", decide
    ("HOTG" ∉ optionNames)),
  ("Megalodon selection and infinity remain distinct",
    "niChoiceOption" != "niInfinityOption")]

theorem all_verdicts : verdicts.all Prod.snd = true := by decide +kernel

end Mettapedia.Languages.Megalodon.NaturalTheoryProfile
