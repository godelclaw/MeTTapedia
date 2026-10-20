import Mettapedia.Logic.HOL.Semantics.ModelProperties

/-!
# Typed natural-carrier statements with an arbitrary recursion target

The formulas retain numeral wrapping, the result-before-predecessor order of
the recursion method, and Boolean equality in successor injectivity. These
are mathematical statements, independent of a native proof format. The full
model is parameterized by an actual carrier, zero, successor and target type.
Constructing the model does not assume the natural-number laws.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.NaturalFacts

inductive Base where
  | natural
  | result
  deriving DecidableEq, Repr

abbrev number : Ty Base := .base .natural
abbrev target : Ty Base := .base .result

inductive Const : Ty Base → Type where
  | zero : Const number
  | successor : Const (number ⇒ number)
  | numeral : Const (number ⇒ number)
  deriving DecidableEq, Repr

def zero {context : Ctx Base} : Term Const context number := .app (.const .numeral) (.const .zero)

def recursion : ClosedFormula Const :=
  .all (σ := target) (.all (σ := target ⇒ number ⇒ target)
    (.ex (σ := number ⇒ target)
      (.and (.eq (.app (.var .vz) zero) (.var (.vs (.vs .vz))))
        (.all (σ := number)
          (.eq (.app (.var (.vs .vz)) (.app (.const .successor) (.var .vz)))
            (.app (.app (.var (.vs (.vs .vz))) (.app (.var (.vs .vz)) (.var .vz)))
              (.var .vz)))))))

def induction : ClosedFormula Const :=
  .all (σ := number ⇒ .prop)
    (.imp (.and (.app (.var .vz) zero)
      (.all (σ := number) (.imp (.app (.var (.vs .vz)) (.var .vz))
        (.app (.var (.vs .vz)) (.app (.const .successor) (.var .vz))))))
      (.all (σ := number) (.app (.var (.vs .vz)) (.var .vz))))

def noConfusion : ClosedFormula Const :=
  .all (σ := number) (.not (.eq (.app (.const .successor) (.var .vz)) zero))

/-- Native Boolean equality states both directions, including the congruence
direction that is absent from the implication-only Peano axiom. -/
def successorInjective : ClosedFormula Const :=
  .all (σ := number) (.all (σ := number)
    (.eq (.eq (.app (.const .successor) (.var (.vs .vz)))
          (.app (.const .successor) (.var .vz)))
      (.eq (.var (.vs .vz)) (.var .vz))))

/-- An injective endomorphism with an omitted value on this number carrier. -/
def infinity : ClosedFormula Const :=
  .ex (σ := number ⇒ number)
    (.and (.all (σ := number) (.all (σ := number)
      (.imp (.eq (.app (.var (.vs (.vs .vz))) (.var (.vs .vz)))
          (.app (.var (.vs (.vs .vz))) (.var .vz)))
        (.eq (.var (.vs .vz)) (.var .vz)))))
      (.ex (σ := number) (.all (σ := number)
        (.not (.eq (.app (.var (.vs (.vs .vz))) (.var .vz)) (.var (.vs .vz)))))))

def carrier (numbers result : Type 1) : Base → Type 1
  | .natural => numbers
  | .result => result

def constants {numbers result : Type 1} (origin : numbers) (next : numbers → numbers) :
    {type : Ty Base} → Const type → Ty.denote.{0, 0} (carrier numbers result) type
  | _, .zero => origin
  | _, .successor => next
  | _, .numeral => id

def model {numbers : Type 1} (origin : numbers) (next : numbers → numbers) (result : Type 1) :
    HenkinModel.{0, 0, 0} Base Const :=
  .standard (carrier numbers result) (constants origin next)

theorem fullDomains {numbers : Type 1} (origin : numbers) (next : numbers → numbers) (result : Type 1) :
    (model origin next result).FullDomains := HenkinModel.fullDomains_standard _ _

theorem recursion_meaning {numbers : Type 1} (origin : numbers) (next : numbers → numbers)
    (result : Type 1) :
    (model origin next result).models recursion ↔
      ∀ (base : result) (step : result → numbers → result), ∃ function : numbers → result,
        function origin = base ∧ ∀ n, function (next n) = step (function n) n := by
  constructor
  · intro valid base step
    obtain ⟨function, _, atZero, atNext⟩ := valid base trivial step trivial
    exact ⟨function, atZero, fun n => atNext n trivial⟩
  · intro existsFunction base _ step _
    obtain ⟨function, atZero, atNext⟩ := existsFunction base step
    exact ⟨function, trivial, atZero, fun n _ => atNext n⟩

theorem induction_meaning {numbers : Type 1} (origin : numbers) (next : numbers → numbers)
    (result : Type 1) :
    (model origin next result).models induction ↔
      ∀ predicate : numbers → Prop, predicate origin →
        (∀ n, predicate n → predicate (next n)) → ∀ n, predicate n := by
  constructor
  · intro valid predicate atZero atNext n
    exact valid (fun n => ULift.up (predicate n)) trivial
      ⟨atZero, fun n _ => atNext n⟩ n trivial
  · intro inductionPrinciple predicate _ premises n _
    exact inductionPrinciple (fun n => (predicate n).down) premises.1
      (fun n => premises.2 n trivial) n

theorem noConfusion_meaning {numbers : Type 1} (origin : numbers) (next : numbers → numbers)
    (result : Type 1) :
    (model origin next result).models noConfusion ↔ ∀ n, next n ≠ origin := by
  constructor
  · exact fun valid n => valid n trivial
  · exact fun valid n _ => valid n

theorem successorInjective_meaning {numbers : Type 1} (origin : numbers) (next : numbers → numbers)
    (result : Type 1) :
    (model origin next result).models successorInjective ↔ Function.Injective next := by
  constructor
  · exact fun valid first second same => (valid first trivial second trivial).mp same
  · intro injective first _ second _
    exact ⟨fun same => injective same, fun same => congrArg next same⟩

theorem infinity_meaning {numbers : Type 1} (origin : numbers) (next : numbers → numbers)
    (result : Type 1) :
    (model origin next result).models infinity ↔
      ∃ function : numbers → numbers, Function.Injective function ∧
        ∃ missing, ∀ n, function n ≠ missing := by
  constructor
  · rintro ⟨function, _, injective, missing, _, omitted⟩
    exact ⟨function, fun first second same => injective first trivial second trivial same,
      missing, fun n => omitted n trivial⟩
  · rintro ⟨function, injective, missing, omitted⟩
    exact ⟨function, trivial, (fun first _ second _ same => injective same),
      missing, trivial, fun n _ => omitted n⟩

theorem collapsing_noConfusion_refused :
    ¬ (model (⟨()⟩ : ULift.{1} Unit) id (ULift.{1} Unit)).models noConfusion := by
  rw [noConfusion_meaning]
  intro impossible
  exact impossible ⟨()⟩ rfl

end Mettapedia.Logic.HOL.NaturalFacts
