import Mettapedia.Logic.HOL.Semantics.ModelProperties

/-!
# Typed statements for the two Boolean values

The native HOL proposition carrier is a lifted meta-level proposition. Its
classical two-value comparison is explicit; it does not identify every data
type with propositions. The statements use the existing intrinsic HOL syntax.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.BooleanFacts

inductive Base where
  | result
  deriving DecidableEq, Repr

abbrev Const (_type : Ty Base) := Empty
abbrev result : Ty Base := .base .result
abbrev boolean : Ty Base := .prop

def recursion : ClosedFormula Const :=
  .all (σ := result) (.all (σ := result) (.ex (σ := boolean ⇒ result)
    (.and
      (.eq (.app (.var .vz) .bot) (.var (.vs (.vs .vz))))
      (.eq (.app (.var .vz) .top) (.var (.vs .vz))))))

def induction : ClosedFormula Const :=
  .all (σ := boolean ⇒ boolean)
    (.imp (.and (.app (.var .vz) .bot) (.app (.var .vz) .top))
      (.all (σ := boolean) (.app (.var (.vs .vz)) (.var .vz))))

def noConfusion : ClosedFormula Const := .not (.eq (.bot : Term Const [] boolean) .top)

def cases : ClosedFormula Const :=
  .all (σ := boolean) (.or (.eq (.var .vz) .bot) (.eq (.var .vz) .top))

def finite : ClosedFormula Const :=
  .all (σ := boolean ⇒ boolean)
    (.imp
      (.all (σ := boolean) (.all (σ := boolean)
        (.imp
          (.eq (.app (.var (.vs (.vs .vz))) (.var (.vs .vz)))
            (.app (.var (.vs (.vs .vz))) (.var .vz)))
          (.eq (.var (.vs .vz)) (.var .vz)))))
      (.all (σ := boolean) (.ex (σ := boolean)
        (.eq (.app (.var (.vs (.vs .vz))) (.var .vz)) (.var (.vs .vz))))))

inductive Fact where
  | recursion | induction | separation | cases | finite
  deriving DecidableEq, Repr

def formula : Fact → ClosedFormula Const
  | .recursion => recursion
  | .induction => induction
  | .separation => noConfusion
  | .cases => cases
  | .finite => finite

noncomputable def boolPropEquiv : ULift.{1} Bool ≃ ULift.{1} Prop := by
  classical
  exact
    { toFun := fun value => ⟨if value.down then True else False⟩
      invFun := fun value => ⟨decide value.down⟩
      left_inv := by rintro ⟨value⟩; cases value <;> simp
      right_inv := by
        rintro ⟨value⟩
        apply ULift.down_injective
        apply propext
        by_cases holds : value <;> simp [holds] }

@[simp] theorem boolPropEquiv_false : boolPropEquiv ⟨false⟩ = ⟨False⟩ := rfl
@[simp] theorem boolPropEquiv_true : boolPropEquiv ⟨true⟩ = ⟨True⟩ := rfl

def model (Result : Type 1) : HenkinModel.{0, 0, 0} Base Const :=
  HenkinModel.standard (fun | .result => Result) (fun {_type} impossible => impossible.elim)

theorem proposition_cases (value : ULift.{1} Prop) : value = ⟨False⟩ ∨ value = ⟨True⟩ := by
  obtain ⟨⟨flag⟩, rfl⟩ := boolPropEquiv.surjective value
  cases flag
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem finite_propositions : Finite (ULift.{1} Prop) :=
  Finite.of_equiv (ULift.{1} Bool) boolPropEquiv

namespace HenkinChoice

abbrev selectorType : Ty Base := (result ⇒ boolean) ⇒ result

def predicateTerm : Term Const [boolean, selectorType, result, result] (result ⇒ boolean) :=
  .lam (.or
    (.and (.var (.vs .vz)) (.eq (.var .vz) (.var (.vs (.vs (.vs .vz))))))
    (.and (.not (.var (.vs .vz))) (.eq (.var .vz) (.var (.vs (.vs (.vs (.vs .vz))))))))

def selectorTerm : Term Const [selectorType, result, result] (boolean ⇒ result) :=
  .lam (.app (.var (.vs .vz)) predicateTerm)

variable (M : HenkinModel.{0, 0, 0} Base Const)

def valuation (falseResult trueResult : Ty.denote.{0, 0} M.Carrier result)
    (selector : Ty.denote.{0, 0} M.Carrier selectorType) : M.Valuation [selectorType, result, result] :=
  M.extend (M.extend (M.extend (Γ := []) (σ := result)
    (fun {_type} impossible => nomatch impossible) falseResult) trueResult) selector

theorem valuation_admissible (falseResult trueResult : Ty.denote.{0, 0} M.Carrier result)
    (selector : Ty.denote.{0, 0} M.Carrier selectorType)
    (selectorAdmissible : M.adm selectorType selector) :
    M.ValuationAdmissible (valuation M falseResult trueResult selector) := by
  apply M.extend_admissible
  · apply M.extend_admissible
    · apply M.extend_admissible
      · intro _type impossible
        nomatch impossible
      · exact M.base_mem .result falseResult
    · exact M.base_mem .result trueResult
  · exact selectorAdmissible

def function (choice : M.HilbertChoice) (falseResult trueResult : Ty.denote.{0, 0} M.Carrier result) :
    Ty.denote.{0, 0} M.Carrier (boolean ⇒ result) :=
  M.denote selectorTerm (valuation M falseResult trueResult (choice.choose result))

theorem function_admissible (choice : M.HilbertChoice)
    (falseResult trueResult : Ty.denote.{0, 0} M.Carrier result) :
    M.adm (boolean ⇒ result) (function M choice falseResult trueResult) :=
  M.denote_admissible (valuation_admissible M falseResult trueResult _ (choice.choose_admissible result)) selectorTerm

theorem function_false (choice : M.HilbertChoice)
    (falseResult trueResult : Ty.denote.{0, 0} M.Carrier result) :
    function M choice falseResult trueResult ⟨False⟩ = falseResult := by
  let values : M.Valuation [selectorType, result, result] :=
    valuation M falseResult trueResult (choice.choose result)
  let predicate : Ty.denote.{0, 0} M.Carrier (result ⇒ boolean) :=
    M.denote predicateTerm (M.extend (σ := boolean) values ⟨False⟩)
  have predicateAdmissible : M.adm (result ⇒ boolean) predicate :=
    M.denote_admissible
      (M.extend_admissible
        (valuation_admissible M falseResult trueResult _ (choice.choose_admissible result)) (M.prop_mem _)) predicateTerm
  have witness : ∃ value, M.adm result value ∧ (predicate value).down := by
    refine ⟨falseResult, M.base_mem .result falseResult, ?_⟩
    change (False ∧ falseResult = trueResult) ∨ (¬False ∧ falseResult = falseResult)
    exact Or.inr ⟨not_false, rfl⟩
  have selected := choice.specified result predicate predicateAdmissible witness
  change (False ∧ choice.choose result predicate = trueResult) ∨
    (¬False ∧ choice.choose result predicate = falseResult) at selected
  rcases selected with impossible | selected
  · exact impossible.1.elim
  · exact selected.2

theorem function_true (choice : M.HilbertChoice)
    (falseResult trueResult : Ty.denote.{0, 0} M.Carrier result) :
    function M choice falseResult trueResult ⟨True⟩ = trueResult := by
  let values : M.Valuation [selectorType, result, result] :=
    valuation M falseResult trueResult (choice.choose result)
  let predicate : Ty.denote.{0, 0} M.Carrier (result ⇒ boolean) :=
    M.denote predicateTerm (M.extend (σ := boolean) values ⟨True⟩)
  have predicateAdmissible : M.adm (result ⇒ boolean) predicate :=
    M.denote_admissible
      (M.extend_admissible
        (valuation_admissible M falseResult trueResult _ (choice.choose_admissible result)) (M.prop_mem _)) predicateTerm
  have witness : ∃ value, M.adm result value ∧ (predicate value).down := by
    refine ⟨trueResult, M.base_mem .result trueResult, ?_⟩
    change (True ∧ trueResult = trueResult) ∨ (¬True ∧ trueResult = falseResult)
    exact Or.inl ⟨trivial, rfl⟩
  have selected := choice.specified result predicate predicateAdmissible witness
  change (True ∧ choice.choose result predicate = trueResult) ∨
    (¬True ∧ choice.choose result predicate = falseResult) at selected
  rcases selected with selected | impossible
  · exact selected.2
  · exact (impossible.1 trivial).elim

theorem models_recursion (choice : M.HilbertChoice) : M.models recursion := by
  intro falseResult _ trueResult _
  exact ⟨function M choice falseResult trueResult, function_admissible M choice falseResult trueResult,
    function_false M choice falseResult trueResult, function_true M choice falseResult trueResult⟩

end HenkinChoice

theorem models_recursion (Result : Type 1) : (model Result).models recursion := by
  classical
  intro falseResult _ trueResult _
  let function : ULift.{1} Prop → Result := fun value => if value.down then trueResult else falseResult
  refine ⟨function, trivial, ?_, ?_⟩
  · change function ⟨False⟩ = falseResult
    simp [function]
    rfl
  · change function ⟨True⟩ = trueResult
    simp [function]
    rfl

theorem models_induction (Result : Type 1) : (model Result).models induction := by
  intro predicate _ bases value _
  rcases proposition_cases value with same | same
  · subst value
    exact bases.1
  · subst value
    exact bases.2

theorem models_noConfusion (Result : Type 1) : (model Result).models noConfusion := by
  intro impossible
  exact impossible.mpr trivial

theorem models_cases (Result : Type 1) : (model Result).models cases := by
  intro value _
  rcases proposition_cases value with same | same
  · subst value
    exact Or.inl Iff.rfl
  · subst value
    exact Or.inr Iff.rfl

theorem models_finite (Result : Type 1) : (model Result).models finite := by
  intro function _ injective target _
  change (ULift.{1} Prop → ULift.{1} Prop) at function
  change ULift.{1} Prop at target
  have functionInjective : Function.Injective function := by
    intro first second same
    apply ULift.down_injective
    apply propext
    apply injective first trivial second trivial
    change (function first).down ↔ (function second).down
    rw [same]
  let : Finite (ULift.{1} Prop) := finite_propositions
  obtain ⟨source, same⟩ := Finite.surjective_of_injective functionInjective target
  refine ⟨source, trivial, ?_⟩
  change (function source).down ↔ target.down
  rw [same]

theorem all_models (Result : Type 1) (fact : Fact) : (model Result).models (formula fact) := by
  cases fact with
  | recursion => exact models_recursion Result
  | induction => exact models_induction Result
  | separation => exact models_noConfusion Result
  | cases => exact models_cases Result
  | finite => exact models_finite Result

#print axioms HenkinChoice.function_admissible
#print axioms HenkinChoice.function_false
#print axioms HenkinChoice.function_true
#print axioms HenkinChoice.models_recursion
#print axioms boolPropEquiv
#print axioms proposition_cases
#print axioms finite_propositions
#print axioms models_recursion
#print axioms models_induction
#print axioms models_noConfusion
#print axioms models_cases
#print axioms models_finite

end Mettapedia.Logic.HOL.BooleanFacts
