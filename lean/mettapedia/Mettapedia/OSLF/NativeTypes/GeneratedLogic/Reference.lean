import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Semantics
import Mettapedia.OSLF.MeTTaIL.ReferenceStepEquations
import Mettapedia.GSLT.LanguageDef.WellSorted

/-!
# The native structure of a language

A language's terms carry its generated logic (`referenceStructure`). Its elements are the language's
object terms: patterns without a pending explicit substitution or an open collection tail, which occur
only in rule schemas (`IsObject`). Its states are the closed object terms (`IsState`). Terms are read
modulo the equations, through object terms (`ObjectEquivalent`).
- A step is a reference step between states, taken by an equivalent closed redex. A rule label admits
  the steps whose witness fires that rule. A site label `under i l` admits the steps of rule `i` that
  have a premise step admitted by `l`. A chain of site labels therefore follows a step through the
  contexts that congruence rules provide, down to the rule that fires.
- An object term is built by a constructor, split, empty, a singleton, an abstraction or a bound
  variable when some equivalent term has that shape. Bodies of abstractions are open object terms, so
  they have shapes but no steps.
- An object term has a type when some equivalent term is a closed object term of that type, and a term
  names the object terms equivalent to it. Two terms are the same element when they are equivalent.
- A body is applied to an argument by instantiating its outermost bound variable.

Types are those of closed terms, so the quantifiers `someOf` and `everyOf` range over the closed terms
of a type. An abstraction's body is open, so its type is read through the hom formers. The past
modalities range over states only: a schema pattern is not a predecessor.

Every relation is read through the equivalence, so native types do not depend on the representative
chosen (`Invariance`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.GSLT.LanguageDef.WellSorted (OpenPatternWellSorted FreeTypeContext isObjectPattern)

/-- The rule a step witness fires. -/
def ruleOf : Witness → Option ℕ
  | .rule index _ _ => some index
  | _ => none

mutual
/-- The step witnesses a premise witness contains, including those for each element of a quantified
premise. -/
def premiseSteps : Witness → List Witness
  | .premiseStep step _ _ _ => [step]
  | .forAll bodies => premiseStepsList bodies
  | _ => []

/-- The step witnesses among a list of premise witnesses. -/
def premiseStepsList : List Witness → List Witness
  | [] => []
  | witness :: witnesses => premiseSteps witness ++ premiseStepsList witnesses
end

/-- Whether a step label admits a step with this witness. -/
def StepLabel.admits : StepLabel → Witness → Bool
  | .any, _ => true
  | .rule index, witness => ruleOf witness == some index
  | .under index label, .rule index' _ premises =>
    index' == index && (premiseStepsList premises).any label.admits
  | .under _ _, _ => false

/-! ## Object terms and states -/

/-- **An object term**: no pending explicit substitution and no open collection tail. -/
abbrev IsObject (pattern : Pattern) : Prop := isObjectPattern pattern = true

/-- **A state**: a closed object term. -/
abbrev IsState (pattern : Pattern) : Prop := pattern.isWellScopedAt 0 = true ∧ IsObject pattern

/-- One equation step between object terms. -/
def ObjectStep (relEnv : RelationEnv) (language : LanguageDef) (first second : Pattern) : Prop :=
  IsObject first ∧ IsObject second ∧ EquationStep relEnv language first second

/-- **Equivalence of object terms modulo the equations**, through object terms. -/
def ObjectEquivalent (relEnv : RelationEnv) (language : LanguageDef) : Pattern → Pattern → Prop :=
  Relation.EqvGen (ObjectStep relEnv language)

variable {relEnv : RelationEnv} {language : LanguageDef}

theorem ObjectEquivalent.equivalence : Equivalence (ObjectEquivalent relEnv language) :=
  Relation.EqvGen.is_equivalence _

/-- Equivalent object terms are equal or both object terms. -/
theorem ObjectEquivalent.objects {first second : Pattern} (equivalent : ObjectEquivalent relEnv language first second) :
    first = second ∨ (IsObject first ∧ IsObject second) := by
  induction equivalent with
  | rel _ _ step => exact Or.inr ⟨step.1, step.2.1⟩
  | refl => exact Or.inl rfl
  | symm _ _ _ previous =>
    rcases previous with same | ⟨first, second⟩
    · exact Or.inl same.symm
    · exact Or.inr ⟨second, first⟩
  | trans _ _ _ _ _ first second =>
    rcases first with rfl | ⟨firstObject, middleObject⟩
    · exact second
    · rcases second with rfl | ⟨-, secondObject⟩
      · exact Or.inr ⟨firstObject, middleObject⟩
      · exact Or.inr ⟨firstObject, secondObject⟩

/-- An object term is equivalent only to object terms. -/
theorem ObjectEquivalent.object_right {first second : Pattern}
    (equivalent : ObjectEquivalent relEnv language first second) (object : IsObject first) : IsObject second := by
  rcases equivalent.objects with rfl | ⟨-, secondObject⟩
  · exact object
  · exact secondObject

/-- Equivalence through object terms is equivalence. -/
theorem ObjectEquivalent.equivalent {first second : Pattern}
    (equivalent : ObjectEquivalent relEnv language first second) : Equivalent relEnv language first second :=
  Relation.EqvGen.mono (fun _ _ step => step.2.2) _ _ equivalent

/-- **In an equation-free language, equivalence of object terms is equality.** -/
theorem objectEquivalent_iff_eq_of_isEquationFree (free : language.isEquationFree = true) {first second : Pattern} :
    ObjectEquivalent relEnv language first second ↔ first = second :=
  ⟨fun equivalent => (equivalent_iff_eq_of_isEquationFree free).mp equivalent.equivalent,
    fun same => same ▸ Relation.EqvGen.refl _⟩

variable (relEnv language)

/-- **The native structure of a language**: its object terms modulo its equations, with its reference
steps between states. -/
def referenceStructure : NativeStructure Pattern where
  step source label target := IsState source ∧ IsState target ∧ ∃ redex contractum witness,
    ObjectEquivalent relEnv language source redex ∧ IsState redex ∧ StepValid relEnv language redex witness contractum ∧
      IsState contractum ∧ ObjectEquivalent relEnv language contractum target ∧ label.admits witness = true
  built element constructor parts := IsObject element ∧ ObjectEquivalent relEnv language element (.apply constructor parts)
  split element kind first second := IsObject element ∧ ∃ left right,
    ObjectEquivalent relEnv language element (.collection kind (left ++ right) none) ∧
      first = .collection kind left none ∧ second = .collection kind right none
  empty element kind := IsObject element ∧ ObjectEquivalent relEnv language element (.collection kind [] none)
  single element kind member := IsObject element ∧
    ObjectEquivalent relEnv language element (.collection kind [member] none)
  body element inner := IsObject element ∧ ∃ name, ObjectEquivalent relEnv language element (.lambda name inner)
  multiBody element arity inner := IsObject element ∧
    ∃ names, ObjectEquivalent relEnv language element (.multiLambda arity names inner)
  bound element index := IsObject element ∧ ObjectEquivalent relEnv language element (.bvar index)
  typed element type := IsObject element ∧ ∃ representative, ObjectEquivalent relEnv language element representative ∧
    OpenPatternWellSorted language FreeTypeContext.empty [] type representative
  named element term := IsObject element ∧ ObjectEquivalent relEnv language element term
  same first second := ObjectEquivalent relEnv language first second
  apply inner value := Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVar value inner

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
