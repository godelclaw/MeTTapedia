import Mettapedia.OSLF.Syntax.BindingPredicateFutureLogic
import Mathlib.Data.Bool.Basic

/-!
# Boolean guard compatibility on the full substitution base

A current decision commutes with every semantic substitution exactly when
positive membership reflects. The complete Boolean natural transformation
is then constructed, rather than inferred from pointwise decisions.

Singleton contexts represent programs. Consequently every natural readout
from one program sort into a constant presheaf is constant on all terms.
A predicate with an admitted and an excluded term therefore has no such
Boolean guard. Its generic variable satisfies neither the native predicate
nor its Heyting negation. This does not prohibit local executable decisions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.BindingPredicateBooleanGuard

open _root_.CategoryTheory FreeBindingTerms BindingSubstitutionAlgebra
open BindingConstructorPredicates IntrinsicScopedConditionalPresheaf
open BindingPredicateFutureLogic
open Mettapedia.GSLT.LanguageDef.MultiSortedClone

universe u
variable {S : Signature} {A : BindingCloneAlgebra.Algebra.{u} S} {sort : S.Srt}

def pointEnvironment {context : Ctx S} (value : A.substitution.Carrier context sort) :
    Environment S A.substitution.Carrier [sort] context :=
  fun _ position => match position with
    | .zero => value
    | .succ impossible => nomatch impossible

def genericVariable : A.substitution.Carrier [sort] sort :=
  A.substitution.injectVar .zero

@[simp] theorem instantiate_generic {context : Ctx S}
    (value : A.substitution.Carrier context sort) :
    A.substitution.substitute (pointEnvironment value) (genericVariable (A := A)) = value :=
  A.substitution.substitute_var (pointEnvironment value) .zero

/-- Both examples live in the same predicate family, but need not share an
ambient context. The generic variable can be instantiated to either. -/
theorem generic_variable_has_neither (predicate : Predicate A sort)
    {first last : Ctx S} (member : A.substitution.Carrier first sort)
    (excluded : A.substitution.Carrier last sort)
    (admitted : predicate.holds member) (absent : ¬ predicate.holds excluded) :
    ¬ predicate.holds (genericVariable (A := A)) ∧
      ¬ (nativeNegation predicate).holds (genericVariable (A := A)) := by
  constructor
  · intro generic
    apply absent
    simpa only [instantiate_generic] using
      predicate.substitute (pointEnvironment excluded) _ generic
  · intro negative
    have future := negative first (pointEnvironment member)
    rw [instantiate_generic] at future
    exact future admitted

theorem nontrivial_predicate_does_not_reflect (predicate : Predicate A sort)
    {first last : Ctx S} (member : A.substitution.Carrier first sort)
    (excluded : A.substitution.Carrier last sort)
    (admitted : predicate.holds member) (absent : ¬ predicate.holds excluded) :
    ¬ ReflectsMembership predicate := by
  intro reflection
  have generic := reflection (pointEnvironment member) (genericVariable (A := A))
    (by simpa only [instantiate_generic] using admitted)
  exact (generic_variable_has_neither predicate member excluded admitted absent).1 generic

/-- Representability forces every readout into an independently supplied
constant presheaf to take one value, even across different contexts. -/
theorem constant_readout (Output : Type u)
    (readout : semanticPrograms A sort ⟶ (Functor.const (Base A)).obj Output)
    {context : Ctx S} (value : A.substitution.Carrier context sort) :
    readout.app (Opposite.op (ContextObject.ofList A.substitution.toClone context)) value =
      readout.app (Opposite.op (ContextObject.ofList A.substitution.toClone [sort]))
        (genericVariable (A := A)) := by
  let source : Base A := Opposite.op (ContextObject.ofList A.substitution.toClone [sort])
  let target : Base A := Opposite.op (ContextObject.ofList A.substitution.toClone context)
  let change : source ⟶ target := Quiver.Hom.op
    (A.substitution.toClone.operationAsSingletonMorphism value)
  have natural := readout.naturality_apply change (genericVariable (A := A))
  change readout.app target
      (A.substitution.substitute (fromPositions [sort]
        (A.substitution.toClone.operationAsSingletonMorphism value))
        (A.substitution.injectVar .zero)) = _ at natural
  rw [A.substitution.substitute_var] at natural
  exact natural

variable (predicate : Predicate A sort)
variable [∀ context : Ctx S, DecidablePred (predicate.holds (Γ := context))]

def decision {context : Ctx S} (value : A.substitution.Carrier context sort) : Bool :=
  decide (predicate.holds value)

theorem decision_natural_iff :
    (∀ {source target : Ctx S} (env : Environment S A.substitution.Carrier source target)
      (value : A.substitution.Carrier source sort),
        decision predicate (A.substitution.substitute env value) = decision predicate value) ↔
      ReflectsMembership predicate := by
  constructor
  · intro natural source target env value member
    have future : decision predicate (A.substitution.substitute env value) = true :=
      by simp only [decision, decide_eq_true_eq]; exact member
    exact of_decide_eq_true ((natural env value).symm.trans future)
  · intro reflection source target env value
    exact decide_eq_decide.mpr ⟨reflection env value, predicate.substitute env value⟩

def booleans : Base A ⥤ Type u :=
  (Functor.const (Base A)).obj (ULift.{u} Bool)

/-- A compatible current guard supplies the complete natural map. The
compatibility hypothesis is independently shown impossible for nontrivial
predicates over the full substitution base. -/
def decisionTransformation (reflection : ReflectsMembership predicate) :
    semanticPrograms A sort ⟶ booleans (A := A) where
  app _ := TypeCat.ofHom fun value => ⟨decision predicate value⟩
  naturality first last change := by
    apply ConcreteCategory.hom_ext
    intro value
    apply ULift.ext
    exact ((decision_natural_iff predicate).mpr reflection)
      (fromPositions first.unop.context change.unop) value

/-- Calibration of a putative Boolean map on every term fails for a
nontrivial predicate; equal current values are not a substitute for this
whole-family comparison. -/
theorem no_calibrated_boolean_transformation
    {first last : Ctx S} (member : A.substitution.Carrier first sort)
    (excluded : A.substitution.Carrier last sort)
    (admitted : predicate.holds member) (absent : ¬ predicate.holds excluded) :
    ¬ ∃ readout : semanticPrograms A sort ⟶ booleans (A := A),
      ∀ {context : Ctx S} (value : A.substitution.Carrier context sort),
        (readout.app (Opposite.op (ContextObject.ofList A.substitution.toClone context)) value).down =
          decision predicate value := by
  rintro ⟨readout, calibrated⟩
  have same := (constant_readout _ readout member).trans
    (constant_readout _ readout excluded).symm
  have bits : decision predicate member = decision predicate excluded :=
    (calibrated member).symm.trans ((congrArg ULift.down same).trans (calibrated excluded))
  have positive : decision predicate member = true := by simp [decision, admitted]
  have negative : decision predicate excluded = false := by simp [decision, absent]
  rw [positive, negative] at bits
  cases bits

end Mettapedia.OSLF.Binding.BindingPredicateBooleanGuard
