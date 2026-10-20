import Mettapedia.GSLT.LanguageDef.IndexedInductiveNatVec
import Mettapedia.Logic.HOL.SevenVirtues.Peano
import Mettapedia.Logic.HOL.NaturalFacts
import Mettapedia.Languages.HOLLight.NaturalFacts

/-!
# The authored natural carrier in the existing HOL Peano interpretation

The source is the sequentially admitted natural declaration. Its existing
polynomial eliminator supplies recursion; its established representation
proves induction and uniqueness. Zero and successor interpret the existing
HOL Peano formulas in a full-domain model. No natural-number fact is added
as an unchecked declaration or inferred for arbitrary inductive signatures.

The selected native arithmetic statements have this same constructed
interpretation. Native proof replay and exact statement comparison are a
separate qualification gate. Full polymorphic definition-history refinement,
Mathdata/MM0 translation and executable carrier representations retain their
own obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductiveNaturalHOL

open Mettapedia.TypeTheory.IndexedPolynomial
open Mettapedia.Logic
open IndexedInductiveNatVec HOL.SevenVirtues

universe v

/-- A consumer of the admitted eliminator, including the original recursive
child as the first argument of the successor method. -/
def recursionMethods {A : Type v} (zeroCase : A) (step : Natural.Carrier → A → A) :
    Algebra.Displayed (Algebra.initial Natural.polynomial) (fun _ _ _ => A) where
  act := by
    intro _ _ shape children hypotheses
    rcases shape with ⟨occurrence, shape⟩
    refine Fin.cases ?_ (fun occurrence => ?_) occurrence shape children hypotheses
    · intro _ _ _
      exact zeroCase
    · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) occurrence
      intro _ children hypotheses
      exact step (children none) (hypotheses none)

noncomputable def recurse {A : Type v} (zeroCase : A) (step : Natural.Carrier → A → A)
    (number : Natural.Carrier) : A :=
  (Natural.admitted.eliminate (recursionMethods zeroCase step)).toFun PUnit.unit () number

theorem recurse_zero {A : Type v} (zeroCase : A) (step : Natural.Carrier → A → A) :
    recurse zeroCase step Natural.zero = zeroCase := rfl

theorem recurse_succ {A : Type v} (zeroCase : A) (step : Natural.Carrier → A → A)
    (number : Natural.Carrier) :
    recurse zeroCase step (Natural.succ number) = step number (recurse zeroCase step number) := rfl

theorem recurse_unique {A : Type v} (zeroCase : A) (step : Natural.Carrier → A → A)
    (candidate : Natural.Carrier → A) (atZero : candidate Natural.zero = zeroCase)
    (atSucc : ∀ number, candidate (Natural.succ number) = step number (candidate number)) :
    candidate = recurse zeroCase step := by
  have numeral : ∀ count, candidate (Natural.fromNat count) =
      recurse zeroCase step (Natural.fromNat count) := by
    intro count
    induction count with
    | zero => exact atZero.trans (recurse_zero zeroCase step).symm
    | succ count ih =>
        change candidate (Natural.succ (Natural.fromNat count)) =
          recurse zeroCase step (Natural.succ (Natural.fromNat count))
        rw [atSucc, recurse_succ, ih]
  funext number
  simpa only [Natural.fromNat_toNat] using numeral (Natural.toNat number)

theorem recursion_exists_unique {A : Type v} (zeroCase : A) (step : Natural.Carrier → A → A) :
    ∃! function : Natural.Carrier → A,
      function Natural.zero = zeroCase ∧
        ∀ number, function (Natural.succ number) = step number (function number) := by
  refine ⟨recurse zeroCase step, ⟨recurse_zero _ _, recurse_succ _ _⟩, ?_⟩
  intro function equations
  exact recurse_unique zeroCase step function equations.1 equations.2

theorem induction (predicate : Natural.Carrier → Prop) (atZero : predicate Natural.zero)
    (atSucc : ∀ number, predicate number → predicate (Natural.succ number)) :
    ∀ number, predicate number := by
  have numeral : ∀ count, predicate (Natural.fromNat count) := by
    intro count
    induction count with
    | zero => exact atZero
    | succ count ih => exact atSucc _ ih
  intro number
  simpa only [Natural.fromNat_toNat] using numeral (Natural.toNat number)

/-- The carrier is the authored polynomial fixpoint, lifted solely to the
universe of the maintained HOL standard-model interface. -/
def peanoStructure : Metaphysics.PeanoStructure.{1} where
  carrier := ULift.{1} Natural.Carrier
  zero := ⟨Natural.zero⟩
  succ number := ⟨Natural.succ number.down⟩
  succ_inj := by
    intro first second same
    exact ULift.ext _ _ (Natural.succ_injective (congrArg ULift.down same))
  succ_ne_zero := by
    intro number same
    exact Natural.succ_ne_zero number.down (congrArg ULift.down same)
  induction := by
    intro subset atZero atSucc
    apply Set.eq_univ_of_forall
    rintro ⟨number⟩
    exact induction (fun number => (ULift.up number : ULift.{1} Natural.Carrier) ∈ subset)
      atZero (fun number inside => atSucc ⟨number⟩ inside) number

def model : HOL.HenkinModel.{0, 0, 0} Unit Peano.PeanoConst := Peano.standardOf peanoStructure

theorem fullDomains : model.FullDomains := Peano.standardOf_fullDomains peanoStructure

theorem models_axioms : ∀ formula ∈ Peano.axioms Peano.PeanoConst.zero Peano.PeanoConst.succ,
    model.models formula := Peano.standardOf_models peanoStructure

theorem models_noConfusion :
    model.models (Peano.zeroNotSucc Peano.PeanoConst.zero Peano.PeanoConst.succ) ∧
      model.models (Peano.succInjective Peano.PeanoConst.succ) := by
  obtain ⟨zero, successor, _⟩ := (Peano.models_axioms_iff _ _ model).mp models_axioms
  exact ⟨zero, successor⟩

theorem models_induction :
    model.models (Peano.induction Peano.PeanoConst.zero Peano.PeanoConst.succ) :=
  ((Peano.models_axioms_iff _ _ model).mp models_axioms).2.2

section RecursionFormula

open HOL

/-- The equations use the selected zero and successor, with the predecessor
available to the step function. This is an ordinary HOL formula schema. -/
def recursionEquations {context : Ctx Unit} {type : Ty Unit}
    (zeroCase : Term Peano.PeanoConst context type)
    (step : Term Peano.PeanoConst context (Peano.ι ⇒ type ⇒ type))
    (function : Term Peano.PeanoConst context (Peano.ι ⇒ type)) :
    Formula Peano.PeanoConst context :=
  .and (.eq (.app function (.const .zero)) zeroCase)
    (.all (.eq (.app (weaken function) (.app (.const .succ) (.var .vz)))
      (.app (.app (weaken step) (.var .vz)) (.app (weaken function) (.var .vz)))))

def recursionFormula (type : Ty Unit) : ClosedFormula Peano.PeanoConst :=
  .all (σ := type) (.all (σ := Peano.ι ⇒ type ⇒ type) (.ex (σ := Peano.ι ⇒ type)
    (.and (recursionEquations (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))
      (.all (σ := Peano.ι ⇒ type) (.imp
        (recursionEquations (.var (.vs (.vs (.vs .vz)))) (.var (.vs (.vs .vz))) (.var .vz))
        (.eq (.var .vz) (.var (.vs .vz))))))))

/-- Every target simple type has the source eliminator's unique recursive
function in this full-domain interpretation. No completeness or proof
extraction from this semantic theorem is assumed. -/
theorem models_recursion (type : Ty Unit) : model.models (recursionFormula type) := by
  intro zeroCase _ step _
  let function := fun number : model.Carrier () =>
    recurse zeroCase (fun number => step ⟨number⟩) number.down
  refine ⟨function, fullDomains _ _, ⟨?_, ?_⟩, ?_⟩
  · change model.Eqv type (recurse zeroCase (fun number => step ⟨number⟩) Natural.zero) zeroCase
    exact model.eqv_refl (fullDomains _ _)
  · intro number _
    change model.Eqv type
      (recurse zeroCase (fun number => step ⟨number⟩) (Natural.succ number.down))
      (step number (recurse zeroCase (fun number => step ⟨number⟩) number.down))
    exact model.eqv_refl (fullDomains _ _)
  · intro candidate _ equations
    have atZero : candidate ⟨Natural.zero⟩ = zeroCase :=
      model.eq_of_eqv_of_fullDomains fullDomains equations.1
    have atSucc : ∀ number, candidate ⟨Natural.succ number⟩ =
        step ⟨number⟩ (candidate ⟨number⟩) := by
      intro number
      exact model.eq_of_eqv_of_fullDomains fullDomains
        (equations.2 ⟨number⟩ (model.base_mem () ⟨number⟩))
    have same := recurse_unique zeroCase (fun number => step ⟨number⟩)
      (fun number => candidate ⟨number⟩) atZero atSucc
    have sameFunction : candidate = function := by
      funext number
      exact congrFun same number.down
    change model.Eqv (Peano.ι ⇒ type) candidate function
    rw [sameFunction]
    exact model.eqv_refl (fullDomains _ _)

end RecursionFormula

theorem infinite_carrier : Infinite Natural.Carrier := by
  exact Infinite.of_injective Natural.fromNat (fun _ _ same =>
    Natural.representation.symm.injective same)

/-- The equations also explicitly exclude collapse of the source successor
and zero; a finite one-point presentation cannot satisfy this interface. -/
theorem successor_zero_refused (number : Natural.Carrier) :
    ¬ (model.constDen Peano.PeanoConst.succ (ULift.up number) =
      model.constDen Peano.PeanoConst.zero) := by
  intro same
  exact Natural.succ_ne_zero number (congrArg ULift.down same)

namespace NativeFacts

/-- The source's actual carrier and operations, with an arbitrary simple
recursion-result carrier. Numeral wrapping denotes identity. -/
def model (result : Type 1) : HOL.HenkinModel.{0, 0, 0} HOL.NaturalFacts.Base HOL.NaturalFacts.Const :=
  HOL.NaturalFacts.model peanoStructure.zero peanoStructure.succ result

theorem models_recursion (result : Type 1) : (model result).models HOL.NaturalFacts.recursion := by
  apply (HOL.NaturalFacts.recursion_meaning _ _ _).mpr
  intro base step
  refine ⟨(fun number => recurse base (fun n value => step value ⟨n⟩) number.down), ?_, ?_⟩
  · exact recurse_zero _ _
  · intro number
    exact recurse_succ base (fun n value => step value ⟨n⟩) number.down

theorem models_induction (result : Type 1) : (model result).models HOL.NaturalFacts.induction := by
  apply (HOL.NaturalFacts.induction_meaning _ _ _).mpr
  intro predicate atZero atNext number
  exact IndexedInductiveNaturalHOL.induction (fun n => predicate ⟨n⟩) atZero
    (fun n => atNext ⟨n⟩) number.down

theorem models_noConfusion (result : Type 1) : (model result).models HOL.NaturalFacts.noConfusion :=
  (HOL.NaturalFacts.noConfusion_meaning _ _ _).mpr peanoStructure.succ_ne_zero

theorem models_successorInjective (result : Type 1) :
    (model result).models HOL.NaturalFacts.successorInjective :=
  (HOL.NaturalFacts.successorInjective_meaning _ _ _).mpr peanoStructure.succ_inj

theorem models_infinity (result : Type 1) : (model result).models HOL.NaturalFacts.infinity :=
  (HOL.NaturalFacts.infinity_meaning _ _ _).mpr
    ⟨peanoStructure.succ, peanoStructure.succ_inj, peanoStructure.zero, peanoStructure.succ_ne_zero⟩

/-- Every native root's intrinsic statement has the authored carrier's
constructed meaning, including the source recursion method's argument order. -/
theorem all_models (result : Type 1) (fact : Mettapedia.Languages.HOLLight.NaturalFacts.Fact) :
    (model result).models (Mettapedia.Languages.HOLLight.NaturalFacts.formula fact) := by
  cases fact with
  | recursion => exact models_recursion result
  | induction => exact models_induction result
  | zeroNotSuccessor => exact models_noConfusion result
  | successorInjective => exact models_successorInjective result
  | infinity => exact models_infinity result

/-- A nonconstant result carrier witnesses the recursion interpretation. -/
theorem boolean_recursion_witness :
    (recurse (⟨false⟩ : ULift.{1} Bool) (fun _ previous => ⟨!previous.down⟩) Natural.zero).down = false ∧
      (recurse (⟨false⟩ : ULift.{1} Bool) (fun _ previous => ⟨!previous.down⟩)
        (Natural.succ Natural.zero)).down = true := by
  constructor
  · rfl
  · rw [recurse_succ, recurse_zero]
    rfl

end NativeFacts

end Mettapedia.GSLT.LanguageDef.IndexedInductiveNaturalHOL
