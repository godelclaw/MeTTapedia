import Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedEquationCompleteness
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness

open Mettapedia.OSLF.Framework

/-!
# Computable equation classes for the ordered rho constructor carriers

Process and name arguments use their proved canonical section. A parallel
argument is a collection value: its normal form retains the outer HashBag
wrapper, including the empty and singleton cases. The comparison below is
earned from actual authored equation chains on typed object arguments.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Rho.CarrierEquations

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedEquationCompleteness
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefCanonicalSection
open Mettapedia.GSLT.LanguageDef

def canonicalEquations : Setoid Pattern where
  r first second := canonicalize first = canonicalize second
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

/-- A collection representative, with no process-level wrapper collapse. -/
def bagArgument (source : Pattern) : Pattern :=
  .collection .hashBag (normalizeBagElements [canonicalize source]) none

def bagEquations : Setoid Pattern where
  r first second := bagArgument first = bagArgument second
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

theorem bag_argument_collapses (source : Pattern) :
    collapseBag (normalizeBagElements [canonicalize source]) = canonicalize source :=
  collapse_normalize_singleton_of_isCanonical (canonicalize_isCanonical source)

theorem bag_argument_eq_iff (first second : Pattern) :
    bagArgument first = bagArgument second ↔ canonicalize first = canonicalize second := by
  constructor
  · intro same
    have elements := (Pattern.collection.inj same).2.1
    exact (bag_argument_collapses first).symm.trans
      ((congrArg collapseBag elements).trans (bag_argument_collapses second))
  · intro same
    simp only [bagArgument, same]

theorem bag_argument_of_bag (elements : List Pattern) :
    bagArgument (.collection .hashBag elements none) =
      .collection .hashBag (normalizeBagElements (canonicalizeList elements)) none := by
  unfold bagArgument
  change Pattern.collection .hashBag
      (normalizeBagElements [collapseBag (normalizeBagElements (canonicalizeList elements))]) none = _
  rw [show [collapseBag (normalizeBagElements (canonicalizeList elements))] =
      collapseBag (normalizeBagElements (canonicalizeList elements)) :: [] from rfl,
    normalizeBagElements_collapse_cons _ [] (by
      rw [canonicalizeList_eq_map]
      apply isCanonicalList_of_forall
      intro member listed
      obtain ⟨original, _, rfl⟩ := List.mem_map.mp listed
      exact canonicalize_isCanonical original), List.append_nil]

theorem bag_argument_is_collection (source : Pattern) :
    ∃ elements, bagArgument source = .collection .hashBag elements none :=
  ⟨_, rfl⟩

theorem canonical_equations_proc_exact {free : FreeTypeContext} {bound : List TypeExpr}
    {first second : Pattern}
    (firstTyped : HasSort rhoCalc free bound first "Proc")
    (secondTyped : HasSort rhoCalc free bound second "Proc")
    (firstObject : isObjectPattern first = true)
    (secondObject : isObjectPattern second = true) :
    canonicalEquations.r first second ↔ CoreEquiv defaultBasePremises first second := by
  constructor
  · intro same
    have firstChain := coreEquiv_canonicalize_proc (base := defaultBasePremises)
      firstTyped firstObject
    have secondChain := coreEquiv_canonicalize_proc (base := defaultBasePremises)
      secondTyped secondObject
    change canonicalize first = canonicalize second at same
    rw [same] at firstChain
    exact .trans _ _ _ firstChain (.symm _ _ secondChain)
  · exact canonicalize_eq_of_coreEquiv

theorem canonical_equations_name_exact {free : FreeTypeContext} {bound : List TypeExpr}
    {first second : Pattern}
    (firstTyped : HasSort rhoCalc free bound first "Name")
    (secondTyped : HasSort rhoCalc free bound second "Name")
    (firstObject : isObjectPattern first = true)
    (secondObject : isObjectPattern second = true) :
    canonicalEquations.r first second ↔ CoreEquiv defaultBasePremises first second := by
  constructor
  · intro same
    have firstChain := coreEquiv_canonicalize_name (base := defaultBasePremises)
      firstTyped firstObject
    have secondChain := coreEquiv_canonicalize_name (base := defaultBasePremises)
      secondTyped secondObject
    change canonicalize first = canonicalize second at same
    rw [same] at firstChain
    exact .trans _ _ _ firstChain (.symm _ _ secondChain)
  · exact canonicalize_eq_of_coreEquiv

/-- Binding arguments compare their bodies in the actual extended Name
context. The binder wrapper remains part of the ordered argument. -/
theorem canonical_equations_binder_exact {free : FreeTypeContext} {bound : List TypeExpr}
    {binder : Option String} {first second : Pattern}
    (firstTyped : HasSort rhoCalc free (TypeExpr.name :: bound) first "Proc")
    (secondTyped : HasSort rhoCalc free (TypeExpr.name :: bound) second "Proc")
    (firstObject : isObjectPattern first = true)
    (secondObject : isObjectPattern second = true) :
    canonicalEquations.r (.lambda binder first) (.lambda binder second) ↔
      CoreEquiv defaultBasePremises (.lambda binder first) (.lambda binder second) := by
  constructor
  · intro related
    have bodies : canonicalEquations.r first second :=
      (Pattern.lambda.inj related).2
    exact equationEquiv_fill (.lambda binder .hole)
      ((canonical_equations_proc_exact firstTyped secondTyped firstObject secondObject).mp bodies)
  · exact canonicalize_eq_of_coreEquiv

/-- Normalization of a collection argument is a chain of child equations and
the authored parallel algebra. No outer empty/singleton collapse is used. -/
theorem bag_argument_equation_chain {free : FreeTypeContext} {bound : List TypeExpr}
    {elements : List Pattern}
    (typed : ElementsHaveType rhoCalc free bound elements TypeExpr.proc)
    (objects : isObjectPatternList elements = true) :
    CoreEquiv defaultBasePremises (.collection .hashBag elements none)
      (bagArgument (.collection .hashBag elements none)) := by
  rw [bag_argument_of_bag]
  have children := coreEquiv_canonicalizeList_procElements (base := defaultBasePremises)
    typed objects
  have converted := equationEquiv_collection_of_forall₂ .hashBag none children
  have normalized := coreEquiv_normalizeBagElements (base := defaultBasePremises)
    (canonicalize_procElementsHaveType typed objects)
  exact .trans _ _ _ converted normalized

theorem bag_equations_exact {free : FreeTypeContext} {bound : List TypeExpr}
    {first second : List Pattern}
    (firstTyped : ElementsHaveType rhoCalc free bound first TypeExpr.proc)
    (secondTyped : ElementsHaveType rhoCalc free bound second TypeExpr.proc)
    (firstObjects : isObjectPatternList first = true)
    (secondObjects : isObjectPatternList second = true) :
    bagEquations.r (.collection .hashBag first none) (.collection .hashBag second none) ↔
      CoreEquiv defaultBasePremises (.collection .hashBag first none)
        (.collection .hashBag second none) := by
  constructor
  · intro same
    have firstChain := bag_argument_equation_chain firstTyped firstObjects
    have secondChain := bag_argument_equation_chain secondTyped secondObjects
    change bagArgument _ = bagArgument _ at same
    rw [same] at firstChain
    exact .trans _ _ _ firstChain (.symm _ _ secondChain)
  · intro chain
    exact (bag_argument_eq_iff _ _).mpr (canonicalize_eq_of_coreEquiv chain)

#print axioms canonical_equations_proc_exact
#print axioms canonical_equations_name_exact
#print axioms canonical_equations_binder_exact
#print axioms bag_argument_equation_chain
#print axioms bag_equations_exact

end Mettapedia.OSLF.NativeTypes.Instances.Rho.CarrierEquations
