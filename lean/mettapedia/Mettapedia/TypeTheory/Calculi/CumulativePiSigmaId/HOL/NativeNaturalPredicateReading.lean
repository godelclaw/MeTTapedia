import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorFamilies
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLInterface
import Mettapedia.Logic.HOL.PredicateProducts
import Mettapedia.Logic.HOL.NaturalRecursionProofs

/-!
# A predicate reading of the original natural eliminator telescope

The original natural declarations, dependent products and open computation
rows are read into HOL terms. A selected simple result carrier represents
the motive universe by predicates on that carrier. This is an explicitly
indexed reading of the natural telescope, not a model of all cumulative
universes or a total erasure of arbitrary dependent types.

The eliminator denotes the actual selected HOL recursor. Its method adapter
converts the original predecessor-before-result order to HOL Light's
result-before-predecessor order. Renaming and substitution operate on the
original presentation terms and the existing HOL syntax.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation NativeNaturalVectorFamilies
open FormationSensitiveHOLInterface (variableIndex)

universe u v

structure Operations (Base : Type u) (Const : HOL.Ty Base → Type v) where
  number : HOL.Ty Base
  result : HOL.Ty Base
  zero : HOL.ClosedTerm Const number
  successor : HOL.ClosedTerm Const (.arr number number)
  selection : HOL.ClosedTerm Const (HOL.SelectionProofs.Selection (.arr number result))

variable {Base : Type u} {Const : HOL.Ty Base → Type v}

namespace Operations

def motiveType (operations : Operations Base Const) : HOL.Ty Base :=
  .arr operations.number (.arr operations.result .prop)

def methodType (operations : Operations Base Const) : HOL.Ty Base :=
  .arr operations.number (.arr operations.result operations.result)

def eliminatorType (operations : Operations Base Const) : HOL.Ty Base :=
  .arr operations.motiveType (.arr operations.result
    (.arr operations.methodType (.arr operations.number operations.result)))

def flip (operations : Operations Base Const) {Γ : HOL.Ctx Base}
    (method : HOL.Term Const Γ operations.methodType) :
    HOL.Term Const Γ (HOL.NaturalRecursionProofs.Method operations.number operations.result) :=
  .lam (.lam (.app (.app (HOL.weaken (HOL.weaken method)) (.var .vz)) (.var (.vs .vz))))

def recursion (operations : Operations Base Const) {Γ : HOL.Ctx Base}
    (base : HOL.Term Const Γ operations.result)
    (method : HOL.Term Const Γ operations.methodType) :
    HOL.Term Const Γ (.arr operations.number operations.result) :=
  HOL.NaturalRecursionProofs.recursor (HOL.weakenCtx Γ operations.selection)
    (HOL.weakenCtx Γ operations.zero) (HOL.weakenCtx Γ operations.successor)
    base (operations.flip method)

def eliminator (operations : Operations Base Const) {Γ : HOL.Ctx Base} :
    HOL.Term Const Γ operations.eliminatorType :=
  .lam (.lam (.lam (operations.recursion (.var (.vs .vz)) (.var .vz))))

@[simp] theorem rename_flip (operations : Operations Base Const) {Γ Ξ : HOL.Ctx Base}
    (ρ : HOL.Rename Base Γ Ξ) (method : HOL.Term Const Γ operations.methodType) :
    HOL.rename ρ (operations.flip method) = operations.flip (HOL.rename ρ method) := by
  simp only [flip, HOL.rename, HOL.weaken, HOL.rename_comp]
  congr 3

@[simp] theorem subst_flip (operations : Operations Base Const) {Γ Ξ : HOL.Ctx Base}
    (θ : HOL.Subst Const Γ Ξ) (method : HOL.Term Const Γ operations.methodType) :
    HOL.subst θ (operations.flip method) = operations.flip (HOL.subst θ method) := by
  simp [flip, HOL.subst, HOL.subst_weaken, HOL.Subst.lift, HOL.Rename.weaken]


@[simp] theorem subst_recursion (operations : Operations Base Const) {Γ Ξ : HOL.Ctx Base}
    (θ : HOL.Subst Const Γ Ξ) (base : HOL.Term Const Γ operations.result)
    (method : HOL.Term Const Γ operations.methodType) :
    HOL.subst θ (operations.recursion base method) =
      operations.recursion (HOL.subst θ base) (HOL.subst θ method) := by
  simp [recursion, HOL.NaturalRecursionProofs.recursor, HOL.SelectionProofs.selected,
    HOL.subst, HOL.NaturalRecursionProofs.subst_body, HOL.subst_weakenCtx]

@[simp] theorem rename_recursion (operations : Operations Base Const) {Γ Ξ : HOL.Ctx Base}
    (ρ : HOL.Rename Base Γ Ξ) (base : HOL.Term Const Γ operations.result)
    (method : HOL.Term Const Γ operations.methodType) :
    HOL.rename ρ (operations.recursion base method) =
      operations.recursion (HOL.rename ρ base) (HOL.rename ρ method) := by
  simpa only [HOL.subst_ofRename] using operations.subst_recursion (HOL.Subst.ofRename ρ) base method

@[simp] theorem rename_eliminator (operations : Operations Base Const) {Γ Ξ : HOL.Ctx Base}
    (ρ : HOL.Rename Base Γ Ξ) :
    HOL.rename ρ operations.eliminator = (operations.eliminator : HOL.Term Const Ξ _) := by
  simp [eliminator, HOL.rename, HOL.Rename.lift]

@[simp] theorem subst_eliminator (operations : Operations Base Const) {Γ Ξ : HOL.Ctx Base}
    (θ : HOL.Subst Const Γ Ξ) :
    HOL.subst θ operations.eliminator = (operations.eliminator : HOL.Term Const Ξ _) := by
  simp [eliminator, HOL.subst, HOL.Subst.lift, HOL.Rename.weaken]

end Operations

/-- The reading is indexed by the selected simple carrier. Its rules compute
the target from the original source constructors; no root soundness law is
assumed as a field. -/
inductive Reads (operations : Operations Base Const) :
    {Γ : HOL.Ctx Base} → {type : HOL.Ty Base} →
      Tower.Tm Γ.length → HOL.Term Const Γ type → Prop where
  | var {Γ : HOL.Ctx Base} {type : HOL.Ty Base} (index : HOL.Var Γ type) :
      Reads operations (.var (variableIndex index)) (.var index)
  | natural {Γ : HOL.Ctx Base} :
      Reads operations (natTm : Tower.Tm Γ.length) (HOL.PredicateProducts.full operations.number)
  | zero {Γ : HOL.Ctx Base} :
      Reads operations (zeroTm : Tower.Tm Γ.length) (HOL.weakenCtx Γ operations.zero)
  | successor {Γ : HOL.Ctx Base} :
      Reads operations (.const succName : Tower.Tm Γ.length) (HOL.weakenCtx Γ operations.successor)
  | motiveUniverse {Γ : HOL.Ctx Base} :
      Reads operations (sortTm motiveLevel : Tower.Tm Γ.length)
        (HOL.PredicateProducts.full (.arr operations.result .prop))
  | eliminator {Γ : HOL.Ctx Base} :
      Reads operations (.const natEliminateName : Tower.Tm Γ.length)
        (operations.eliminator (Γ := Γ))
  | application {Γ : HOL.Ctx Base} {domain codomain : HOL.Ty Base}
      {function argument : Tower.Tm Γ.length}
      {functionCode : HOL.Term Const Γ (.arr domain codomain)}
      {argumentCode : HOL.Term Const Γ domain} :
      Reads operations function functionCode → Reads operations argument argumentCode →
      Reads operations (.app function argument) (.app functionCode argumentCode)
  | abstraction {Γ : HOL.Ctx Base} {domain codomain : HOL.Ty Base}
      {body : Tower.Tm (domain :: Γ).length} {code : HOL.Term Const (domain :: Γ) codomain} :
      Reads operations body code → Reads operations (.lam body) (.lam code)
  | product {Γ : HOL.Ctx Base} {domain codomain : HOL.Ty Base}
      {sourceDomain : Tower.Tm Γ.length} {sourceFamily : Tower.Tm (domain :: Γ).length}
      {domainCode : HOL.Term Const Γ (.arr domain .prop)}
      {familyCode : HOL.Term Const (domain :: Γ) (.arr codomain .prop)} :
      Reads operations sourceDomain domainCode → Reads operations sourceFamily familyCode →
      Reads operations (.pi sourceDomain sourceFamily) (HOL.PredicateProducts.pi domainCode familyCode)

namespace Reads

theorem rename {operations : Operations Base Const}
    {Γ Ξ : HOL.Ctx Base} {type : HOL.Ty Base}
    {source : Tower.Tm Γ.length} {code : HOL.Term Const Γ type}
    (reading : Reads operations source code)
    (ρ : HOL.Rename Base Γ Ξ) (raw : Ren Γ.length Ξ.length)
    (compatible : ∀ {type} (index : HOL.Var Γ type),
      variableIndex (ρ index) = raw (variableIndex index)) :
    Reads operations (Presentation.rename raw source) (HOL.rename ρ code) := by
  induction reading generalizing Ξ with
  | var index => simpa only [Presentation.rename, HOL.rename, compatible] using Reads.var (ρ index)
  | natural => simpa only [rename_natTm, HOL.PredicateProducts.rename_full] using (Reads.natural (Γ := Ξ))
  | zero => simpa only [zeroTm, Presentation.rename, HOL.rename_weakenCtx] using (Reads.zero (Γ := Ξ))
  | successor => simpa only [Presentation.rename, HOL.rename_weakenCtx] using (Reads.successor (Γ := Ξ))
  | motiveUniverse => exact .motiveUniverse
  | eliminator => simpa only [Presentation.rename, Operations.rename_eliminator] using (Reads.eliminator (Γ := Ξ))
  | application first second firstIH secondIH => exact .application (firstIH ρ raw compatible) (secondIH ρ raw compatible)
  | abstraction body ih =>
      apply Reads.abstraction
      apply ih (HOL.Rename.lift ρ) (liftRen raw)
      intro type index
      cases index with
      | vz => rfl
      | vs prior => exact congrArg Fin.succ (compatible prior)
  | product domain family domainIH familyIH =>
      rw [HOL.PredicateProducts.rename_pi]
      apply Reads.product (domainIH ρ raw compatible)
      apply familyIH (HOL.Rename.lift ρ) (liftRen raw)
      intro type index
      cases index with
      | vz => rfl
      | vs prior => exact congrArg Fin.succ (compatible prior)

theorem substitute {operations : Operations Base Const}
    {Γ Ξ : HOL.Ctx Base} {type : HOL.Ty Base}
    {source : Tower.Tm Γ.length} {code : HOL.Term Const Γ type}
    (reading : Reads operations source code)
    (θ : HOL.Subst Const Γ Ξ) (raw : Sub Tower.Head Γ.length Ξ.length)
    (components : ∀ {type} (index : HOL.Var Γ type),
      Reads operations (raw (variableIndex index)) (θ index)) :
    Reads operations (Presentation.subst raw source) (HOL.subst θ code) := by
  induction reading generalizing Ξ with
  | var index => exact components index
  | natural => simpa only [subst_natTm, HOL.PredicateProducts.subst_full] using (Reads.natural (Γ := Ξ))
  | zero => simpa only [zeroTm, Presentation.subst, HOL.subst_weakenCtx] using (Reads.zero (Γ := Ξ))
  | successor => simpa only [Presentation.subst, HOL.subst_weakenCtx] using (Reads.successor (Γ := Ξ))
  | motiveUniverse => exact .motiveUniverse
  | eliminator => simpa only [Presentation.subst, Operations.subst_eliminator] using (Reads.eliminator (Γ := Ξ))
  | application first second firstIH secondIH => exact .application (firstIH θ raw components) (secondIH θ raw components)
  | abstraction body ih =>
      apply Reads.abstraction
      apply ih (HOL.Subst.lift θ) (liftSub raw)
      intro type index
      cases index with
      | vz => exact .var .vz
      | vs prior => exact (components prior).rename HOL.Rename.weaken wk (fun _ => rfl)
  | product domain family domainIH familyIH =>
      rw [HOL.PredicateProducts.subst_pi]
      apply Reads.product (domainIH θ raw components)
      apply familyIH (HOL.Subst.lift θ) (liftSub raw)
      intro type index
      cases index with
      | vz => exact .var .vz
      | vs prior => exact (components prior).rename HOL.Rename.weaken wk (fun _ => rfl)

end Reads

#print axioms Reads.rename
#print axioms Reads.substitute

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
