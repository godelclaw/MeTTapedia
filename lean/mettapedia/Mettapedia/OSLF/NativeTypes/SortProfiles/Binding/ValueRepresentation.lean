import Mettapedia.GSLT.LanguageDef.BindingSignatureValuation

open Mettapedia.OSLF.Framework

/-!
# Full function readouts determine binding semantic values

The declaration-derived valuation model contains natural families at every
stage. Naturality at the generic ordered context determines the complete
family from its function readout. This representation keeps arbitrary
function-valued dependencies and supports closing open values at each actual
ordered valuation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.Binding.ValueRepresentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open _root_.CategoryTheory

universe u

variable {language : LanguageDef} {base : String → Type u}

theorem value_factors_through_context
    (constructors : Valuation.Constructors language base)
    {bound : List TypeExpr} {type : TypeExpr}
    (value : (Valuation.algebra constructors).substitution.Carrier bound type)
    (stage : Type u) (point : stage ⟶ PUnit.{u + 1})
    (environment : (Valuation.model constructors).Env stage bound) :
    value.value stage point environment =
      (Valuation.model constructors).tupleEnv environment ≫
        TypeCat.ofHom (Valuation.readContext constructors value) := by
  let genericPoint : Valuation.Context language base bound ⟶ PUnit.{u + 1} :=
    TypeCat.ofHom fun _ => PUnit.unit
  have samePoint : (Valuation.model constructors).tupleEnv environment ≫ genericPoint = point := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext entry
    exact Subsingleton.elim _ _
  have sameEnvironment :
      (Valuation.model constructors).restage
          ((Valuation.model constructors).tupleEnv environment)
          ((Valuation.model constructors).projections bound) = environment := by
    funext sort position
    exact (Valuation.model constructors).tupleEnv_projectVar environment position
  have natural := value.natural ((Valuation.model constructors).tupleEnv environment)
    genericPoint ((Valuation.model constructors).projections bound)
  rw [samePoint, sameEnvironment] at natural
  exact natural

theorem ofFunction_readContext
    (constructors : Valuation.Constructors language base)
    {bound : List TypeExpr} {type : TypeExpr}
    (value : (Valuation.algebra constructors).substitution.Carrier bound type) :
    Valuation.ofFunction constructors (Valuation.readContext constructors value) = value := by
  apply Model.ElemOver.ext
  funext stage point environment
  exact (value_factors_through_context constructors value stage point environment).symm

theorem readContext_injective
    (constructors : Valuation.Constructors language base)
    {bound : List TypeExpr} {type : TypeExpr} :
    Function.Injective
      (Valuation.readContext constructors (Γ := bound) (sort := type)) := by
  intro first second same
  rw [← ofFunction_readContext constructors first, ← ofFunction_readContext constructors second, same]

theorem readContext_eq_read
    (constructors : Valuation.Constructors language base)
    {bound : List TypeExpr} {type : TypeExpr}
    (value : (Valuation.algebra constructors).substitution.Carrier bound type)
    (assignment : Valuation.Context language base bound) :
    Valuation.readContext constructors value assignment =
      Valuation.read constructors value
        (fun sort position => (Valuation.model constructors).projections bound sort position assignment) := by
  let atAssignment : PUnit.{u + 1} ⟶ Valuation.Context language base bound :=
    TypeCat.ofHom fun _ => assignment
  have natural := value.natural atAssignment
    (TypeCat.ofHom fun _ => PUnit.unit) ((Valuation.model constructors).projections bound)
  exact (congrArg (fun reading => reading PUnit.unit) natural).symm

def closeAt (constructors : Valuation.Constructors language base)
    {bound : List TypeExpr} (assignment : Valuation.Context language base bound) :
    BindingSubstitutionAlgebra.Environment (signatureOf language)
      (Valuation.algebra constructors).substitution.Carrier bound [] :=
  fun sort position => Valuation.ofFunction constructors
    (fun _ => (Valuation.model constructors).projections bound sort position assignment)

theorem read_closeAt
    (constructors : Valuation.Constructors language base)
    {bound : List TypeExpr} (assignment : Valuation.Context language base bound)
    (sort : TypeExpr) (position : Var bound sort) :
    Valuation.read constructors (closeAt constructors assignment sort position)
        (fun _ impossible => nomatch impossible) =
      (Valuation.model constructors).projections bound sort position assignment := rfl

theorem closed_readout
    (constructors : Valuation.Constructors language base)
    {bound : List TypeExpr} {type : TypeExpr}
    (value : (Valuation.algebra constructors).substitution.Carrier bound type)
    (assignment : Valuation.Context language base bound) :
    Valuation.readContext constructors value assignment =
      Valuation.read constructors
        ((Valuation.algebra constructors).substitution.substitute
          (closeAt constructors assignment) value) (fun _ impossible => nomatch impossible) := by
  rw [Valuation.read_substitute, readContext_eq_read]
  rfl

theorem equal_of_all_closings
    (constructors : Valuation.Constructors language base)
    {bound : List TypeExpr} {type : TypeExpr}
    {first second : (Valuation.algebra constructors).substitution.Carrier bound type}
    (closed : ∀ assignment : Valuation.Context language base bound,
      (Valuation.algebra constructors).substitution.substitute (closeAt constructors assignment) first =
        (Valuation.algebra constructors).substitution.substitute (closeAt constructors assignment) second) :
    first = second := by
  apply readContext_injective constructors
  funext assignment
  rw [closed_readout constructors first assignment, closed_readout constructors second assignment,
    closed assignment]

end Mettapedia.OSLF.NativeTypes.SortProfiles.Binding.ValueRepresentation
