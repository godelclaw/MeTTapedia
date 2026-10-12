import Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.FiniteBinding
import Mettapedia.OSLF.NativeTypes.SortProfiles.Binding.ValueRepresentation
import Mettapedia.OSLF.NativeTypes.SortProfiles.Binding.EmptyAmbient
import Mettapedia.OSLF.Syntax.BindingEquationInterpretation

open Mettapedia.OSLF.Framework

/-!
# Finite binding checks imply full contextual equation stability

The finite checker enumerates complete functions on declared dependency
contexts. Naturality identifies these functions with all dependency values
of the binding model. Closing each captured context then proves every
contextual equation instance, with arbitrary ordinary substitutions and
every operator's actual binders. Existing congruence soundness consequently
applies to all descendants of each accepted source equation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.Binding.CenterStability

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FreeBindingTerms
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.OSLF.Binding.BindingEquationalModels
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.FiniteBinding
open Mettapedia.OSLF.NativeTypes.SortProfiles.Binding.ValueRepresentation Mettapedia.OSLF.NativeTypes.SortProfiles.Binding.EmptyAmbient

variable {language : LanguageDef}

theorem dependency_values_equal
    (constructors : Constructors language)
    (metas : List (MetaArity (signatureOf language)))
    {bound : List TypeExpr} {type : TypeExpr}
    {left right : Term (withMetas (signatureOf language) metas) bound type}
    (accepted : Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.FiniteBinding.Satisfies language constructors metas left right)
    (valuation : MetaValuation (Valuation.algebra constructors) metas) :
    BindingEquationInterpretation.interpretSchema (Valuation.algebra constructors) valuation left =
      BindingEquationInterpretation.interpretSchema (Valuation.algebra constructors) valuation right := by
  let functions : MetaFunctions language metas := fun index =>
    Valuation.readContext constructors (valuation index)
  have represented :
      (fun index => Valuation.ofFunction constructors (functions index)) = valuation := by
    funext index
    exact ofFunction_readContext constructors (valuation index)
  apply readContext_injective constructors
  funext assignment
  have same := accepted functions assignment
  change Valuation.readContext constructors
      (BindingEquationInterpretation.interpretSchema (Valuation.algebra constructors)
        (fun index => Valuation.ofFunction constructors (functions index)) left) assignment =
    Valuation.readContext constructors
      (BindingEquationInterpretation.interpretSchema (Valuation.algebra constructors)
        (fun index => Valuation.ofFunction constructors (functions index)) right) assignment at same
  rw [represented] at same
  exact same

theorem contextual_values_equal
    (constructors : Constructors language)
    (metas : List (MetaArity (signatureOf language)))
    {bound : List TypeExpr} {type : TypeExpr}
    {left right : Term (withMetas (signatureOf language) metas) bound type}
    (accepted : Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.FiniteBinding.Satisfies language constructors metas left right)
    {captured target : List TypeExpr}
    (body : SemanticContextualMetavariables.Valuation (M := metas) (Valuation.algebra constructors) captured)
    (ambient : Environment (signatureOf language) (Valuation.algebra constructors).substitution.Carrier
      captured target)
    (ordinary : Environment (signatureOf language) (Valuation.algebra constructors).substitution.Carrier
      bound target) :
    SemanticContextualMetavariables.interpretSchema (Valuation.algebra constructors) body ambient ordinary left =
      SemanticContextualMetavariables.interpretSchema (Valuation.algebra constructors) body ambient ordinary right := by
  apply equal_of_all_closings constructors
  intro assignment
  rw [IntrinsicScopedConditionalSubstitution.substitute_interpretSchema,
    IntrinsicScopedConditionalSubstitution.substitute_interpretSchema,
    close_captured_context, close_captured_context]
  exact congrArg ((Valuation.algebra constructors).substitution.substitute _)
    (dependency_values_equal constructors metas accepted _)

def singletonEquation (language : LanguageDef)
    (metas : List (MetaArity (signatureOf language)))
    {bound : List TypeExpr} {type : TypeExpr}
    (left right : Term (withMetas (signatureOf language) metas) bound type) :
    EqAxiom (signatureOf language) metas :=
  ⟨bound, type, left, right⟩

theorem singleton_satisfies_contextually
    (constructors : Constructors language)
    (metas : List (MetaArity (signatureOf language)))
    {bound : List TypeExpr} {type : TypeExpr}
    {left right : Term (withMetas (signatureOf language) metas) bound type}
    (accepted : Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.FiniteBinding.Satisfies language constructors metas left right) :
    BindingEquationInterpretation.Satisfies (Valuation.algebra constructors)
      [singletonEquation language metas left right] := by
  intro index captured target body ambient ordinary
  have only : index = ⟨0, by simp⟩ := by
    apply Fin.ext
    change index.val = 0
    have range : index.val < 1 := index.isLt
    omega
  subst index
  exact contextual_values_equal constructors metas accepted body ambient ordinary

theorem accepted_equation_descendants
    (constructors : Constructors language)
    (metas : List (MetaArity (signatureOf language)))
    {bound : List TypeExpr} {type : TypeExpr}
    {left right : Term (withMetas (signatureOf language) metas) bound type}
    (accepted : Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.FiniteBinding.Satisfies language constructors metas left right) :
    BindingEquationInterpretation.CongruenceSound (Valuation.algebra constructors)
      [singletonEquation language metas left right] :=
  (singleton_satisfies_contextually constructors metas accepted).congruenceSound

end Mettapedia.OSLF.NativeTypes.SortProfiles.Binding.CenterStability
