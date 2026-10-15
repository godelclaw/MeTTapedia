import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingEventPresheaf
import Mettapedia.OSLF.Syntax.BindingContextExtensionComparison
import Mettapedia.OSLF.NativeTypes.Modal.NativeAuthoredEventPresheaf

/-!
# Authored native function carriers and ordered contextual bodies

The local binder list is the actual innermost-first source context. Its
native function telescope is outermost-first. The comparison uses the
generated binding clone's genuine presheaf exponential and preserves all
ambient substitutions, rather than identifying raw lambdas with set maps.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeBindingScopedBodies

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.NativeTypes.Generation
open CurriedBindingLanguage BindingSemanticAdmission
open IntrinsicScopedConditionalPresheaf MultiBinderPresheaf
open BindingSubstitutionAlgebra

variable {language : LanguageDef}

theorem print_scoped_substitution {source target : List String}
    (substitution : Sub (signature language) source target) (scope : List String)
    {sort : String} (body : Term (signature language) (scope ++ source) sort) :
    toPattern (Binding.bind (liftSub substitution scope) body) =
      ContextSubstitution.substitute
        (ContextSubstitution.lift scope.length (NativeBindingRendering.assignment substitution))
        (toPattern body) := by
  calc
    toPattern (Binding.bind (liftSub substitution scope) body) =
        PatternRendering.encodeTerm (NativeBindingRendering.rendering language)
          (Binding.bind (liftSub substitution scope) body) :=
      NativeBindingRendering.print_render _
    _ = ContextSubstitution.substitute
        (ContextSubstitution.lift scope.length (NativeBindingRendering.assignment substitution))
        (PatternRendering.encodeTerm (NativeBindingRendering.rendering language) body) := ?_
    _ = _ := congrArg (ContextSubstitution.substitute _) (NativeBindingRendering.print_render body).symm
  apply PatternRendering.encodeTerm_bind_of_assignment
    (NativeBindingRendering.rendering language) (liftSub substitution scope)
  apply PatternRendering.encodedAssignment_lift
  intro sort position
  change String at sort
  change Var (Srt := String) source sort at position
  exact (congrArg (NativeBindingRendering.assignment substitution)
    (NativeBindingRendering.variable_index position)).trans
    ((NativeBindingRendering.assignment_variable substitution position).trans
      (NativeBindingRendering.print_render _))

theorem morphism_environment {environment : GeneralPremise.Environment}
    {X Y : Base (algebra environment.language)} (morphism : X ⟶ Y) :
    environmentArrow (algebra environment.language)
      (NativeBindingEventPresheaf.morphismSub morphism) = morphism.unop := by
  funext position
  exact fromPositions_varOfIdx X.unop.context morphism.unop position

theorem authored_morphism_environment {X Y : Base (algebra language)} (morphism : X ⟶ Y) :
    environmentArrow (algebra language)
      (NativeAuthoredEventPresheaf.morphismSub morphism) = morphism.unop := by
  funext position
  exact fromPositions_varOfIdx X.unop.context morphism.unop position

theorem scoped_map (scope : List String) (sort : String)
    {X Y : Base (algebra language)} (morphism : X ⟶ Y)
    (body : (scopedBodies (algebra language) scope sort).obj X) :
    (scopedBodies (algebra language) scope sort).map morphism body =
      Binding.bind (liftSub (NativeAuthoredEventPresheaf.morphismSub morphism) scope) body := by
  change (algebra language).substitution.toClone.substitute body
    (extendScope (algebra language) scope morphism.unop) = _
  have extended := extendScope_environment (algebra language) scope
    (NativeAuthoredEventPresheaf.morphismSub morphism)
  have actualExtended := (congrArg (extendScope (algebra language) scope)
    (authored_morphism_environment morphism)).symm.trans extended
  have replaced := congrArg ((algebra language).substitution.toClone.substitute body) actualExtended
  apply replaced.trans
  change Binding.bind (fromPositions _ (environmentArrow (algebra language)
    ((algebra language).substitution.liftEnvironment
      (NativeAuthoredEventPresheaf.morphismSub morphism) scope))) body = _
  congr 1
  funext result position
  exact (fromPositions_ofEnvironment
    ((algebra language).substitution.liftEnvironment
      (NativeAuthoredEventPresheaf.morphismSub morphism) scope) position).trans
    (congrFun (congrFun (terms_liftEnvironment_eq_liftSub
      (NativeAuthoredEventPresheaf.morphismSub morphism) scope) result) position)

/-- The carrier's source spine determines its exact contextual function
meaning; no independently supplied admissibility map is used. -/
noncomputable def nativeBodyIso (carrier : NativeSignature.Carrier language)
    {domains : List String} {result : String}
    (spine : BinderSpine carrier.source domains result) :
    meaning carrier ≅ scopedBodies (algebra language) domains.reverse result :=
  eqToIso (meaning_spine carrier spine) ≪≫
    curriedBinderIso (algebra language) result domains ≪≫
    scopedBodiesIso (algebra language) domains.reverse result

end Mettapedia.OSLF.NativeTypes.Modal.NativeBindingScopedBodies
