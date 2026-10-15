import Mettapedia.TypeTheory.Calculi.NativeDependent.TheoryRepresentableEquations

/-!
# Earned native admission of original category declarations

All three declared equations compare independently evaluated substitutions.
The fibre law uses the actual stored source inhabitant and its indexing
proof, not an erased endpoint or an assumed comprehension law.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.TheoryRepresentables

open _root_.CategoryTheory
open RepresentableIndexedDeclarations
open TheoryEquations

universe u
variable {C : Type u} [Category.{u} C]

noncomputable section

theorem fibre_projection_read (index : ArrowSymbol C) :
    (model C).evaluateSubstitution (fibreScope index) (objectScope index.target)
      (fun position => TermExpr.var position.succ) =
        some ((NativeModel C).toCwf.wk (fibreMeaning index)) := by
  apply ((model C).evaluateSubstitution_eq_some_iff _ _ _ _).2
  intro position
  cases position using Fin.cases with
  | zero => rfl
  | succ impossible => exact Fin.elim0 impossible

theorem forget_then_original (index : ArrowSymbol C) :
    forgetMap index ≫ originalMap index.arrow = (NativeModel C).toCwf.wk (fibreMeaning index) := by
  ext world value
  rcases value with ⟨⟨singleton, argument⟩, ⟨source, indexed⟩⟩
  cases singleton
  change (⟨PUnit.unit, source ≫ index.arrow⟩ : (objectScope index.target).1.obj world) =
    ⟨PUnit.unit, argument⟩
  exact congrArg (fun result => (⟨PUnit.unit, result⟩ : (objectScope index.target).1.obj world)) indexed

theorem native_admitted (origin : Origin C) : (declaration origin).NativeAdmitted (model C) := by
  cases origin with
  | identity object =>
      intro Γ Δ sourceRead targetRead
      have sourceSame := Option.some.inj (sourceRead.symm.trans (object_context_read object))
      have targetSame := Option.some.inj (targetRead.symm.trans (object_context_read object))
      subst Γ Δ
      rw [original_substitution_read, (model C).evaluateSubstitution_identity]
      exact congrArg some (RepresentableDeclarations.originalPresheafArrow_identity object)
  | composition earlier later =>
      intro Γ Δ sourceRead targetRead
      have sourceSame := Option.some.inj (sourceRead.symm.trans (object_context_read _))
      have targetSame := Option.some.inj (targetRead.symm.trans (object_context_read _))
      subst Γ Δ
      change (model C).evaluateSubstitution (objectScope _) (objectScope _)
        (originalSubstitution (earlier ≫ later)) = _
      rw [original_substitution_read,
        (model C).evaluateSubstitution_composition (NativeLocalTypeOperations.products_substitution C)
          (objectScope _) (objectScope _) (objectScope _)
          (originalSubstitution later) (originalSubstitution earlier)
          (originalMap later) (originalMap earlier)
          (original_substitution_read later) (original_substitution_read earlier)]
      exact congrArg some (RepresentableDeclarations.originalPresheafArrow_composition earlier later)
  | fibreProjection index =>
      intro Γ Δ sourceRead targetRead
      have sourceSame := Option.some.inj (sourceRead.symm.trans (fibre_context_read index))
      have targetSame := Option.some.inj (targetRead.symm.trans (object_context_read index.target))
      subst Γ Δ
      change (model C).evaluateSubstitution (fibreScope index) (objectScope index.target)
        (composeSubstitution (originalSubstitution index.arrow) (forgetSubstitution index)) = _
      rw [(model C).evaluateSubstitution_composition (NativeLocalTypeOperations.products_substitution C)
        (objectScope index.source) (objectScope index.target) (fibreScope index)
        (originalSubstitution index.arrow) (forgetSubstitution index)
        (originalMap index.arrow) (forgetMap index)
        (original_substitution_read index.arrow) (forget_substitution_read index),
        fibre_projection_read]
      exact congrArg some (forget_then_original index)

theorem admitted : TheoryEquations.Admitted (model C).toAbstract (equations C) :=
  nativeAdmission_toAbstract (model C) (equations C) native_admitted

/-- The independent native primitive interpretation qualifies the full
extended rule fold by only the earned local declaration comparisons. -/
def qualifiedModel : TheoryEquations.Contextual.Interpretation.QualifiedModel
    (theory C) (NativeModel C) where
  localModel := PresheafNativePredicateModel.model C
  data := (model C).toAbstract
  realization := (realization C).toAbstract
  qualification := PresheafNativePredicateModel.qualification C
  equations_admitted := admitted

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.TheoryRepresentables
