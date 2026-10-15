import Mettapedia.OSLF.Syntax.ScopedBindingContextSubstitution
import Mettapedia.OSLF.Syntax.BindingEquationQuotientModel
import Mettapedia.OSLF.Syntax.BindingEquationExtension

/-!
# Complete scoped context actions on authored equation classes

Every actual binding frame and path acts on the existing term quotient.
Congruence beneath each declared binder earns well-definedness, and the
independent path and capture-avoiding substitution laws earn composition
and reindexing. Equation extension commutes with this complete context action.

The paths retain their selected positions and raw siblings. This is a
functor of equation-class values over retained paths, not an assertion that
these paths are distinct in an equational quotient of contexts.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedEquationContexts

open _root_.CategoryTheory ScopedEncoding

variable {S : Signature} {M : List (MetaArity S)}

local instance : Quiver (Scope S) := bindingFrameQuiver S

abbrev ContextCategory (S : Signature) :=
  @Paths (Scope S)

abbrev State (E : List (EqAxiom S M)) (scope : ContextCategory S) :=
  TermQ E scope.1 scope.2

theorem assemble_related (E : List (EqAxiom S M)) (context : Ctx S) :
    ∀ (declarations : List (List S.Srt × S.Srt))
      (first second : (position : Fin declarations.length) →
        Term S ((declarations.get position).1 ++ context) (declarations.get position).2),
      (∀ position, EqClosure E (first position) (second position)) →
      EqArgs E (assembleArguments context declarations first)
        (assembleArguments context declarations second)
  | [], _, _, _ => .nil
  | _ :: tail, first, second, related =>
      .cons (related 0) (assemble_related E context tail
        (fun position => first position.succ) (fun position => second position.succ)
        (fun position => related position.succ))

theorem frame_respects (E : List (EqAxiom S M)) {source target : Scope S}
    (frame : BindingFrame S source target)
    {first second : Term S source.1 source.2} (related : EqClosure E first second) :
    EqClosure E (frame.fill first) (frame.fill second) := by
  cases frame with
  | slot context sort operator position siblings =>
    apply EqClosure.cong operator
    apply assemble_related E context
    intro other
    by_cases same : other = position
    · subst other
      simpa only [dite_true] using related
    · simp only [dif_neg same]
      exact .refl _

theorem path_respects (E : List (EqAxiom S M)) {source target : Scope S}
    (context : BindingContext S source target)
    {first second : Term S source.1 source.2} (related : EqClosure E first second) :
    EqClosure E (fillContext context first) (fillContext context second) := by
  induction context with
  | nil => exact related
  | cons previous frame ih => exact frame_respects E frame ih

/-- Filling a complete class is independent of its raw representative. -/
def fillClass (E : List (EqAxiom S M)) {source target : Scope S}
    (context : BindingContext S source target) : State E source → State E target :=
  Quotient.lift (fun term => Quotient.mk _ (fillContext context term))
    (fun _ _ related => Quotient.sound (path_respects E context related))

theorem fillClass_mk (E : List (EqAxiom S M)) {source target : Scope S}
    (context : BindingContext S source target) (term : Term S source.1 source.2) :
    fillClass E context (Quotient.mk _ term) = Quotient.mk _ (fillContext context term) := rfl

theorem fillClass_identity (E : List (EqAxiom S M)) {scope : Scope S}
    (value : State E scope) : fillClass E (.nil : BindingContext S scope scope) value = value := by
  induction value using Quotient.inductionOn with
  | _ term => rfl

theorem fillClass_comp (E : List (EqAxiom S M)) {first middle last : Scope S}
    (inner : BindingContext S first middle) (outer : BindingContext S middle last)
    (value : State E first) :
    fillClass E (inner.comp outer) value = fillClass E outer (fillClass E inner value) := by
  induction value using Quotient.inductionOn with
  | _ term =>
    exact congrArg (fun value : Term S last.1 last.2 => (Quotient.mk _ value : State E last))
      (Mettapedia.CategoryTheory.GroundPath.Action.path_comp (bindingAction S) inner outer term)

/-- The functor uses the actual scoped paths and complete existing term classes. -/
def action (E : List (EqAxiom S M)) : ContextCategory S ⥤ Type where
  obj := State E
  map context := TypeCat.ofHom (fillClass E context)
  map_id scope := by
    apply ConcreteCategory.hom_ext
    intro value
    exact fillClass_identity E value
  map_comp inner outer := by
    apply ConcreteCategory.hom_ext
    intro value
    exact fillClass_comp E inner outer value

/-- The entire filling square commutes through every capture-avoiding
substitution, including variable identifications and opened binder contexts. -/
theorem substitution_square (E : List (EqAxiom S M)) {source target : Scope S}
    (context : BindingContext S source target) (destination : Ctx S)
    (sigma : Sub S target.1 destination) (value : State E source) :
    bindQ sigma (fillClass E context value) =
      fillClass E (substituteContext context destination sigma).path
        (bindQ (substituteContext context destination sigma).holeVariables value) := by
  induction value using Quotient.inductionOn with
  | _ term =>
    exact congrArg (fun value : Term S destination target.2 =>
      (Quotient.mk _ value : TermQ E destination target.2))
      (substituteContext_fill context destination sigma term)

/-- Extending equations preserves the complete retained context action. -/
theorem extension_square {E F : List (EqAxiom S M)}
    (includeEquation : BindingEquationExtension.AxiomInclusion E F)
    {source target : Scope S} (context : BindingContext S source target)
    (value : State E source) :
    (BindingEquationExtension.comparisonHom includeEquation).raw.map (fillClass E context value) =
      fillClass F context ((BindingEquationExtension.comparisonHom includeEquation).raw.map value) := by
  induction value using Quotient.inductionOn with
  | _ term =>
    rw [fillClass_mk, BindingEquationExtension.comparisonHom_mk,
      BindingEquationExtension.comparisonHom_mk, fillClass_mk]

noncomputable def extension {E F : List (EqAxiom S M)}
    (includeEquation : BindingEquationExtension.AxiomInclusion E F) : action E ⟶ action F where
  app scope := TypeCat.ofHom (BindingEquationExtension.comparisonHom includeEquation).raw.map
  naturality source target context := by
    apply ConcreteCategory.hom_ext
    intro value
    exact extension_square includeEquation context value

end Mettapedia.OSLF.Binding.ScopedEquationContexts
