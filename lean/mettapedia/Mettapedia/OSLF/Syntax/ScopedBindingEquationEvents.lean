import Mettapedia.OSLF.Syntax.ScopedBindingEquationContextAction
import Mettapedia.OSLF.Syntax.ScopedBindingPermissionSubstitution
import Mettapedia.OSLF.Syntax.ContextualRootEvents

/-!
# Permitted binding occurrences and their exact equation-class endpoints

An occurrence keeps its authored rule index, root assignment, actual opened
hole context, complete reaction path and slot-permission evidence. Its
endpoints use the existing source equation quotient. Capture-avoiding
substitution transports the complete occurrence and both endpoint squares.
Equation extension changes the endpoint classes while retaining that event.

The root rules here are unconditional binding schemas. Context permission is
explicit; the construction does not certify every authored language or
silently enable reactions beneath inactive binders or quotations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedEquationEvents

open _root_.CategoryTheory ScopedEncoding ScopedEquationContexts
open Mettapedia.CategoryTheory.GroundPath

universe r

variable {S : Signature} {M : List (MetaArity S)} {Index : Type r}
  (rules : Index → UnpositionedRewrite (withMetas S M)) (permission : PositionPermission S)

local instance : Quiver (Scope S) := bindingFrameQuiver S

structure Event (scope : Scope S) where
  index : Index
  holeContext : Ctx S
  root : ContextualRootEvents.Instance (rules index) holeContext
  context : BindingContext S (holeContext, (rules index).sort) scope
  permitted : FramePermission.PermittedPath
    (framePermission S (uniformSlotPermission S permission)) context

namespace Event

variable {rules permission}

def source {scope : Scope S} (event : Event rules permission scope) :
    Term S scope.1 scope.2 := fillContext event.context event.root.source

def target {scope : Scope S} (event : Event rules permission scope) :
    Term S scope.1 scope.2 := fillContext event.context event.root.target

def sourceClass (E : List (EqAxiom S M)) {scope : Scope S}
    (event : Event rules permission scope) : State E scope := Quotient.mk _ event.source

def targetClass (E : List (EqAxiom S M)) {scope : Scope S}
    (event : Event rules permission scope) : State E scope := Quotient.mk _ event.target

/-- The inherited hole substitution is computed beneath every actual binder. -/
def map {scope : Scope S} (destination : Ctx S) (sigma : Sub S scope.1 destination)
    (event : Event rules permission scope) : Event rules permission (destination, scope.2) where
  index := event.index
  holeContext := (substituteContext event.context destination sigma).holeContext
  root := event.root.map (substituteContext event.context destination sigma).holeVariables
  context := (substituteContext event.context destination sigma).path
  permitted := (substituteContext_permission_iff permission event.context destination sigma).mpr
    event.permitted

theorem source_map {scope : Scope S} (destination : Ctx S) (sigma : Sub S scope.1 destination)
    (event : Event rules permission scope) :
    (event.map destination sigma).source = bind sigma event.source := by
  unfold source map
  rw [ContextualRootEvents.Instance.source_map]
  exact (substituteContext_fill event.context destination sigma event.root.source).symm

theorem target_map {scope : Scope S} (destination : Ctx S) (sigma : Sub S scope.1 destination)
    (event : Event rules permission scope) :
    (event.map destination sigma).target = bind sigma event.target := by
  unfold target map
  rw [ContextualRootEvents.Instance.target_map]
  exact (substituteContext_fill event.context destination sigma event.root.target).symm

theorem sourceClass_map (E : List (EqAxiom S M)) {scope : Scope S}
    (destination : Ctx S) (sigma : Sub S scope.1 destination)
    (event : Event rules permission scope) :
    (event.map destination sigma).sourceClass E = bindQ sigma (event.sourceClass E) :=
  congrArg (fun term : Term S destination scope.2 =>
    (Quotient.mk _ term : TermQ E destination scope.2)) (source_map destination sigma event)

theorem targetClass_map (E : List (EqAxiom S M)) {scope : Scope S}
    (destination : Ctx S) (sigma : Sub S scope.1 destination)
    (event : Event rules permission scope) :
    (event.map destination sigma).targetClass E = bindQ sigma (event.targetClass E) :=
  congrArg (fun term : Term S destination scope.2 =>
    (Quotient.mk _ term : TermQ E destination scope.2)) (target_map destination sigma event)

theorem complete_origin_map {scope : Scope S} (destination : Ctx S)
    (sigma : Sub S scope.1 destination) (event : Event rules permission scope) :
    (event.map destination sigma).index = event.index := rfl

theorem reaction_length_map {scope : Scope S} (destination : Ctx S)
    (sigma : Sub S scope.1 destination) (event : Event rules permission scope) :
    (event.map destination sigma).context.length = event.context.length :=
  substituteContext_frame_count event.context destination sigma

theorem sourceClass_extension {E F : List (EqAxiom S M)}
    (includeEquation : BindingEquationExtension.AxiomInclusion E F) {scope : Scope S}
    (event : Event rules permission scope) :
    (BindingEquationExtension.comparisonHom includeEquation).raw.map (event.sourceClass E) =
      event.sourceClass F := BindingEquationExtension.comparisonHom_mk includeEquation event.source

theorem targetClass_extension {E F : List (EqAxiom S M)}
    (includeEquation : BindingEquationExtension.AxiomInclusion E F) {scope : Scope S}
    (event : Event rules permission scope) :
    (BindingEquationExtension.comparisonHom includeEquation).raw.map (event.targetClass E) =
      event.targetClass F := BindingEquationExtension.comparisonHom_mk includeEquation event.target

end Event

end Mettapedia.OSLF.Binding.ScopedEquationEvents
