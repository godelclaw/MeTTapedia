import Mettapedia.CategoryTheory.GroundPathRelativePushout

/-!
# Authored frame permissions and their actual context category

A permission selects complete local frames. The resulting arrows retain
the original path and a proof that every selected frame is permitted.
Values are unchanged. Factor closure is proved for arrows out of an actual
interface; it is not asserted for a value whose filling can hide a frame.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.GroundPath.FramePermission

open _root_.CategoryTheory

universe u v w

variable {V : Type u} [Quiver.{v} V]

abbrev Permission (V : Type u) [Quiver.{v} V] :=
  {source target : V} → (source ⟶ target) → Prop

variable (permission : Permission V)

inductive PermittedPath : {source target : V} → Quiver.Path source target → Prop where
  | nil (source : V) : PermittedPath (.nil : Quiver.Path source source)
  | cons {source middle target : V} {previous : Quiver.Path source middle}
      {frame : middle ⟶ target} : PermittedPath previous → permission frame →
        PermittedPath (previous.cons frame)

theorem permittedPath_comp_iff {source middle target : V}
    (first : Quiver.Path source middle) (second : Quiver.Path middle target) :
    PermittedPath permission (first.comp second) ↔
      PermittedPath permission first ∧ PermittedPath permission second := by
  induction second with
  | nil => exact ⟨fun given => ⟨given, .nil _⟩, fun given => given.1⟩
  | cons previous frame inductionHypothesis =>
    constructor
    · intro given
      cases given with
      | cons inner last =>
        obtain ⟨before, after⟩ := inductionHypothesis.mp inner
        exact ⟨before, .cons after last⟩
    · rintro ⟨before, after⟩
      cases after with
      | cons inner last => exact .cons (inductionHypothesis.mpr ⟨before, inner⟩) last

variable (action : Action.{u,v,w} V)

inductive PermittedArrow : {source target : GroundPath.Object action} →
    (source ⟶ target) → Prop where
  | identity : PermittedArrow (𝟙 (.origin : GroundPath.Object action))
  | value {target : V} (supplied : action.Value target) :
      PermittedArrow (valueArrow action supplied)
  | context {source target : V} {path : Quiver.Path source target} :
      PermittedPath permission path → PermittedArrow (contextArrow action path)

theorem PermittedArrow.id (object : GroundPath.Object action) :
    PermittedArrow permission action (𝟙 object) := by
  cases object with
  | origin => exact .identity
  | interface vertex => exact .context (.nil vertex)

theorem PermittedArrow.comp {source middle target : GroundPath.Object action}
    {first : source ⟶ middle} {second : middle ⟶ target}
    (before : PermittedArrow permission action first)
    (after : PermittedArrow permission action second) :
    PermittedArrow permission action (first ≫ second) := by
  cases before with
  | identity => exact after
  | value supplied =>
    cases after with
    | context allowed => exact .value _
  | context allowed =>
    cases after with
    | context next => exact .context ((permittedPath_comp_iff permission _ _).mpr ⟨allowed, next⟩)

/-- Interface arrows retain their entire path. Both factors of a permitted
composite are therefore permitted, even through an independently chosen apex. -/
theorem factors_permitted {source : V} {middle target : GroundPath.Object action}
    (first : (.interface source : GroundPath.Object action) ⟶ middle)
    (second : middle ⟶ target)
    (given : PermittedArrow permission action (first ≫ second)) :
    PermittedArrow permission action first ∧ PermittedArrow permission action second := by
  cases middle with
  | origin => cases first
  | interface middle =>
    cases target with
    | origin => cases second
    | interface target =>
      cases first with
      | context firstPath =>
        cases second with
        | context secondPath =>
          cases given with
          | context allowed =>
            obtain ⟨before, after⟩ := (permittedPath_comp_iff permission _ _).mp allowed
            exact ⟨.context before, .context after⟩

structure Object (permission : Permission V) (action : Action.{u,v,w} V) where
  base : GroundPath.Object action

instance category : Category.{max u v w} (Object permission action) where
  Hom before after := {arrow : before.base ⟶ after.base // PermittedArrow permission action arrow}
  id object := ⟨𝟙 object.base, PermittedArrow.id permission action object.base⟩
  comp before after := ⟨before.val ≫ after.val,
    PermittedArrow.comp permission action before.property after.property⟩
  id_comp arrow := Subtype.ext (Category.id_comp arrow.val)
  comp_id arrow := Subtype.ext (Category.comp_id arrow.val)
  assoc before middle after := Subtype.ext (Category.assoc before.val middle.val after.val)

def origin : Object permission action := ⟨.origin⟩
def interface (vertex : V) : Object permission action := ⟨.interface vertex⟩

def inclusion : Object permission action ⥤ GroundPath.Object action where
  obj object := object.base
  map arrow := arrow.val
  map_id _ := rfl
  map_comp _ _ := rfl

instance inclusion_faithful : (inclusion permission action).Faithful where
  map_injective := fun same => Subtype.ext same

def value {target : V} (supplied : action.Value target) :
    origin permission action ⟶ interface permission action target := ⟨valueArrow action supplied, .value _⟩

def context {source target : V} (path : Quiver.Path source target)
    (allowed : PermittedPath permission path) :
    interface permission action source ⟶ interface permission action target :=
  ⟨contextArrow action path, .context allowed⟩

end Mettapedia.CategoryTheory.GroundPath.FramePermission
