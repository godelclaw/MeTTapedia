import Mettapedia.CategoryTheory.GroundPathFramePermissionFiring
import Mathlib.Data.Set.Finite.Basic

/-!
# Ground-rule transitions at the distinguished origin

The original declaration presentation induces the ambient reaction relation.
Its ordinary interface firings coincide with the independently retained raw
records. At the distinguished origin, IPO minimality forces the reaction
context to have length zero. The complete target is therefore an authored
reactum, with its original scope retained in the dependent readout.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.GroundPath.FramePermission

open _root_.CategoryTheory
open Mettapedia.GSLT.RelativePushout Mettapedia.GSLT.RedexRelativeCongruence

universe u v w r

variable {V : Type u} [Quiver.{v} V] (action : Action.{u,v,w} V)
  {Origins : Type r} (admitted : Declaration action Origins → Prop)

def rawRules (rule : ReactionRule (.origin : GroundPath.Object action)) : Prop :=
  ∃ declaration, admitted declaration ∧ declaration.rawRule action = rule

variable {action admitted} {source target : V}

theorem rawFiring_iff_actIPO {agent : action.Value source} {next : action.Value target}
    {label : (.interface source : GroundPath.Object action) ⟶ .interface target} :
    Nonempty (RawFiring (admitted := admitted) agent label next) ↔
      ActIPO (rawRules action admitted) label (valueArrow action agent) (valueArrow action next) := by
  constructor
  · rintro ⟨firing⟩
    exact ⟨firing.declaration.rawRule action, ⟨firing.declaration, firing.admitted, rfl⟩,
      firing.reaction, firing.square, firing.minimal, firing.target_readout⟩
  · rintro ⟨rule, ⟨declaration, selected, rfl⟩, reaction, square, minimal, result⟩
    exact ⟨⟨declaration, selected, reaction, square, minimal, result⟩⟩

theorem origin_actIPO_target_readout
    (label : (.origin : GroundPath.Object action) ⟶ .interface target)
    (next : action.Value target)
    (actual : ActIPO (rawRules action admitted) label (𝟙 _) (valueArrow action next)) :
    ∃ declaration, admitted declaration ∧
      (⟨target, next⟩ : (vertex : V) × action.Value vertex) =
        ⟨declaration.scope, declaration.reactum⟩ := by
  rcases actual with ⟨rule, ⟨declaration, selected, rfl⟩, reaction, square, minimal, result⟩
  let candidate : Candidate (𝟙 (.origin : GroundPath.Object action))
      (valueArrow action declaration.redex) label reaction := {
    apex := .interface declaration.scope
    inl := valueArrow action declaration.redex
    inr := 𝟙 _
    down := reaction
    comm := (Category.id_comp _).trans (Category.comp_id _).symm
    fac_left := square.symm.trans (Category.id_comp _)
    fac_right := Category.id_comp _ }
  obtain ⟨section_, splits⟩ := minimal.down_splits candidate
  cases reaction with
  | context reactionPath =>
    cases section_ with
    | context sectionPath =>
      have paths := Arrow.context.inj splits
      have counted := congrArg Quiver.Path.length paths
      simp only [Quiver.Path.length_comp, Quiver.Path.length_nil] at counted
      cases reactionPath with
      | nil =>
        refine ⟨declaration, selected, ?_⟩
        exact congrArg (fun value => (⟨declaration.scope, value⟩ :
          (vertex : V) × action.Value vertex)) (Arrow.value.inj result)
      | cons previous frame =>
        simp only [Quiver.Path.length_cons] at counted
        omega

theorem origin_actIPO_values_finite
    (declarations : List (Declaration action Origins))
    (label : (.origin : GroundPath.Object action) ⟶ .interface target) :
    Set.Finite {next : action.Value target |
      ActIPO (rawRules action (fun declaration => declaration ∈ declarations))
        label (𝟙 _) (valueArrow action next)} := by
  let readouts : List ((vertex : V) × action.Value vertex) :=
    declarations.map (fun declaration => ⟨declaration.scope, declaration.reactum⟩)
  refine Set.Finite.of_injOn
    (f := fun next : action.Value target =>
      (⟨target, next⟩ : (vertex : V) × action.Value vertex)) ?_ ?_
    (List.finite_toSet readouts)
  · intro next actual
    obtain ⟨declaration, selected, readout⟩ := origin_actIPO_target_readout label next actual
    exact List.mem_map.mpr ⟨declaration, selected, readout.symm⟩
  · intro first _firstSelected second _secondSelected same
    exact eq_of_heq (Sigma.mk.inj same).2

variable {permission : Permission V}

theorem permitted_origin_actIPO_target_readout
    (label : origin permission action ⟶ interface permission action target)
    (next : action.Value target)
    (actual : ActIPO (rules permission action admitted) label (𝟙 _)
      (value permission action next)) :
    ∃ declaration, admitted declaration ∧
      (⟨target, next⟩ : (vertex : V) × action.Value vertex) =
        ⟨declaration.scope, declaration.reactum⟩ := by
  rcases actual with ⟨rule, ⟨declaration, selected, rfl⟩, reaction, square, minimal, result⟩
  let candidate : Candidate (𝟙 (origin permission action))
      (value permission action declaration.redex) label reaction := {
    apex := interface permission action declaration.scope
    inl := value permission action declaration.redex
    inr := 𝟙 _
    down := reaction
    comm := (Category.id_comp _).trans (Category.comp_id _).symm
    fac_left := square.symm.trans (Category.id_comp _)
    fac_right := Category.id_comp _ }
  obtain ⟨section_, splits⟩ := minimal.down_splits candidate
  rcases reaction with ⟨reaction, _reactionAllowed⟩
  cases reaction with
  | context reactionPath =>
    rcases section_ with ⟨section_, _sectionAllowed⟩
    cases section_ with
    | context sectionPath =>
      have paths := Arrow.context.inj (congrArg Subtype.val splits)
      have counted := congrArg Quiver.Path.length paths
      simp only [Quiver.Path.length_comp, Quiver.Path.length_nil] at counted
      cases reactionPath with
      | nil =>
        refine ⟨declaration, selected, ?_⟩
        exact congrArg (fun supplied => (⟨declaration.scope, supplied⟩ :
          (vertex : V) × action.Value vertex)) (Arrow.value.inj (congrArg Subtype.val result))
      | cons previous frame =>
        simp only [Quiver.Path.length_cons] at counted
        omega

theorem permitted_origin_actIPO_values_finite
    (declarations : List (Declaration action Origins))
    (label : origin permission action ⟶ interface permission action target) :
    Set.Finite {next : action.Value target |
      ActIPO (rules permission action (fun declaration => declaration ∈ declarations))
        label (𝟙 _) (value permission action next)} := by
  let readouts : List ((vertex : V) × action.Value vertex) :=
    declarations.map (fun declaration => ⟨declaration.scope, declaration.reactum⟩)
  refine Set.Finite.of_injOn
    (f := fun next : action.Value target =>
      (⟨target, next⟩ : (vertex : V) × action.Value vertex)) ?_ ?_
    (List.finite_toSet readouts)
  · intro next actual
    obtain ⟨declaration, selected, readout⟩ := permitted_origin_actIPO_target_readout label next actual
    exact List.mem_map.mpr ⟨declaration, selected, readout.symm⟩
  · intro first _firstSelected second _secondSelected same
    exact eq_of_heq (Sigma.mk.inj same).2

end Mettapedia.CategoryTheory.GroundPath.FramePermission
