import Mettapedia.CategoryTheory.GroundPathFramePermissionRPO
import Mettapedia.GSLT.Logic.RelativePushoutIdentity
import Mettapedia.GSLT.Logic.RedexRelativeCongruence

/-!
# Retained firings and actual context congruence for permitted frames

Each declared reaction keeps its supplied origin and complete redex/reactum.
Its firing keeps the selected declaration, reaction context, IPO and entire
target. Permission restriction reflects precisely ambient firings with a
permitted reaction context. It does not assert reflection from a permitted
label alone. Literal-label congruence is earned by actual redex RPOs.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.GroundPath.FramePermission

open _root_.CategoryTheory
open Mettapedia.GSLT.RelativePushout Mettapedia.GSLT.RedexRelativeCongruence

universe u v w r

variable {V : Type u} [Quiver.{v} V]
variable (permission : Permission V) (action : Action.{u,v,w} V)

structure Declaration (Origins : Type r) where
  origin : Origins
  scope : V
  redex : action.Value scope
  reactum : action.Value scope

variable {Origins : Type r}

def Declaration.rule (declaration : Declaration action Origins) :
    ReactionRule (FramePermission.origin permission action) where
  codomain := interface permission action declaration.scope
  redex := value permission action declaration.redex
  reactum := value permission action declaration.reactum

def Declaration.rawRule (declaration : Declaration action Origins) :
    ReactionRule (.origin : GroundPath.Object action) where
  codomain := .interface declaration.scope
  redex := valueArrow action declaration.redex
  reactum := valueArrow action declaration.reactum

variable (admitted : Declaration action Origins → Prop)

def rules (rule : ReactionRule (origin permission action)) : Prop :=
  ∃ declaration, admitted declaration ∧ declaration.rule permission action = rule

variable {permission action admitted}
variable {source target : V}

structure Firing (agent : action.Value source) (label : interface permission action source ⟶
    interface permission action target) (next : action.Value target) where
  declaration : Declaration action Origins
  admitted : admitted declaration
  reaction : interface permission action declaration.scope ⟶ interface permission action target
  square : value permission action agent ≫ label = value permission action declaration.redex ≫ reaction
  minimal : IsIdemPushout (value permission action agent) (value permission action declaration.redex)
    label reaction square
  target_readout : value permission action next = value permission action declaration.reactum ≫ reaction

structure RawFiring (agent : action.Value source)
    (label : (.interface source : GroundPath.Object action) ⟶ .interface target)
    (next : action.Value target) where
  declaration : Declaration action Origins
  admitted : admitted declaration
  reaction : (.interface declaration.scope : GroundPath.Object action) ⟶ .interface target
  square : valueArrow action agent ≫ label = valueArrow action declaration.redex ≫ reaction
  minimal : IsIdemPushout (valueArrow action agent) (valueArrow action declaration.redex) label reaction square
  target_readout : valueArrow action next = valueArrow action declaration.reactum ≫ reaction

def Firing.raw {agent : action.Value source} {next : action.Value target}
    {label : interface permission action source ⟶ interface permission action target}
    (firing : Firing (admitted := admitted) agent label next) :
    RawFiring (admitted := admitted) agent label.val next where
  declaration := firing.declaration
  admitted := firing.admitted
  reaction := firing.reaction.val
  square := congrArg Subtype.val firing.square
  minimal := (idemPushout_iff permission action firing.square).mp firing.minimal
  target_readout := congrArg Subtype.val firing.target_readout

def RawFiring.restrict {agent : action.Value source} {next : action.Value target}
    {label : interface permission action source ⟶ interface permission action target}
    (firing : RawFiring (admitted := admitted) agent label.val next)
    (reactionAllowed : PermittedArrow permission action firing.reaction) :
    Firing (admitted := admitted) agent label next where
  declaration := firing.declaration
  admitted := firing.admitted
  reaction := ⟨firing.reaction, reactionAllowed⟩
  square := Subtype.ext firing.square
  minimal := (idemPushout_iff permission action (before := agent) (redex := firing.declaration.redex)
    (left := label) (right := ⟨firing.reaction, reactionAllowed⟩)
      (Subtype.ext firing.square)).mpr firing.minimal
  target_readout := Subtype.ext firing.target_readout

theorem restrict_raw {agent : action.Value source} {next : action.Value target}
    {label : interface permission action source ⟶ interface permission action target}
    (firing : RawFiring (admitted := admitted) agent label.val next)
    (reactionAllowed : PermittedArrow permission action firing.reaction) :
    (firing.restrict reactionAllowed).raw = firing := by
  cases firing
  rfl

theorem raw_restrict {agent : action.Value source} {next : action.Value target}
    {label : interface permission action source ⟶ interface permission action target}
    (firing : Firing (admitted := admitted) agent label next) :
    firing.raw.restrict firing.reaction.property = firing := by
  cases firing
  rfl

theorem retained_firing_iff {agent : action.Value source} {next : action.Value target}
    {label : interface permission action source ⟶ interface permission action target} :
    Nonempty (Firing (admitted := admitted) agent label next) ↔
      ∃ firing : RawFiring (admitted := admitted) agent label.val next,
        PermittedArrow permission action firing.reaction :=
  ⟨fun ⟨firing⟩ => ⟨firing.raw, firing.reaction.property⟩,
    fun ⟨firing, allowed⟩ => ⟨firing.restrict allowed⟩⟩

theorem firing_iff_actIPO {agent : action.Value source} {next : action.Value target}
    {label : interface permission action source ⟶ interface permission action target} :
    Nonempty (Firing (admitted := admitted) agent label next) ↔
      ActIPO (rules permission action admitted) label (value permission action agent)
        (value permission action next) := by
  constructor
  · rintro ⟨firing⟩
    exact ⟨firing.declaration.rule permission action, ⟨firing.declaration, firing.admitted, rfl⟩,
      firing.reaction, firing.square, firing.minimal, firing.target_readout⟩
  · rintro ⟨rule, ⟨declaration, selected, rfl⟩, reaction, square, minimal, result⟩
    exact ⟨⟨declaration, selected, reaction, square, minimal, result⟩⟩

variable (permission action admitted)

theorem rules_redex_relativePushouts (interface : Object permission action)
    (agent : origin permission action ⟶ interface)
    (rule : ReactionRule (origin permission action)) (member : rules permission action admitted rule) :
    HasRelativePushouts agent rule.redex := by
  obtain ⟨declaration, selected, rfl⟩ := member
  rcases interface with ⟨object⟩
  cases object with
  | origin =>
    rcases agent with ⟨agent, permissionProof⟩
    cases agent with
    | identity => exact hasRelativePushouts_identity_left _
  | interface vertex =>
    rcases agent with ⟨agent, permissionProof⟩
    cases agent with
    | value supplied => exact redex_relativePushouts permission action supplied declaration.redex

theorem literal_context_congruence {interface outer : Object permission action}
    {before after : origin permission action ⟶ interface}
    (related : IPOBisimilar (rules permission action admitted) before after)
    (context : interface ⟶ outer) :
    IPOBisimilar (rules permission action admitted) (before ≫ context) (after ≫ context) :=
  ipoBisimilar_comp (rules_redex_relativePushouts permission action admitted) related context

end Mettapedia.CategoryTheory.GroundPath.FramePermission
