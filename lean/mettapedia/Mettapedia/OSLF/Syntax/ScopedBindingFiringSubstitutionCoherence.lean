import Mettapedia.OSLF.Syntax.ScopedBindingDeclarationInstances
import Mettapedia.OSLF.Syntax.ScopedBindingFiringSubstitution
import Mettapedia.OSLF.Syntax.ScopedBindingSubstitutionCoherence

/-!
# Complete identity and composition readouts for binding firings

The readout retains the entire scoped agent and label, the rule origin,
both complete declaration terms, the reaction path, and the independently
supplied target. It is extracted from an actual firing. Its substitution
is computed from the independent context and term operations. The whole
identity and composition equations follow from those earned laws, and
compare both actual firing constructions. The original receipt chains
remain distinct data; flattening their readings does not erase them.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedEncoding

open Mettapedia.CategoryTheory.GroundPath

universe r
variable {S : Binding.Signature} {Origins : Type r}
local instance bindingFiringCoherenceQuiver : Quiver (Scope S) := bindingFrameQuiver S

abbrev ScopedTermPathReadout (S : Binding.Signature) (inputSort outputSort : S.Srt)
    (context : Binding.Ctx S) :=
  Σ hole : Binding.Ctx S,
    Binding.Term S hole inputSort × BindingContext S (hole, inputSort) (context, outputSort)

abbrev ScopedRulePathReadout (S : Binding.Signature) (ruleSort outputSort : S.Srt)
    (context : Binding.Ctx S) :=
  Σ hole : Binding.Ctx S,
    Binding.Term S hole ruleSort × Binding.Term S hole ruleSort ×
      BindingContext S (hole, ruleSort) (context, outputSort)

def termPathReadout {source : Scope S} {outputSort : S.Srt} {destination : Binding.Ctx S}
    (term : Binding.Term S source.1 source.2)
    (computed : SubstitutedContext S source outputSort destination) :
    ScopedTermPathReadout S source.2 outputSort destination :=
  ⟨computed.holeContext, Binding.bind computed.holeVariables term, computed.path⟩

def rulePathReadout {source : Scope S} {outputSort : S.Srt} {destination : Binding.Ctx S}
    (redex reactum : Binding.Term S source.1 source.2)
    (computed : SubstitutedContext S source outputSort destination) :
    ScopedRulePathReadout S source.2 outputSort destination :=
  ⟨computed.holeContext, Binding.bind computed.holeVariables redex,
    Binding.bind computed.holeVariables reactum, computed.path⟩

def substituteTermPathReadout {inputSort outputSort : S.Srt} {context : Binding.Ctx S}
    (readout : ScopedTermPathReadout S inputSort outputSort context)
    (destination : Binding.Ctx S) (sigma : Binding.Sub S context destination) :
    ScopedTermPathReadout S inputSort outputSort destination :=
  termPathReadout readout.2.1 (substituteContext readout.2.2 destination sigma)

def substituteRulePathReadout {ruleSort outputSort : S.Srt} {context : Binding.Ctx S}
    (readout : ScopedRulePathReadout S ruleSort outputSort context)
    (destination : Binding.Ctx S) (sigma : Binding.Sub S context destination) :
    ScopedRulePathReadout S ruleSort outputSort destination :=
  rulePathReadout readout.2.1 readout.2.2.1 (substituteContext readout.2.2.2 destination sigma)

theorem substituteTermPathReadout_identity {inputSort outputSort : S.Srt} {context : Binding.Ctx S}
    (readout : ScopedTermPathReadout S inputSort outputSort context) :
    substituteTermPathReadout readout context (fun _ value => .var value) = readout := by
  rcases readout with ⟨hole, term, path⟩
  unfold substituteTermPathReadout
  rw [substituteContext_identity]
  exact congrArg (fun value : Binding.Term S hole inputSort =>
    (⟨hole, value, path⟩ : ScopedTermPathReadout S inputSort outputSort context)) (Binding.bind_id term)

theorem substituteRulePathReadout_identity {ruleSort outputSort : S.Srt} {context : Binding.Ctx S}
    (readout : ScopedRulePathReadout S ruleSort outputSort context) :
    substituteRulePathReadout readout context (fun _ value => .var value) = readout := by
  rcases readout with ⟨hole, redex, reactum, path⟩
  unfold substituteRulePathReadout
  rw [substituteContext_identity]
  exact congrArg₂ (fun (left right : Binding.Term S hole ruleSort) =>
    (⟨hole, left, right, path⟩ : ScopedRulePathReadout S ruleSort outputSort context))
    (Binding.bind_id redex) (Binding.bind_id reactum)

theorem substituteTermPathReadout_composition {inputSort outputSort : S.Srt} {context : Binding.Ctx S}
    (readout : ScopedTermPathReadout S inputSort outputSort context)
    (middle destination : Binding.Ctx S) (first : Binding.Sub S context middle)
    (second : Binding.Sub S middle destination) :
    substituteTermPathReadout readout destination (fun sort value => Binding.bind second (first sort value)) =
      substituteTermPathReadout (substituteTermPathReadout readout middle first) destination second := by
  rcases readout with ⟨hole, term, path⟩
  let inner := substituteContext path middle first
  let outer := substituteContext inner.path destination second
  have whole := congrArg (termPathReadout (source := (hole, inputSort)) term)
    (substituteContext_composition path middle destination first second)
  refine whole.trans ?_
  change (⟨outer.holeContext,
      Binding.bind (fun sort value => Binding.bind outer.holeVariables (inner.holeVariables sort value)) term,
      outer.path⟩ : ScopedTermPathReadout S inputSort outputSort destination) =
    ⟨outer.holeContext, Binding.bind outer.holeVariables (Binding.bind inner.holeVariables term), outer.path⟩
  exact congrArg (fun value : Binding.Term S outer.holeContext inputSort =>
    (⟨outer.holeContext, value, outer.path⟩ : ScopedTermPathReadout S inputSort outputSort destination))
    (Binding.bind_comp inner.holeVariables outer.holeVariables term).symm

theorem substituteRulePathReadout_composition {ruleSort outputSort : S.Srt} {context : Binding.Ctx S}
    (readout : ScopedRulePathReadout S ruleSort outputSort context)
    (middle destination : Binding.Ctx S) (first : Binding.Sub S context middle)
    (second : Binding.Sub S middle destination) :
    substituteRulePathReadout readout destination (fun sort value => Binding.bind second (first sort value)) =
      substituteRulePathReadout (substituteRulePathReadout readout middle first) destination second := by
  rcases readout with ⟨hole, redex, reactum, path⟩
  let inner := substituteContext path middle first
  let outer := substituteContext inner.path destination second
  have whole := congrArg (rulePathReadout (source := (hole, ruleSort)) redex reactum)
    (substituteContext_composition path middle destination first second)
  refine whole.trans ?_
  change (⟨outer.holeContext,
      Binding.bind (fun sort value => Binding.bind outer.holeVariables (inner.holeVariables sort value)) redex,
      Binding.bind (fun sort value => Binding.bind outer.holeVariables (inner.holeVariables sort value)) reactum,
      outer.path⟩ : ScopedRulePathReadout S ruleSort outputSort destination) =
    ⟨outer.holeContext, Binding.bind outer.holeVariables (Binding.bind inner.holeVariables redex),
      Binding.bind outer.holeVariables (Binding.bind inner.holeVariables reactum), outer.path⟩
  exact congrArg₂ (fun (left right : Binding.Term S outer.holeContext ruleSort) =>
    (⟨outer.holeContext, left, right, outer.path⟩ : ScopedRulePathReadout S ruleSort outputSort destination))
    (Binding.bind_comp inner.holeVariables outer.holeVariables redex).symm
    (Binding.bind_comp inner.holeVariables outer.holeVariables reactum).symm

/-- All computational fields of a firing, with both entire context paths. -/
structure BindingFiringReadout (S : Binding.Signature) (Origins : Type r)
    (inputSort ruleSort outputSort : S.Srt) (context : Binding.Ctx S) where
  input : ScopedTermPathReadout S inputSort outputSort context
  origin : Origins
  rule : ScopedRulePathReadout S ruleSort outputSort context
  target : Binding.Term S context outputSort

def BindingFiringReadout.declaration {inputSort ruleSort outputSort : S.Srt} {context : Binding.Ctx S}
    (readout : BindingFiringReadout S Origins inputSort ruleSort outputSort context) :
    FramePermission.Declaration (bindingAction S) Origins where
  origin := readout.origin
  scope := (readout.rule.1, ruleSort)
  redex := readout.rule.2.1
  reactum := readout.rule.2.2.1

def substituteFiringReadout {inputSort ruleSort outputSort : S.Srt} {context : Binding.Ctx S}
    (readout : BindingFiringReadout S Origins inputSort ruleSort outputSort context)
    (destination : Binding.Ctx S) (sigma : Binding.Sub S context destination) :
    BindingFiringReadout S Origins inputSort ruleSort outputSort destination where
  input := substituteTermPathReadout readout.input destination sigma
  origin := readout.origin
  rule := substituteRulePathReadout readout.rule destination sigma
  target := Binding.bind sigma readout.target

theorem substituteFiringReadout_identity {inputSort ruleSort outputSort : S.Srt} {context : Binding.Ctx S}
    (readout : BindingFiringReadout S Origins inputSort ruleSort outputSort context) :
    substituteFiringReadout readout context (fun _ value => .var value) = readout := by
  cases readout with
  | mk input origin rule target =>
    change BindingFiringReadout.mk (substituteTermPathReadout input context (fun _ value => .var value))
      origin (substituteRulePathReadout rule context (fun _ value => .var value))
      (Binding.bind (fun _ value => .var value) target) = _
    rw [substituteTermPathReadout_identity, substituteRulePathReadout_identity, Binding.bind_id]

theorem substituteFiringReadout_composition {inputSort ruleSort outputSort : S.Srt} {context : Binding.Ctx S}
    (readout : BindingFiringReadout S Origins inputSort ruleSort outputSort context)
    (middle destination : Binding.Ctx S) (first : Binding.Sub S context middle)
    (second : Binding.Sub S middle destination) :
    substituteFiringReadout readout destination (fun sort value => Binding.bind second (first sort value)) =
      substituteFiringReadout (substituteFiringReadout readout middle first) destination second := by
  cases readout with
  | mk input origin rule target =>
    change BindingFiringReadout.mk
      (substituteTermPathReadout input destination (fun sort value => Binding.bind second (first sort value)))
      origin
      (substituteRulePathReadout rule destination (fun sort value => Binding.bind second (first sort value)))
      (Binding.bind (fun sort value => Binding.bind second (first sort value)) target) = _
    rw [substituteTermPathReadout_composition input middle destination first second,
      substituteRulePathReadout_composition rule middle destination first second,
      ←Binding.bind_comp first second target]
    rfl

variable {admitted : FramePermission.Declaration (bindingAction S) Origins → Prop}
variable {source target : Scope S}
variable {agent : Binding.Term S source.1 source.2} {next : Binding.Term S target.1 target.2}
variable {label : BindingContext S source target}

def rawFiringReadout
    (firing : FramePermission.RawFiring (admitted := admitted) agent (bindingContextArrow label) next) :
    BindingFiringReadout S Origins source.2 firing.declaration.scope.2 target.2 target.1 where
  input := ⟨source.1, agent, label⟩
  origin := firing.declaration.origin
  rule := ⟨firing.declaration.scope.1, firing.declaration.redex, firing.declaration.reactum,
    rawFiringReactionPath firing⟩
  target := next

theorem rawFiringReadout_declaration
    (firing : FramePermission.RawFiring (admitted := admitted) agent (bindingContextArrow label) next) :
    (rawFiringReadout firing).declaration = firing.declaration := rfl

theorem rawFiringSubstitution_readout
    (firing : FramePermission.RawFiring (admitted := admitted) agent (bindingContextArrow label) next)
    (destination : Binding.Ctx S) (sigma : Binding.Sub S target.1 destination) :
    rawFiringReadout (rawFiringSubstitution firing destination sigma) =
      substituteFiringReadout (rawFiringReadout firing) destination sigma := rfl

theorem rawFiringSubstitution_identity_readout
    (firing : FramePermission.RawFiring (admitted := admitted) agent (bindingContextArrow label) next) :
    rawFiringReadout (rawFiringSubstitution firing target.1 (fun _ value => .var value)) =
      rawFiringReadout firing :=
  (rawFiringSubstitution_readout firing target.1 (fun _ value => .var value)).trans
    (substituteFiringReadout_identity (rawFiringReadout firing))

theorem rawFiringSubstitution_composition_readout
    (firing : FramePermission.RawFiring (admitted := admitted) agent (bindingContextArrow label) next)
    (middle destination : Binding.Ctx S) (first : Binding.Sub S target.1 middle)
    (second : Binding.Sub S middle destination) :
    rawFiringReadout (rawFiringSubstitution (rawFiringSubstitution firing middle first) destination second) =
      rawFiringReadout (rawFiringSubstitution firing destination
        (fun sort value => Binding.bind second (first sort value))) := by
  change substituteFiringReadout (substituteFiringReadout (rawFiringReadout firing) middle first)
    destination second =
      substituteFiringReadout (rawFiringReadout firing) destination
        (fun sort value => Binding.bind second (first sort value))
  exact (substituteFiringReadout_composition (rawFiringReadout firing) middle destination first second).symm

theorem rawFiringSubstitution_identity_declaration
    (firing : FramePermission.RawFiring (admitted := admitted) agent (bindingContextArrow label) next) :
    (rawFiringSubstitution firing target.1 (fun _ value => .var value)).declaration = firing.declaration :=
  congrArg BindingFiringReadout.declaration (rawFiringSubstitution_identity_readout firing)

theorem rawFiringSubstitution_composition_declaration
    (firing : FramePermission.RawFiring (admitted := admitted) agent (bindingContextArrow label) next)
    (middle destination : Binding.Ctx S) (first : Binding.Sub S target.1 middle)
    (second : Binding.Sub S middle destination) :
    (rawFiringSubstitution (rawFiringSubstitution firing middle first) destination second).declaration =
      (rawFiringSubstitution firing destination
        (fun sort value => Binding.bind second (first sort value))).declaration :=
  congrArg BindingFiringReadout.declaration
    (rawFiringSubstitution_composition_readout firing middle destination first second)

theorem permittedFiringSubstitution_identity_readout (permission : PositionPermission S)
    (allowed : FramePermission.PermittedPath
      (framePermission S (uniformSlotPermission S permission)) label)
    (firing : FramePermission.Firing
      (permission := framePermission S (uniformSlotPermission S permission))
      (source := source) (target := target) (admitted := admitted)
      agent (permittedContextArrow label allowed) next) :
    rawFiringReadout
      (permittedFiringSubstitution permission allowed firing target.1 (fun _ value => .var value)).raw =
      rawFiringReadout firing.raw := by
  exact rawFiringSubstitution_identity_readout firing.raw

theorem permittedFiringSubstitution_composition_readout (permission : PositionPermission S)
    (allowed : FramePermission.PermittedPath
      (framePermission S (uniformSlotPermission S permission)) label)
    (firing : FramePermission.Firing
      (permission := framePermission S (uniformSlotPermission S permission))
      (source := source) (target := target) (admitted := admitted)
      agent (permittedContextArrow label allowed) next)
    (middle destination : Binding.Ctx S) (first : Binding.Sub S target.1 middle)
    (second : Binding.Sub S middle destination) :
    rawFiringReadout
      (permittedFiringSubstitution permission
        ((substituteContext_permission_iff permission label middle first).mpr allowed)
        (permittedFiringSubstitution permission allowed firing middle first) destination second).raw =
      rawFiringReadout (permittedFiringSubstitution permission allowed firing destination
        (fun sort value => Binding.bind second (first sort value))).raw := by
  exact rawFiringSubstitution_composition_readout firing.raw middle destination first second

end Mettapedia.OSLF.Binding.ScopedEncoding
