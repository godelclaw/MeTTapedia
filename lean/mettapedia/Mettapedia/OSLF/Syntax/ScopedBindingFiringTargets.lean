import Mettapedia.OSLF.Syntax.ScopedBindingFiringSearchReceipts
import Mettapedia.OSLF.Syntax.ScopedBindingPermittedFiringSearch
import Mathlib.Data.Set.Finite.Basic

/-!
# Actual target fibres of the complete scoped firing search

The target lists project the independently earned complete receipts. Their
membership is equivalent to the existing raw or permitted firing relation,
and therefore decides that relation at a supplied complete target. Repeated
declaration positions and equal targets remain repeated list entries.

The finiteness theorem concerns one complete label and a finite list of
actual instantiated rules. It does not enumerate rule-schema instances or
charge complete structural comparisons as unit-cost observations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedEncoding

open Mettapedia.CategoryTheory.GroundPath

universe r

variable {S : Binding.Signature} {Origins : Type r}

local instance bindingFiringTargetQuiver : Quiver (Scope S) := bindingFrameQuiver S

variable [DecidableEq S.Srt] [∀ sort : S.Srt, DecidableEq (S.Op sort)]
variable {source target : Scope S}
variable {declarations : List (FramePermission.Declaration (bindingAction S) Origins)}

def bindingFiringTargets (agent : Binding.Term S source.1 source.2)
    (label : BindingContext S source target)
    (declarations : List (FramePermission.Declaration (bindingAction S) Origins)) :
    List (Binding.Term S target.1 target.2) :=
  (bindingFiringSearchReceipts agent label declarations).map (fun receipt => receipt.result)

theorem mem_bindingFiringTargets (agent : Binding.Term S source.1 source.2)
    (label : BindingContext S source target) (next : Binding.Term S target.1 target.2) :
    next ∈ bindingFiringTargets agent label declarations ↔
      Nonempty (FramePermission.RawFiring (source := source) (target := target)
        (admitted := fun declaration => declaration ∈ declarations)
        agent (bindingContextArrow label) next) := by
  constructor
  · intro member
    obtain ⟨receipt, _listed, rfl⟩ := List.mem_map.mp member
    exact ⟨receipt.firing⟩
  · rintro ⟨firing⟩
    obtain ⟨receipt, listed, _declarationRead, _reactionRead, targetRead⟩ :=
      bindingFiringSearchReceipts_complete agent label next firing
    exact List.mem_map.mpr ⟨receipt, listed, targetRead⟩

instance bindingRawFiringTargetDecidable (agent : Binding.Term S source.1 source.2)
    (label : BindingContext S source target) (next : Binding.Term S target.1 target.2) :
    Decidable (Nonempty (FramePermission.RawFiring (source := source) (target := target)
      (admitted := fun declaration => declaration ∈ declarations)
      agent (bindingContextArrow label) next)) :=
  decidable_of_iff (next ∈ bindingFiringTargets agent label declarations)
    (mem_bindingFiringTargets agent label next)

theorem bindingRawFiring_targets_finite (agent : Binding.Term S source.1 source.2)
    (label : BindingContext S source target) :
    Set.Finite {next : Binding.Term S target.1 target.2 |
      Nonempty (FramePermission.RawFiring (source := source) (target := target)
        (admitted := fun declaration => declaration ∈ declarations)
        agent (bindingContextArrow label) next)} := by
  have same : {next : Binding.Term S target.1 target.2 |
      Nonempty (FramePermission.RawFiring (source := source) (target := target)
        (admitted := fun declaration => declaration ∈ declarations)
        agent (bindingContextArrow label) next)} =
      {next | next ∈ bindingFiringTargets agent label declarations} := by
    ext next
    exact (mem_bindingFiringTargets agent label next).symm
  rw [same]
  exact List.finite_toSet _

theorem bindingFiringTargets_length_le (agent : Binding.Term S source.1 source.2)
    (label : BindingContext S source target)
    (declarations : List (FramePermission.Declaration (bindingAction S) Origins)) :
    (bindingFiringTargets agent label declarations).length ≤
      declarations.length * Binding.termSize (fillContext label agent) := by
  unfold bindingFiringTargets
  rw [List.length_map, bindingFiringSearchReceipts_length]
  exact bindingFiringSearch_length_le agent label declarations

variable {permission : SlotPermission S}
variable [∀ context sort operator position, Decidable (permission context sort operator position)]

def bindingPermittedFiringTargets (agent : Binding.Term S source.1 source.2)
    (label : BindingContext S source target)
    (declarations : List (FramePermission.Declaration (bindingAction S) Origins)) :
    List (Binding.Term S target.1 target.2) :=
  (bindingPermittedFiringSearch (permission := permission) agent label declarations).attach.map
    (fun selected => selected.val.result label
      ((mem_bindingFiringSearch agent label selected.val).mp
        ((mem_bindingPermittedFiringSearch agent label selected.val).mp selected.property).1).2)

theorem mem_bindingPermittedFiringTargets (agent : Binding.Term S source.1 source.2)
    (label : BindingContext S source target)
    (labelAllowed : FramePermission.PermittedPath (framePermission S permission) label)
    (next : Binding.Term S target.1 target.2) :
    next ∈ bindingPermittedFiringTargets (permission := permission) agent label declarations ↔
      Nonempty (FramePermission.Firing (source := source) (target := target)
        (permission := framePermission S permission)
        (admitted := fun declaration => declaration ∈ declarations)
        agent (permittedContextArrow label labelAllowed) next) := by
  constructor
  · intro member
    obtain ⟨selected, _listed, rfl⟩ := List.mem_map.mp member
    exact ⟨bindingPermittedFiringSearchSelected agent label labelAllowed
      selected.val selected.property⟩
  · rintro ⟨firing⟩
    obtain ⟨candidate, member, _declarationRead, _reactionRead, targetRead⟩ :=
      bindingPermittedFiringSearch_complete agent label labelAllowed next firing
    exact List.mem_map.mpr ⟨⟨candidate, member⟩, List.mem_attach _ _, targetRead⟩

instance bindingPermittedFiringTargetDecidable (agent : Binding.Term S source.1 source.2)
    (label : BindingContext S source target)
    (labelAllowed : FramePermission.PermittedPath (framePermission S permission) label)
    (next : Binding.Term S target.1 target.2) :
    Decidable (Nonempty (FramePermission.Firing (source := source) (target := target)
      (permission := framePermission S permission)
      (admitted := fun declaration => declaration ∈ declarations)
      agent (permittedContextArrow label labelAllowed) next)) :=
  decidable_of_iff (next ∈ bindingPermittedFiringTargets (permission := permission) agent label declarations)
    (mem_bindingPermittedFiringTargets agent label labelAllowed next)

theorem bindingPermittedFiring_targets_finite (agent : Binding.Term S source.1 source.2)
    (label : BindingContext S source target)
    (labelAllowed : FramePermission.PermittedPath (framePermission S permission) label) :
    Set.Finite {next : Binding.Term S target.1 target.2 |
      Nonempty (FramePermission.Firing (source := source) (target := target)
        (permission := framePermission S permission)
        (admitted := fun declaration => declaration ∈ declarations)
        agent (permittedContextArrow label labelAllowed) next)} := by
  have same : {next : Binding.Term S target.1 target.2 |
      Nonempty (FramePermission.Firing (source := source) (target := target)
        (permission := framePermission S permission)
        (admitted := fun declaration => declaration ∈ declarations)
        agent (permittedContextArrow label labelAllowed) next)} =
      {next | next ∈ bindingPermittedFiringTargets (permission := permission) agent label declarations} := by
    ext next
    exact (mem_bindingPermittedFiringTargets agent label labelAllowed next).symm
  rw [same]
  exact List.finite_toSet _

theorem bindingPermittedFiringTargets_length_le (agent : Binding.Term S source.1 source.2)
    (label : BindingContext S source target)
    (declarations : List (FramePermission.Declaration (bindingAction S) Origins)) :
    (bindingPermittedFiringTargets (permission := permission) agent label declarations).length ≤
      declarations.length * Binding.termSize (fillContext label agent) := by
  unfold bindingPermittedFiringTargets
  rw [List.length_map, List.length_attach]
  exact bindingPermittedFiringSearch_length_le agent label declarations

end Mettapedia.OSLF.Binding.ScopedEncoding
