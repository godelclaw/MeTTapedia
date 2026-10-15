import Mettapedia.OSLF.Syntax.ScopedBindingFiringSearch

/-!
# Actual complete firing receipts from the executable search

Every successful search entry yields an earned raw firing, retaining the
original declaration-list position and the entire independently computed
target. Conversely, every independently supplied admitted raw firing has
a corresponding receipt with its full declaration and reaction path.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedEncoding

open Mettapedia.CategoryTheory.GroundPath

universe r

variable {S : Binding.Signature} {Origins : Type r}

local instance bindingFiringReceiptQuiver : Quiver (Scope S) := bindingFrameQuiver S

variable [DecidableEq S.Srt] [∀ sort : S.Srt, DecidableEq (S.Op sort)]
variable {source target : Scope S}
variable {declarations : List (FramePermission.Declaration (bindingAction S) Origins)}

structure BindingFiringSearchReceipt
    (agent : Binding.Term S source.1 source.2) (label : BindingContext S source target)
    (declarations : List (FramePermission.Declaration (bindingAction S) Origins)) where
  candidate : BindingFiringCandidate S Origins target declarations
  member : candidate ∈ bindingFiringSearch agent label declarations

def BindingFiringSearchReceipt.result
    {agent : Binding.Term S source.1 source.2} {label : BindingContext S source target}
    (receipt : BindingFiringSearchReceipt agent label declarations) : Binding.Term S target.1 target.2 :=
  receipt.candidate.result label ((mem_bindingFiringSearch agent label receipt.candidate).mp receipt.member).2

def BindingFiringSearchReceipt.firing
    {agent : Binding.Term S source.1 source.2} {label : BindingContext S source target}
    (receipt : BindingFiringSearchReceipt agent label declarations) :
    FramePermission.RawFiring (admitted := fun declaration => declaration ∈ declarations)
      agent (bindingContextArrow label) receipt.result :=
  bindingFiringSearchSelected agent label receipt.candidate receipt.member

def bindingFiringSearchReceipts
    (agent : Binding.Term S source.1 source.2) (label : BindingContext S source target)
    (declarations : List (FramePermission.Declaration (bindingAction S) Origins)) :
    List (BindingFiringSearchReceipt agent label declarations) :=
  (bindingFiringSearch agent label declarations).attach.map
    (fun selected => ⟨selected.val, selected.property⟩)

theorem BindingFiringSearchReceipt.retained_declaration
    {agent : Binding.Term S source.1 source.2} {label : BindingContext S source target}
    (receipt : BindingFiringSearchReceipt agent label declarations) :
    receipt.firing.declaration = declarations.get receipt.candidate.position := rfl

theorem BindingFiringSearchReceipt.retained_origin
    {agent : Binding.Term S source.1 source.2} {label : BindingContext S source target}
    (receipt : BindingFiringSearchReceipt agent label declarations) :
    receipt.firing.declaration.origin = (declarations.get receipt.candidate.position).origin := rfl

theorem BindingFiringSearchReceipt.complete_result
    {agent : Binding.Term S source.1 source.2} {label : BindingContext S source target}
    (receipt : BindingFiringSearchReceipt agent label declarations) :
    receipt.result = fillContext (rawFiringReactionPath receipt.firing)
      (declarations.get receipt.candidate.position).reactum := rfl

theorem bindingFiringSearchReceipts_complete
    (agent : Binding.Term S source.1 source.2) (label : BindingContext S source target)
    (next : Binding.Term S target.1 target.2)
    (firing : FramePermission.RawFiring (admitted := fun declaration => declaration ∈ declarations)
      agent (bindingContextArrow label) next) :
    ∃ receipt ∈ bindingFiringSearchReceipts agent label declarations,
      receipt.firing.declaration = firing.declaration ∧
      HEq (rawFiringReactionPath receipt.firing) (rawFiringReactionPath firing) ∧
      receipt.result = next := by
  obtain ⟨candidate, member, declarationRead, reactionRead, targetRead⟩ :=
    bindingFiringSearch_complete agent label next firing
  let receipt : BindingFiringSearchReceipt agent label declarations := ⟨candidate, member⟩
  refine ⟨receipt, ?_, declarationRead, reactionRead, targetRead⟩
  apply List.mem_map.mpr
  refine ⟨⟨candidate, member⟩, List.mem_attach _ _, rfl⟩

theorem bindingFiringSearchReceipts_length
    (agent : Binding.Term S source.1 source.2) (label : BindingContext S source target)
    (declarations : List (FramePermission.Declaration (bindingAction S) Origins)) :
    (bindingFiringSearchReceipts agent label declarations).length =
      (bindingFiringSearch agent label declarations).length := by
  unfold bindingFiringSearchReceipts
  rw [List.length_map, List.length_attach]

end Mettapedia.OSLF.Binding.ScopedEncoding
