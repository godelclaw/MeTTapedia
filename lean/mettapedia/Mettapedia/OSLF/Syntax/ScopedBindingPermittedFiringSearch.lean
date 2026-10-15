import Mettapedia.OSLF.Syntax.ScopedBindingFiringSearch

/-!
# Executable complete search in the actual permitted binding category

The supplied label has an independently checked whole-path permission.
Reaction permission is tested separately on every enumerated complete
path. The resulting search is sound and complete for the existing actual
restricted firing record, not just for its own acceptance predicate.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedEncoding

open _root_.CategoryTheory
open Mettapedia.CategoryTheory.GroundPath

universe r

variable {S : Binding.Signature} {Origins : Type r}

local instance bindingPermittedSearchQuiver : Quiver (Scope S) := bindingFrameQuiver S

variable (permission : SlotPermission S)

instance bindingPermittedPathDecidable
    [∀ context sort operator position, Decidable (permission context sort operator position)]
    {source target : Scope S} (path : BindingContext S source target) :
    Decidable (FramePermission.PermittedPath (framePermission S permission) path) := by
  induction path with
  | nil => exact isTrue (.nil _)
  | cons previous frame previousDecision =>
      cases frame with
      | slot context sort operator position siblings =>
        letI := previousDecision
        exact decidable_of_iff
          (FramePermission.PermittedPath (framePermission S permission) previous ∧
            permission context sort operator position)
          ⟨fun allowed => .cons allowed.1 allowed.2,
            fun allowed => by cases allowed; exact ⟨‹_›, ‹_›⟩⟩

variable {permission}
variable [DecidableEq S.Srt] [∀ sort : S.Srt, DecidableEq (S.Op sort)]
variable [∀ context sort operator position, Decidable (permission context sort operator position)]
variable {source target : Scope S}
variable {declarations : List (FramePermission.Declaration (bindingAction S) Origins)}

def bindingPermittedFiringSearch (agent : Binding.Term S source.1 source.2)
    (label : BindingContext S source target)
    (declarations : List (FramePermission.Declaration (bindingAction S) Origins)) :
    List (BindingFiringCandidate S Origins target declarations) :=
  (bindingFiringSearch agent label declarations).filter (fun candidate =>
    decide (FramePermission.PermittedPath (framePermission S permission) candidate.factor.path))

theorem mem_bindingPermittedFiringSearch (agent : Binding.Term S source.1 source.2)
    (label : BindingContext S source target)
    (candidate : BindingFiringCandidate S Origins target declarations) :
    candidate ∈ bindingPermittedFiringSearch (permission := permission) agent label declarations ↔
      candidate ∈ bindingFiringSearch agent label declarations ∧
        FramePermission.PermittedPath (framePermission S permission) candidate.factor.path := by
  unfold bindingPermittedFiringSearch
  rw [List.mem_filter]
  exact and_congr Iff.rfl (by simp only [decide_eq_true_eq])

omit [DecidableEq S.Srt] [∀ sort : S.Srt, DecidableEq (S.Op sort)]
    [∀ context sort operator position, Decidable (permission context sort operator position)] in
theorem BindingFiringCandidate.reaction_permitted
    (candidate : BindingFiringCandidate S Origins target declarations)
    (label : BindingContext S source target) (accepted : candidate.accepted label)
    (allowed : FramePermission.PermittedPath (framePermission S permission) candidate.factor.path) :
    FramePermission.PermittedPath (framePermission S permission) (candidate.reaction label accepted) := by
  rcases candidate with ⟨position, factor⟩
  rcases factor with ⟨scope, value, path⟩
  obtain ⟨⟨sameScope, sameValue⟩, separated⟩ := accepted
  change scope = (declarations.get position).scope at sameScope
  subst scope
  exact allowed

def bindingPermittedFiringSearchSelected
    (agent : Binding.Term S source.1 source.2) (label : BindingContext S source target)
    (labelAllowed : FramePermission.PermittedPath (framePermission S permission) label)
    (candidate : BindingFiringCandidate S Origins target declarations)
    (member : candidate ∈ bindingPermittedFiringSearch (permission := permission) agent label declarations) :
    FramePermission.Firing (permission := framePermission S permission)
      (admitted := fun declaration => declaration ∈ declarations)
      agent (permittedContextArrow label labelAllowed)
      (candidate.result label ((mem_bindingFiringSearch agent label candidate).mp
        ((mem_bindingPermittedFiringSearch agent label candidate).mp member).1).2) := by
  let rawMember := ((mem_bindingPermittedFiringSearch agent label candidate).mp member).1
  let allowed := ((mem_bindingPermittedFiringSearch agent label candidate).mp member).2
  exact (bindingFiringSearchSelected agent label candidate rawMember).restrict
    (.context (candidate.reaction_permitted label
      ((mem_bindingFiringSearch agent label candidate).mp rawMember).2 allowed))

theorem bindingPermittedFiringSearchSelected_complete_raw
    (agent : Binding.Term S source.1 source.2) (label : BindingContext S source target)
    (labelAllowed : FramePermission.PermittedPath (framePermission S permission) label)
    (candidate : BindingFiringCandidate S Origins target declarations)
    (member : candidate ∈ bindingPermittedFiringSearch (permission := permission) agent label declarations) :
    (bindingPermittedFiringSearchSelected agent label labelAllowed candidate member).raw =
      bindingFiringSearchSelected agent label candidate
        ((mem_bindingPermittedFiringSearch agent label candidate).mp member).1 :=
  FramePermission.restrict_raw _ _

theorem bindingPermittedFiringSearch_complete
    (agent : Binding.Term S source.1 source.2) (label : BindingContext S source target)
    (labelAllowed : FramePermission.PermittedPath (framePermission S permission) label)
    (next : Binding.Term S target.1 target.2)
    (firing : FramePermission.Firing (permission := framePermission S permission)
      (admitted := fun declaration => declaration ∈ declarations)
      agent (permittedContextArrow label labelAllowed) next) :
    ∃ candidate : BindingFiringCandidate S Origins target declarations,
      ∃ member : candidate ∈ bindingPermittedFiringSearch (permission := permission) agent label declarations,
        candidate.declaration = firing.declaration ∧
        HEq (candidate.reaction label ((mem_bindingFiringSearch agent label candidate).mp
          ((mem_bindingPermittedFiringSearch agent label candidate).mp member).1).2)
          (rawFiringReactionPath firing.raw) ∧
        candidate.result label ((mem_bindingFiringSearch agent label candidate).mp
          ((mem_bindingPermittedFiringSearch agent label candidate).mp member).1).2 = next := by
  rcases firing with ⟨declaration, admission, ⟨reaction, reactionAllowed⟩, square, minimal, targetReadout⟩
  cases reaction with
  | context path =>
    cases reactionAllowed with
    | context pathAllowed =>
      obtain ⟨position, sameDeclaration⟩ := List.mem_iff_get.mp admission
      subst declaration
      let candidate : BindingFiringCandidate S Origins target declarations :=
        ⟨position, ⟨(declarations.get position).scope, (declarations.get position).redex, path⟩⟩
      have rawSquare := congrArg Subtype.val square
      have rawMinimal := (FramePermission.idemPushout_iff (framePermission S permission)
        (bindingAction S) square).mp minimal
      have accepted : candidate.accepted label :=
        ⟨⟨rfl, HEq.rfl⟩, binding_ipo_excludes_shared_outer_slot agent
          (declarations.get position).redex label path rawSquare rawMinimal⟩
      have rawMember : candidate ∈ bindingFiringSearch agent label declarations :=
        (mem_bindingFiringSearch agent label candidate).mpr
          ⟨(Arrow.value.inj rawSquare).symm, accepted⟩
      have member : candidate ∈ bindingPermittedFiringSearch (permission := permission) agent label declarations :=
        (mem_bindingPermittedFiringSearch agent label candidate).mpr ⟨rawMember, pathAllowed⟩
      refine ⟨candidate, member, rfl, HEq.rfl, ?_⟩
      exact (Arrow.value.inj (congrArg Subtype.val targetReadout)).symm

theorem bindingPermittedFiringSearch_nonempty_iff
    (agent : Binding.Term S source.1 source.2) (label : BindingContext S source target)
    (labelAllowed : FramePermission.PermittedPath (framePermission S permission) label) :
    bindingPermittedFiringSearch (permission := permission) agent label declarations ≠ [] ↔
      ∃ next : Binding.Term S target.1 target.2,
        Nonempty (FramePermission.Firing (permission := framePermission S permission)
          (admitted := fun declaration => declaration ∈ declarations)
          agent (permittedContextArrow label labelAllowed) next) := by
  constructor
  · intro nonempty
    obtain ⟨candidate, member⟩ := List.exists_mem_of_ne_nil _ nonempty
    exact ⟨_, ⟨bindingPermittedFiringSearchSelected agent label labelAllowed candidate member⟩⟩
  · rintro ⟨next, ⟨firing⟩⟩ empty
    obtain ⟨candidate, member, _⟩ := bindingPermittedFiringSearch_complete agent label labelAllowed next firing
    rw [empty] at member
    exact List.not_mem_nil member

theorem bindingPermittedFiringSearch_length_le
    (agent : Binding.Term S source.1 source.2) (label : BindingContext S source target)
    (declarations : List (FramePermission.Declaration (bindingAction S) Origins)) :
    (bindingPermittedFiringSearch (permission := permission) agent label declarations).length ≤
      declarations.length * Binding.termSize (fillContext label agent) :=
  (List.length_filter_le _ _).trans (bindingFiringSearch_length_le agent label declarations)

end Mettapedia.OSLF.Binding.ScopedEncoding
