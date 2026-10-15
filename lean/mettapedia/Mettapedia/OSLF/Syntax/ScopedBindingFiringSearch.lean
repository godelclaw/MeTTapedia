import Mettapedia.OSLF.Syntax.ScopedBindingFactors
import Mettapedia.OSLF.Syntax.ScopedBindingFiringSubstitution
import Mathlib.Data.List.ProdSigma

/-!
# Executable fixed-label search for complete raw binding firings

The supplied declaration list contains actual rules, including their full
scopes, redexes, reacta and origins. Search keeps the original list position
and every complete factor of the independently filled label. Its only
tests are literal scope/term equality and the earned outer-slot IPO test.
Completeness is compared to the independently defined raw firing record.
The finite bound is for this supplied label and finite list of actual rule
instances; it does not solve higher-order instantiation or bound all labels.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedEncoding

open _root_.CategoryTheory
open Mettapedia.CategoryTheory.GroundPath

universe r

variable {S : Binding.Signature} {Origins : Type r}

local instance bindingFiringSearchQuiver : Quiver (Scope S) := bindingFrameQuiver S

variable [DecidableEq S.Srt] [∀ sort : S.Srt, DecidableEq (S.Op sort)]

instance bindingSlotCodeDecidableEq : DecidableEq (BindingSlotCode S) := by
  intro first second
  cases first with
  | mk sort operator position =>
    cases second with
    | mk otherSort otherOperator otherPosition =>
      by_cases sameSort : sort = otherSort
      · subst otherSort
        by_cases sameOperator : operator = otherOperator
        · subst otherOperator
          exact decidable_of_iff (position = otherPosition) (by
            simp only [BindingSlotCode.mk.injEq, heq_eq_eq, eq_self, true_and])
        · exact isFalse (fun same => by cases same; exact sameOperator rfl)
      · exact isFalse (fun same => by cases same; exact sameSort rfl)

instance sharedOuterSlotDecidable {first second target : Scope S}
    (left : BindingContext S first target) (right : BindingContext S second target) :
    Decidable (SharedOuterSlot left right) := by
  unfold SharedOuterSlot
  cases leftSlot : lastSlot left with
  | none => exact isFalse (by rintro ⟨_, same, _⟩; cases same)
  | some firstCode =>
    cases rightSlot : lastSlot right with
    | none => exact isFalse (by rintro ⟨_, _, same⟩; cases same)
    | some secondCode =>
      exact decidable_of_iff (firstCode = secondCode) (by
        constructor
        · intro same
          exact ⟨firstCode, rfl, congrArg some same.symm⟩
        · rintro ⟨code, firstRead, secondRead⟩
          exact (Option.some.inj firstRead).trans (Option.some.inj secondRead).symm)

def BindingFactor.isRedex {target : Scope S} (factor : BindingFactor S target)
    (declaration : FramePermission.Declaration (bindingAction S) Origins) : Prop :=
  factor.source = declaration.scope ∧ HEq factor.value declaration.redex

instance bindingFactorIsRedexDecidable {target : Scope S} (factor : BindingFactor S target)
    (declaration : FramePermission.Declaration (bindingAction S) Origins) :
    Decidable (factor.isRedex declaration) := by
  cases factor with
  | mk source value path =>
    cases declaration with
    | mk origin scope redex reactum =>
      change Decidable (source = scope ∧ HEq value redex)
      by_cases sameScope : source = scope
      · subst scope
        change Binding.Term S source.1 source.2 at redex reactum
        exact decidable_of_iff (value = redex)
          ⟨fun same => ⟨rfl, heq_of_eq same⟩, fun same => eq_of_heq same.2⟩
      · exact isFalse (fun same => sameScope same.1)

structure BindingFiringCandidate (S : Binding.Signature) (Origins : Type r)
    (target : Scope S) (declarations : List (FramePermission.Declaration (bindingAction S) Origins)) where
  position : Fin declarations.length
  factor : BindingFactor S target

variable {declarations : List (FramePermission.Declaration (bindingAction S) Origins)}
variable {source target : Scope S}

def BindingFiringCandidate.declaration (candidate : BindingFiringCandidate S Origins target declarations) :
    FramePermission.Declaration (bindingAction S) Origins := declarations.get candidate.position

def BindingFiringCandidate.accepted (candidate : BindingFiringCandidate S Origins target declarations)
    (label : BindingContext S source target) : Prop :=
  candidate.factor.isRedex candidate.declaration ∧ ¬SharedOuterSlot label candidate.factor.path

instance bindingFiringCandidateAcceptedDecidable
    (candidate : BindingFiringCandidate S Origins target declarations)
    (label : BindingContext S source target) : Decidable (candidate.accepted label) :=
  inferInstanceAs (Decidable
    (candidate.factor.isRedex candidate.declaration ∧ ¬SharedOuterSlot label candidate.factor.path))

def bindingFiringCandidates (agent : Binding.Term S source.1 source.2)
    (label : BindingContext S source target)
    (declarations : List (FramePermission.Declaration (bindingAction S) Origins)) :
    List (BindingFiringCandidate S Origins target declarations) :=
  ((List.finRange declarations.length).product (bindingFactors (fillContext label agent))).map
    (fun selected => ⟨selected.1, selected.2⟩)

def bindingFiringSearch (agent : Binding.Term S source.1 source.2)
    (label : BindingContext S source target)
    (declarations : List (FramePermission.Declaration (bindingAction S) Origins)) :
    List (BindingFiringCandidate S Origins target declarations) :=
  (bindingFiringCandidates agent label declarations).filter (fun candidate => decide (candidate.accepted label))

omit [DecidableEq S.Srt] [∀ sort : S.Srt, DecidableEq (S.Op sort)] in
theorem mem_bindingFiringCandidates (agent : Binding.Term S source.1 source.2)
    (label : BindingContext S source target)
    (candidate : BindingFiringCandidate S Origins target declarations) :
    candidate ∈ bindingFiringCandidates agent label declarations ↔
      candidate.factor.fill = fillContext label agent := by
  constructor
  · intro member
    obtain ⟨selected, selectedMember, same⟩ := List.mem_map.mp member
    have factorMember := (List.mem_product.mp selectedMember).2
    cases same
    exact bindingFactors_sound _ _ factorMember
  · intro same
    apply List.mem_map.mpr
    refine ⟨(candidate.position, candidate.factor), ?_, ?_⟩
    · exact List.mem_product.mpr ⟨List.mem_finRange candidate.position,
        (mem_bindingFactors_iff _ _).mpr same⟩
    · cases candidate
      rfl

theorem mem_bindingFiringSearch (agent : Binding.Term S source.1 source.2)
    (label : BindingContext S source target)
    (candidate : BindingFiringCandidate S Origins target declarations) :
    candidate ∈ bindingFiringSearch agent label declarations ↔
      candidate.factor.fill = fillContext label agent ∧ candidate.accepted label := by
  change candidate ∈ (bindingFiringCandidates agent label declarations).filter _ ↔ _
  rw [List.mem_filter]
  exact and_congr (mem_bindingFiringCandidates agent label candidate)
    (by simp only [decide_eq_true_eq])

omit [DecidableEq S.Srt] [∀ sort : S.Srt, DecidableEq (S.Op sort)] in
theorem bindingFiringCandidates_length (agent : Binding.Term S source.1 source.2)
    (label : BindingContext S source target)
    (declarations : List (FramePermission.Declaration (bindingAction S) Origins)) :
    (bindingFiringCandidates agent label declarations).length =
      declarations.length * Binding.termSize (fillContext label agent) := by
  unfold bindingFiringCandidates
  rw [List.length_map]
  exact (List.length_product (List.finRange declarations.length)
    (bindingFactors (fillContext label agent))).trans
      (congrArg₂ Nat.mul List.length_finRange (bindingFactors_length _))

theorem bindingFiringSearch_length_le (agent : Binding.Term S source.1 source.2)
    (label : BindingContext S source target)
    (declarations : List (FramePermission.Declaration (bindingAction S) Origins)) :
    (bindingFiringSearch agent label declarations).length ≤
      declarations.length * Binding.termSize (fillContext label agent) := by
  exact (List.length_filter_le _ _).trans_eq (bindingFiringCandidates_length agent label declarations)

def BindingFiringCandidate.reaction (candidate : BindingFiringCandidate S Origins target declarations)
    (label : BindingContext S source target) (accepted : candidate.accepted label) :
    BindingContext S candidate.declaration.scope target := accepted.1.1 ▸ candidate.factor.path

def BindingFiringCandidate.result (candidate : BindingFiringCandidate S Origins target declarations)
    (label : BindingContext S source target) (accepted : candidate.accepted label) :
    Binding.Term S target.1 target.2 := fillContext (candidate.reaction label accepted) candidate.declaration.reactum

omit [DecidableEq S.Srt] [∀ sort : S.Srt, DecidableEq (S.Op sort)] in
theorem BindingFiringCandidate.reaction_redex
    (candidate : BindingFiringCandidate S Origins target declarations)
    (label : BindingContext S source target) (accepted : candidate.accepted label) :
    fillContext (candidate.reaction label accepted) candidate.declaration.redex = candidate.factor.fill := by
  rcases candidate with ⟨position, factor⟩
  rcases factor with ⟨scope, value, path⟩
  obtain ⟨⟨sameScope, sameValue⟩, separated⟩ := accepted
  change scope = (declarations.get position).scope at sameScope
  subst scope
  have same : value = (declarations.get position).redex := eq_of_heq sameValue
  subst value
  rfl

omit [DecidableEq S.Srt] [∀ sort : S.Srt, DecidableEq (S.Op sort)] in
theorem BindingFiringCandidate.reaction_separated
    (candidate : BindingFiringCandidate S Origins target declarations)
    (label : BindingContext S source target) (accepted : candidate.accepted label) :
    ¬SharedOuterSlot label (candidate.reaction label accepted) := by
  rcases candidate with ⟨position, factor⟩
  rcases factor with ⟨scope, value, path⟩
  obtain ⟨⟨sameScope, sameValue⟩, separated⟩ := accepted
  change scope = (declarations.get position).scope at sameScope
  subst scope
  exact separated

def bindingFiringSearchSelected (agent : Binding.Term S source.1 source.2)
    (label : BindingContext S source target)
    (candidate : BindingFiringCandidate S Origins target declarations)
    (member : candidate ∈ bindingFiringSearch agent label declarations) :
    FramePermission.RawFiring (admitted := fun declaration => declaration ∈ declarations)
      agent (bindingContextArrow label)
      (candidate.result label ((mem_bindingFiringSearch agent label candidate).mp member).2) := by
  let accepted := ((mem_bindingFiringSearch agent label candidate).mp member).2
  have matching : fillContext label agent =
      fillContext (candidate.reaction label accepted) candidate.declaration.redex :=
    (((candidate.reaction_redex label accepted).trans
      ((mem_bindingFiringSearch agent label candidate).mp member).1)).symm
  let square := congrArg (bindingTermArrow (S := S) (scope := target)) matching
  exact {
    declaration := candidate.declaration
    admitted := List.get_mem declarations candidate.position
    reaction := bindingContextArrow (candidate.reaction label accepted)
    square := square
    minimal := binding_ipo_of_no_shared_outer_slot agent candidate.declaration.redex
      label (candidate.reaction label accepted) square (candidate.reaction_separated label accepted)
    target_readout := rfl }

theorem bindingFiringSearchSelected_complete_declaration
    (agent : Binding.Term S source.1 source.2) (label : BindingContext S source target)
    (candidate : BindingFiringCandidate S Origins target declarations)
    (member : candidate ∈ bindingFiringSearch agent label declarations) :
    (bindingFiringSearchSelected agent label candidate member).declaration =
      declarations.get candidate.position := rfl

theorem bindingFiringSearchSelected_complete_target
    (agent : Binding.Term S source.1 source.2) (label : BindingContext S source target)
    (candidate : BindingFiringCandidate S Origins target declarations)
    (member : candidate ∈ bindingFiringSearch agent label declarations) :
    (candidate.result label ((mem_bindingFiringSearch agent label candidate).mp member).2) =
      fillContext (rawFiringReactionPath (bindingFiringSearchSelected agent label candidate member))
        (declarations.get candidate.position).reactum := rfl

theorem bindingFiringSearch_complete
    (agent : Binding.Term S source.1 source.2) (label : BindingContext S source target)
    (next : Binding.Term S target.1 target.2)
    (firing : FramePermission.RawFiring (admitted := fun declaration => declaration ∈ declarations)
      agent (bindingContextArrow label) next) :
    ∃ candidate : BindingFiringCandidate S Origins target declarations,
      ∃ member : candidate ∈ bindingFiringSearch agent label declarations,
        candidate.declaration = firing.declaration ∧
        HEq (candidate.reaction label ((mem_bindingFiringSearch agent label candidate).mp member).2)
          (rawFiringReactionPath firing) ∧
        candidate.result label ((mem_bindingFiringSearch agent label candidate).mp member).2 = next := by
  rcases firing with ⟨declaration, admission, reaction, square, minimal, targetReadout⟩
  cases reaction with
  | context path =>
    obtain ⟨position, sameDeclaration⟩ := List.mem_iff_get.mp admission
    subst declaration
    let candidate : BindingFiringCandidate S Origins target declarations :=
      ⟨position, ⟨(declarations.get position).scope, (declarations.get position).redex, path⟩⟩
    have accepted : candidate.accepted label :=
      ⟨⟨rfl, HEq.rfl⟩, binding_ipo_excludes_shared_outer_slot agent
        (declarations.get position).redex label path square minimal⟩
    have member : candidate ∈ bindingFiringSearch agent label declarations :=
      (mem_bindingFiringSearch agent label candidate).mpr
        ⟨(Arrow.value.inj square).symm, accepted⟩
    refine ⟨candidate, member, rfl, HEq.rfl, ?_⟩
    exact (Arrow.value.inj targetReadout).symm

theorem bindingFiringSearch_nonempty_iff
    (agent : Binding.Term S source.1 source.2) (label : BindingContext S source target) :
    bindingFiringSearch agent label declarations ≠ [] ↔
      ∃ next : Binding.Term S target.1 target.2,
        Nonempty (FramePermission.RawFiring (admitted := fun declaration => declaration ∈ declarations)
          agent (bindingContextArrow label) next) := by
  constructor
  · intro nonempty
    obtain ⟨candidate, member⟩ := List.exists_mem_of_ne_nil _ nonempty
    exact ⟨_, ⟨bindingFiringSearchSelected agent label candidate member⟩⟩
  · rintro ⟨next, ⟨firing⟩⟩ empty
    obtain ⟨candidate, member, _⟩ := bindingFiringSearch_complete agent label next firing
    rw [empty] at member
    exact List.not_mem_nil member

end Mettapedia.OSLF.Binding.ScopedEncoding
