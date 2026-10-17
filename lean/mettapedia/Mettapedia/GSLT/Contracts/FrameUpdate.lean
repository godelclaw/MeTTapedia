import Mettapedia.GSLT.Logic.SeparationTransport

/-!
# Frame-preserving updates of authority

A separation algebra says which resources can be held side by side.  Read as
authority, an element is what one party may do, and the elements separate
from it are its *frames*: what other parties may hold at the same time.  An
update from `a` to `b` is **frame-preserving** when every frame of `a` is
still a frame of `b`: converting `a` into `b` invalidates nothing that anybody
else could have been holding.  This is the deterministic frame-preserving
update of the resource algebras of the Iris program logic, with separateness in
the role of validity, and the authority shadow of the action judgement of the
Views framework (Dinsdale-Young, Birkedal, Gardner, Parkinson and Yang,
POPL 2013); see `Mettapedia.GSLT.Contracts.ReifiedActions`.

## The order

* `FrameUpdate a b` is a preorder (`refl`, `trans`).  Discarding is always
  allowed (`to_zero`), and updates are stable under adding a separate frame
  (`add_right`, `add`).  So a separation algebra with its frame-preserving
  updates is a commutative monoid, on separate pairs, preordered compatibly
  with its addition: the preorder of a resource theory in the sense of Coecke,
  Fritz and Spekkens, where the order says which conversions are free.

## Two kinds of authority

* `Exclusive a`: `a` is not empty and nothing else can be held beside it.  An
  exclusive holder may update to anything (`Exclusive.frameUpdate`).
* `Shared a`: something non-empty can be held beside `a`.
* **Shared authority never updates to exclusive authority**
  (`not_frameUpdate_of_shared_exclusive`).  A read permission is shared, a
  consume permission is exclusive, so reading never becomes consuming by an
  update.  The converse direction, weakening exclusive authority to a shared
  one, is always allowed.

## Transport between algebras

A change of world or representation carries authority along a resource
homomorphism (`SeparationTransport.Hom`).

* Self-separate authority stays self-separate along every homomorphism
  (`selfSeparate_map`), hence never becomes exclusive
  (`not_exclusive_map_of_selfSeparate`).
* Shared authority stays shared along every homomorphism that erases no
  resource (`shared_map`).  The hypothesis is needed: a homomorphism that
  erases a co-holder can make the remaining holder exclusive (the control
  `AuthorityControls.revokeRight_upgrades`).
* A homomorphism preserves frame-preserving updates when it lifts extensions
  (`preservesUpdates_of_liftsExtensions`).  Lifting extensions is the
  same condition under which reindexing preserves every separating
  implication (`SeparationTransport.Hom.liftsExtensions_iff_pull_wand`).  Being
  a homomorphism is not enough (`AuthorityControls.splitOwner_not_preservesUpdates`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts

open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.SeparationAlgebra.SepAlgebra
open Mettapedia.GSLT.Logic.SeparationTransport
open scoped Mettapedia.GSLT.SeparationAlgebra

universe u v w

section Order

variable {α : Type u} [Zero α] [Add α] [SepAlgebra α]

/-- The frames of a resource: what another party may hold beside it. -/
def frames (a : α) : Set α := {c | a ## c}

/-- **A frame-preserving update**: every frame of `a` is a frame of `b`. -/
def FrameUpdate (a b : α) : Prop := ∀ c, a ## c → b ## c

theorem frameUpdate_iff_frames_subset {a b : α} : FrameUpdate a b ↔ frames a ⊆ frames b :=
  Iff.rfl

namespace FrameUpdate

theorem refl (a : α) : FrameUpdate a a := fun _ separate => separate

theorem trans {a b c : α} (first : FrameUpdate a b) (second : FrameUpdate b c) :
    FrameUpdate a c :=
  fun frame separate => second frame (first frame separate)

/-- **Discarding is free**: every resource updates to the empty one. -/
theorem to_zero (a : α) : FrameUpdate a 0 := fun c _ => zero_separate c

/-- **Updates are stable under a separate frame.** -/
theorem add_right {a b c : α} (update : FrameUpdate a b) (separate : a ## c) :
    b ## c ∧ FrameUpdate (a + c) (b + c) := by
  refine ⟨update c separate, ?_⟩
  intro d separateSum
  obtain ⟨separateA, separateCD⟩ := separate_add_right separate separateSum
  exact (separate_add_left separateCD (update _ separateA)).1

/-- Updates on two separate parts combine. -/
theorem add {a b a' b' : α} (update : FrameUpdate a b) (update' : FrameUpdate a' b')
    (separate : a ## a') : b ## b' ∧ FrameUpdate (a + a') (b + b') := by
  obtain ⟨separateBA', left⟩ := update.add_right separate
  have separateA'B : a' ## b := separate_symm separateBA'
  obtain ⟨separateB'B, right⟩ := update'.add_right separateA'B
  refine ⟨separate_symm separateB'B, ?_⟩
  have swapLeft : b + a' = a' + b := SepAlgebra.add_comm separateBA'
  have swapRight : b' + b = b + b' := SepAlgebra.add_comm separateB'B
  intro d holds
  have middle := left d holds
  rw [swapLeft] at middle
  have last := right d middle
  rwa [swapRight] at last

end FrameUpdate

/-! ## Exclusive and shared authority -/

/-- **Exclusive authority**: non-empty, and only the empty resource can be held
beside it. -/
def Exclusive (a : α) : Prop := a ≠ 0 ∧ ∀ c, a ## c → c = 0

/-- **Shared authority**: something non-empty can be held beside it. -/
def Shared (a : α) : Prop := ∃ c, c ≠ 0 ∧ a ## c

theorem not_exclusive_of_shared {a : α} (shared : Shared a) : ¬ Exclusive a := by
  rintro ⟨-, only⟩
  obtain ⟨c, nonempty, separate⟩ := shared
  exact nonempty (only c separate)

/-- A non-empty resource that is separate from itself is shared. -/
theorem shared_of_selfSeparate {a : α} (nonempty : a ≠ 0) (self : a ## a) : Shared a :=
  ⟨a, nonempty, self⟩

theorem not_exclusive_of_selfSeparate {a : α} (self : a ## a) : ¬ Exclusive a := by
  rintro ⟨nonempty, only⟩
  exact nonempty (only a self)

/-- **Shared authority never updates to exclusive authority.** -/
theorem not_frameUpdate_of_shared_exclusive {a b : α} (shared : Shared a)
    (exclusive : Exclusive b) : ¬ FrameUpdate a b := by
  intro update
  obtain ⟨c, nonempty, separate⟩ := shared
  exact nonempty (exclusive.2 c (update c separate))

/-- An exclusive holder may update to anything. -/
theorem Exclusive.frameUpdate {a : α} (exclusive : Exclusive a) (b : α) : FrameUpdate a b := by
  intro c separate
  rw [exclusive.2 c separate]
  exact separate_zero b

end Order

/-! ## Transport between separation algebras -/

section Transport

variable {A : Type u} {B : Type v} {C : Type w}
  [Zero A] [Add A] [SepAlgebra A]
  [Zero B] [Add B] [SepAlgebra B]
  [Zero C] [Add C] [SepAlgebra C]

/-- A transport **preserves updates** when it is monotone for frame-preserving
updates. -/
def PreservesUpdates (f : Hom A B) : Prop :=
  ∀ a b : A, FrameUpdate a b → FrameUpdate (f a) (f b)

/-- **Lifting extensions suffices for preserving updates.** -/
theorem preservesUpdates_of_liftsExtensions (f : Hom A B) (lifts : f.LiftsExtensions) :
    PreservesUpdates f := by
  intro a b update d separate
  obtain ⟨c, separateAC, image⟩ := lifts a d separate
  rw [← image]
  exact f.map_separate (update c separateAC)

theorem id_preservesUpdates : PreservesUpdates (Hom.id A) := fun _ _ update => update

theorem comp_preservesUpdates (g : Hom B C) (f : Hom A B) (hg : PreservesUpdates g)
    (hf : PreservesUpdates f) : PreservesUpdates (Hom.comp g f) :=
  fun a b update => hg _ _ (hf a b update)

/-- **Self-separate authority stays self-separate along every transport.** -/
theorem selfSeparate_map (f : Hom A B) {a : A} (self : a ## a) : f a ## f a :=
  f.map_separate self

/-- **Self-separate authority never becomes exclusive along any transport**,
whether or not the transport erases resources. -/
theorem not_exclusive_map_of_selfSeparate (f : Hom A B) {a : A} (self : a ## a) :
    ¬ Exclusive (f a) :=
  not_exclusive_of_selfSeparate (selfSeparate_map f self)

/-- **Shared authority stays shared along a transport that erases no
resource.** -/
theorem shared_map (f : Hom A B) (reflects : f.ReflectsZero) {a : A} (shared : Shared a) :
    Shared (f a) := by
  obtain ⟨c, nonempty, separate⟩ := shared
  exact ⟨f c, fun erased => nonempty (reflects c erased), f.map_separate separate⟩

theorem not_exclusive_map_of_shared (f : Hom A B) (reflects : f.ReflectsZero) {a : A}
    (shared : Shared a) : ¬ Exclusive (f a) :=
  not_exclusive_of_shared (shared_map f reflects shared)

end Transport

/-! ## Axiom audit -/

#print axioms FrameUpdate.add
#print axioms not_frameUpdate_of_shared_exclusive
#print axioms preservesUpdates_of_liftsExtensions
#print axioms not_exclusive_map_of_selfSeparate
#print axioms shared_map

end Mettapedia.GSLT.Contracts
