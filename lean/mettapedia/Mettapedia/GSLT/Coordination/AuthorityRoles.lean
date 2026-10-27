import Mettapedia.GSLT.Contracts.AuthorityControls
import Mettapedia.GSLT.Coordination.FencedLeases

/-!
# Coordination roles as authority

Who may take, spend, or arbitrate is an authority question, and the contract layer's separation
algebras answer it.

## An escrow share is a delegated linear right

`Share total` holds an amount of a budget of `total` units. Two shares can be held side by side
when together they fit the budget (`instSepAlgebra`). This is a counting permission in the sense of
Bornat, Calcagno, O'Hearn and Parkinson, *Permission accounting in separation logic*.

* **The whole budget is exclusive** (`whole_exclusive`); a strict part of it is shared
  (`part_shared`).
* **Spending is a frame-preserving update** (`spend_frameUpdate`): it breaks no other holder's
  share. This is why escrow spends need no coordination.
* **Minting is not** (`no_mint`): no holder can grow its own share while the rest of the budget is
  held elsewhere. A rebalance therefore needs the sender to give up part of its share: a transfer is
  a right in flight, and the receiver alone cannot create it.

## An owner holds the consume right

For a linear occurrence, the right to take it is `Access.consume`, which excludes every other right.

* **At most one location can take** (`at_most_one_consumer`): in any assignment of rights to
  locations that are pairwise separate, at most one location holds the consume right.
* **The home assignment is valid** (`homeRights_separate`): the home holds the consume right of a
  linear occurrence and the other locations hold nothing of it; every location may read a fact.
* **Two takers is not an assignment** (`two_consumers_not_separate`): giving the consume right to
  two replicas violates separation, which is the authority-level reason for the double take.

## A fencing epoch is a versioned capability

A capability names an object and an epoch; it is valid while the object's register holds that
epoch (`Valid`). Only the register's owner bumps it.

* **A bump revokes every capability of the object at once** (`bump_revokes`) and leaves other
  objects' capabilities alone (`bump_other_valid`); the capability issued at the bump is valid
  (`bump_issues_valid`).
* **At most one capability per object is valid** (`valid_unique`).
* **The fenced lease's token is one** (`current_iff_valid`): an effect is current at the owner of
  `FencedLeases` exactly when its sender holds the lease and its token is valid for the register.

Validity is decided by the register, never by what the capability says about its holder: the
holder's identity is checked against the transport's authentication, as the controls of
`FencedLeases` (`named_impersonation`) show.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Coordination.AuthorityRoles

open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Contracts
open scoped Mettapedia.GSLT.SeparationAlgebra

universe u

/-! ## Escrow shares -/

/-- An amount of a budget of `total` units. -/
@[ext]
structure Share (total : ℕ) where
  val : ℕ
  le : val ≤ total

namespace Share

variable {total : ℕ}

instance : Zero (Share total) := ⟨⟨0, Nat.zero_le _⟩⟩

/-- Putting two amounts together, capped at the budget; the cap matters only for amounts that do
not fit, about which no law speaks. -/
instance : Add (Share total) := ⟨fun x y => ⟨min (x.val + y.val) total, Nat.min_le_right _ _⟩⟩

@[simp] theorem zero_val : (0 : Share total).val = 0 := rfl

@[simp] theorem add_val (x y : Share total) : (x + y).val = min (x.val + y.val) total := rfl

instance instSepAlgebra : SepAlgebra (Share total) where
  Separate x y := x.val + y.val ≤ total
  separate_zero x := by simp only [zero_val, Nat.add_zero]; exact x.le
  separate_symm := by intro x y h; omega
  add_zero x := Share.ext (by simp only [add_val, zero_val, Nat.add_zero]; exact Nat.min_eq_left x.le)
  add_comm := by intro x y _; exact Share.ext (by simp only [add_val]; omega)
  add_assoc := by intro x y z _ _ _; exact Share.ext (by simp only [add_val]; omega)
  separate_of_separate_add := by
    intro x y z h₁ h₂
    simp only [add_val] at h₁ h₂ ⊢
    omega
  separate_add_of_separate_add := by
    intro x y z h₁ h₂
    simp only [add_val] at h₁ h₂ ⊢
    omega

theorem separate_iff {x y : Share total} : x ## y ↔ x.val + y.val ≤ total := Iff.rfl

/-- The whole budget. -/
def whole (total : ℕ) : Share total := ⟨total, le_rfl⟩

/-- **The whole budget is exclusive.** -/
theorem whole_exclusive (positive : 0 < total) : Exclusive (whole total) := by
  refine ⟨fun same => ?_, fun c separate => Share.ext ?_⟩
  · have := congrArg Share.val same
    simp only [whole, zero_val] at this
    omega
  · rw [separate_iff] at separate
    simp only [whole] at separate
    simp only [zero_val]
    omega

/-- **A strict part of the budget is shared.** -/
theorem part_shared (s : Share total) (strict : s.val < total) : Shared s := by
  refine ⟨⟨total - s.val, Nat.sub_le _ _⟩, fun same => ?_, ?_⟩
  · have := congrArg Share.val same
    simp only [zero_val] at this
    omega
  · rw [separate_iff]
    simp only
    omega

/-- **Spending is a frame-preserving update**: every share that fits beside `s` still fits beside
what remains of it. -/
theorem spend_frameUpdate (s : Share total) (amount : ℕ) :
    FrameUpdate s ⟨s.val - amount, le_trans (Nat.sub_le _ _) s.le⟩ := fun c separate => by
  rw [separate_iff] at separate ⊢
  simp only
  omega

/-- **Minting is not a frame-preserving update**: while the rest of the budget is held elsewhere,
`s` cannot grow by one. -/
theorem no_mint (s : Share total) (room : s.val < total) :
    ¬ FrameUpdate s ⟨s.val + 1, room⟩ := by
  intro update
  have rest : s ## (⟨total - s.val, Nat.sub_le _ _⟩ : Share total) := by
    rw [separate_iff]; simp only; omega
  have := update _ rest
  rw [separate_iff] at this
  simp only at this
  omega

/-- A transfer moves an amount from one share to another without changing what the pair holds:
the pair is the same resource before and after. -/
theorem transfer_preserves_pair (s t : Share total) (amount : ℕ) (enough : amount ≤ s.val)
    (fits : s.val + t.val ≤ total) :
    (⟨s.val - amount, le_trans (Nat.sub_le _ _) s.le⟩ : Share total) +
        ⟨t.val + amount, by omega⟩ = s + t := by
  apply Share.ext
  simp only [add_val]
  omega

end Share

/-! ## The consume right -/

section Consume

variable {L : Type u}

/-- **At most one location can take**: in an assignment of rights whose locations hold pairwise
separate rights, at most one holds the consume right. -/
theorem at_most_one_consumer (rights : L → Access)
    (separate : ∀ first second, first ≠ second → rights first ## rights second) {first second : L}
    (consumesFirst : rights first = .consume) (consumesSecond : rights second = .consume) :
    first = second := by
  by_contra apart
  have := separate first second apart
  rw [consumesFirst, consumesSecond] at this
  exact absurd this (by decide)

variable [DecidableEq L]

/-- The home's assignment of rights over a linear occurrence: the home consumes, the others hold
nothing. -/
def homeRights (homeSite : L) : L → Access := fun site => if site = homeSite then .consume else .none

/-- **The home assignment is valid.** -/
theorem homeRights_separate (homeSite : L) (first second : L) (apart : first ≠ second) :
    homeRights homeSite first ## homeRights homeSite second := by
  unfold homeRights
  split_ifs with h₁ h₂ h₂
  · exact absurd (h₁.trans h₂.symm) apart
  · exact SepAlgebra.separate_zero _
  · exact SepAlgebra.zero_separate _
  · exact SepAlgebra.separate_zero _

omit [DecidableEq L] in
/-- Every location may read a fact: read rights are separate from each other. -/
theorem factRights_separate (first second : L) :
    (fun (_ : L) => Access.read) first ## (fun (_ : L) => Access.read) second :=
  Access.read_selfSeparate

/-- **Two takers is not an assignment**: two replicas each holding the consume right are not
separate. -/
theorem two_consumers_not_separate : ¬ (Access.consume ## Access.consume) := by decide

end Consume

/-! ## Versioned capabilities -/

section Versioned

variable {X : Type u} [DecidableEq X]

/-- A capability: an object and an epoch. -/
structure Capability (X : Type u) where
  object : X
  epoch : ℕ

/-- A capability is valid while its object's register holds its epoch. -/
def Valid (register : X → ℕ) (c : Capability X) : Prop := register c.object = c.epoch

/-- The owner bumps an object's register. -/
def bump (register : X → ℕ) (object : X) : X → ℕ :=
  Function.update register object (register object + 1)

/-- **A bump revokes every capability of the object.** -/
theorem bump_revokes {register : X → ℕ} {c : Capability X} (valid : Valid register c) :
    ¬ Valid (bump register c.object) c := by
  unfold Valid bump at *
  rw [Function.update_self]
  omega

/-- A bump leaves other objects' capabilities as they were. -/
theorem bump_other_valid {register : X → ℕ} {c : Capability X} {object : X} (other : c.object ≠ object) :
    Valid (bump register object) c ↔ Valid register c := by
  unfold Valid bump
  rw [Function.update_of_ne other]

/-- The capability issued at a bump is valid. -/
theorem bump_issues_valid (register : X → ℕ) (object : X) :
    Valid (bump register object) ⟨object, register object + 1⟩ := by
  unfold Valid bump
  rw [Function.update_self]

omit [DecidableEq X] in
/-- **At most one capability per object is valid.** -/
theorem valid_unique {register : X → ℕ} {c d : Capability X} (sameObject : c.object = d.object)
    (validC : Valid register c) (validD : Valid register d) : c.epoch = d.epoch := by
  unfold Valid at validC validD
  rw [← validC, ← validD, sameObject]

omit [DecidableEq X] in
/-- **A fenced lease's token is a versioned capability**: an effect of `who` on `task` with token
`epoch` is current at the owner (`FencedLeases.Current`) exactly when `who` holds the lease and the
capability `⟨task, epoch⟩` is valid for the owner's epoch register. -/
theorem current_iff_valid {W : Type u} [DecidableEq W] {s : FencedLeases.Owner X W} {who : W}
    {task : X} {epoch : ℕ} :
    FencedLeases.Current s who task epoch ↔
      (s.role task).heldBy who = true ∧ Valid s.epoch ⟨task, epoch⟩ :=
  Iff.rfl

end Versioned

end Mettapedia.GSLT.Coordination.AuthorityRoles
