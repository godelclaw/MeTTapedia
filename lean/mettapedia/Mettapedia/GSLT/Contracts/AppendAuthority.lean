import Mettapedia.GSLT.Contracts.RelyGuaranteeClaims
import Mettapedia.GSLT.Contracts.AuthorityControls
import Mettapedia.GSLT.Contracts.CoordinationFreedom
import Mathlib.Data.Fintype.Prod

/-!
# Append and monotone-read authority: when appends coordinate freely

`Access` distinguishes a shared read right from an exclusive consume right.  A
store that only grows needs two finer rights: **appending**, a write that only
adds, and **monotone reading**, a read whose conclusions survive additions (a
presence test, as opposed to an absence test, a count or a snapshot of the whole
store).  A right is a read mode and a write mode (`Rights`); rights combine by
taking the larger mode of each kind.

## The rights are rely–guarantee claims

Over a preordered store, a right reifies to a rely–guarantee claim
(`toClaim`): a full reader relies on no change, a monotone reader on changes that
only grow the store, a full writer on no change by others; an appender
guarantees growth, a full writer guarantees nothing.  Reification is a
homomorphism (`toClaim_add`), and **two rights coexist exactly when their claims
coexist in Jones's sense** (`separate_iff_coexist`), on every store that can grow
strictly and change otherwise.  So this algebra adds no new kind of structure to
`Mettapedia.GSLT.Contracts.RelyGuaranteeClaims`; it is the part of it that
appending and monotone reading occupy.

## What coexists

* **Appenders coexist with appenders and with monotone readers**
  (`Controls.appenders_coexist`): neither needs to coordinate with the other.
* **An appender does not coexist with a full reader** (`Controls.appender_full_reader_conflict`):
  an absence test or a count is invalidated by an addition.
* **A full writer is exclusive** (`full_writer_exclusive`).
* **Upgrading a monotone read to a full read is not frame preserving**
  (`Controls.monotone_read_not_upgraded`): reading absence is a stronger right
  than reading presence.
* `Access` embeds: none, read and consume are no rights, a full read, and a full
  read with a full write (`ofAccess`, `separate_ofAccess_iff`).

## Presence-only rules hold append rights

Every step of a presence-only rule
(`Mettapedia.GSLT.Contracts.Coordination.PresenceOnly`) lies within the guarantee
of an appender (`presenceOnly_step_within_append`).  The coordination freedom of
such programs (`Mettapedia.GSLT.Contracts.Coordination.coordinationFree_of_presenceOnly`)
and the coexistence of their rights are two sides of one condition, the
condition of the CALM theorem.

What remains outside: appends that must also keep a key unique, respect a quota,
or be received by a consuming reader are not appends in this sense; the first two
read the store fully, and a consuming receive writes it fully.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.AppendAuthority

open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.SeparationTransport
open scoped Mettapedia.GSLT.SeparationAlgebra

universe u

/-! ## The rights -/

/-- How a party reads the store. -/
inductive ReadMode where
  | none
  | monotone
  | full
  deriving DecidableEq, Repr

/-- How a party writes the store. -/
inductive WriteMode where
  | none
  | append
  | full
  deriving DecidableEq, Repr

/-- A right: a read mode and a write mode. -/
structure Rights where
  read : ReadMode
  write : WriteMode
  deriving DecidableEq, Repr

instance : Fintype ReadMode :=
  ⟨{.none, .monotone, .full}, fun mode => by cases mode <;> simp⟩

instance : Fintype WriteMode :=
  ⟨{.none, .append, .full}, fun mode => by cases mode <;> simp⟩

/-- Rights are pairs of modes. -/
def Rights.equivProd : Rights ≃ ReadMode × WriteMode where
  toFun rights := (rights.read, rights.write)
  invFun pair := ⟨pair.1, pair.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype Rights := Fintype.ofEquiv _ Rights.equivProd.symm

namespace ReadMode

/-- The larger read mode. -/
def join : ReadMode → ReadMode → ReadMode
  | none, other => other
  | monotone, none => monotone
  | monotone, other => other
  | full, _ => full

end ReadMode

namespace WriteMode

/-- The larger write mode. -/
def join : WriteMode → WriteMode → WriteMode
  | none, other => other
  | append, none => append
  | append, other => other
  | full, _ => full

end WriteMode

namespace Rights

instance : Zero Rights := ⟨⟨.none, .none⟩⟩

instance : Add Rights := ⟨fun first second => ⟨first.read.join second.read, first.write.join second.write⟩⟩

/-- What `first` writes is tolerated by `second`. -/
def tolerates (first second : Rights) : Bool :=
  match first.write with
  | .none => true
  | .append => second.read != .full && second.write != .full
  | .full => second.read == .none && second.write != .full

/-- Two rights coexist when each tolerates what the other writes. -/
def separate (first second : Rights) : Bool := tolerates first second && tolerates second first

instance instSepAlgebra : SepAlgebra Rights where
  Separate first second := separate first second = true
  separate_zero := by decide
  separate_symm := by
    intro first second
    revert first second
    decide
  add_zero := by decide
  add_comm := by
    intro first second
    revert first second
    decide
  add_assoc := by
    intro first second third
    revert first second third
    decide
  separate_of_separate_add := by
    intro first second third
    revert first second third
    decide
  separate_add_of_separate_add := by
    intro first second third
    revert first second third
    decide

instance (first second : Rights) : Decidable (first ## second) :=
  inferInstanceAs (Decidable (separate first second = true))

/-- A monotone reader and appender. -/
def appender : Rights := ⟨.monotone, .append⟩

/-- A full reader. -/
def fullReader : Rights := ⟨.full, .none⟩

/-- A monotone reader. -/
def monotoneReader : Rights := ⟨.monotone, .none⟩

end Rights

open Rights

/-- **A full writer is exclusive.** -/
theorem full_writer_exclusive (read : ReadMode) : Exclusive (⟨read, .full⟩ : Rights) := by
  refine ⟨by cases read <;> decide, fun other => ?_⟩
  revert other
  cases read <;> decide

/-! ## Reification into rely–guarantee claims -/

section Claims

variable {S : Type u} [Preorder S]

/-- What a read mode relies on. -/
def ReadMode.rely : ReadMode → S → S → Prop
  | .none => fun _ _ => True
  | .monotone => fun before after => before ≤ after
  | .full => fun before after => after = before

/-- What a write mode relies on: a full writer owns the store. -/
def WriteMode.rely : WriteMode → S → S → Prop
  | .full => fun before after => after = before
  | _ => fun _ _ => True

/-- What a write mode guarantees. -/
def WriteMode.guarantee : WriteMode → S → S → Prop
  | .none => fun _ _ => False
  | .append => fun before after => before ≤ after
  | .full => fun _ _ => True

/-- **The claim of a right.** -/
def toClaim (rights : Rights) : RGClaim S where
  assertion := Set.univ
  rely before after := rights.read.rely before after ∧ rights.write.rely before after
  guarantee := rights.write.guarantee
  stable _ _ _ _ := trivial

theorem readRely_join (first second : ReadMode) (before after : S) :
    (first.join second).rely before after ↔ first.rely before after ∧ second.rely before after := by
  cases first <;> cases second <;> simp only [ReadMode.join, ReadMode.rely] <;>
    constructor <;> intro holds <;> simp_all

omit [Preorder S] in
theorem writeRely_join (first second : WriteMode) (before after : S) :
    (first.join second).rely before after ↔ first.rely before after ∧ second.rely before after := by
  cases first <;> cases second <;> simp [WriteMode.join, WriteMode.rely]

theorem writeGuarantee_join (first second : WriteMode) (before after : S) :
    (first.join second).guarantee before after ↔
      first.guarantee before after ∨ second.guarantee before after := by
  cases first <;> cases second <;> simp [WriteMode.join, WriteMode.guarantee]

/-- **Reification is a homomorphism.** -/
theorem toClaim_add (first second : Rights) :
    (toClaim (first + second) : RGClaim S) = toClaim first + toClaim second := by
  apply RGClaim.ext
  · simp [toClaim]
  · funext before after
    apply propext
    change ((first.read.join second.read).rely before after ∧
        (first.write.join second.write).rely before after) ↔
      ((first.read.rely before after ∧ first.write.rely before after) ∧
        (second.read.rely before after ∧ second.write.rely before after))
    rw [readRely_join, writeRely_join]
    tauto
  · funext before after
    apply propext
    exact writeGuarantee_join first.write second.write before after

/-- Separate rights have coexisting claims, on every preordered store. -/
theorem coexist_of_separate {first second : Rights} (separate : first ## second) :
    RGClaim.Coexist (toClaim first : RGClaim S) (toClaim second) := by
  obtain ⟨read₁, write₁⟩ := first
  obtain ⟨read₂, write₂⟩ := second
  have table : Rights.separate ⟨read₁, write₁⟩ ⟨read₂, write₂⟩ = true := separate
  refine ⟨?_, ?_⟩ <;> intro before after step <;>
    cases read₁ <;> cases write₁ <;> cases read₂ <;> cases write₂ <;>
    simp_all [toClaim, Rights.separate, Rights.tolerates, ReadMode.rely, WriteMode.rely,
      WriteMode.guarantee]

/-- **Two rights coexist exactly when their claims do**, on a store that can grow
strictly and can change without growing. -/
theorem separate_iff_coexist (increase : ∃ before after : S, before ≤ after ∧ after ≠ before)
    (change : ∃ before after : S, ¬ before ≤ after) (first second : Rights) :
    first ## second ↔ RGClaim.Coexist (toClaim first : RGClaim S) (toClaim second) := by
  refine ⟨coexist_of_separate, fun coexist => ?_⟩
  obtain ⟨low, high, grows, strict⟩ := increase
  obtain ⟨from_, to_, notGrow⟩ := change
  obtain ⟨read₁, write₁⟩ := first
  obtain ⟨read₂, write₂⟩ := second
  obtain ⟨forward, backward⟩ := coexist
  have forwardGrow := forward low high
  have forwardChange := forward from_ to_
  have backwardGrow := backward low high
  have backwardChange := backward from_ to_
  change Rights.separate ⟨read₁, write₁⟩ ⟨read₂, write₂⟩ = true
  cases read₁ <;> cases write₁ <;> cases read₂ <;> cases write₂ <;>
    simp_all [toClaim, Rights.separate, Rights.tolerates, ReadMode.rely, WriteMode.rely,
      WriteMode.guarantee]

end Claims

/-! ## `Access` embeds -/

/-- Read and consume as rights. -/
def ofAccess : Mettapedia.GSLT.Contracts.Access → Rights
  | .none => 0
  | .read => ⟨.full, .none⟩
  | .consume => ⟨.full, .full⟩

theorem separate_ofAccess_iff (first second : Mettapedia.GSLT.Contracts.Access) :
    ofAccess first ## ofAccess second ↔ first ## second := by
  cases first <;> cases second <;> decide

/-- The embedding is a resource homomorphism. -/
def ofAccessHom : Hom Mettapedia.GSLT.Contracts.Access Rights where
  toFun := ofAccess
  map_zero := rfl
  map_add := by
    intro first second
    cases first <;> cases second <;> decide
  map_separate := fun separate => (separate_ofAccess_iff _ _).mpr separate

/-! ## Presence-only rules hold append rights -/

/-- **Every step of a presence-only rule lies within the guarantee of an
appender.** -/
theorem presenceOnly_step_within_append {α : Type u} [CompleteLattice α] {ι : Type u}
    {rules : ι → α → α} (presence : Mettapedia.GSLT.Contracts.Coordination.PresenceOnly rules)
    (rule : ι) (store : α) :
    (toClaim appender : RGClaim α).guarantee store (rules rule store) :=
  presence.inflationary rule store

/-! ## Controls -/

namespace Controls

/-- **Appenders coexist**, each reading monotonically. -/
theorem appenders_coexist : appender ## appender := by decide

/-- An appender coexists with a monotone reader. -/
theorem appender_monotoneReader_coexist : appender ## monotoneReader := by decide

/-- **An appender does not coexist with a full reader.** -/
theorem appender_full_reader_conflict : ¬ appender ## fullReader := by decide

/-- **Upgrading a monotone read to a full read breaks an appender's frame.** -/
theorem monotone_read_not_upgraded : ¬ FrameUpdate monotoneReader fullReader := by
  intro update
  exact (by decide : ¬ fullReader ## appender) (update appender (by decide))

/-- Weakening a full read to a monotone read preserves every frame. -/
theorem full_read_weakens : FrameUpdate fullReader monotoneReader := by
  intro other
  revert other
  decide

/-- On a store of sets, the claims of an appender and of a full reader do not
coexist: adding an element invalidates the reader. -/
theorem appender_full_reader_claims_conflict :
    ¬ RGClaim.Coexist (toClaim appender : RGClaim (Set ℕ)) (toClaim fullReader) := by
  rintro ⟨forward, -⟩
  have relied := forward ∅ {0} (Set.empty_subset _)
  have unchanged : ({0} : Set ℕ) = ∅ := relied.1
  exact (Set.singleton_ne_empty 0) unchanged

end Controls

end Mettapedia.GSLT.Contracts.AppendAuthority
