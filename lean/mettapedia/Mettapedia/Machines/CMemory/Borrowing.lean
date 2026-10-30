import Mettapedia.Machines.CMemory.Block
import Mettapedia.Machines.CMemory.SpatialLoans
import Lean.Elab.Tactic.Omega

/-!
# Allocation ranges and scoped loans

An allocation's lifetime, a permission to access a subobject, and authority to
release the allocation are different resources. A loan never acquires release
authority. The model is independent of value types, field names, allocators and
scheduling: a frontend supplies allocation identities and subobject ranges.

The access rule accounts for *all* outstanding loans. Reborrowing suspends the
overlapping part of a parent; disjoint fields remain usable. Shared loans permit
shared reads. Ancestor identifiers decrease strictly, so a pair of loans cannot
justify conflicting accesses by each calling the other its ancestor.

This is a permission model, not an interpretation of arbitrary C or an unsafe
pointer aliasing model. The connection to the separation heap below establishes
the resource law on which exclusive access relies.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CMemory.Borrowing

/-- The root is an allocation identity, not its numerical address. -/
structure Region where
  root : Nat
  first : Nat
  count : Nat
  deriving DecidableEq, Repr, BEq, ReflBEq, LawfulBEq

def Region.finish (r : Region) : Nat := r.first + r.count

def Region.Contains (outer inner : Region) : Prop :=
  outer.root = inner.root ∧ outer.first ≤ inner.first ∧ inner.finish ≤ outer.finish

def Region.Disjoint (a b : Region) : Prop :=
  a.root ≠ b.root ∨ a.finish ≤ b.first ∨ b.finish ≤ a.first

instance (a b : Region) : Decidable (a.Contains b) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))
instance (a b : Region) : Decidable (a.Disjoint b) := inferInstanceAs (Decidable (_ ∨ _ ∨ _))

theorem Region.contains_refl (r : Region) : r.Contains r := ⟨rfl, le_rfl, le_rfl⟩

theorem Region.contains_trans {a b c : Region} (ab : a.Contains b) (bc : b.Contains c) :
    a.Contains c := ⟨ab.1.trans bc.1, ab.2.1.trans bc.2.1, bc.2.2.trans ab.2.2⟩

theorem Region.disjoint_symm {a b : Region} (h : a.Disjoint b) : b.Disjoint a := by
  rcases h with h | h | h
  · exact Or.inl (Ne.symm h)
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

/-- Subobjects of separate ranges remain separate, including padded records. -/
theorem Region.disjoint_subregions {a b x y : Region} (apart : a.Disjoint b)
    (ax : a.Contains x) (by' : b.Contains y) : x.Disjoint y := by
  rcases apart with different | before | after
  · exact Or.inl (fun same => different (ax.1.trans (same.trans by'.1.symm)))
  · exact Or.inr (Or.inl (ax.2.2.trans (before.trans by'.2.1)))
  · exact Or.inr (Or.inr (by'.2.2.trans (after.trans ax.2.1)))

def Region.Covers (r : Region) (p : Ptr) : Prop :=
  r.root = p.block ∧ r.first ≤ p.offset ∧ p.offset < r.finish

theorem Region.disjoint_no_common_cell {a b : Region} (apart : a.Disjoint b)
    {p : Ptr} (ha : a.Covers p) (hb : b.Covers p) : False := by
  rcases apart with h | h | h
  · exact h (ha.1.trans hb.1.symm)
  · have := ha.2.2; have := hb.2.1; omega
  · have := hb.2.2; have := ha.2.1; omega

def regionGeometry : Geometry Region where
  contains := Region.Contains
  disjoint := Region.Disjoint
  contains_refl := Region.contains_refl
  contains_trans := Region.contains_trans
  disjoint_symm := Region.disjoint_symm
  disjoint_subregions := Region.disjoint_subregions

instance : DecidableRel regionGeometry.contains := fun a b =>
  inferInstanceAs (Decidable (a.Contains b))
instance : DecidableRel regionGeometry.disjoint := fun a b =>
  inferInstanceAs (Decidable (a.Disjoint b))

abbrev Loan := LoanOf Region

/-- Well-founded lineage prevents circular permission justifications. -/
def Ordered (loans : List Loan) : Prop := OrderedIn loans

instance (loans : List Loan) : Decidable (Ordered loans) :=
  inferInstanceAs (Decidable (∀ l ∈ loans, ∀ parent ∈ l.ancestors, parent < l.id))

/-- Access to a range through a loan. The parent is suspended only where a child
overlaps it; unrelated shared loans permit reads, and no loan permits writes
through a shared reference. -/
def Access (loans : List Loan) (id : Nat) (part : Region) (writing : Bool) : Prop :=
  AccessIn regionGeometry loans id part writing

instance (loans : List Loan) (id : Nat) (part : Region) (writing : Bool) :
    Decidable (Access loans id part writing) :=
  inferInstanceAs (Decidable (∃ l ∈ loans, l.id = id ∧ l.region.Contains part ∧
    (writing = true → l.mode = .exclusive) ∧
    ∀ other ∈ loans, other.id ≠ id → ¬part.Disjoint other.region →
      other.id ∈ l.ancestors ∨ (writing = false ∧ other.mode = .shared)))

theorem access_has_live_loan {loans : List Loan} {id : Nat} {r : Region} {w : Bool}
    (h : Access loans id r w) : ∃ l ∈ loans, l.id = id ∧ l.region.Contains r := by
  obtain ⟨l, mem, same, contained, _, _⟩ := h
  exact ⟨l, mem, same, contained⟩

/-- The central alias law: two different usable loans cannot overlap if either
access writes. It also covers parent/child loans, rather than assuming they are
unrelated. -/
theorem exclusive_access_disjoint {loans : List Loan} (ordered : Ordered loans)
    {a b : Nat} {x y : Region} {writeB : Bool} (different : a ≠ b)
    (ha : Access loans a x true) (hb : Access loans b y writeB) : x.Disjoint y :=
  exclusive_access_disjoint_in regionGeometry ordered different ha hb

/-- Ending a loan requires all of its descendants to have ended first. -/
def MayEnd (loans : List Loan) (id : Nat) : Prop :=
  (∃ l ∈ loans, l.id = id) ∧ ∀ l ∈ loans, id ∉ l.ancestors

instance (loans : List Loan) (id : Nat) : Decidable (MayEnd loans id) :=
  inferInstanceAs (Decidable ((∃ l ∈ loans, l.id = id) ∧ ∀ l ∈ loans, id ∉ l.ancestors))

def endLoan (loans : List Loan) (id : Nat) : List Loan := loans.filter (fun l => l.id != id)

theorem ended_cannot_access (loans : List Loan) (id : Nat) (r : Region) (w : Bool) :
    ¬Access (endLoan loans id) id r w := by
  rintro ⟨l, mem, same, _⟩
  have := (List.mem_filter.mp mem).2
  simp [same] at this

theorem end_preserves_order {loans : List Loan} (h : Ordered loans) (id : Nat) :
    Ordered (endLoan loans id) := by
  intro l mem p parent
  exact h l (List.mem_filter.mp mem).1 p parent

/-- Release authority is separate from a loan. Only the authority's holder may
release a root, and every outstanding loan of that root must first end. The
family identifies the allocator/deallocator contract; static/foreign roots
have no release authority. -/
structure ReleaseAuthority where
  root : Nat
  holder : Nat
  family : Nat
  deriving DecidableEq, Repr, BEq, ReflBEq, LawfulBEq

def MayRelease (loans : List Loan) (authority : ReleaseAuthority)
    (actor family : Nat) : Prop :=
  actor = authority.holder ∧ family = authority.family ∧
  ∀ l ∈ loans, l.region.root ≠ authority.root

instance (ls : List Loan) (a : ReleaseAuthority) (actor family : Nat) :
    Decidable (MayRelease ls a actor family) :=
  inferInstanceAs (Decidable (actor = a.holder ∧ family = a.family ∧
    ∀ l ∈ ls, l.region.root ≠ a.root))

theorem live_loan_prevents_release {ls : List Loan} {a : ReleaseAuthority}
    {actor family : Nat} {l : Loan} (mem : l ∈ ls) (same : l.region.root = a.root) :
    ¬MayRelease ls a actor family := fun h => h.2.2 l mem same

def ReleaseAuthority.move (a : ReleaseAuthority) (newHolder : Nat) : ReleaseAuthority :=
  { a with holder := newHolder }

theorem moved_authority_rejects_old_holder (a : ReleaseAuthority) (next : Nat)
    (different : a.holder ≠ next) (loans : List Loan) (family : Nat) :
    ¬MayRelease loans (a.move next) a.holder family := fun h => different h.1

/-! ## Separation-memory interpretation -/

open Mettapedia.GSLT.SeparationAlgebra
open scoped Mettapedia.GSLT.SeparationAlgebra

/-- Exclusive write permission excludes any simultaneous read permission in a
separate frame, for every instance of the existing cell permission algebra. -/
theorem whole_excludes_framed_reader {L C : Type} [Zero L] [Add L]
    [SepAlgebra L] [CellPermission L C] {σ τ : Heap L} (apart : σ ## τ)
    (p : Ptr) (old seen : C) (writable : (σ p.block).2 p.offset = CellPermission.whole old)
    (readable : CellPermission.read ((τ p.block).2 p.offset) = some seen) : False := by
  have cells := (apart p.block).2 p.offset
  rw [writable] at cells
  have zero := CellPermission.eq_zero_of_whole_separate cells
  rw [zero, CellPermission.read_zero] at readable
  cases readable

/-! ## Positive and negative controls -/

namespace Controls

def whole : Loan := ⟨0, ⟨7, 0, 16⟩, .exclusive, []⟩
def left : Loan := ⟨1, ⟨7, 0, 8⟩, .exclusive, [0]⟩
def right : Loan := ⟨2, ⟨7, 8, 8⟩, .exclusive, [0]⟩
def reader : Loan := ⟨3, ⟨7, 0, 8⟩, .shared, [1, 0]⟩

theorem disjoint_fields_both_writable :
    Access [whole, left, right] 1 left.region true ∧
    Access [whole, left, right] 2 right.region true := by decide

theorem parent_suspended_only_on_borrowed_field :
    ¬Access [whole, left] 0 left.region true ∧
    Access [whole, left] 0 right.region true := by decide

theorem read_reborrow_suspends_write :
    Access [whole, left, reader] 3 reader.region false ∧
    ¬Access [whole, left, reader] 1 left.region true := by decide

theorem child_must_end_before_parent : ¬MayEnd [whole, left, reader] 1 := by decide

theorem wrong_allocator_refused : ¬MayRelease [] ⟨7, 0, 4⟩ 0 5 := by decide

theorem dangling_access_refused : ¬Access [] 1 left.region false := by decide

end Controls

end Mettapedia.Machines.CMemory.Borrowing
