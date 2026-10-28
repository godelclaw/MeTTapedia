import Mathlib.Data.Finset.Basic
import Lean.Elab.Tactic.Omega

/-!
# Loans over abstract footprints

The access law needs containment and separation, not addresses or contiguous
intervals. Ranges, finite sets of cells and other footprint representations can
instantiate this interface. Allocation and cleanup authority are separate.

Finite footprints demonstrate that two interleaved views can be borrowed
independently even though their bounding intervals overlap. The C frontend's
range representation is a conservative instance, not a restriction on the
underlying ownership theory.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CMemory.Borrowing

universe u

structure Geometry (Shape : Type u) where
  contains : Shape → Shape → Prop
  disjoint : Shape → Shape → Prop
  contains_refl (a : Shape) : contains a a
  contains_trans {a b c : Shape} : contains a b → contains b c → contains a c
  disjoint_symm {a b : Shape} : disjoint a b → disjoint b a
  disjoint_subregions {a b x y : Shape} :
    disjoint a b → contains a x → contains b y → disjoint x y

inductive Mode where
  | shared
  | exclusive
  deriving DecidableEq, Repr, BEq, ReflBEq, LawfulBEq

structure LoanOf (Shape : Type u) where
  id : Nat
  region : Shape
  mode : Mode
  ancestors : List Nat
  deriving DecidableEq, Repr, BEq, ReflBEq, LawfulBEq

def OrderedIn {Shape : Type u} (loans : List (LoanOf Shape)) : Prop :=
  ∀ l ∈ loans, ∀ parent ∈ l.ancestors, parent < l.id

def AccessIn {Shape : Type u} (g : Geometry Shape) (loans : List (LoanOf Shape))
    (id : Nat) (part : Shape) (writing : Bool) : Prop :=
  ∃ l ∈ loans, l.id = id ∧ g.contains l.region part ∧
    (writing = true → l.mode = .exclusive) ∧
    ∀ other ∈ loans, other.id ≠ id → ¬g.disjoint part other.region →
      other.id ∈ l.ancestors ∨ (writing = false ∧ other.mode = .shared)

instance {Shape : Type u} (g : Geometry Shape)
    [DecidableRel g.contains] [DecidableRel g.disjoint]
    (loans : List (LoanOf Shape)) (id : Nat) (part : Shape) (writing : Bool) :
    Decidable (AccessIn g loans id part writing) :=
  inferInstanceAs (Decidable (∃ l ∈ loans, l.id = id ∧ g.contains l.region part ∧
    (writing = true → l.mode = .exclusive) ∧
    ∀ other ∈ loans, other.id ≠ id → ¬g.disjoint part other.region →
      other.id ∈ l.ancestors ∨ (writing = false ∧ other.mode = .shared)))

/-- A callee may project a field or slice of a passed footprint. Shrinking
that footprint cannot introduce a conflict with any outstanding caller loan. -/
theorem access_subfootprint {Shape : Type u} (g : Geometry Shape)
    {loans : List (LoanOf Shape)} {id : Nat} {whole part : Shape} {writing : Bool}
    (access : AccessIn g loans id whole writing) (inside : g.contains whole part) :
    AccessIn g loans id part writing := by
  obtain ⟨l, present, identity, contains, mode, others⟩ := access
  refine ⟨l, present, identity, g.contains_trans contains inside, mode, ?_⟩
  intro other presentOther different overlaps
  apply others other presentOther different
  intro separated
  exact overlaps (g.disjoint_subregions separated inside (g.contains_refl other.region))

/-- Access separation for every admitted footprint geometry. Strict lineage
rules out a circular parent justification, including for overlapping reborrows. -/
theorem exclusive_access_disjoint_in {Shape : Type u} (g : Geometry Shape)
    [DecidableRel g.disjoint] {loans : List (LoanOf Shape)} (ordered : OrderedIn loans)
    {a b : Nat} {x y : Shape} {writeB : Bool} (different : a ≠ b)
    (ha : AccessIn g loans a x true) (hb : AccessIn g loans b y writeB) : g.disjoint x y := by
  by_contra overlap
  obtain ⟨la, ma, ia, ca, wa, aa⟩ := ha
  obtain ⟨lb, mb, ib, cb, _, ab⟩ := hb
  have overlapXB : ¬g.disjoint x lb.region := by
    intro apart
    exact overlap (g.disjoint_subregions apart (g.contains_refl x) cb)
  have overlapYA : ¬g.disjoint y la.region := by
    intro apart
    exact overlap (g.disjoint_symm
      (g.disjoint_subregions apart (g.contains_refl y) ca))
  have ba : lb.id ∈ la.ancestors := by
    rcases aa lb mb (by simpa [ia, ib] using Ne.symm different) overlapXB with h | h
    · exact h
    · cases h.1
  rcases ab la ma (by simpa [ia, ib] using different) overlapYA with h | h
  · have := ordered la ma lb.id ba
    have := ordered lb mb la.id h
    omega
  · have := wa rfl
    simp_all

def finiteGeometry (Cell : Type u) [DecidableEq Cell] : Geometry (Finset Cell) where
  contains := (· ⊇ ·)
  disjoint := Disjoint
  contains_refl _ := le_rfl
  contains_trans ab bc := bc.trans ab
  disjoint_symm h := h.symm
  disjoint_subregions apart ax by' := by
    apply Finset.disjoint_left.mpr
    intro cell hx hy
    exact (Finset.disjoint_left.mp apart) (ax hx) (by' hy)

instance (Cell : Type u) [DecidableEq Cell] : DecidableRel (finiteGeometry Cell).contains :=
  fun a b => inferInstanceAs (Decidable (b ⊆ a))
instance (Cell : Type u) [DecidableEq Cell] : DecidableRel (finiteGeometry Cell).disjoint :=
  fun a b => inferInstanceAs (Decidable (Disjoint a b))

namespace FootprintControls

def whole : LoanOf (Finset Nat) := ⟨0, {0, 1, 2, 3, 4, 5}, .exclusive, []⟩
def evens : LoanOf (Finset Nat) := ⟨1, {0, 2, 4}, .exclusive, [0]⟩
def odds : LoanOf (Finset Nat) := ⟨2, {1, 3, 5}, .exclusive, [0]⟩

theorem strided_views_both_writable :
    AccessIn (finiteGeometry Nat) [whole, evens, odds] 1 evens.region true ∧
    AccessIn (finiteGeometry Nat) [whole, evens, odds] 2 odds.region true := by decide

theorem overlapping_view_refused :
    ¬AccessIn (finiteGeometry Nat) [whole, evens, odds] 0 {4, 5} true := by decide

end FootprintControls

end Mettapedia.Machines.CMemory.Borrowing
