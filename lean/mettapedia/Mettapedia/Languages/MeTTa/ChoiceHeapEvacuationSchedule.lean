import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin

/-!
# Choice-heap evacuation scheduling

This file isolates two laws used by a copying collector for a relational
machine with retained alternatives.

First, a collector whose roots are opaque cannot safely skip a root field:
an unvisited field can be changed from an old pointer to a nursery pointer
without changing anything the scan observed.  Visiting every root exactly
once therefore attains the lower bound for this observation model.

Second, copying payloads is not the collector's only cost.  Goals, rollback
trail entries, choices, visible variables, and obligations are live vectors
that must be scanned even when their atoms already live in an older
generation.  The schedule below waits for four times those vector bytes.
Consequently one scan-byte is charged to at least four bytes of admitted
nursery allocation between collections.

The model proves the scheduling law and its lower bound.  Agreement between
the concrete C visitors and their declared root set remains an implementation
conformance obligation, checked separately by relocation and sanitizer tests.
-/

namespace Mettapedia.Languages.MeTTa.ChoiceHeapEvacuationSchedule

/-- The information available at the end of a choice-aware collection. -/
structure CollectionState where
  floorBytes : Nat
  survivorBytes : Nat
  tenuredBytes : Nat
  rootVectorBytes : Nat
  deriving DecidableEq, Repr

/--
The next nursery threshold.  The four terms respectively bound tiny-heap
frequency, repeated payload copying, major-collection frequency, and scans of
retained control vectors.
-/
def nextWindow (state : CollectionState) : Nat :=
  max state.floorBytes
    (max (2 * state.survivorBytes)
      (max (state.tenuredBytes / 2) (4 * state.rootVectorBytes)))

theorem root_scan_budget (state : CollectionState) :
    4 * state.rootVectorBytes ≤ nextWindow state := by
  simp [nextWindow]

theorem survivor_copy_budget (state : CollectionState) :
    2 * state.survivorBytes ≤ nextWindow state := by
  simp [nextWindow]

theorem nursery_floor_budget (state : CollectionState) :
    state.floorBytes ≤ nextWindow state := by
  simp [nextWindow]

/-- If the runtime waits for the threshold, vector scanning consumes at most
one unit of work per four admitted allocation bytes in this byte-cost model. -/
theorem root_scan_amortized
    (state : CollectionState) (allocated : Nat)
    (reached : nextWindow state ≤ allocated) :
    4 * state.rootVectorBytes ≤ allocated :=
  (root_scan_budget state).trans reached

/-- An opaque vector says only whether each field points into the nursery. -/
abbrev OpaqueRoots (count : Nat) := Fin count → Bool

/-- Two root vectors give the same answers at every field the scanner read. -/
def Indistinguishable {count : Nat} (visited : Finset (Fin count))
    (left right : OpaqueRoots count) : Prop :=
  ∀ field, field ∈ visited → left field = right field

def HasNurseryRoot {count : Nat} (roots : OpaqueRoots count) : Prop :=
  ∃ field, roots field = true

/--
An omitted opaque field is an adversarial witness: a clean vector and a vector
with one nursery pointer look identical on every visited field but require
different relocation decisions.
-/
theorem omitted_root_adversary {count : Nat}
    (visited : Finset (Fin count)) (omitted : Fin count)
    (notVisited : omitted ∉ visited) :
    ∃ clean dirty : OpaqueRoots count,
      Indistinguishable visited clean dirty ∧
      ¬HasNurseryRoot clean ∧ HasNurseryRoot dirty := by
  let clean : OpaqueRoots count := fun _ => false
  let dirty : OpaqueRoots count := fun field => decide (field = omitted)
  refine ⟨clean, dirty, ?_, ?_, ?_⟩
  · intro field member
    have different : field ≠ omitted := by
      intro equal
      subst field
      exact notVisited member
    simp [clean, dirty, different]
  · rintro ⟨field, nursery⟩
    simp [clean] at nursery
  · exact ⟨omitted, by simp [dirty]⟩

/-- The exact scanner meets the opaque-root lower bound with one visit per
field. -/
theorem exact_scan_cardinality (count : Nat) :
    (Finset.univ : Finset (Fin count)).card = count := by
  simp

/-- Positive control: all four bounds can participate in the maximum. -/
example : nextWindow ⟨1024, 700, 2000, 600⟩ = 2400 := by decide

/-- Negative control: with no retained root vectors, that term contributes no
extra threshold. -/
example : nextWindow ⟨1024, 700, 2000, 0⟩ = 1400 := by decide

end Mettapedia.Languages.MeTTa.ChoiceHeapEvacuationSchedule
