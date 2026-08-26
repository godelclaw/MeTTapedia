/-!
# Regression fixture: universal SQ3 migration is false

The deterministic counterexample to universal square migration is a planar
tangle built from the Frucht graph: two disjoint edges of one face are deleted,
a square is inserted and attached in cyclic order, and an unrelated edge is
opened into two stubs.  Both of its planar square reductions have a connected
Kempe reconfiguration graph, while the tangle's own reconfiguration graph has
two components.  Universal migration would forbid exactly that.

What this module checks in the kernel, from the encoded incidence data:

* the expanded tangle has eighteen vertices and twenty-five edges, with all
  sixteen internal vertices cubic and both boundary vertices stubs;
* each reduction has fourteen vertices and nineteen edges, with twelve cubic
  vertices and the same two stubs;
* both satisfy Euler's relation against their reported face counts, stated
  additively to stay inside the naturals;
* the reported Kempe class sizes are consistent — they sum to the reported
  colouring counts, and the expanded classes lie one on each reduction side;
* and those numbers do refute universal migration: one class on each side,
  two classes upstairs.

What this module does *not* re-derive is the enumeration itself.  The eighteen
Tait colourings, the six and twelve on the two sides, and the class
decomposition are the deterministic fixture's output, recorded here as
numerals so the document cannot drift away from them.  The incidence data is
transcribed and is checked; the search is not replayed in the kernel.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SquareMigrationRegression

/-- Edges of the tangle outside the inserted square, including the two opened
stub edges. -/
def exteriorEdges : List (Nat × Nat) :=
  [(0, 7), (1, 2), (1, 7), (2, 3), (2, 8), (3, 9), (4, 5), (4, 9), (5, 6),
    (5, 10), (6, 10), (7, 11), (8, 11), (8, 9), (10, 11), (0, 16), (1, 17)]

/-- The four attachments of the inserted square, in cyclic order. -/
def attachmentEdges : List (Nat × Nat) := [(12, 0), (13, 6), (14, 4), (15, 3)]

/-- The inserted square itself. -/
def squareEdges : List (Nat × Nat) := [(12, 13), (13, 14), (14, 15), (15, 12)]

/-- The expanded tangle. -/
def expandedEdges : List (Nat × Nat) :=
  exteriorEdges ++ attachmentEdges ++ squareEdges

/-- The first planar reduction restores the two deleted edges. -/
def reductionZeroEdges : List (Nat × Nat) := exteriorEdges ++ [(0, 6), (4, 3)]

/-- The second planar reduction joins the other planar pairing. -/
def reductionOneEdges : List (Nat × Nat) := exteriorEdges ++ [(6, 4), (3, 0)]

/-- Degree of a vertex in an encoded edge list. -/
def degree (edges : List (Nat × Nat)) (vertex : Nat) : Nat :=
  (edges.filter (fun edge => edge.1 = vertex ∨ edge.2 = vertex)).length

/-! ## The incidence data -/

theorem expandedEdges_length : expandedEdges.length = 25 := by decide

theorem reductionZeroEdges_length : reductionZeroEdges.length = 19 := by decide

theorem reductionOneEdges_length : reductionOneEdges.length = 19 := by decide

/-- Every internal vertex of the expanded tangle is cubic. -/
theorem expanded_internal_cubic :
    ∀ vertex ∈ List.range 16, degree expandedEdges vertex = 3 := by decide

/-- Both boundary vertices of the expanded tangle are stubs. -/
theorem expanded_stubs :
    degree expandedEdges 16 = 1 ∧ degree expandedEdges 17 = 1 := by decide

/-- Every internal vertex of either reduction is cubic. -/
theorem reductions_internal_cubic :
    (∀ vertex ∈ List.range 12, degree reductionZeroEdges vertex = 3) ∧
      (∀ vertex ∈ List.range 12, degree reductionOneEdges vertex = 3) := by
  decide

/-- Both reductions keep the same two stubs. -/
theorem reductions_stubs :
    degree reductionZeroEdges 16 = 1 ∧ degree reductionZeroEdges 17 = 1 ∧
      degree reductionOneEdges 16 = 1 ∧ degree reductionOneEdges 17 = 1 := by
  decide

/-! ## Euler's relation, additively -/

/-- The expanded tangle: eighteen vertices, twenty-five edges, nine faces. -/
theorem expanded_euler : 18 + 9 = expandedEdges.length + 2 := by decide

/-- Each reduction: fourteen vertices, nineteen edges, seven faces. -/
theorem reductions_euler :
    14 + 7 = reductionZeroEdges.length + 2 ∧
      14 + 7 = reductionOneEdges.length + 2 := by decide

/-! ## The enumeration recorded by the fixture -/

/-- Kempe class sizes of the expanded tangle. -/
def expandedKempeClassSizes : List Nat := [6, 12]

/-- Kempe class sizes of the two reductions. -/
def reductionZeroKempeClassSizes : List Nat := [6]

def reductionOneKempeClassSizes : List Nat := [12]

/-- Each expanded Kempe class lies entirely on one reduction side. -/
def expandedClassSideCounts : List (Nat × Nat) := [(6, 0), (0, 12)]

/-- Number of expanded colourings whose square boundary is all-equal. -/
def expandedAllEqualCount : Nat := 0

/-- The class sizes sum to the reported colouring counts. -/
theorem class_sizes_sum :
    expandedKempeClassSizes.sum = 18 ∧
      reductionZeroKempeClassSizes.sum = 6 ∧
      reductionOneKempeClassSizes.sum = 12 := by decide

/-- The side counts partition each expanded class onto a single side, and
account for all eighteen colourings. -/
theorem class_side_counts_consistent :
    (expandedClassSideCounts.map (fun pair => pair.1 + pair.2)) =
        expandedKempeClassSizes ∧
      (expandedClassSideCounts.map Prod.fst).sum = 6 ∧
      (expandedClassSideCounts.map Prod.snd).sum = 12 ∧
      ∀ pair ∈ expandedClassSideCounts, pair.1 = 0 ∨ pair.2 = 0 := by decide

/-- No colouring has an all-equal square boundary, so the two sides of the
fibre table are disjoint in this specimen. -/
theorem expanded_no_all_equal : expandedAllEqualCount = 0 := by decide

/-! ## The refutation -/

/-- **Universal SQ3 migration is false.**  Migration would say that connected
reconfiguration on both reductions forces connected reconfiguration upstairs.
Here each reduction has exactly one Kempe class while the expanded tangle has
two, so the implication fails on this specimen. -/
theorem universal_migration_refuted :
    reductionZeroKempeClassSizes.length = 1 ∧
      reductionOneKempeClassSizes.length = 1 ∧
      2 ≤ expandedKempeClassSizes.length := by decide

/-- The specimen does not refute the route's loaded target, since the two stub
colours agree in every one of the eighteen states; that is recorded by the
fixture and is why the repair keeps the target predicate. -/
def allStubWordsExtendable : Bool := true

theorem stub_words_extendable : allStubWordsExtendable = true := by decide

end GoertzelV24SquareMigrationRegression

end Mettapedia.GraphTheory.FourColor
