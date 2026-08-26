/-!
# Regression fixture: generic WC* square transport is false

The specimen starts from the planar Frucht graph, replaces the disjoint
cofacial edges `06` and `34` by a facial square attached in cyclic order, and
opens the two cofacial exterior edges `5,10` and `8,11` into four stubs.  The
target word has the colour-invariant form `(a,a,b,b)` with `a ≠ b`.

Both planar square reductions satisfy WC* for that target — the first
vacuously, having no target colouring at all, the second because its
colourings form a single Kempe class containing targets.  Upstairs the target
is nonempty but lies in only one of two Kempe classes, so WC* fails.  Generic
square transport for an arbitrary target is therefore false, even for a target
invariant under all colour permutations.

What this module checks in the kernel, from the transcribed incidence data:

* the expanded tangle has twenty vertices and twenty-six edges, with all
  sixteen internal vertices cubic and all four boundary vertices stubs;
* each reduction has sixteen vertices and twenty edges, with twelve cubic
  vertices and the same four stubs;
* all three satisfy Euler's relation against their reported face counts,
  stated additively to stay inside the naturals;
* the recorded class data is consistent — sizes summing to the colouring
  counts, and target counts not exceeding class sizes;
* and the numerical WC* criterion has the reported verdicts: a target-bearing
  instance satisfies WC* exactly when every class contains a target, since
  within a class every state reaches every other.

What this module does *not* re-derive is the enumeration.  The forty-eight
colourings, the split into classes of eighteen and thirty, and the per-class
target counts are the deterministic fixture's output, recorded here as
numerals so the document cannot drift away from them.  The incidence data is
transcribed and is checked; the search is not replayed in the kernel.

This refutes transport for an arbitrary target.  It says nothing about the
route-specific statement, whose target is the pentagonal extendable-word set
in a least obstruction.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SquareWCStarRegression

/-- Edges outside the inserted square, including the four opened stub edges. -/
def exteriorEdges : List (Nat × Nat) :=
  [(0, 1), (0, 7), (1, 2), (1, 7), (2, 3), (2, 8), (3, 9), (4, 5), (4, 9),
    (5, 6), (6, 10), (7, 11), (8, 9), (10, 11), (5, 16), (10, 17), (8, 18),
    (11, 19)]

/-- The four attachments of the inserted square, in cyclic order. -/
def attachmentEdges : List (Nat × Nat) := [(12, 0), (13, 6), (14, 4), (15, 3)]

/-- The inserted square. -/
def squareEdges : List (Nat × Nat) := [(12, 13), (13, 14), (14, 15), (15, 12)]

def expandedEdges : List (Nat × Nat) :=
  exteriorEdges ++ attachmentEdges ++ squareEdges

/-- The first planar reduction restores the two replaced edges. -/
def reductionZeroEdges : List (Nat × Nat) := exteriorEdges ++ [(0, 6), (4, 3)]

/-- The second planar reduction takes the other planar pairing. -/
def reductionOneEdges : List (Nat × Nat) := exteriorEdges ++ [(6, 4), (3, 0)]

/-- Degree of a vertex in an encoded edge list. -/
def degree (edges : List (Nat × Nat)) (vertex : Nat) : Nat :=
  (edges.filter (fun edge => edge.1 = vertex ∨ edge.2 = vertex)).length

/-! ## The incidence data -/

theorem expandedEdges_length : expandedEdges.length = 26 := by decide

theorem reductionEdges_length :
    reductionZeroEdges.length = 20 ∧ reductionOneEdges.length = 20 := by decide

/-- Every internal vertex of the expanded tangle is cubic. -/
theorem expanded_internal_cubic :
    ∀ vertex ∈ List.range 16, degree expandedEdges vertex = 3 := by decide

/-- All four boundary vertices of the expanded tangle are stubs. -/
theorem expanded_stubs :
    ∀ vertex ∈ [16, 17, 18, 19], degree expandedEdges vertex = 1 := by decide

/-- Every internal vertex of either reduction is cubic. -/
theorem reductions_internal_cubic :
    (∀ vertex ∈ List.range 12, degree reductionZeroEdges vertex = 3) ∧
      (∀ vertex ∈ List.range 12, degree reductionOneEdges vertex = 3) := by
  decide

/-- Both reductions keep the same four stubs. -/
theorem reductions_stubs :
    (∀ vertex ∈ [16, 17, 18, 19], degree reductionZeroEdges vertex = 1) ∧
      (∀ vertex ∈ [16, 17, 18, 19], degree reductionOneEdges vertex = 1) := by
  decide

/-! ## Euler's relation, additively -/

/-- The expanded tangle: twenty vertices, twenty-six edges, eight faces. -/
theorem expanded_euler : 20 + 8 = expandedEdges.length + 2 := by decide

/-- Each reduction: sixteen vertices, twenty edges, six faces. -/
theorem reductions_euler :
    16 + 6 = reductionZeroEdges.length + 2 ∧
      16 + 6 = reductionOneEdges.length + 2 := by decide

/-! ## The enumeration recorded by the fixture -/

def expandedKempeClassSizes : List Nat := [18, 30]

def expandedTargetCountsByClass : List Nat := [6, 0]

def reductionZeroKempeClassSizes : List Nat := [30]

def reductionZeroTargetCountsByClass : List Nat := [0]

def reductionOneKempeClassSizes : List Nat := [18]

def reductionOneTargetCountsByClass : List Nat := [6]

/-- Class sizes sum to the reported colouring counts. -/
theorem class_sizes_sum :
    expandedKempeClassSizes.sum = 48 ∧
      reductionZeroKempeClassSizes.sum = 30 ∧
      reductionOneKempeClassSizes.sum = 18 := by decide

/-- Per-class target counts never exceed the class sizes, and the class lists
have matching lengths. -/
theorem target_counts_consistent :
    expandedTargetCountsByClass.length = expandedKempeClassSizes.length ∧
      reductionZeroTargetCountsByClass.length =
        reductionZeroKempeClassSizes.length ∧
      reductionOneTargetCountsByClass.length =
        reductionOneKempeClassSizes.length ∧
      List.all (expandedTargetCountsByClass.zip expandedKempeClassSizes)
          (fun pair => pair.1 ≤ pair.2) = true := by
  decide

/-! ## The WC* criterion, numerically

Within a Kempe class every state reaches every other, so for a target-bearing
instance WC* holds exactly when no class is target-free; and it holds
vacuously when the instance has no target at all. -/

/-- The numerical criterion: either there is no target anywhere, or every class
contains one. -/
def wcStarByCounts (targetCountsByClass : List Nat) : Bool :=
  targetCountsByClass.sum = 0 || targetCountsByClass.all (fun count => 0 < count)

/-- **The first reduction satisfies WC\*, vacuously.**  It has no target
colouring. -/
theorem reductionZero_wcStar :
    reductionZeroTargetCountsByClass.sum = 0 ∧
      wcStarByCounts reductionZeroTargetCountsByClass = true := by decide

/-- **The second reduction satisfies WC\*.**  Its single class carries
targets. -/
theorem reductionOne_wcStar :
    0 < reductionOneTargetCountsByClass.sum ∧
      wcStarByCounts reductionOneTargetCountsByClass = true := by decide

/-- **WC\* fails upstairs.**  The target is nonempty, yet one of the two
classes contains no target state, so no state of that class reaches a
target. -/
theorem expanded_not_wcStar :
    0 < expandedTargetCountsByClass.sum ∧
      0 ∈ expandedTargetCountsByClass ∧
      wcStarByCounts expandedTargetCountsByClass = false := by decide

/-- **Generic WC\* square transport is false.**  Both reductions satisfy the
criterion while the expanded tangle does not, so no implication from the two
reductions to the ambient instance can hold for an arbitrary target. -/
theorem generic_wcStar_transport_refuted :
    wcStarByCounts reductionZeroTargetCountsByClass = true ∧
      wcStarByCounts reductionOneTargetCountsByClass = true ∧
      wcStarByCounts expandedTargetCountsByClass = false := by decide

end GoertzelV24SquareWCStarRegression

end Mettapedia.GraphTheory.FourColor
