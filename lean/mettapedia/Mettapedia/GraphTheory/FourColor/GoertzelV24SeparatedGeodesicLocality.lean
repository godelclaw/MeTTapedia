import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Geodesic locality, for a geodesic of the dual with faces deleted

The corridor construction extracts its axis from the facial dual **with a
forbidden set `S` deleted**, so the locality statement it consumes has to be
about a geodesic of that deleted graph, not of the ambient dual.  The two are
genuinely different: a shortest path avoiding `S` may be longer than a shortest
path allowed to pass through it.

The lemma survives the correction essentially unchanged, and for a reason worth
recording.  The side face `H` at issue is required to lie outside `S`, so both
dual edges `F_i H` and `H F_j` survive the deletion and form a walk of length
two *there*.  Geodesicity in the deleted graph then bounds `|i - j|` by two
directly.  What fails, and is excluded by the hypothesis, is the same inference
for a side face inside `S`.

The carrier count is then arithmetic over that locality: four axis faces with at
most `B` incidences each give at most `4B` unmarked side neighbours costing at
most `B` darts apiece, the axis incidences cost at most `4B`, and the at most
`h` marked faces cost at most `B` each.  The total `4B² + 4B + hB` mentions only
`B` and `h`, so it is independent of the corridor length `L` -- which is the
only property the corridor argument uses.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SeparatedGeodesicLocality

variable {F : Type*}

/-- Vertex deletion, kept on the ambient vertex type: an edge survives exactly
when neither endpoint is deleted. -/
def deleteFaces (D : SimpleGraph F) (S : Set F) : SimpleGraph F where
  Adj u v := D.Adj u v ∧ u ∉ S ∧ v ∉ S
  symm := ⟨fun {u v} (h : D.Adj u v ∧ u ∉ S ∧ v ∉ S) =>
    (⟨h.1.symm, h.2.2, h.2.1⟩ : D.Adj v u ∧ v ∉ S ∧ u ∉ S)⟩
  loopless := ⟨fun _ h => D.ne_of_adj h.1 rfl⟩

theorem deleteFaces_adj {D : SimpleGraph F} {S : Set F} {u v : F}
    (hadj : D.Adj u v) (hu : u ∉ S) (hv : v ∉ S) :
    (deleteFaces D S).Adj u v :=
  ⟨hadj, hu, hv⟩

/-- **Locality along an `S`-avoiding geodesic.**  A side face outside `S` that
is adjacent in the ambient dual to two axis faces sits within two steps of the
axis, because its two dual edges survive the deletion and give a length-two walk
in the deleted graph.

The hypothesis `hgeo` is geodesicity *in the deleted dual*, which is what the
extraction actually provides. -/
theorem index_dist_le_two
    {D : SimpleGraph F} {S : Set F} {L : ℕ} {p : ℕ → F}
    (hp : ∀ k, k ≤ L → p k ∉ S)
    (hgeo : ∀ a b, a ≤ L → b ≤ L →
      (deleteFaces D S).dist (p a) (p b) = max a b - min a b)
    {H : F} (hH : H ∉ S) {i j : ℕ} (hi : i ≤ L) (hj : j ≤ L)
    (hadjLeft : D.Adj (p i) H) (hadjRight : D.Adj H (p j)) :
    max i j - min i j ≤ 2 := by
  have hleft : (deleteFaces D S).Adj (p i) H :=
    deleteFaces_adj hadjLeft (hp i hi) hH
  have hright : (deleteFaces D S).Adj H (p j) :=
    deleteFaces_adj hadjRight hH (hp j hj)
  have hdist : (deleteFaces D S).dist (p i) (p j) ≤ 2 := by
    simpa using SimpleGraph.dist_le
      (SimpleGraph.Walk.cons hleft (SimpleGraph.Walk.cons hright SimpleGraph.Walk.nil))
  rwa [hgeo i j hi hj] at hdist

/-- A side neighbour count of at most `4B`, each retaining at most `B` darts,
costs at most `4B²`. -/
theorem sideCost_le {neighbours dartsEach B : ℕ}
    (hneighbours : neighbours ≤ 4 * B) (hdarts : dartsEach ≤ B) :
    neighbours * dartsEach ≤ 4 * B * B :=
  Nat.mul_le_mul hneighbours hdarts

/-- At most `h` marked faces, each retaining at most `B` darts, cost at most
`hB`. -/
theorem markedCost_le {marked dartsEach B h : ℕ}
    (hmarked : marked ≤ h) (hdarts : dartsEach ≤ B) :
    marked * dartsEach ≤ h * B :=
  Nat.mul_le_mul hmarked hdarts

/-- **The interacting carrier bound.**  Assembling the three contributions
gives `4B² + 4B + hB`.  The bound names only `B` and `h`, so it does not grow
with the corridor length. -/
theorem carrier_le {sideCost axisCost markedCost B h : ℕ}
    (hside : sideCost ≤ 4 * B * B) (haxis : axisCost ≤ 4 * B)
    (hmarked : markedCost ≤ h * B) :
    sideCost + axisCost + markedCost ≤ 4 * B * B + 4 * B + h * B := by
  omega

/-- The same bound, from the counts the lemma's proof actually produces. -/
theorem carrier_le_of_counts
    {sideNeighbours sideDarts axisCost markedFaces markedDarts B h : ℕ}
    (hneighbours : sideNeighbours ≤ 4 * B) (hsideDarts : sideDarts ≤ B)
    (haxis : axisCost ≤ 4 * B)
    (hmarked : markedFaces ≤ h) (hmarkedDarts : markedDarts ≤ B) :
    sideNeighbours * sideDarts + axisCost + markedFaces * markedDarts ≤
      4 * B * B + 4 * B + h * B :=
  carrier_le (sideCost_le hneighbours hsideDarts) haxis
    (markedCost_le hmarked hmarkedDarts)

end GoertzelV24SeparatedGeodesicLocality

end Mettapedia.GraphTheory.FourColor
