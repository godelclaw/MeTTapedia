import Mettapedia.GraphTheory.FourColor.GoertzelV24CompositeSeamCubic
import Mettapedia.GraphTheory.FourColor.GoertzelV24PortTangleGluing

/-!
# Cut parity for finite open cubic port tangles

Every proper nonzero Tait colouring of a finite open cubic tangle has zero
total colour on its boundary ports.  This is the open-tangle form of the
Klein-group cut-parity law.  It applies to the literal `PortTangle` carrier
used by the exact Count gluing theorem, rather than only to a graph-side cut.

The proof is purely incidence algebra.  At every cubic vertex the three
distinct nonzero colours sum to zero.  Summing over vertices counts every
interior dart and every port once.  Interior darts cancel in pairs under the
edge involution, leaving precisely the boundary sum.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24PortTangleCutParity

open scoped BigOperators
open GoertzelV24OpenTangleComposition
open GoertzelV24PortTangleGluing
open GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24CompositeSeamCubic

universe u

variable {V I P : Type u}

section Finite

variable [Fintype V] [Fintype I] [Fintype P]
  [DecidableEq V] [DecidableEq I] [DecidableEq P]

/-- Darts of a port tangle incident with one vertex, including ports. -/
def dartsAt (T : PortTangle V I P) (vertex : V) : Finset (I ⊕ P) :=
  Finset.univ.filter fun dart => T.vert dart = vertex

/-- Cubicity for an open port tangle: every vertex carries exactly three
darts, where a boundary port contributes one dart. -/
def IsCubic (T : PortTangle V I P) : Prop :=
  ∀ vertex : V, (dartsAt T vertex).card = 3

/-- Forgetting the rotations of an open cubic tangle preserves cubicity. -/
theorem isCubic_ofOpenTangleData
    (T : OpenTangleData V I P) (hcubic : OpenIsCubic T) :
    IsCubic (ofOpenTangleData T) := by
  intro vertex
  simpa [IsCubic, dartsAt, openDartsAt, ofOpenTangleData] using hcubic vertex

/-- Sum of dart colours incident with one vertex. -/
def vertexColorSum (T : PortTangle V I P) (coloring : Coloring T)
    (vertex : V) : Color :=
  ∑ dart ∈ dartsAt T vertex, coloring.color dart

private theorem three_distinct_nonzero_sum_eq_zero
    {first second third : Color}
    (hfirst : first ≠ 0) (hsecond : second ≠ 0) (hthird : third ≠ 0)
    (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    first + second + third = 0 := by
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero first hfirst with
      rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero second hsecond with
      rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero third hthird with
      rfl | rfl | rfl <;>
    simp at hfirstSecond hfirstThird hsecondThird ⊢

/-- Properness at a cubic open vertex gives the Klein Kirchhoff equation. -/
theorem vertexColorSum_eq_zero
    (T : PortTangle V I P) (hcubic : IsCubic T)
    (coloring : Coloring T) (hproper : IsProper coloring)
    (vertex : V) :
    vertexColorSum T coloring vertex = 0 := by
  have hcard : (dartsAt T vertex).card = 3 := hcubic vertex
  rcases Finset.card_eq_three.mp hcard with
    ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hset⟩
  have hfirstMem : first ∈ dartsAt T vertex := by rw [hset]; simp
  have hsecondMem : second ∈ dartsAt T vertex := by rw [hset]; simp
  have hthirdMem : third ∈ dartsAt T vertex := by rw [hset]; simp
  have hfirstVert : T.vert first = vertex := by
    simpa [dartsAt] using hfirstMem
  have hsecondVert : T.vert second = vertex := by
    simpa [dartsAt] using hsecondMem
  have hthirdVert : T.vert third = vertex := by
    simpa [dartsAt] using hthirdMem
  unfold vertexColorSum
  rw [hset]
  simpa [hfirstSecond, hfirstThird, hsecondThird, add_assoc] using
    three_distinct_nonzero_sum_eq_zero
      (hproper.1 first) (hproper.1 second) (hproper.1 third)
      (hproper.2 first second (hfirstVert.trans hsecondVert.symm) hfirstSecond)
      (hproper.2 first third (hfirstVert.trans hthirdVert.symm) hfirstThird)
      (hproper.2 second third (hsecondVert.trans hthirdVert.symm) hsecondThird)

/-- Summing the vertex incidence sums counts every dart exactly once. -/
theorem sum_vertexColorSum_eq_sum_color
    (T : PortTangle V I P) (coloring : Coloring T) :
    (∑ vertex : V, vertexColorSum T coloring vertex) =
      ∑ dart : I ⊕ P, coloring.color dart := by
  classical
  unfold vertexColorSum dartsAt
  simpa only [Finset.sum_filter] using
    (Finset.sum_fiberwise_of_maps_to
      (s := Finset.univ) (t := Finset.univ) (g := T.vert)
      (fun dart _ => Finset.mem_univ (T.vert dart)) coloring.color)

/-- The interior-dart contribution vanishes: the edge involution pairs equal
colours, and `Color` has characteristic two. -/
theorem sum_interiorColor_eq_zero
    (T : PortTangle V I P) (coloring : Coloring T) :
    (∑ dart : I, coloring.color (Sum.inl dart)) = 0 := by
  classical
  apply Finset.sum_ninvolution T.alpha
  · intro dart
    rw [coloring.invariant]
    exact color_add_self _
  · intro dart hnonzero
    exact T.alpha_fixfree dart
  · intro dart
    simp
  · exact T.alpha_involutive

/-- **Open cut parity.**  Every proper Tait colouring of a finite open cubic
port tangle has zero total colour on its exposed ports. -/
theorem sum_boundaryWord_eq_zero
    (T : PortTangle V I P) (hcubic : IsCubic T)
    (coloring : Coloring T) (hproper : IsProper coloring) :
    (∑ port : P, word coloring port) = 0 := by
  have hvertices : (∑ vertex : V, vertexColorSum T coloring vertex) = 0 := by
    apply Finset.sum_eq_zero
    intro vertex _
    exact vertexColorSum_eq_zero T hcubic coloring hproper vertex
  have hdarts : (∑ dart : I ⊕ P, coloring.color dart) = 0 := by
    rw [← sum_vertexColorSum_eq_sum_color T coloring]
    exact hvertices
  rw [Fintype.sum_sum_type, sum_interiorColor_eq_zero T coloring,
    zero_add] at hdarts
  exact hdarts

/-- Exact support of a finite port tangle on genuine nonzero Tait words. -/
def taitSupport (T : PortTangle V I P) : Set (P → {color : Color // color ≠ 0}) :=
  {boundary | Nonempty (Col T fun port => (boundary port).1)}

/-- Every genuine word in the exact support of an open cubic port tangle obeys
the universal cut-parity equation. -/
theorem taitSupport_subset_zeroSum
    (T : PortTangle V I P) (hcubic : IsCubic T) :
    taitSupport T ⊆
      {boundary | (∑ port : P, (boundary port).1) = 0} := by
  intro boundary hboundary
  obtain ⟨coloring, hproper, hword⟩ := hboundary
  have hsum := sum_boundaryWord_eq_zero T hcubic coloring hproper
  calc
    (∑ port : P, (boundary port).1) =
        ∑ port : P, word coloring port := by
      apply Finset.sum_congr rfl
      intro port _
      exact (congrFun hword port).symm
    _ = 0 := hsum

end Finite

end GoertzelV24PortTangleCutParity

end Mettapedia.GraphTheory.FourColor
