import Mettapedia.GraphTheory.FourColor.Compositional.PathPrefixBoundary
import Mettapedia.GraphTheory.FourColor.RootedCutSaturation

/-!
# Cyclic cuts from path prefixes with two large margins

A bounded prefix boundary becomes a useful compositional interface once the
displayed path has more vertices than an acyclic cubic shore can hold on both
sides of the cut.  The prefix is connected along the path.  On the other side,
the component rooted at the first omitted path vertex contains the entire
remaining suffix.  Cubic tree counting therefore forces cycles on both sides.
Rooted saturation then gives connected complementary shores without increasing
the boundary width.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.PathPrefixCyclicCut

open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24CyclicThreeCutConnectedSides
open Mettapedia.GraphTheory
open PathPrefixBoundary
open RootedCutSaturation
open SimpleGraph

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The first omitted path vertex is outside the strict prefix. -/
theorem not_pathPrefixSide_getVert_cut
    {start finish : V} {path : G.Walk start finish} (hpath : path.IsPath)
    (cut : Fin (path.length + 1)) :
    ¬pathPrefixSide path cut (path.getVert cut) := by
  rw [pathPrefixSide_getVert_iff hpath cut cut]
  exact lt_irrefl cut

/-- The complementary component rooted at the first omitted vertex. -/
def prefixExteriorComponent
    {start finish : V} {path : G.Walk start finish} (hpath : path.IsPath)
    (cut : Fin (path.length + 1)) : V → Prop :=
  inducedReachableSide G (fun vertex => ¬pathPrefixSide path cut vertex)
    (path.getVert cut) (not_pathPrefixSide_getVert_cut hpath cut)

/-- Every vertex at or after the cut remains in the rooted complementary
component. -/
theorem getVert_mem_prefixExteriorComponent
    {start finish : V} {path : G.Walk start finish} (hpath : path.IsPath)
    (cut coordinate : Fin (path.length + 1)) (horder : cut ≤ coordinate) :
    prefixExteriorComponent hpath cut (path.getVert coordinate) := by
  let interval := walkInterval path cut.val coordinate.val horder
  have hcoordinateBound : coordinate.val ≤ path.length :=
    Nat.lt_succ_iff.mp coordinate.isLt
  have hintervalLength : interval.length = coordinate.val - cut.val := by
    exact walkInterval_length path cut.val coordinate.val horder
      hcoordinateBound
  have hsupport : ∀ vertex, vertex ∈ interval.support →
      ¬pathPrefixSide path cut vertex := by
    intro vertex hvertex
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hvertex
    rcases hvertex with ⟨offset, hoffsetVertex, hoffsetBound⟩
    rw [hintervalLength] at hoffsetBound
    have htranslatedBound : cut.val + offset ≤ path.length := by omega
    let translated : Fin (path.length + 1) :=
      ⟨cut.val + offset, Nat.lt_succ_iff.mpr htranslatedBound⟩
    have htranslatedVertex : path.getVert translated = vertex := by
      change path.getVert (cut.val + offset) = vertex
      rw [← hoffsetVertex]
      exact (walkInterval_getVert path cut.val coordinate.val offset horder
        hoffsetBound).symm
    rw [← htranslatedVertex, pathPrefixSide_getVert_iff hpath cut translated]
    change ¬cut.val + offset < cut.val
    omega
  refine ⟨?_, ?_⟩
  · change ¬pathPrefixSide path cut (path.getVert coordinate)
    rw [pathPrefixSide_getVert_iff hpath cut coordinate]
    exact not_lt_of_ge horder
  · let inside := interval.induce
      (fun vertex => ¬pathPrefixSide path cut vertex) hsupport
    have hreach :
        (G.induce (fun vertex => ¬pathPrefixSide path cut vertex)).Reachable
          ⟨path.getVert cut, not_pathPrefixSide_getVert_cut hpath cut⟩
          ⟨path.getVert coordinate, by
            change ¬pathPrefixSide path cut (path.getVert coordinate)
            rw [pathPrefixSide_getVert_iff hpath cut coordinate]
            exact not_lt_of_ge horder⟩ := by
      exact ⟨inside⟩
    exact hreach

/-- The rooted exterior component contains at least all distinct vertices of
the displayed suffix. -/
theorem suffixLength_le_natCard_prefixExteriorComponent
    {start finish : V} {path : G.Walk start finish} (hpath : path.IsPath)
    (cut : Fin (path.length + 1)) :
    path.length + 1 - cut.val ≤
      Fintype.card {vertex : V // prefixExteriorComponent hpath cut vertex} := by
  let suffixVertex : Fin (path.length + 1 - cut.val) →
      {vertex : V // prefixExteriorComponent hpath cut vertex} :=
    fun index =>
      let coordinate : Fin (path.length + 1) :=
        ⟨cut.val + index.val, by
          have := index.isLt
          omega⟩
      ⟨path.getVert coordinate,
        getVert_mem_prefixExteriorComponent hpath cut coordinate (by
          change cut.val ≤ cut.val + index.val
          omega)⟩
  have hinjective : Function.Injective suffixVertex := by
    intro first second heq
    apply Fin.ext
    have hvertices := congrArg Subtype.val heq
    have hcutBound : cut.val ≤ path.length :=
      Nat.lt_succ_iff.mp cut.isLt
    have hcoordinates : cut.val + first.val = cut.val + second.val := by
      apply hpath.getVert_injOn
      · have hsuffixSucc : path.length + 1 - cut.val =
            path.length - cut.val + 1 := by omega
        have hfirstLt := first.isLt
        have hfirstLe : first.val ≤ path.length - cut.val := by
          omega
        have hadd := Nat.add_le_of_le_sub hcutBound hfirstLe
        simpa [Nat.add_comm] using hadd
      · have hsuffixSucc : path.length + 1 - cut.val =
            path.length - cut.val + 1 := by omega
        have hsecondLt := second.isLt
        have hsecondLe : second.val ≤ path.length - cut.val := by
          omega
        have hadd := Nat.add_le_of_le_sub hcutBound hsecondLe
        simpa [Nat.add_comm] using hadd
      · exact hvertices
    exact Nat.add_left_cancel hcoordinates
  simpa using Fintype.card_le_of_injective suffixVertex hinjective

/-- A connected cubic side whose boundary is bounded by `bound` and whose
cardinality exceeds the corresponding tree budget must contain a cycle. -/
theorem hasCycleOnSide_of_connected_cubic_of_boundary_lt_card_add_two
    (hregular : G.IsRegularOfDegree 3)
    (side : V → Prop)
    (hsideNonempty : ∃ vertex, side vertex)
    (hsideConnected : (G.induce side).Connected)
    (bound : Nat)
    (hboundary : (crossingEdgeFinset G side).card ≤ bound)
    (hlarge : bound < Fintype.card {vertex : V // side vertex} + 2) :
    HasCycleOnSide G side := by
  classical
  rcases hasCycleOnSide_or_card_le_two_mul_exception_add_removed_sub_two
      side (fun _ => False)
      (by intro _ _ hfalse; exact False.elim hfalse)
      (by intro vertex _ _; exact hregular.degree_eq vertex)
      hsideConnected (crossingEdgeFinset G side) (by
        intro dart
        apply (mem_crossingEdgeFinset_iff side _).2
        exact ⟨dart.1.fst, dart.1.snd,
          (by change dart.1.fst ∈ s(dart.1.fst, dart.1.snd); simp),
          (by change dart.1.snd ∈ s(dart.1.fst, dart.1.snd); simp),
          dart.2.1, dart.2.2⟩) with hcycle | hsmall
  · exact hcycle
  · simp only [Finset.filter_false, Finset.card_empty, Nat.mul_zero,
      zero_add] at hsmall
    have hpositive : 0 < Fintype.card {vertex : V // side vertex} :=
      Fintype.card_pos_iff.mpr ⟨⟨hsideNonempty.choose,
        hsideNonempty.choose_spec⟩⟩
    omega

/-- A path prefix whose boundary is bounded and whose two path margins exceed
the cubic tree budget realizes a cyclic cut. -/
def pathPrefixCyclicEdgeCutRealization
    {start finish : V} {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (cut : Fin (path.length + 1)) (hcut : 0 < cut.val)
    (bound : Nat)
    (hboundary :
      (crossingEdgeFinset G (pathPrefixSide path cut)).card ≤ bound)
    (hprefixLarge : bound < cut.val + 2)
    (hsuffixLarge : bound < (path.length + 1 - cut.val) + 2) :
    CyclicEdgeCutRealization G
      (crossingEdgeFinset G (pathPrefixSide path cut)) := by
  let exterior := prefixExteriorComponent hpath cut
  have hprefixConnected := induce_pathPrefixSide_connected hpath cut hcut
  have hprefixNonempty : ∃ vertex, pathPrefixSide path cut vertex := by
    let coordinate : Fin (path.length + 1) := ⟨0, by omega⟩
    refine ⟨path.getVert coordinate, ?_⟩
    rw [pathPrefixSide_getVert_iff hpath cut coordinate]
    exact hcut
  have hprefixCycle : HasCycleOnSide G (pathPrefixSide path cut) := by
    apply hasCycleOnSide_of_connected_cubic_of_boundary_lt_card_add_two
      hregular (pathPrefixSide path cut) hprefixNonempty hprefixConnected
      bound hboundary
    have hcard : Fintype.card {vertex : V // pathPrefixSide path cut vertex} =
        cut.val := by
      rw [← Nat.card_eq_fintype_card]
      exact natCard_pathPrefixSide_eq hpath cut hcut
    simpa [hcard] using hprefixLarge
  have hexteriorConnected : (G.induce exterior).Connected := by
    exact induce_inducedReachableSide_connected
      (fun vertex => ¬pathPrefixSide path cut vertex) (path.getVert cut)
      (not_pathPrefixSide_getVert_cut hpath cut)
  have hexteriorNonempty : ∃ vertex, exterior vertex := by
    refine ⟨path.getVert cut, ?_⟩
    exact inducedReachableSide_root
      (fun vertex => ¬pathPrefixSide path cut vertex) (path.getVert cut)
      (not_pathPrefixSide_getVert_cut hpath cut)
  have hexteriorBoundary :
      (crossingEdgeFinset G exterior).card ≤ bound := by
    apply le_trans (Finset.card_le_card ?_) hboundary
    intro edge hedge
    apply (mem_crossingEdgeFinset_iff (pathPrefixSide path cut) edge).2
    have hcrossExterior :=
      (mem_crossingEdgeFinset_iff exterior edge).1 hedge
    have hcrossComplement : EdgeCrossesVertexSide G
        (fun vertex => ¬pathPrefixSide path cut vertex) edge :=
      edgeCrossesVertexSide_of_inducedReachableSide
        (fun vertex => ¬pathPrefixSide path cut vertex)
        (path.getVert cut) (not_pathPrefixSide_getVert_cut hpath cut)
        edge hcrossExterior
    exact (edgeCrossesVertexSide_compl G (pathPrefixSide path cut) edge).1
      hcrossComplement
  have hexteriorCycle : HasCycleOnSide G exterior := by
    apply hasCycleOnSide_of_connected_cubic_of_boundary_lt_card_add_two
      hregular exterior hexteriorNonempty hexteriorConnected bound
      hexteriorBoundary
    have hsuffixCard : path.length + 1 - cut.val ≤
        Fintype.card {vertex : V // exterior vertex} := by
      simpa [exterior] using
        suffixLength_le_natCard_prefixExteriorComponent hpath cut
    omega
  refine
    { side := pathPrefixSide path cut
      hcut_eq := fun edge => mem_crossingEdgeFinset_iff _ _
      hinside_cycle := hprefixCycle
      houtside_cycle := ?_ }
  apply HasCycleOnSide.mono
      (side₁ := exterior) (side₂ := fun vertex => ¬pathPrefixSide path cut vertex)
  · intro _ hcomponent
    simpa [exterior, prefixExteriorComponent] using hcomponent.choose
  · exact hexteriorCycle

/-- After rooted saturation, the same two-margin prefix cut has connected
complementary shores and no larger boundary. -/
theorem exists_connectedAtWidth_pathPrefix
    (hconnected : G.Connected)
    {start finish : V} {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (cut : Fin (path.length + 1)) (hcut : 0 < cut.val)
    (bound : Nat)
    (hboundary :
      (crossingEdgeFinset G (pathPrefixSide path cut)).card ≤ bound)
    (hprefixLarge : bound < cut.val + 2)
    (hsuffixLarge : bound < (path.length + 1 - cut.val) + 2) :
    Nonempty (CyclicEdgeCutRealization.ConnectedAtWidth G bound) := by
  let raw := pathPrefixCyclicEdgeCutRealization hpath hregular cut hcut bound
    hboundary hprefixLarge hsuffixLarge
  rcases raw.houtside_cycle with
    ⟨outsideRoot, houtsideRoot, outsideCycle, hcycle, hsupport⟩
  have hrawConnected : (G.induce raw.side).Connected := by
    rw [show raw.side = pathPrefixSide path cut from rfl]
    exact induce_pathPrefixSide_connected hpath cut hcut
  rcases RootedCutSaturation.exists_connectedAtWidth hconnected raw
      hrawConnected
      outsideRoot houtsideRoot outsideCycle hcycle hsupport bound hboundary with
    ⟨connected, _hedges, _hside⟩
  exact ⟨connected⟩

end

end Mettapedia.GraphTheory.FourColor.Compositional.PathPrefixCyclicCut
