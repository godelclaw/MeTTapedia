import Mettapedia.GraphTheory.FourColor.GoertzelV24DualCycleCrossingInjective
import Mettapedia.GraphTheory.FourColor.GoertzelV24FiniteDeletionCyclicCut
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedDualCycleSeparator

/-!
# A bridge-safe separator from literally selected dual-cycle crossings

The older framed separator chooses the primal edge crossed by each facial-dual
step from a global unique-shared-edge hypothesis.  Source corridor geometry
instead supplies a particular crossing edge at each step.  This module records
that source-faithful presentation and proves the same parity separator directly
from the selected edges.

No global two-sidedness or pairwise face-intersection uniqueness is used.  The
only incidence input is the rotation system's ordinary at-most-two facial
incidences per primal edge.  This is generic rotation-system infrastructure;
it does not construct a source corridor or eliminate any resulting small cut.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceParityBoundary
open GoertzelV24PrimalCycleSpace
open GoertzelV24WalkCycleParity
open SimpleGraph
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

namespace GoertzelV24SelectedDualCycleSeparator

/-- A simple closed facial-dual walk together with the actual primal edge
crossed at every step. -/
structure SelectedDualCycle (RS : RotationSystem V E)
    (start : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))) where
  walk : (interiorDualGraph
    (orbitFaceBoundary RS)
    (Finset.univ : Finset (OrbitFace RS))).Walk start start
  isCycle : walk.IsCycle
  crossingEdge : Fin walk.length → E
  crossing_mem_shared : ∀ step,
    crossingEdge step ∈ sharedInteriorEdges
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))
      (walk.getVert step.val).1
      (walk.getVert (step.val + 1)).1

namespace SelectedDualCycle

/-- Choose one literal shared primal edge for each step of an already-built
simple dual cycle.  Adjacency supplies the nonempty shared-edge witness. -/
noncomputable def ofWalk (RS : RotationSystem V E)
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Walk start start)
    (hcycle : walk.IsCycle) : SelectedDualCycle RS start where
  walk := walk
  isCycle := hcycle
  crossingEdge := fun step => Classical.choose
    (exists_mem_sharedInteriorEdges_of_adj
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))
      (walk.adj_getVert_succ step.isLt))
  crossing_mem_shared := fun step => Classical.choose_spec
    (exists_mem_sharedInteriorEdges_of_adj
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))
      (walk.adj_getVert_succ step.isLt))

/-- Choose literal shared primal crossings for a simple dual cycle while
pinning one specified crossing at one specified step.  This preserves the
source provenance of a distinguished corridor rung without requiring choices
at the other steps to be canonical. -/
noncomputable def ofWalkWithCrossingAt (RS : RotationSystem V E)
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Walk start start)
    (hcycle : walk.IsCycle)
    (anchor : Fin walk.length) (edge : E)
    (hedge : edge ∈ sharedInteriorEdges
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))
      (walk.getVert anchor.val).1
      (walk.getVert (anchor.val + 1)).1) : SelectedDualCycle RS start where
  walk := walk
  isCycle := hcycle
  crossingEdge := fun step => if step = anchor then edge else Classical.choose
    (exists_mem_sharedInteriorEdges_of_adj
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))
      (walk.adj_getVert_succ step.isLt))
  crossing_mem_shared := by
    intro step
    by_cases hstep : step = anchor
    · simpa [hstep] using hedge
    · simp only [hstep, ↓reduceIte]
      exact Classical.choose_spec
        (exists_mem_sharedInteriorEdges_of_adj
          (orbitFaceBoundary RS)
          (Finset.univ : Finset (OrbitFace RS))
          (walk.adj_getVert_succ step.isLt))

@[simp] theorem ofWalkWithCrossingAt_crossingEdge
    (RS : RotationSystem V E)
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Walk start start)
    (hcycle : walk.IsCycle)
    (anchor : Fin walk.length) (edge : E)
    (hedge : edge ∈ sharedInteriorEdges
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))
      (walk.getVert anchor.val).1
      (walk.getVert (anchor.val + 1)).1) :
    (ofWalkWithCrossingAt RS walk hcycle anchor edge hedge).crossingEdge anchor = edge := by
  simp [ofWalkWithCrossingAt]

/-- The finite carrier of the selected primal crossings. -/
def crossingEdges {RS : RotationSystem V E}
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (cycle : SelectedDualCycle RS start) : Finset E :=
  Finset.univ.image cycle.crossingEdge

@[simp] theorem mem_crossingEdges_iff
    {RS : RotationSystem V E}
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (cycle : SelectedDualCycle RS start) (edge : E) :
    edge ∈ cycle.crossingEdges ↔
      ∃ step : Fin cycle.walk.length, cycle.crossingEdge step = edge := by
  simp [crossingEdges]

/-- A selected crossing lies on the face before its dual step. -/
theorem crossingEdge_mem_leftFace
    {RS : RotationSystem V E}
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (cycle : SelectedDualCycle RS start)
    (step : Fin cycle.walk.length) :
    cycle.crossingEdge step ∈
      orbitFaceBoundary RS (cycle.walk.getVert step.val).1 := by
  exact (mem_sharedInteriorEdges_iff
    (orbitFaceBoundary RS)
    (Finset.univ : Finset (OrbitFace RS))).1
      (cycle.crossing_mem_shared step) |>.2.1

/-- A selected crossing lies on the face after its dual step. -/
theorem crossingEdge_mem_rightFace
    {RS : RotationSystem V E}
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (cycle : SelectedDualCycle RS start)
    (step : Fin cycle.walk.length) :
    cycle.crossingEdge step ∈
      orbitFaceBoundary RS (cycle.walk.getVert (step.val + 1)).1 := by
  exact (mem_sharedInteriorEdges_iff
    (orbitFaceBoundary RS)
    (Finset.univ : Finset (OrbitFace RS))).1
      (cycle.crossing_mem_shared step) |>.2.2

/-- Equal selected primal crossings force equal unoriented dual edges when
each primal edge has at most two facial incidences. -/
theorem coreDualWalkGraphEdge_eq_of_crossingEdge_eq
    {RS : RotationSystem V E}
    (hall : ∀ edge, totalIncidenceCount
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) edge ≤ 2)
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (cycle : SelectedDualCycle RS start)
    {first second : Fin cycle.walk.length}
    (hedges : cycle.crossingEdge first = cycle.crossingEdge second) :
    GoertzelV24DualPathTransversal.coreDualWalkGraphEdge
        (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) cycle.walk first =
      GoertzelV24DualPathTransversal.coreDualWalkGraphEdge
        (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) cycle.walk second := by
  let firstLeft := cycle.walk.getVert first.val
  let firstRight := cycle.walk.getVert (first.val + 1)
  let secondLeft := cycle.walk.getVert second.val
  let secondRight := cycle.walk.getVert (second.val + 1)
  have hfirstAdj := cycle.walk.adj_getVert_succ first.isLt
  have hsecondAdj := cycle.walk.adj_getVert_succ second.isLt
  have hfirstFaces : firstLeft.1 ≠ firstRight.1 := by
    intro hfaces
    exact hfirstAdj.ne (Subtype.ext hfaces)
  have hsecondFaces : secondLeft.1 ≠ secondRight.1 := by
    intro hfaces
    exact hsecondAdj.ne (Subtype.ext hfaces)
  have hfirstLeft : cycle.crossingEdge first ∈
      orbitFaceBoundary RS firstLeft.1 :=
    cycle.crossingEdge_mem_leftFace first
  have hfirstRight : cycle.crossingEdge first ∈
      orbitFaceBoundary RS firstRight.1 :=
    cycle.crossingEdge_mem_rightFace first
  have hsecondLeft : cycle.crossingEdge first ∈
      orbitFaceBoundary RS secondLeft.1 := by
    rw [hedges]
    exact cycle.crossingEdge_mem_leftFace second
  have hsecondRight : cycle.crossingEdge first ∈
      orbitFaceBoundary RS secondRight.1 := by
    rw [hedges]
    exact cycle.crossingEdge_mem_rightFace second
  have hleft :=
    eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) hall
      firstLeft.2 firstRight.2 secondLeft.2 hfirstFaces
      hfirstLeft hfirstRight hsecondLeft
  have hright :=
    eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) hall
      firstLeft.2 firstRight.2 secondRight.2 hfirstFaces
      hfirstLeft hfirstRight hsecondRight
  change s(firstLeft, firstRight) = s(secondLeft, secondRight)
  rcases hleft with hleft | hleft <;>
    rcases hright with hright | hright
  · exact False.elim (hsecondFaces (hleft.trans hright.symm))
  · apply Sym2.eq_iff.mpr
    exact Or.inl ⟨Subtype.ext hleft.symm, Subtype.ext hright.symm⟩
  · apply Sym2.eq_iff.mpr
    exact Or.inr ⟨Subtype.ext hright.symm, Subtype.ext hleft.symm⟩
  · exact False.elim (hsecondFaces (hleft.trans hright.symm))

/-- A simple selected dual cycle crosses pairwise distinct primal edges. -/
theorem crossingEdge_injective
    {RS : RotationSystem V E}
    (hall : ∀ edge, totalIncidenceCount
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) edge ≤ 2)
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (cycle : SelectedDualCycle RS start) :
    Function.Injective cycle.crossingEdge := by
  intro first second hedges
  have hgraphEdge := cycle.coreDualWalkGraphEdge_eq_of_crossingEdge_eq
    hall hedges
  have hinjective : Function.Injective cycle.walk.edges.get :=
    List.nodup_iff_injective_get.mp cycle.isCycle.edges_nodup
  let first' : Fin cycle.walk.edges.length :=
    Fin.cast cycle.walk.length_edges.symm first
  let second' : Fin cycle.walk.edges.length :=
    Fin.cast cycle.walk.length_edges.symm second
  have hget : cycle.walk.edges.get first' = cycle.walk.edges.get second' := by
    rw [GoertzelV24DualPathTransversal.edges_get_coreDualWalkGraphEdge
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) cycle.walk first,
      GoertzelV24DualPathTransversal.edges_get_coreDualWalkGraphEdge
        (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) cycle.walk second]
    exact hgraphEdge
  exact Fin.cast_injective cycle.walk.length_edges.symm (hinjective hget)

/-- A selected simple dual cycle of length `n` crosses exactly `n` primal
edges. -/
theorem card_crossingEdges_eq_length
    {RS : RotationSystem V E}
    (hall : ∀ edge, totalIncidenceCount
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) edge ≤ 2)
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (cycle : SelectedDualCycle RS start) :
    cycle.crossingEdges.card = cycle.walk.length := by
  rw [crossingEdges,
    Finset.card_image_of_injective _ (cycle.crossingEdge_injective hall),
    Finset.card_univ, Fintype.card_fin]

/-- If every face visited by a literally selected dual cycle belongs to a
chosen interior family, then none of its selected primal crossings lies on
the boundary of a face outside that family.  This is the selected-edge form
of hole-boundary safety and uses only the ordinary at-most-two incidence
bound. -/
theorem crossingEdges_disjoint_faceBoundary_of_support
    {RS : RotationSystem V E}
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (cycle : SelectedDualCycle RS start)
    (interiorFaces : Finset (OrbitFace RS))
    (hsupport : ∀ face ∈ cycle.walk.support,
      face.1 ∈ interiorFaces)
    (hole : OrbitFace RS)
    (hhole : hole ∉ interiorFaces) :
    Disjoint cycle.crossingEdges (orbitFaceBoundary RS hole) := by
  rw [Finset.disjoint_left]
  intro edge hcrossing hholeBoundary
  rcases (cycle.mem_crossingEdges_iff edge).1 hcrossing with ⟨step, hstep⟩
  let leftFace := cycle.walk.getVert step.val
  let rightFace := cycle.walk.getVert (step.val + 1)
  have hleftRight : leftFace.1 ≠ rightFace.1 := by
    intro hfaces
    exact (cycle.walk.adj_getVert_succ step.isLt).ne (Subtype.ext hfaces)
  have hleft : edge ∈ orbitFaceBoundary RS leftFace.1 := by
    rw [← hstep]
    exact cycle.crossingEdge_mem_leftFace step
  have hright : edge ∈ orbitFaceBoundary RS rightFace.1 := by
    rw [← hstep]
    exact cycle.crossingEdge_mem_rightFace step
  have hcases :=
    eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))
      (orbitFace_incidence_le_two RS)
      leftFace.2 rightFace.2 (Finset.mem_univ hole)
      hleftRight hleft hright hholeBoundary
  rcases hcases with hholeLeft | hholeRight
  · apply hhole
    have hint := hsupport leftFace
      (cycle.walk.getVert_mem_support step.val)
    simpa [hholeLeft] using hint
  · apply hhole
    have hint := hsupport rightFace
      (cycle.walk.getVert_mem_support (step.val + 1))
    simpa [hholeRight] using hint

/-- The parity boundary of one selected crossing is the sum of the labels on
the two consecutive dual faces. -/
theorem orbitFaceParityBoundaryLinearMap_apply_crossingEdge
    {RS : RotationSystem V E}
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (cycle : SelectedDualCycle RS start)
    (step : Fin cycle.walk.length)
    (coefficients : OrbitFace RS → F2) :
    orbitFaceParityBoundaryLinearMap RS coefficients
        (cycle.crossingEdge step) =
      coefficients (cycle.walk.getVert step.val).1 +
        coefficients (cycle.walk.getVert (step.val + 1)).1 := by
  have hadj := cycle.walk.adj_getVert_succ step.isLt
  have hfaces : (cycle.walk.getVert step.val).1 ≠
      (cycle.walk.getVert (step.val + 1)).1 := by
    intro hface
    exact hadj.ne (Subtype.ext hface)
  have hleft := cycle.crossingEdge_mem_leftFace step
  have hright := cycle.crossingEdge_mem_rightFace step
  rcases (mem_orbitFaceBoundary_iff RS
      (cycle.walk.getVert step.val).1 _).1 hleft with
    ⟨leftDart, hleftDart, hleftEdge⟩
  rcases (mem_orbitFaceBoundary_iff RS
      (cycle.walk.getVert (step.val + 1)).1 _).1 hright with
    ⟨rightDart, hrightDart, hrightEdge⟩
  have hleftFace : dartOrbitFace RS leftDart =
      (cycle.walk.getVert step.val).1 :=
    (mem_orbitFaceDarts_iff RS _ _).1 hleftDart
  have hrightFace : dartOrbitFace RS rightDart =
      (cycle.walk.getVert (step.val + 1)).1 :=
    (mem_orbitFaceDarts_iff RS _ _).1 hrightDart
  have hrightDartEq : rightDart = RS.alpha leftDart := by
    rcases RS.edge_fiber_two_cases hleftEdge hrightEdge with heq | heq
    · exfalso
      apply hfaces
      rw [← hleftFace, ← hrightFace, heq]
    · exact heq
  have halphaFace : dartOrbitFace RS (RS.alpha leftDart) =
      (cycle.walk.getVert (step.val + 1)).1 := by
    rw [← hrightDartEq]
    exact hrightFace
  rw [← hleftEdge, orbitFaceParityBoundaryLinearMap_apply_edgeOf,
    hleftFace, halphaFace]

omit [Fintype V] [DecidableEq V] [Fintype E] in
private theorem getVert_succ_eq_getVert_finRotate
    {H : SimpleGraph V} {start : V}
    (walk : H.Walk start start) (hcycle : walk.IsCycle)
    (step : Fin walk.length) :
    walk.getVert (step.val + 1) =
      walk.getVert (finRotate walk.length step).val := by
  have hpositive : 0 < walk.length :=
    lt_of_lt_of_le (by omega) hcycle.three_le_length
  have hone : 1 < walk.length :=
    lt_of_lt_of_le (by omega) hcycle.three_le_length
  letI : NeZero walk.length := ⟨Nat.ne_of_gt hpositive⟩
  by_cases hnext : step.val + 1 < walk.length
  · have hrotate : (finRotate walk.length step).val = step.val + 1 := by
      rw [finRotate_apply, Fin.val_add, Fin.val_one',
        Nat.mod_eq_of_lt hone, Nat.mod_eq_of_lt hnext]
    rw [hrotate]
  · have hlast : step.val + 1 = walk.length := by omega
    have hrotate : (finRotate walk.length step).val = 0 := by
      rw [finRotate_apply, Fin.val_add, Fin.val_one',
        Nat.mod_eq_of_lt hone, hlast, Nat.mod_self]
    rw [hlast, hrotate, walk.getVert_length, walk.getVert_zero]

/-- The total parity boundary on the selected crossings of a simple dual
cycle vanishes. -/
theorem sum_orbitFaceParityBoundaryLinearMap_crossings_eq_zero
    {RS : RotationSystem V E}
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (cycle : SelectedDualCycle RS start)
    (coefficients : OrbitFace RS → F2) :
    (∑ step : Fin cycle.walk.length,
      orbitFaceParityBoundaryLinearMap RS coefficients
        (cycle.crossingEdge step)) = 0 := by
  simp_rw [cycle.orbitFaceParityBoundaryLinearMap_apply_crossingEdge]
  rw [Finset.sum_add_distrib]
  have hshift :
      (∑ step : Fin cycle.walk.length,
        coefficients (cycle.walk.getVert (step.val + 1)).1) =
      ∑ step : Fin cycle.walk.length,
        coefficients (cycle.walk.getVert step.val).1 := by
    calc
      (∑ step : Fin cycle.walk.length,
          coefficients (cycle.walk.getVert (step.val + 1)).1) =
          ∑ step : Fin cycle.walk.length,
            coefficients
              (cycle.walk.getVert
                (finRotate cycle.walk.length step).val).1 := by
        apply Finset.sum_congr rfl
        intro step _hstep
        rw [getVert_succ_eq_getVert_finRotate cycle.walk cycle.isCycle step]
      _ = ∑ step : Fin cycle.walk.length,
          coefficients (cycle.walk.getVert step.val).1 :=
        Equiv.sum_comp (finRotate cycle.walk.length)
          (fun step : Fin cycle.walk.length =>
            coefficients (cycle.walk.getVert step.val).1)
  rw [hshift]
  simp

end SelectedDualCycle

variable {G : SimpleGraph V} [DecidableRel G.Adj]

local instance graphEdgeSetDecidableEq (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Subtype.instDecidableEq

namespace SelectedDualCycle

/-- Every primal cycle has even intersection with the literally selected
crossings of a simple facial-dual cycle. -/
theorem f2CycleSpace_sum_crossings_eq_zero
    (data : Data G)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (heuler : (Fintype.card V : Int) - Fintype.card G.edgeSet +
      Fintype.card (OrbitFace data.toRotationSystem) = 2)
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (cycle : SelectedDualCycle data.toRotationSystem start)
    {primalCycle : G.edgeSet → F2}
    (hcycle : primalCycle ∈ f2CycleSpace G) :
    (∑ step : Fin cycle.walk.length,
      primalCycle (cycle.crossingEdge step)) = 0 := by
  have hspan : primalCycle ∈ LinearMap.range
      (orbitFaceParityBoundaryLinearMap data.toRotationSystem) := by
    rw [range_orbitFaceParityBoundaryLinearMap_eq_f2CycleSpace
      data hdual hconnected heuler]
    exact hcycle
  rcases hspan with ⟨coefficients, rfl⟩
  exact cycle.sum_orbitFaceParityBoundaryLinearMap_crossings_eq_zero
    coefficients

/-- The set of underlying graph edges selected by the dual cycle. -/
def primalCut
    {data : Data G}
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (cycle : SelectedDualCycle data.toRotationSystem start) :
    Set (Sym2 V) :=
  {edge | ∃ step : Fin cycle.walk.length,
    (cycle.crossingEdge step).1 = edge}

/-- The set-valued selected cut is exactly the ambient-value image of its
finite crossing-edge support.  This is the representation bridge into the
generic finite-deletion component API; it adds no geometric hypothesis. -/
theorem primalCut_eq_edgeFinsetValueSet_crossingEdges
    {data : Data G}
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (cycle : SelectedDualCycle data.toRotationSystem start) :
    cycle.primalCut =
      GoertzelV24FiniteDeletionCyclicCut.edgeFinsetValueSet
        cycle.crossingEdges := by
  ext edge
  rw [GoertzelV24FiniteDeletionCyclicCut.mem_edgeFinsetValueSet_iff]
  constructor
  · rintro ⟨step, hstep⟩
    exact ⟨cycle.crossingEdge step,
      (cycle.mem_crossingEdges_iff _).2 ⟨step, rfl⟩, hstep⟩
  · rintro ⟨crossing, hcrossing, hvalue⟩
    rcases (cycle.mem_crossingEdges_iff crossing).1 hcrossing with
      ⟨step, hstep⟩
    exact ⟨step, congrArg Subtype.val hstep |>.trans hvalue⟩

/-- Deleting the literally selected crossings of a simple facial-dual cycle
disconnects the underlying graph of a framed spherical cellulation. -/
theorem not_connected_deleteEdges_primalCut
    (data : Data G)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (heuler : (Fintype.card V : Int) - Fintype.card G.edgeSet +
      Fintype.card (OrbitFace data.toRotationSystem) = 2)
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (cycle : SelectedDualCycle data.toRotationSystem start) :
    ¬ (G.deleteEdges cycle.primalCut).Connected := by
  intro hdeleteConnected
  let firstStep : Fin cycle.walk.length :=
    ⟨0, lt_of_lt_of_le (by omega) cycle.isCycle.three_le_length⟩
  let firstEdge : G.edgeSet := cycle.crossingEdge firstStep
  rcases data.toRotationSystem.dartsOn_nonempty firstEdge with ⟨dart, hdart⟩
  have hdartEdge : data.toRotationSystem.edgeOf dart = firstEdge :=
    (data.toRotationSystem.mem_dartsOn).1 hdart
  have hdartEdgeValue : dart.edge = firstEdge.1 :=
    congrArg Subtype.val hdartEdge
  rcases hdeleteConnected dart.snd dart.fst with ⟨returnWalkDeleted⟩
  let returnWalk : G.Walk dart.snd dart.fst :=
    returnWalkDeleted.mapLe (G.deleteEdges_le cycle.primalCut)
  have hreturnEdges : returnWalk.edges = returnWalkDeleted.edges := by
    exact returnWalkDeleted.edges_mapLe_eq_edges
      (G.deleteEdges_le cycle.primalCut)
  have hcrossingCut (step : Fin cycle.walk.length) :
      (cycle.crossingEdge step).1 ∈ cycle.primalCut := ⟨step, rfl⟩
  have hreturnAvoid (step : Fin cycle.walk.length) :
      (cycle.crossingEdge step).1 ∉ returnWalk.edges := by
    intro hmem
    have hdeleted := returnWalkDeleted.edges_subset_edgeSet
      (by simpa [hreturnEdges] using hmem)
    rw [SimpleGraph.edgeSet_deleteEdges] at hdeleted
    exact hdeleted.2 (hcrossingCut step)
  let closedWalk : G.Walk dart.fst dart.fst :=
    SimpleGraph.Walk.cons dart.adj returnWalk
  have hcycle : walkEdgeParity closedWalk ∈ f2CycleSpace G :=
    walkEdgeParity_mem_f2CycleSpace_of_closed closedWalk
  have hcoordinates := cycle.f2CycleSpace_sum_crossings_eq_zero
    data hdual hconnected heuler hcycle
  have hinjective := cycle.crossingEdge_injective
    (orbitFace_incidence_le_two data.toRotationSystem)
  have hfirstCoordinate : walkEdgeParity closedWalk firstEdge = 1 := by
    have hreturnCount : returnWalk.edges.count firstEdge.1 = 0 :=
      List.count_eq_zero.2 (hreturnAvoid firstStep)
    have hdartPairValue : s(dart.fst, dart.snd) = firstEdge.1 :=
      hdartEdgeValue
    change ((List.count firstEdge.1
      (s(dart.fst, dart.snd) :: returnWalk.edges) : Nat) : F2) = 1
    simp [hdartPairValue, hreturnCount]
  have hotherCoordinate (step : Fin cycle.walk.length)
      (hne : step ≠ firstStep) :
      walkEdgeParity closedWalk (cycle.crossingEdge step) = 0 := by
    let edge := cycle.crossingEdge step
    have hreturnCount : returnWalk.edges.count edge.1 = 0 :=
      List.count_eq_zero.2 (hreturnAvoid step)
    have hdartPairNe : s(dart.fst, dart.snd) ≠ edge.1 := by
      intro heq
      apply hne
      apply hinjective
      apply Subtype.ext
      exact (hdartEdgeValue.symm.trans heq).symm
    change ((List.count edge.1
      (s(dart.fst, dart.snd) :: returnWalk.edges) : Nat) : F2) = 0
    simp [hdartPairNe, hreturnCount]
  have hsumOne :
      (∑ step : Fin cycle.walk.length,
        walkEdgeParity closedWalk (cycle.crossingEdge step)) = 1 := by
    rw [Finset.sum_eq_single firstStep]
    · exact hfirstCoordinate
    · intro step _hstep hne
      exact hotherCoordinate step hne
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ firstStep))
  rw [hsumOne] at hcoordinates
  exact one_ne_zero hcoordinates

end SelectedDualCycle

end GoertzelV24SelectedDualCycleSeparator

end

end Mettapedia.GraphTheory.FourColor
