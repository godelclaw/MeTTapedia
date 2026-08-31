import Mettapedia.GraphTheory.Embedding.FaceCut
import Mettapedia.GraphTheory.FourColor.GoertzelV24LocalFaceCutCycleWalkTransport

/-!
# Exact face cuts along locally cubic cycle turns

This module exposes the rotation-system algebra used when a face cut is
traced along one side of an embedded cycle.  The statements are independent
of four-colour-specific objects: they concern an exact face cut and three
darts in one locally cubic rotation fiber.

The implementation delegates the unselected-turn case to the established
rotation-system library while presenting a stable semantic API for new
consumers.
-/

namespace SimpleGraph.Walk

variable {Vertex : Type*} {Graph : SimpleGraph Vertex}

/-- A trail traverses a given unoriented edge in at most one orientation. -/
theorem IsTrail.dart_eq_of_mem_darts_and_edge_eq
    {left right : Vertex} {walk : Graph.Walk left right}
    (htrail : walk.IsTrail)
    {first second : Graph.Dart}
    (hfirst : first ∈ walk.darts)
    (hsecond : second ∈ walk.darts)
    (hedge : first.edge = second.edge) :
    first = second := by
  rcases List.mem_iff_get.mp hfirst with ⟨firstPosition, hfirstGet⟩
  rcases List.mem_iff_get.mp hsecond with ⟨secondPosition, hsecondGet⟩
  rw [← hfirstGet, ← hsecondGet] at hedge
  have hedgeGet :
      walk.edges.get (Fin.cast (by simp) firstPosition) =
        walk.edges.get (Fin.cast (by simp) secondPosition) := by
    simpa [SimpleGraph.Walk.edges] using hedge
  have hpositions :
      (Fin.cast (by simp) firstPosition : Fin walk.edges.length) =
        Fin.cast (by simp) secondPosition :=
    htrail.edges_nodup.get_inj_iff.mp hedgeGet
  have : firstPosition = secondPosition := by
    apply Fin.ext
    simpa using congrArg Fin.val hpositions
  subst secondPosition
  exact hfirstGet.symm.trans hsecondGet

end SimpleGraph.Walk

namespace Mettapedia.GraphTheory.Embedding

open Mettapedia.GraphTheory.FourColor
open Mettapedia.GraphTheory.FourColor.GoertzelV24FaceDualConnectedness
open Mettapedia.GraphTheory.FourColor.GoertzelV24FaceOrbitIncidence

noncomputable section

/-! ## Linear propagation -/

/-- A value propagated across every successor step of a natural-number
interval has equal values at the interval endpoints. -/
theorem eq_of_eq_succ_on_interval {A : Type*} (value : Nat → A)
    {first last : Nat} (hfirstLast : first ≤ last)
    (hstep : ∀ index, first ≤ index → index < last →
      value index = value (index + 1)) :
    value first = value last := by
  induction last, hfirstLast using Nat.le_induction with
  | base => rfl
  | succ last hfirstLast ih =>
      exact (ih (fun index hfirstIndex hindexLast =>
        hstep index hfirstIndex (hindexLast.trans (Nat.lt_succ_self last)))) |>.trans
          (hstep last hfirstLast (Nat.lt_succ_self last))

/-- A binary value that is constant except for one successor transition has
different values at the two ends of the interval. -/
theorem ne_of_single_f2_flip_on_interval (value : Nat → F2)
    {first pivot last : Nat} (hfirstPivot : first < pivot)
    (hpivotLast : pivot < last)
    (hbefore : ∀ index, first ≤ index → index + 1 < pivot →
      value index = value (index + 1))
    (hflip : value (pivot - 1) + value pivot = 1)
    (hafter : ∀ index, pivot ≤ index → index < last →
      value index = value (index + 1)) :
    value first ≠ value last := by
  have hfirstPred : first ≤ pivot - 1 := by omega
  have hbeforeEq : value first = value (pivot - 1) :=
    eq_of_eq_succ_on_interval value hfirstPred (by
      intro index hfirstIndex hindexPred
      apply hbefore index hfirstIndex
      omega)
  have hafterEq : value pivot = value last :=
    eq_of_eq_succ_on_interval value hpivotLast.le hafter
  apply (f2_add_eq_one_iff_ne (value first) (value last)).mp
  calc
    value first + value last = value (pivot - 1) + value pivot := by
      rw [hbeforeEq, hafterEq]
    _ = 1 := hflip

namespace ExactFaceCut

variable {V E A : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]
  {RS : RotationSystem V E} {selected : E → Prop}

/-- An exact-cut label is preserved through one locally cubic cycle turn
when the unused incident edge is not selected. -/
theorem label_eq_across_locallyCubicCycleTurn
    (cut : ExactFaceCut RS selected A)
    (hrotation : VertexRotationCyclic RS)
    (previous outgoing : RS.D)
    (hcard : (RS.dartsAt (RS.vertOf outgoing)).card = 3)
    (hbase : RS.vertOf outgoing = RS.vertOf (RS.alpha previous))
    (hnonback : RS.alpha previous ≠ outgoing)
    (hother : ∀ dart : RS.D,
      RS.vertOf dart = RS.vertOf outgoing →
      dart ≠ RS.alpha previous → dart ≠ outgoing →
      ¬selected (RS.edgeOf dart)) :
    cut.label (dartOrbitFace RS previous) =
      cut.label (dartOrbitFace RS outgoing) := by
  exact RS.labels_eq_of_cutCycle_turn_at_card_dartsAt_eq_three
    hrotation cut.label selected cut.separates previous outgoing
      hcard hbase hnonback hother

/-- The label on the opposite side of the same locally cubic cycle turn is
also preserved.  Algebraically this is the preceding theorem applied to the
reversed pair of opposite darts. -/
theorem label_eq_opposite_across_locallyCubicCycleTurn
    (cut : ExactFaceCut RS selected A)
    (hrotation : VertexRotationCyclic RS)
    (previous outgoing : RS.D)
    (hcard : (RS.dartsAt (RS.vertOf outgoing)).card = 3)
    (hbase : RS.vertOf outgoing = RS.vertOf (RS.alpha previous))
    (hnonback : RS.alpha previous ≠ outgoing)
    (hother : ∀ dart : RS.D,
      RS.vertOf dart = RS.vertOf outgoing →
      dart ≠ RS.alpha previous → dart ≠ outgoing →
      ¬selected (RS.edgeOf dart)) :
    cut.label (dartOrbitFace RS (RS.alpha outgoing)) =
      cut.label (dartOrbitFace RS (RS.alpha previous)) := by
  apply cut.label_eq_across_locallyCubicCycleTurn hrotation
    (previous := RS.alpha outgoing) (outgoing := RS.alpha previous)
  · simpa [hbase] using hcard
  · simpa only [RS.alpha_involutive] using hbase.symm
  · simpa only [RS.alpha_involutive] using hnonback.symm
  · intro dart hdart hdartOutgoing hdartPrevious
    apply hother dart
    · exact hdart.trans hbase.symm
    · exact hdartPrevious
    · simpa only [RS.alpha_involutive] using hdartOutgoing

/-- Suppose the vertex rotation encounters `middle` between the dart arriving
along `previous` and the dart `outgoing`.  Following that side of the cycle
crosses the edge of `middle`; hence selecting that edge forces the two
endpoint face labels to differ. -/
theorem label_ne_across_cycleTurn_of_selected_middle
    (cut : ExactFaceCut RS selected A)
    (previous middle outgoing : RS.D)
    (harrivedMiddle : RS.rho (RS.alpha previous) = middle)
    (hmiddleOutgoing : RS.rho middle = outgoing)
    (hmiddle : selected (RS.edgeOf middle)) :
    cut.label (dartOrbitFace RS previous) ≠
      cut.label (dartOrbitFace RS outgoing) := by
  have hmiddleLabels := (cut.separates middle).2 hmiddle
  have hpreviousMiddle :
      dartOrbitFace RS previous = dartOrbitFace RS middle := by
    calc
      dartOrbitFace RS previous = dartOrbitFace RS (RS.phi previous) :=
        (dartOrbitFace_phi_eq RS previous).symm
      _ = dartOrbitFace RS middle := by
        rw [RotationSystem.phi_apply, harrivedMiddle]
  have hmiddleOutgoingFace :
      dartOrbitFace RS (RS.alpha middle) = dartOrbitFace RS outgoing := by
    calc
      dartOrbitFace RS (RS.alpha middle) =
          dartOrbitFace RS (RS.rho middle) :=
        dartOrbitFace_alpha_eq_dartOrbitFace_rho RS middle
      _ = dartOrbitFace RS outgoing := by rw [hmiddleOutgoing]
  intro heq
  apply hmiddleLabels
  calc
    cut.label (dartOrbitFace RS middle) =
        cut.label (dartOrbitFace RS previous) :=
      congrArg cut.label hpreviousMiddle.symm
    _ = cut.label (dartOrbitFace RS outgoing) := heq
    _ = cut.label (dartOrbitFace RS (RS.alpha middle)) :=
      congrArg cut.label hmiddleOutgoingFace.symm

/-- Binary exact-cut recurrence on the oriented side of a turn: if the
rotation runs from the arriving dart through `middle` to `outgoing`, the
side label flips exactly when the middle edge is selected. -/
theorem label_add_across_cycleTurn_eq_one_iff_selected_middle
    (cut : ExactFaceCut RS selected F2)
    (previous middle outgoing : RS.D)
    (harrivedMiddle : RS.rho (RS.alpha previous) = middle)
    (hmiddleOutgoing : RS.rho middle = outgoing) :
    cut.label (dartOrbitFace RS previous) +
        cut.label (dartOrbitFace RS outgoing) = 1 ↔
      selected (RS.edgeOf middle) := by
  have hpreviousMiddle : dartOrbitFace RS previous =
      dartOrbitFace RS middle := by
    calc
      dartOrbitFace RS previous = dartOrbitFace RS (RS.phi previous) :=
        (dartOrbitFace_phi_eq RS previous).symm
      _ = dartOrbitFace RS middle := by
        rw [RotationSystem.phi_apply, harrivedMiddle]
  have houtgoingMiddle : dartOrbitFace RS outgoing =
      dartOrbitFace RS (RS.alpha middle) := by
    calc
      dartOrbitFace RS outgoing = dartOrbitFace RS (RS.rho middle) := by
        rw [hmiddleOutgoing]
      _ = dartOrbitFace RS (RS.alpha middle) :=
        (dartOrbitFace_alpha_eq_dartOrbitFace_rho RS middle).symm
  rw [hpreviousMiddle, houtgoingMiddle]
  exact cut.label_add_opposite_eq_one_iff_selected middle

/-- The companion binary recurrence on the opposite side of a turn.  When
the rotation runs from `outgoing` through `middle` to the arriving dart, the
opposite-side label flips exactly when the middle edge is selected. -/
theorem label_add_opposite_across_cycleTurn_eq_one_iff_selected_middle
    (cut : ExactFaceCut RS selected F2)
    (previous middle outgoing : RS.D)
    (houtgoingMiddle : RS.rho outgoing = middle)
    (hmiddleArrived : RS.rho middle = RS.alpha previous) :
    cut.label (dartOrbitFace RS (RS.alpha previous)) +
        cut.label (dartOrbitFace RS (RS.alpha outgoing)) = 1 ↔
      selected (RS.edgeOf middle) := by
  have hpreviousMiddle : dartOrbitFace RS (RS.alpha previous) =
      dartOrbitFace RS (RS.alpha middle) := by
    calc
      dartOrbitFace RS (RS.alpha previous) =
          dartOrbitFace RS (RS.rho middle) := by rw [hmiddleArrived]
      _ = dartOrbitFace RS (RS.alpha middle) :=
        (dartOrbitFace_alpha_eq_dartOrbitFace_rho RS middle).symm
  have houtgoingMiddleFace : dartOrbitFace RS (RS.alpha outgoing) =
      dartOrbitFace RS middle := by
    calc
      dartOrbitFace RS (RS.alpha outgoing) =
          dartOrbitFace RS (RS.rho outgoing) :=
        dartOrbitFace_alpha_eq_dartOrbitFace_rho RS outgoing
      _ = dartOrbitFace RS middle := by rw [houtgoingMiddle]
  rw [hpreviousMiddle, houtgoingMiddleFace, add_comm]
  exact cut.label_add_opposite_eq_one_iff_selected middle

end ExactFaceCut

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- On a locally cubic simple cycle, an exact cut supported by that cycle has
one constant label along the cycle's oriented face side. -/
theorem ExactFaceCut.label_eq_on_orientedCycle
    (graphData : SimpleGraphDartRotation.Data G)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    {A : Type*} {base : V} (cycle : G.Walk base base)
    (hcycle : cycle.IsCycle)
    (cut : ExactFaceCut graphData.toRotationSystem
      (fun edge : G.edgeSet => edge.1 ∈ cycle.edges) A)
    (hlocalCubic : ∀ dart ∈ cycle.darts,
      (graphData.toRotationSystem.dartsAt
        (graphData.toRotationSystem.vertOf dart)).card = 3)
    (target : G.Dart) (htarget : target ∈ cycle.darts) :
    cut.label (dartOrbitFace graphData.toRotationSystem
        (cycle.firstDart hcycle.not_nil)) =
      cut.label (dartOrbitFace graphData.toRotationSystem target) := by
  exact graphData.cycle_labels_eq_firstDart_dart_of_mem_darts_of_local_cubic
    hrotation cut.label cycle hcycle cut.separates hlocalCubic target htarget

end

end Mettapedia.GraphTheory.Embedding
