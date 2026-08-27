import Mettapedia.GraphTheory.FourColor.GoertzelV24SelectedDualCycleBond
import Mettapedia.GraphTheory.FourColor.GoertzelV24SelectedDualPathTransversalCycle

/-!
# Deletion components of a selected transversal pair

A separated pair of selected facial-dual transversals closes to a selected
dual cycle.  The cycle separator disconnects the primal graph after deleting
exactly the selected crossing support.  Generic finite-deletion theory then
chooses a component with nonempty boundary, and the selected-cycle bond
saturates that boundary to the entire support.

Only the faces visited by the closed dual walk must be two-sided.  No global
unique-shared-edge or global face-two-sidedness hypothesis is used.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SelectedDualPathTransversal

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24FramedLocalDualCycleBond
open GoertzelV24SelectedDualCycleBond
open GoertzelV24SelectedDualCycleSeparator
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace SeparatedAlignedSelectedDualTransversals

/- Reuse the graph-edge equality instance carried by the selected-cycle
separator and finite-deletion interfaces. -/
local instance selectedDeletionEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The finite primal separator is the literal union of the crossings selected
by the two source transversals. -/
def primalCutEdges
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) start finish) :
    Finset G.edgeSet :=
  pair.crossingSupport

/-- The selected closed cycle crosses exactly the finite source separator. -/
theorem selectedDualCycle_crossingEdges_eq_primalCutEdges
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) start finish) :
    pair.selectedDualCycle.crossingEdges = pair.primalCutEdges data := by
  exact pair.selectedDualCycle_crossingEdges

/-- The set-valued separator is the value image of the selected finite edge
carrier. -/
theorem selectedDualCycle_primalCut_eq_edgeFinsetValueSet_primalCutEdges
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) start finish) :
    pair.selectedDualCycle.primalCut =
      edgeFinsetValueSet (pair.primalCutEdges data) := by
  rw [pair.selectedDualCycle.primalCut_eq_edgeFinsetValueSet_crossingEdges,
    pair.selectedDualCycle_crossingEdges_eq_primalCutEdges data]

/-- The selected primal support disconnects a connected spherical graph. -/
theorem not_connected_deleteEdges_primalCutEdges
    (data : Data G)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (heuler : (Fintype.card V : Int) - Fintype.card G.edgeSet +
      Fintype.card (OrbitFace data.toRotationSystem) = 2)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) start finish) :
    ¬ (G.deleteEdges
      (edgeFinsetValueSet (pair.primalCutEdges data))).Connected := by
  rw [← pair.selectedDualCycle_primalCut_eq_edgeFinsetValueSet_primalCutEdges data]
  exact pair.selectedDualCycle.not_connected_deleteEdges_primalCut
    data hdual hconnected heuler

/-- A deletion component remains connected when viewed in the original
graph. -/
theorem connected_induce_primalCutComponent
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) start finish)
    (component : (G.deleteEdges
      (edgeFinsetValueSet (pair.primalCutEdges data))).ConnectedComponent) :
    (G.induce component.supp).Connected :=
  connected_induce_component (pair.primalCutEdges data) component

/-- The generic component boundary and the local side-crossing finset are the
same finite set. -/
theorem componentCrossingEdges_eq_localCrossingEdgeFinset
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) start finish)
    (component : (G.deleteEdges
      (edgeFinsetValueSet (pair.primalCutEdges data))).ConnectedComponent) :
    componentCrossingEdges (pair.primalCutEdges data) component =
      localCrossingEdgeFinset G (fun vertex => vertex ∈ component.supp) := by
  ext edge
  rw [mem_componentCrossingEdges_iff, mem_localCrossingEdgeFinset_iff]

/-- A selected transversal pair constructs a connected retained component
whose original-graph boundary is exactly its literal crossing support.

The only facial regularity required by the bond is local: every face visited
by the closed selected walk is two-sided. -/
theorem exists_primalCutComponent_exactBoundary_of_euler
    (data : Data G)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (heuler : (Fintype.card V : Int) - Fintype.card G.edgeSet +
      Fintype.card (OrbitFace data.toRotationSystem) = 2)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) start finish)
    (hsupportTwoSided : ∀ face,
      face ∈ pair.selectedDualCycle.walk.support → ∀ dart,
        dartOrbitFace data.toRotationSystem dart = face.1 →
          dartOrbitFace data.toRotationSystem dart ≠
            dartOrbitFace data.toRotationSystem
              (data.toRotationSystem.alpha dart)) :
    ∃ component : (G.deleteEdges
        (edgeFinsetValueSet (pair.primalCutEdges data))).ConnectedComponent,
      componentCrossingEdges (pair.primalCutEdges data) component =
        pair.primalCutEdges data := by
  have hdelete := pair.not_connected_deleteEdges_primalCutEdges
    data hdual hconnected heuler
  rcases exists_componentCrossingEdges_nonempty_of_not_connected
      hconnected (pair.primalCutEdges data) hdelete with
    ⟨component, hcomponentNonempty⟩
  let side : V → Prop := fun vertex => vertex ∈ component.supp
  have hcomponentLocal :
      componentCrossingEdges (pair.primalCutEdges data) component =
        localCrossingEdgeFinset G side := by
    exact pair.componentCrossingEdges_eq_localCrossingEdgeFinset data component
  have hsubset : localCrossingEdgeFinset G side ⊆
      pair.selectedDualCycle.crossingEdges := by
    rw [← hcomponentLocal,
      pair.selectedDualCycle_crossingEdges_eq_primalCutEdges data]
    exact componentCrossingEdges_subset_removed
      (pair.primalCutEdges data) component
  have hnonempty : (localCrossingEdgeFinset G side).Nonempty := by
    rw [← hcomponentLocal]
    exact hcomponentNonempty
  have hsaturated :=
    crossingEdgeFinset_eq_crossingEdges_of_isCycle_of_subset_of_supportTwoSided
      data pair.selectedDualCycle side hsubset hnonempty hsupportTwoSided
  refine ⟨component, ?_⟩
  calc
    componentCrossingEdges (pair.primalCutEdges data) component =
        localCrossingEdgeFinset G side := hcomponentLocal
    _ = pair.selectedDualCycle.crossingEdges := hsaturated
    _ = pair.primalCutEdges data :=
      pair.selectedDualCycle_crossingEdges_eq_primalCutEdges data

end SeparatedAlignedSelectedDualTransversals

end

end GoertzelV24SelectedDualPathTransversal

end Mettapedia.GraphTheory.FourColor
