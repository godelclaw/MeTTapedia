import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceDeletionComponentFactorGraphFree
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseStableTrackedState

/-!
# Project an exact exterior code to a supported residual interface

A deletion-stable exterior code remembers complete reachability on a bounded
carrier.  A serial finite-state recurrence observes only a smaller, padded
target interface together with named persistent ports.  This file gives the
graph-free projection between those two presentations.

The construction is exact whenever the full carrier contains the support of
the represented graph.  Activity is then recoverable from literal adjacency,
and the graph-free closure recovers connectivity.  No corridor geometry or
choice of carrier coordinates appears in the statement.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24InterfaceExteriorSupportedPortProjection

open GoertzelV24FramedTrail
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceDeletionComponentFactorGraphFree
open GoertzelV24SimpleGraphPortResidualFactorContraction
open GoertzelV24SimpleGraphSupportedPortResidualFactorContraction
open SimpleGraph

/-- Fieldwise extensionality for the supported residual structure. -/
theorem boundedSupportedPortResidualCode_ext
    {Interface Port : Type*}
    (left right : BoundedSupportedPortResidualCode Interface Port)
    (hattaches : left.attaches = right.attaches)
    (hresidual : left.residualConnected = right.residualConnected)
    (hinterface : left.interfaceActive = right.interfaceActive)
    (hport : left.portActive = right.portActive) : left = right := by
  cases left with
  | mk leftBase leftInterface leftPort =>
      cases right with
      | mk rightBase rightInterface rightPort =>
          cases leftBase with
          | mk leftAttaches leftResidual =>
              cases rightBase with
              | mk rightAttaches rightResidual =>
                  simp_all

/-- A Boolean exterior code is determined fieldwise by the propositions its
three rows recognize. -/
theorem boundedInterfaceExteriorCode_ext_iff
    {Interface : Type*}
    (left right : BoundedInterfaceExteriorCode Interface)
    (hvertex : ∀ first second,
      left.vertexEq first second = true ↔
        right.vertexEq first second = true)
    (hadj : ∀ first second,
      left.directAdj first second = true ↔
        right.directAdj first second = true)
    (hexterior : ∀ first second,
      left.exteriorConnected first second = true ↔
        right.exteriorConnected first second = true) : left = right := by
  cases left with
  | mk leftVertex leftAdj leftExterior =>
      cases right with
      | mk rightVertex rightAdj rightExterior =>
          have hv : leftVertex = rightVertex := by
            funext first second
            exact Bool.eq_iff_iff.mpr (hvertex first second)
          have ha : leftAdj = rightAdj := by
            funext first second
            exact Bool.eq_iff_iff.mpr (hadj first second)
          have he : leftExterior = rightExterior := by
            funext first second
            exact Bool.eq_iff_iff.mpr (hexterior first second)
          cases hv
          cases ha
          cases he
          rfl

/-- A coordinate is active when it has a literal adjacent coordinate in the
interface or an exterior excursion returning to itself.  The diagonal
exterior bit is load-bearing: it detects a coordinate whose only neighbour is
outside the represented interface. -/
noncomputable def interfaceExteriorActive
    {Interface : Type*} [Fintype Interface]
    (code : BoundedInterfaceExteriorCode Interface)
    (coordinate : Interface) : Bool := by
  classical
  exact decide
    ((∃ other, code.directAdj coordinate other = true) ∨
      code.exteriorConnected coordinate coordinate = true)

/-- Project a full exterior code to a padded target interface and named ports.
Missing target coordinates are explicitly inactive. -/
noncomputable def projectSupportedPortResidualCode
    {Full Stable Port : Type*} [Fintype Full] [Fintype Port]
    (code : BoundedInterfaceExteriorCode Full)
    (decode : Stable → Option Full)
    (portCoordinate : Port → Full) :
    BoundedSupportedPortResidualCode Stable Port where
  interfaceActive stable :=
    match decode stable with
    | some coordinate => interfaceExteriorActive code coordinate
    | none => false
  portActive port := interfaceExteriorActive code (portCoordinate port)
  attaches stable port := by
    classical
    exact match decode stable with
      | some coordinate => decide
          (interfaceExteriorActive code coordinate = true ∧
            interfaceExteriorActive code (portCoordinate port) = true ∧
            InterfaceExteriorClosure code coordinate (portCoordinate port))
      | none => false
  residualConnected left right := by
    classical
    exact match decode left, decode right with
      | some leftCoordinate, some rightCoordinate => decide
          (InterfaceExteriorClosure code leftCoordinate rightCoordinate ∧
            ∀ port,
              ¬ (interfaceExteriorActive code leftCoordinate = true ∧
                interfaceExteriorActive code (portCoordinate port) = true ∧
                InterfaceExteriorClosure code leftCoordinate
                  (portCoordinate port)))
      | _, _ => false

@[simp] theorem projectSupportedPortResidualCode_interfaceActive_of_decode
    {Full Stable Port : Type*} [Fintype Full] [Fintype Port]
    (code : BoundedInterfaceExteriorCode Full)
    (decode : Stable → Option Full) (portCoordinate : Port → Full)
    (stable : Stable) (coordinate : Full)
    (hdecode : decode stable = some coordinate) :
    (projectSupportedPortResidualCode code decode portCoordinate
      ).interfaceActive stable = interfaceExteriorActive code coordinate := by
  simp [projectSupportedPortResidualCode, hdecode]

@[simp] theorem projectSupportedPortResidualCode_fields_of_decode_none
    {Full Stable Port : Type*} [Fintype Full] [Fintype Port]
    (code : BoundedInterfaceExteriorCode Full)
    (decode : Stable → Option Full) (portCoordinate : Port → Full)
    (stable : Stable) (hdecode : decode stable = none) :
    (projectSupportedPortResidualCode code decode portCoordinate
        ).interfaceActive stable = false ∧
      (∀ port, (projectSupportedPortResidualCode code decode portCoordinate
          ).attaches stable port = false) ∧
      (∀ other,
        (projectSupportedPortResidualCode code decode portCoordinate
            ).residualConnected stable other = false ∧
          (projectSupportedPortResidualCode code decode portCoordinate
            ).residualConnected other stable = false) := by
  simp [projectSupportedPortResidualCode, hdecode]

/-- On an exact carrier, the direct-adjacency row together with the diagonal
exterior row recovers graph support exactly.  No support-saturation hypothesis
is needed. -/
theorem interfaceExteriorActive_exact_eq_true_iff
    {N Interface : Type*} [Fintype Interface]
    (graph : SimpleGraph N) (interfaceVertex : Interface → N)
    (coordinate : Interface) :
    interfaceExteriorActive
        (exactInterfaceExteriorCode graph interfaceVertex) coordinate = true ↔
      interfaceVertex coordinate ∈ graph.support := by
  classical
  simp only [interfaceExteriorActive, decide_eq_true_eq]
  constructor
  · rintro (⟨other, hadj⟩ | hexterior)
    · have hadj' : graph.Adj (interfaceVertex coordinate)
          (interfaceVertex other) := by
        simpa [exactInterfaceExteriorCode] using hadj
      exact (SimpleGraph.mem_support graph).2 ⟨interfaceVertex other, hadj'⟩
    · simp only [exactInterfaceExteriorCode, decide_eq_true_eq] at hexterior
      rcases hexterior with
        ⟨entry, _exit, _hentryOutside, _hexitOutside, hentry, _hreach,
          _hexit⟩
      exact (SimpleGraph.mem_support graph).2 ⟨entry, hentry⟩
  · intro hcoordinate
    rcases (SimpleGraph.mem_support graph).1 hcoordinate with
      ⟨neighbor, hadj⟩
    by_cases hinside : ∃ other, interfaceVertex other = neighbor
    · left
      rcases hinside with ⟨other, rfl⟩
      refine ⟨other, ?_⟩
      simpa [exactInterfaceExteriorCode] using hadj
    · right
      simp only [exactInterfaceExteriorCode, decide_eq_true_eq]
      have houtside : OutsideInterface interfaceVertex neighbor := by
        intro other heq
        exact hinside ⟨other, heq.symm⟩
      exact ⟨neighbor, neighbor, houtside, houtside, hadj,
        SimpleGraph.Reachable.rfl, hadj.symm⟩

/-- Exact semantics of a projected attachment bit. -/
theorem projectSupportedPortResidualCode_exact_attaches_eq_true_iff
    {N Full Stable Port : Type*} [Fintype Full] [Fintype Port]
    (graph : SimpleGraph N) (fullVertex : Full → N)
    (hinjective : Function.Injective fullVertex)
    (decode : Stable → Option Full) (portCoordinate : Port → Full)
    (stable : Stable) (coordinate : Full) (port : Port)
    (hdecode : decode stable = some coordinate) :
    (projectSupportedPortResidualCode
        (exactInterfaceExteriorCode graph fullVertex) decode portCoordinate
      ).attaches stable port = true ↔
      fullVertex coordinate ∈ graph.support ∧
        fullVertex (portCoordinate port) ∈ graph.support ∧
        graph.Reachable (fullVertex coordinate)
          (fullVertex (portCoordinate port)) := by
  classical
  simp only [projectSupportedPortResidualCode, hdecode, decide_eq_true_eq]
  rw [interfaceExteriorActive_exact_eq_true_iff graph fullVertex,
    interfaceExteriorActive_exact_eq_true_iff graph fullVertex,
    exactInterfaceExteriorCode_closure_iff_of_injective graph fullVertex
      hinjective]

/-- Exact semantics of a projected port-free residual-component bit. -/
theorem projectSupportedPortResidualCode_exact_residualConnected_eq_true_iff
    {N Full Stable Port : Type*} [Fintype Full] [Fintype Port]
    (graph : SimpleGraph N) (fullVertex : Full → N)
    (hinjective : Function.Injective fullVertex)
    (decode : Stable → Option Full) (portCoordinate : Port → Full)
    (left right : Stable) (leftCoordinate rightCoordinate : Full)
    (hleft : decode left = some leftCoordinate)
    (hright : decode right = some rightCoordinate) :
    (projectSupportedPortResidualCode
        (exactInterfaceExteriorCode graph fullVertex) decode portCoordinate
      ).residualConnected left right = true ↔
      graph.Reachable (fullVertex leftCoordinate)
          (fullVertex rightCoordinate) ∧
        ∀ port,
          ¬ (fullVertex leftCoordinate ∈ graph.support ∧
            fullVertex (portCoordinate port) ∈ graph.support ∧
            graph.Reachable (fullVertex leftCoordinate)
              (fullVertex (portCoordinate port))) := by
  classical
  simp only [projectSupportedPortResidualCode, hleft, hright,
    decide_eq_true_eq]
  rw [exactInterfaceExteriorCode_closure_iff_of_injective graph fullVertex
      hinjective]
  constructor
  · rintro ⟨hreach, hports⟩
    refine ⟨hreach, fun port hdata => hports port ?_⟩
    simpa only [
      interfaceExteriorActive_exact_eq_true_iff graph fullVertex,
      exactInterfaceExteriorCode_closure_iff_of_injective graph fullVertex
        hinjective] using hdata
  · rintro ⟨hreach, hports⟩
    refine ⟨hreach, fun port hdata => hports port ?_⟩
    simpa only [
      interfaceExteriorActive_exact_eq_true_iff graph fullVertex,
      exactInterfaceExteriorCode_closure_iff_of_injective graph fullVertex
        hinjective] using hdata

/-- Projecting an exact target-interface code is literally the canonical
supported residual state, padded along the same partial decoder. -/
theorem projectSupportedPortResidualCode_exact_eq_pad
    {N Interface Stable Port : Type*} [Fintype Interface] [Fintype Port]
    (graph : SimpleGraph N) (interfaceVertex : Interface → N)
    (hinjective : Function.Injective interfaceVertex)
    (decode : Stable → Option Interface)
    (portCoordinate : Port → Interface) :
    projectSupportedPortResidualCode
        (exactInterfaceExteriorCode graph interfaceVertex) decode
          portCoordinate =
      padSupportedPortResidualCode decode
        (exactSupportedPortResidualCode graph interfaceVertex
          (fun port => interfaceVertex (portCoordinate port))) := by
  classical
  apply boundedSupportedPortResidualCode_ext
  · funext stable port
    cases hdecode : decode stable with
    | none => simp [projectSupportedPortResidualCode,
        padSupportedPortResidualCode, hdecode]
    | some coordinate =>
        apply Bool.eq_iff_iff.mpr
        rw [projectSupportedPortResidualCode_exact_attaches_eq_true_iff graph
          interfaceVertex hinjective decode portCoordinate stable coordinate
            port hdecode]
        simp [padSupportedPortResidualCode, hdecode]
  · funext left right
    cases hleft : decode left with
    | none => simp [projectSupportedPortResidualCode,
        padSupportedPortResidualCode, hleft]
    | some leftCoordinate =>
        cases hright : decode right with
        | none => simp [projectSupportedPortResidualCode,
            padSupportedPortResidualCode, hleft, hright]
        | some rightCoordinate =>
            apply Bool.eq_iff_iff.mpr
            rw [
              projectSupportedPortResidualCode_exact_residualConnected_eq_true_iff
                graph interfaceVertex hinjective decode portCoordinate left
                  right leftCoordinate rightCoordinate hleft hright]
            simp [padSupportedPortResidualCode, hleft, hright]
  · funext stable
    cases hdecode : decode stable with
    | none => simp [projectSupportedPortResidualCode,
        padSupportedPortResidualCode, hdecode]
    | some coordinate =>
        apply Bool.eq_iff_iff.mpr
        rw [projectSupportedPortResidualCode_interfaceActive_of_decode _ _ _ _
          _ hdecode]
        rw [interfaceExteriorActive_exact_eq_true_iff graph interfaceVertex]
        simp [padSupportedPortResidualCode, hdecode]
  · funext port
    apply Bool.eq_iff_iff.mpr
    simp only [projectSupportedPortResidualCode,
      padSupportedPortResidualCode]
    rw [interfaceExteriorActive_exact_eq_true_iff graph interfaceVertex]
    simp

/-- Canonical supported residual states are invariant under an equivalence of
their finite interface coordinates, including after padding through a partial
stable decoder. -/
theorem pad_exactSupportedPortResidualCode_equiv
    {N Interface Coordinate Stable Port : Type*}
    (graph : SimpleGraph N) (vertex : Interface → N)
    (coordinate : Interface ≃ Coordinate)
    (decode : Stable → Option Interface) (port : Port → Interface) :
    padSupportedPortResidualCode
        (fun stable => (decode stable).map coordinate)
        (exactSupportedPortResidualCode graph
          (fun slot => vertex (coordinate.symm slot))
          (fun named => vertex (port named))) =
      padSupportedPortResidualCode decode
        (exactSupportedPortResidualCode graph vertex
          (fun named => vertex (port named))) := by
  classical
  apply boundedSupportedPortResidualCode_ext
  · funext stable named
    cases hdecode : decode stable with
    | none => simp [padSupportedPortResidualCode, hdecode]
    | some interface =>
        simp [padSupportedPortResidualCode, exactSupportedPortResidualCode,
          exactPortResidualCode, hdecode]
  · funext left right
    cases hleft : decode left with
    | none => simp [padSupportedPortResidualCode, hleft]
    | some leftInterface =>
        cases hright : decode right with
        | none => simp [padSupportedPortResidualCode, hleft, hright]
        | some rightInterface =>
            simp [padSupportedPortResidualCode, exactSupportedPortResidualCode,
              exactPortResidualCode, hleft, hright]
  · funext stable
    cases hdecode : decode stable with
    | none => simp [padSupportedPortResidualCode, hdecode]
    | some interface =>
        simp [padSupportedPortResidualCode, exactSupportedPortResidualCode,
          hdecode]
  · rfl

end GoertzelV24InterfaceExteriorSupportedPortProjection

end Mettapedia.GraphTheory.FourColor
