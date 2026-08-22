import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphPortFactorContraction

/-!
# Factoring graph reachability through ports with an explicit residual

Not every finite interface position has to meet a persistent port.  A
component may be wholly internal to the finite interface exposed by one
letter.  This module retains that case rather than turning portal coverage
into a hypothesis.

The exact code below separates two possibilities: a component meets a named
port, or it is port-free.  Reachability on the finite interface is then the
disjunction of a port-free component bit and the usual port-factored move.
This is the support-sensitive analogue of a finite automaton state carrying
both visible and hidden components.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SimpleGraphPortResidualFactorContraction

open SimpleGraph

/-- Finite component data relative to a family of persistent ports. -/
structure BoundedPortResidualCode (Interface Port : Type*) where
  attaches : Interface → Port → Bool
  residualConnected : Interface → Interface → Bool

private def boundedPortResidualCodeEquiv (Interface Port : Type*) :
    BoundedPortResidualCode Interface Port ≃
      (Interface → Port → Bool) × (Interface → Interface → Bool) where
  toFun code := ⟨code.attaches, code.residualConnected⟩
  invFun data :=
    { attaches := data.1
      residualConnected := data.2 }
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance boundedPortResidualCodeDecidableEq
    {Interface Port : Type*} :
    DecidableEq (BoundedPortResidualCode Interface Port) :=
  Classical.decEq _

noncomputable instance boundedPortResidualCodeFintype
    {Interface Port : Type*} [Fintype Interface] [Fintype Port] :
    Fintype (BoundedPortResidualCode Interface Port) := by
  letI : Fintype (Interface → Port → Bool) := Fintype.ofFinite _
  letI : Fintype (Interface → Interface → Bool) := Fintype.ofFinite _
  exact Fintype.ofEquiv _
    (boundedPortResidualCodeEquiv Interface Port).symm

/-- Reachability reconstructed from either a port-free component or a move
through persistent ports. -/
def PortResidualFactoredReachability
    {Interface Port : Type*}
    (code : BoundedPortResidualCode Interface Port)
    (portConnected : Port → Port → Prop)
    (left right : Interface) : Prop :=
  code.residualConnected left right = true ∨
    ∃ leftPort rightPort,
      code.attaches left leftPort = true ∧
        portConnected leftPort rightPort ∧
        code.attaches right rightPort = true

/-- The canonical exact code extracted from a graph, a finite interface, and
named persistent ports.  Attachment is support-sensitive so an inactive
coordinate is not promoted to a portal merely by reflexivity.  The residual
bit records exactly the components that meet no supported port. -/
noncomputable def exactPortResidualCode
    {N Interface Port : Type*} (graph : SimpleGraph N)
    (interfaceVertex : Interface → N) (portVertex : Port → N) :
    BoundedPortResidualCode Interface Port where
  attaches interface port := by
    classical
    exact decide
      (interfaceVertex interface ∈ graph.support ∧
        portVertex port ∈ graph.support ∧
        graph.Reachable (interfaceVertex interface) (portVertex port))
  residualConnected left right := by
    classical
    exact decide
      (graph.Reachable (interfaceVertex left) (interfaceVertex right) ∧
        ∀ port,
          ¬ (interfaceVertex left ∈ graph.support ∧
            portVertex port ∈ graph.support ∧
            graph.Reachable (interfaceVertex left) (portVertex port)))

@[simp]
theorem exactPortResidualCode_attaches_eq_true_iff
    {N Interface Port : Type*} (graph : SimpleGraph N)
    (interfaceVertex : Interface → N) (portVertex : Port → N)
    (interface : Interface) (port : Port) :
    (exactPortResidualCode graph interfaceVertex portVertex).attaches
        interface port = true ↔
      interfaceVertex interface ∈ graph.support ∧
        portVertex port ∈ graph.support ∧
        graph.Reachable (interfaceVertex interface) (portVertex port) := by
  classical
  simp [exactPortResidualCode]

@[simp]
theorem exactPortResidualCode_residualConnected_eq_true_iff
    {N Interface Port : Type*} (graph : SimpleGraph N)
    (interfaceVertex : Interface → N) (portVertex : Port → N)
    (left right : Interface) :
    (exactPortResidualCode graph interfaceVertex portVertex).residualConnected
        left right = true ↔
      graph.Reachable (interfaceVertex left) (interfaceVertex right) ∧
        ∀ port,
          ¬ (interfaceVertex left ∈ graph.support ∧
            portVertex port ∈ graph.support ∧
            graph.Reachable (interfaceVertex left) (portVertex port)) := by
  classical
  simp [exactPortResidualCode]

/-- The canonical residual code and any exact supported port relation recover
graph reachability on the whole finite interface.  No portal-coverage premise
is required: a component that misses every port is represented by the
residual matrix. -/
theorem reachable_iff_exactPortResidualFactoredReachability
    {N Interface Port : Type*} (graph : SimpleGraph N)
    (interfaceVertex : Interface → N) (portVertex : Port → N)
    (portConnected : Port → Port → Prop)
    (hportSound : ∀ left right,
      portConnected left right →
        graph.Reachable (portVertex left) (portVertex right))
    (hportComplete : ∀ left right,
      portVertex left ∈ graph.support →
      portVertex right ∈ graph.support →
      graph.Reachable (portVertex left) (portVertex right) →
        portConnected left right)
    (left right : Interface) :
    graph.Reachable (interfaceVertex left) (interfaceVertex right) ↔
      PortResidualFactoredReachability
        (exactPortResidualCode graph interfaceVertex portVertex)
        portConnected left right := by
  constructor
  · intro hreachable
    by_cases hmeetsPort : ∃ port,
        (exactPortResidualCode graph interfaceVertex portVertex).attaches
          left port = true
    · rcases hmeetsPort with ⟨port, hleft⟩
      have hleftData :=
        (exactPortResidualCode_attaches_eq_true_iff graph interfaceVertex
          portVertex left port).1 hleft
      have hrightSupport : interfaceVertex right ∈ graph.support := by
        by_cases heq : interfaceVertex left = interfaceVertex right
        · simpa [← heq] using hleftData.1
        · exact SimpleGraph.mem_support_of_reachable
            (fun h => heq h.symm) hreachable.symm
      have hrightReach :
          graph.Reachable (interfaceVertex right) (portVertex port) :=
        hreachable.symm.trans hleftData.2.2
      have hright :
          (exactPortResidualCode graph interfaceVertex portVertex).attaches
              right port = true :=
        (exactPortResidualCode_attaches_eq_true_iff graph interfaceVertex
          portVertex right port).2
          ⟨hrightSupport, hleftData.2.1, hrightReach⟩
      apply Or.inr
      exact ⟨port, port, hleft,
        hportComplete port port hleftData.2.1 hleftData.2.1
          (SimpleGraph.Reachable.refl (G := graph) (portVertex port)),
        hright⟩
    · apply Or.inl
      apply (exactPortResidualCode_residualConnected_eq_true_iff graph
        interfaceVertex portVertex left right).2
      refine ⟨hreachable, ?_⟩
      intro port hdata
      exact hmeetsPort ⟨port,
        (exactPortResidualCode_attaches_eq_true_iff graph interfaceVertex
          portVertex left port).2 hdata⟩
  · intro hfactored
    rcases hfactored with hresidual |
      ⟨leftPort, rightPort, hleft, hports, hright⟩
    · exact
        ((exactPortResidualCode_residualConnected_eq_true_iff graph
          interfaceVertex portVertex left right).1 hresidual).1
    · have hleftData :=
        (exactPortResidualCode_attaches_eq_true_iff graph interfaceVertex
          portVertex left leftPort).1 hleft
      have hrightData :=
        (exactPortResidualCode_attaches_eq_true_iff graph interfaceVertex
          portVertex right rightPort).1 hright
      exact hleftData.2.2.trans
        ((hportSound leftPort rightPort hports).trans hrightData.2.2.symm)

end GoertzelV24SimpleGraphPortResidualFactorContraction

end Mettapedia.GraphTheory.FourColor
