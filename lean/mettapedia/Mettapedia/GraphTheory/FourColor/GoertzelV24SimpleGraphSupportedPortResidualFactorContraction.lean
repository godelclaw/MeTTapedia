import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphPortResidualFactorContraction

/-!
# Support-sensitive residual factorization through finite ports

`BoundedPortResidualCode` records the component relation seen from a finite
interface, separating components which meet persistent ports from components
which do not.  A recurrence needs one more bit of information: graph
reachability is reflexive even at an isolated vertex, so its diagonal does not
say whether that coordinate belongs to the graph support.

This file adds the missing activity tables without changing the component
factorization.  The canonical code extracted from a graph records support of
every interface coordinate and every persistent port exactly, while its
underlying residual code remains the existing exact one.  This is finite state
and is the support-sensitive input required by a later union/letter update; it
does not itself construct such an update.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SimpleGraphSupportedPortResidualFactorContraction

open GoertzelV24SimpleGraphPortResidualFactorContraction
open SimpleGraph

/-- Residual component data together with exact support activity on the
finite interface and its persistent ports. -/
structure BoundedSupportedPortResidualCode (Interface Port : Type*)
    extends BoundedPortResidualCode Interface Port where
  interfaceActive : Interface → Bool
  portActive : Port → Bool

private def boundedSupportedPortResidualCodeEquiv
    (Interface Port : Type*) :
    BoundedSupportedPortResidualCode Interface Port ≃
      BoundedPortResidualCode Interface Port ×
        (Interface → Bool) × (Port → Bool) where
  toFun code :=
    ⟨code.toBoundedPortResidualCode, code.interfaceActive, code.portActive⟩
  invFun data :=
    { toBoundedPortResidualCode := data.1
      interfaceActive := data.2.1
      portActive := data.2.2 }
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance boundedSupportedPortResidualCodeDecidableEq
    {Interface Port : Type*} :
    DecidableEq (BoundedSupportedPortResidualCode Interface Port) :=
  Classical.decEq _

noncomputable instance boundedSupportedPortResidualCodeFintype
    {Interface Port : Type*} [Fintype Interface] [Fintype Port] :
    Fintype (BoundedSupportedPortResidualCode Interface Port) := by
  letI : Fintype (Interface → Bool) := Fintype.ofFinite _
  letI : Fintype (Port → Bool) := Fintype.ofFinite _
  exact Fintype.ofEquiv _
    (boundedSupportedPortResidualCodeEquiv Interface Port).symm

/-- Interpret the component part of a supported residual code.  Activity is
kept orthogonal because it controls later attachments, not reachability
itself. -/
def SupportedPortResidualFactoredReachability
    {Interface Port : Type*}
    (code : BoundedSupportedPortResidualCode Interface Port)
    (portConnected : Port → Port → Prop)
    (left right : Interface) : Prop :=
  PortResidualFactoredReachability code.toBoundedPortResidualCode
    portConnected left right

/-- Canonical support-sensitive residual data extracted from a graph. -/
noncomputable def exactSupportedPortResidualCode
    {N Interface Port : Type*} (graph : SimpleGraph N)
    (interfaceVertex : Interface → N) (portVertex : Port → N) :
    BoundedSupportedPortResidualCode Interface Port where
  toBoundedPortResidualCode :=
    exactPortResidualCode graph interfaceVertex portVertex
  interfaceActive interface := by
    classical
    exact decide (interfaceVertex interface ∈ graph.support)
  portActive port := by
    classical
    exact decide (portVertex port ∈ graph.support)

@[simp]
theorem exactSupportedPortResidualCode_toBoundedPortResidualCode
    {N Interface Port : Type*} (graph : SimpleGraph N)
    (interfaceVertex : Interface → N) (portVertex : Port → N) :
    (exactSupportedPortResidualCode graph interfaceVertex portVertex
      ).toBoundedPortResidualCode =
      exactPortResidualCode graph interfaceVertex portVertex :=
  rfl

@[simp]
theorem exactSupportedPortResidualCode_interfaceActive_eq_true_iff
    {N Interface Port : Type*} (graph : SimpleGraph N)
    (interfaceVertex : Interface → N) (portVertex : Port → N)
    (interface : Interface) :
    (exactSupportedPortResidualCode graph interfaceVertex portVertex
      ).interfaceActive interface = true ↔
      interfaceVertex interface ∈ graph.support := by
  classical
  simp [exactSupportedPortResidualCode]

@[simp]
theorem exactSupportedPortResidualCode_portActive_eq_true_iff
    {N Interface Port : Type*} (graph : SimpleGraph N)
    (interfaceVertex : Interface → N) (portVertex : Port → N)
    (port : Port) :
    (exactSupportedPortResidualCode graph interfaceVertex portVertex
      ).portActive port = true ↔
      portVertex port ∈ graph.support := by
  classical
  simp [exactSupportedPortResidualCode]

/-- The supported code retains the exact residual component factorization.
The activity bits add information; they do not weaken or strengthen the
existing reachability theorem. -/
theorem reachable_iff_exactSupportedPortResidualFactoredReachability
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
      SupportedPortResidualFactoredReachability
        (exactSupportedPortResidualCode graph interfaceVertex portVertex)
        portConnected left right := by
  exact reachable_iff_exactPortResidualFactoredReachability graph
    interfaceVertex portVertex portConnected hportSound hportComplete
      left right

end GoertzelV24SimpleGraphSupportedPortResidualFactorContraction

end Mettapedia.GraphTheory.FourColor
