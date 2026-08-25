import Mettapedia.GraphTheory.FourColor.GoertzelV24TrackedComponentDeletionCounterexample

/-!
# Finite component receipts stable under bounded support deletion

A boundary rebase changes a bounded family of interface coordinates.  The
ordinary supported residual code remembers the component partition before the
change, which is not enough to recover connectivity after a switch coordinate
is removed.  The counterexample in the imported module proves that this loss
is real.

This file gives the minimal generic repair.  A deletion-sensitive receipt
carries one Boolean mask on the finite interface and the exact
support-sensitive residual code of the graph restricted away from the selected
interface vertices.  The adequacy theorem retains port-free components, port
attachments, and activity bits.

The table is intentionally generic in the interface and port types.  The
source-specific Cell--rebase factor will instantiate it only on its bounded
tracked and facial carriers.  No reachable-set size or source transition is
asserted here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24DeletionSensitivePortResidualFactorContraction

open GoertzelV24SimpleGraphSupportedPortResidualFactorContraction
open SimpleGraph

/-- Restrict a graph to a predicate while retaining the original vertex type.
Vertices outside the predicate become inactive. -/
def supportRestriction {N : Type*} (graph : SimpleGraph N) (keep : N → Prop) :
    SimpleGraph N where
  Adj left right := graph.Adj left right ∧ keep left ∧ keep right
  symm := ⟨fun _ _ hadj => ⟨hadj.1.symm, hadj.2.2, hadj.2.1⟩⟩
  loopless := ⟨fun vertex hadj => graph.loopless.irrefl vertex hadj.1⟩

@[simp]
theorem supportRestriction_adj {N : Type*} (graph : SimpleGraph N)
    (keep : N → Prop) (left right : N) :
    (supportRestriction graph keep).Adj left right ↔
      graph.Adj left right ∧ keep left ∧ keep right :=
  Iff.rfl

@[simp]
theorem supportRestriction_true {N : Type*} (graph : SimpleGraph N) :
    supportRestriction graph (fun _ => True) = graph := by
  ext left right
  simp

/-- One exact residual receipt at one deletion mask on a finite interface.
`removed slot = true` means that the represented graph vertex is inactive.
The current transition carries only its own mask; it does not materialize the
exponential table of all masks. -/
structure BoundedDeletionSensitivePortResidualCode
    (Interface Port : Type*) where
  removed : Interface → Bool
  core : BoundedSupportedPortResidualCode Interface Port

noncomputable instance {Interface Port : Type*} :
    DecidableEq (BoundedDeletionSensitivePortResidualCode Interface Port) :=
  Classical.decEq _

private def boundedDeletionSensitivePortResidualCodeEquiv
    (Interface Port : Type*) :
    BoundedDeletionSensitivePortResidualCode Interface Port ≃
      (Interface → Bool) ×
        BoundedSupportedPortResidualCode Interface Port where
  toFun state := ⟨state.removed, state.core⟩
  invFun data := ⟨data.1, data.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance {Interface Port : Type*}
    [Fintype Interface] [Fintype Port] :
    Fintype (BoundedDeletionSensitivePortResidualCode Interface Port) := by
  letI : Fintype (Interface → Bool) := Fintype.ofFinite _
  exact Fintype.ofEquiv _
    (boundedDeletionSensitivePortResidualCodeEquiv Interface Port).symm

/-- A graph vertex survives a mask exactly when it is unequal to every
interface vertex selected for removal. -/
def survivesMask {N Interface : Type*}
    (interfaceVertex : Interface → N) (removed : Interface → Bool)
    (vertex : N) : Prop :=
  ∀ slot, removed slot = true → vertex ≠ interfaceVertex slot

/-- The graph after applying a finite interface-removal mask. -/
def restrictedByMask {N Interface : Type*} (graph : SimpleGraph N)
    (interfaceVertex : Interface → N) (removed : Interface → Bool) :
    SimpleGraph N :=
  supportRestriction graph (survivesMask interfaceVertex removed)

/-- Canonical deletion-sensitive receipt extracted from a graph. -/
noncomputable def exactDeletionSensitivePortResidualCode
    {N Interface Port : Type*} (graph : SimpleGraph N)
    (interfaceVertex : Interface → N) (portVertex : Port → N)
    (removed : Interface → Bool) :
    BoundedDeletionSensitivePortResidualCode Interface Port where
  removed := removed
  core := exactSupportedPortResidualCode
    (restrictedByMask graph interfaceVertex removed)
    interfaceVertex portVertex

/-- Interpret one deletion-mask row through an exact relation on the retained
persistent ports. -/
def DeletionSensitivePortResidualFactoredReachability
    {Interface Port : Type*}
    (state : BoundedDeletionSensitivePortResidualCode Interface Port)
    (portConnected : Port → Port → Prop) (left right : Interface) : Prop :=
  SupportedPortResidualFactoredReachability state.core
    portConnected left right

/-- Every deletion-mask row of the canonical table exactly reconstructs
reachability in the correspondingly restricted graph. -/
theorem reachable_iff_exactDeletionSensitivePortResidualFactoredReachability
    {N Interface Port : Type*} (graph : SimpleGraph N)
    (interfaceVertex : Interface → N) (portVertex : Port → N)
    (removed : Interface → Bool) (portConnected : Port → Port → Prop)
    (hportSound : ∀ left right,
      portConnected left right →
        (restrictedByMask graph interfaceVertex removed).Reachable
          (portVertex left) (portVertex right))
    (hportComplete : ∀ left right,
      portVertex left ∈
          (restrictedByMask graph interfaceVertex removed).support →
      portVertex right ∈
          (restrictedByMask graph interfaceVertex removed).support →
      (restrictedByMask graph interfaceVertex removed).Reachable
          (portVertex left) (portVertex right) →
        portConnected left right)
    (left right : Interface) :
    (restrictedByMask graph interfaceVertex removed).Reachable
        (interfaceVertex left) (interfaceVertex right) ↔
      DeletionSensitivePortResidualFactoredReachability
        (exactDeletionSensitivePortResidualCode graph interfaceVertex
          portVertex removed)
        portConnected left right := by
  exact reachable_iff_exactSupportedPortResidualFactoredReachability
    (restrictedByMask graph interfaceVertex removed) interfaceVertex portVertex
      portConnected hportSound hportComplete left right

/-- Interface activity in an exact mask row is literal support in the
restricted graph. -/
@[simp]
theorem exactDeletionSensitivePortResidualCode_interfaceActive_eq_true_iff
    {N Interface Port : Type*} (graph : SimpleGraph N)
    (interfaceVertex : Interface → N) (portVertex : Port → N)
    (removed : Interface → Bool) (slot : Interface) :
    ((exactDeletionSensitivePortResidualCode graph interfaceVertex portVertex
      removed).core).interfaceActive slot = true ↔
      interfaceVertex slot ∈
        (restrictedByMask graph interfaceVertex removed).support := by
  exact exactSupportedPortResidualCode_interfaceActive_eq_true_iff
    (restrictedByMask graph interfaceVertex removed) interfaceVertex portVertex
      slot

/-- The all-false row is exactly the ordinary pre-removal receipt. -/
@[simp]
theorem exactDeletionSensitivePortResidualCode_false :
    ∀ {N Interface Port : Type*} (graph : SimpleGraph N)
      (interfaceVertex : Interface → N) (portVertex : Port → N),
      (exactDeletionSensitivePortResidualCode graph interfaceVertex portVertex
        (fun _ => false)).core =
          exactSupportedPortResidualCode graph interfaceVertex portVertex := by
  intro N Interface Port graph interfaceVertex portVertex
  change exactSupportedPortResidualCode
      (supportRestriction graph (fun vertex =>
        ∀ slot, false = true → vertex ≠ interfaceVertex slot))
      interfaceVertex portVertex =
    exactSupportedPortResidualCode graph interfaceVertex portVertex
  rw [show supportRestriction graph
      (fun vertex => ∀ slot, false = true →
        vertex ≠ interfaceVertex slot) = graph by
    convert supportRestriction_true graph using 2
    funext vertex
    simp]

end GoertzelV24DeletionSensitivePortResidualFactorContraction

end Mettapedia.GraphTheory.FourColor
