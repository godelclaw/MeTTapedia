import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceDeletionComponentFactorUpdate

/-!
# Updating an interface-exterior code by an injective deletion mask

On an injectively represented finite interface, deleting selected interface
vertices has a row-wise effect on the exact exterior code.  Equality of the
represented vertices is unchanged.  Literal adjacency and attachment to one
common exterior component survive exactly when both endpoint coordinates are
retained.

This is the deletion half of a bounded local recurrence.  Together with
`addInterfaceAdjacency_exact_code_eq`, it permits a transition to delete a
finite switch and then add a graph supported entirely on the same interface,
without materializing the resulting ambient graph or its component table.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24InterfaceDeletionComponentFactorMaskUpdate

open GoertzelV24DeletionSensitivePortResidualFactorContraction
open GoertzelV24InterfaceDeletionComponentFactor
open SimpleGraph

/-- Zero the two support-sensitive rows at every removed endpoint.  The
equality row remains total because graph reachability is reflexive even at an
inactive named vertex. -/
def maskInterfaceExteriorCode {Interface : Type*}
    (code : BoundedInterfaceExteriorCode Interface)
    (removed : Interface → Bool) :
    BoundedInterfaceExteriorCode Interface where
  vertexEq := code.vertexEq
  directAdj left right :=
    (!removed left) && (!removed right) && code.directAdj left right
  exteriorConnected left right :=
    (!removed left) && (!removed right) && code.exteriorConnected left right

/-- At an injective interface, a named vertex survives exactly when its one
coordinate is not selected. -/
theorem survivesMask_interfaceVertex_iff
    {N Interface : Type*} (interfaceVertex : Interface → N)
    (hinjective : Function.Injective interfaceVertex)
    (removed : Interface → Bool) (slot : Interface) :
    survivesMask interfaceVertex removed (interfaceVertex slot) ↔
      removed slot = false := by
  constructor
  · intro hsurvives
    cases hremoved : removed slot with
    | false => rfl
    | true => exact (hsurvives slot hremoved rfl).elim
  · intro hretained other hremoved heq
    have hslot : other = slot := hinjective heq.symm
    subst other
    simp_all

/-- Every vertex strictly outside the represented interface survives every
interface deletion mask. -/
theorem survivesMask_of_outsideInterface
    {N Interface : Type*} (interfaceVertex : Interface → N)
    (removed : Interface → Bool) {vertex : N}
    (houtside : OutsideInterface interfaceVertex vertex) :
    survivesMask interfaceVertex removed vertex := by
  intro slot _
  exact houtside slot

/-- Deleting vertices represented on the interface does not alter the graph
induced strictly outside that interface. -/
theorem exteriorGraph_restrictedByMask_eq
    {N Interface : Type*} (graph : SimpleGraph N)
    (interfaceVertex : Interface → N) (removed : Interface → Bool) :
    exteriorGraph (restrictedByMask graph interfaceVertex removed)
        interfaceVertex =
      exteriorGraph graph interfaceVertex := by
  ext left right
  simp only [exteriorGraph, restrictedByMask, supportRestriction_adj]
  constructor
  · rintro ⟨⟨hadj, _hleftSurvives, _hrightSurvives⟩,
      hleftOutside, hrightOutside⟩
    exact ⟨hadj, hleftOutside, hrightOutside⟩
  · rintro ⟨hadj, hleftOutside, hrightOutside⟩
    exact ⟨⟨hadj,
      survivesMask_of_outsideInterface interfaceVertex removed hleftOutside,
      survivesMask_of_outsideInterface interfaceVertex removed hrightOutside⟩,
      hleftOutside, hrightOutside⟩

/-- An interface-to-exterior adjacency survives precisely when its interface
endpoint is retained. -/
theorem restrictedByMask_adj_interface_outside_iff
    {N Interface : Type*} (graph : SimpleGraph N)
    (interfaceVertex : Interface → N)
    (hinjective : Function.Injective interfaceVertex)
    (removed : Interface → Bool) (slot : Interface) {outside : N}
    (houtside : OutsideInterface interfaceVertex outside) :
    (restrictedByMask graph interfaceVertex removed).Adj
        (interfaceVertex slot) outside ↔
      removed slot = false ∧ graph.Adj (interfaceVertex slot) outside := by
  rw [restrictedByMask, supportRestriction_adj]
  rw [survivesMask_interfaceVertex_iff interfaceVertex hinjective removed slot]
  simp only [survivesMask_of_outsideInterface interfaceVertex removed houtside]
  tauto

/-- Symmetric exterior-to-interface form. -/
theorem restrictedByMask_adj_outside_interface_iff
    {N Interface : Type*} (graph : SimpleGraph N)
    (interfaceVertex : Interface → N)
    (hinjective : Function.Injective interfaceVertex)
    (removed : Interface → Bool) {outside : N}
    (houtside : OutsideInterface interfaceVertex outside) (slot : Interface) :
    (restrictedByMask graph interfaceVertex removed).Adj outside
        (interfaceVertex slot) ↔
      removed slot = false ∧ graph.Adj outside (interfaceVertex slot) := by
  rw [restrictedByMask, supportRestriction_adj]
  rw [survivesMask_interfaceVertex_iff interfaceVertex hinjective removed slot]
  simp only [survivesMask_of_outsideInterface interfaceVertex removed houtside]
  tauto

/-- The exterior-attachment proposition is zeroed exactly at removed
endpoints; its strictly exterior middle is unchanged. -/
theorem exists_exteriorConnection_restrictedByMask_iff
    {N Interface : Type*} (graph : SimpleGraph N)
    (interfaceVertex : Interface → N)
    (hinjective : Function.Injective interfaceVertex)
    (removed : Interface → Bool) (left right : Interface) :
    (∃ entry exit : N,
        OutsideInterface interfaceVertex entry ∧
        OutsideInterface interfaceVertex exit ∧
        (restrictedByMask graph interfaceVertex removed).Adj
          (interfaceVertex left) entry ∧
        (exteriorGraph (restrictedByMask graph interfaceVertex removed)
          interfaceVertex).Reachable entry exit ∧
        (restrictedByMask graph interfaceVertex removed).Adj exit
          (interfaceVertex right)) ↔
      removed left = false ∧ removed right = false ∧
        ∃ entry exit : N,
          OutsideInterface interfaceVertex entry ∧
          OutsideInterface interfaceVertex exit ∧
          graph.Adj (interfaceVertex left) entry ∧
          (exteriorGraph graph interfaceVertex).Reachable entry exit ∧
          graph.Adj exit (interfaceVertex right) := by
  rw [exteriorGraph_restrictedByMask_eq graph interfaceVertex removed]
  constructor
  · rintro ⟨entry, exit, hentryOutside, hexitOutside, hentry, hreach, hexit⟩
    have hentry' :=
      (restrictedByMask_adj_interface_outside_iff graph interfaceVertex
        hinjective removed left hentryOutside).1 hentry
    have hexit' :=
      (restrictedByMask_adj_outside_interface_iff graph interfaceVertex
        hinjective removed hexitOutside right).1 hexit
    exact ⟨hentry'.1, hexit'.1, entry, exit, hentryOutside, hexitOutside,
      hentry'.2, hreach, hexit'.2⟩
  · rintro ⟨hleft, hright, entry, exit, hentryOutside, hexitOutside,
      hentry, hreach, hexit⟩
    refine ⟨entry, exit, hentryOutside, hexitOutside, ?_, hreach, ?_⟩
    · exact (restrictedByMask_adj_interface_outside_iff graph interfaceVertex
        hinjective removed left hentryOutside).2 ⟨hleft, hentry⟩
    · exact (restrictedByMask_adj_outside_interface_iff graph interfaceVertex
        hinjective removed hexitOutside right).2 ⟨hright, hexit⟩

/-- Crown row-wise exactness theorem for an injective interface deletion.
The result is equality of three-row codes, so a subsequent local update or
interface contraction may inspect the rows independently. -/
theorem maskInterfaceExteriorCode_exact_code_eq
    {N Interface : Type*} (graph : SimpleGraph N)
    (interfaceVertex : Interface → N)
    (hinjective : Function.Injective interfaceVertex)
    (removed : Interface → Bool) :
    maskInterfaceExteriorCode
        (exactInterfaceExteriorCode graph interfaceVertex) removed =
      exactInterfaceExteriorCode
        (restrictedByMask graph interfaceVertex removed) interfaceVertex := by
  classical
  unfold maskInterfaceExteriorCode exactInterfaceExteriorCode
  congr 1
  · funext left right
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      restrictedByMask, supportRestriction_adj]
    rw [survivesMask_interfaceVertex_iff interfaceVertex hinjective removed left,
      survivesMask_interfaceVertex_iff interfaceVertex hinjective removed right]
    tauto
  · funext left right
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
    rw [exists_exteriorConnection_restrictedByMask_iff graph
      interfaceVertex hinjective removed left right]
    constructor
    · rintro ⟨⟨hleft, hright⟩, hwitness⟩
      exact ⟨hleft, hright, hwitness⟩
    · rintro ⟨hleft, hright, hwitness⟩
      exact ⟨⟨hleft, hright⟩, hwitness⟩

end GoertzelV24InterfaceDeletionComponentFactorMaskUpdate

end Mettapedia.GraphTheory.FourColor
