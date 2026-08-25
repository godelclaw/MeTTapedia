import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceDeletionComponentFactor

/-!
# Updating a deletion-stable interface factor by an internal graph

If an added graph is supported entirely on the bounded interface, it cannot
change any component strictly outside that interface.  It can only add literal
adjacency between interface coordinates.  Consequently the deletion-stable
code has a very small executable update: Boolean-OR the direct-adjacency table
and leave the exterior-component table unchanged.

This is the generic recurrence used when the prefix-independent Cell and seam
graphs are adjoined to a cumulative prefix state.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24InterfaceDeletionComponentFactorUpdate

open GoertzelV24InterfaceDeletionComponentFactor
open SimpleGraph

/-- Add one finite interface-adjacency relation to a deletion-stable code. -/
def addInterfaceAdjacency {Interface : Type*}
    (code : BoundedInterfaceExteriorCode Interface)
    (adjacency : Interface → Interface → Bool) :
    BoundedInterfaceExteriorCode Interface where
  vertexEq := code.vertexEq
  directAdj left right := code.directAdj left right || adjacency left right
  exteriorConnected := code.exteriorConnected

private theorem extra_not_adj_interface_outside
    {N Interface : Type*} (extra : SimpleGraph N)
    (interfaceVertex : Interface → N)
    (hsupport : extra.support ⊆ Set.range interfaceVertex)
    (slot : Interface) {outside : N}
    (houtside : OutsideInterface interfaceVertex outside) :
    ¬ extra.Adj (interfaceVertex slot) outside := by
  intro hadj
  have hsupported : outside ∈ extra.support := ⟨interfaceVertex slot, hadj.symm⟩
  rcases hsupport hsupported with ⟨otherSlot, hotherSlot⟩
  exact houtside otherSlot hotherSlot.symm

private theorem extra_not_adj_outside_interface
    {N Interface : Type*} (extra : SimpleGraph N)
    (interfaceVertex : Interface → N)
    (hsupport : extra.support ⊆ Set.range interfaceVertex)
    {outside : N} (houtside : OutsideInterface interfaceVertex outside)
    (slot : Interface) :
    ¬ extra.Adj outside (interfaceVertex slot) := by
  intro hadj
  have hsupported : outside ∈ extra.support := ⟨interfaceVertex slot, hadj⟩
  rcases hsupport hsupported with ⟨otherSlot, hotherSlot⟩
  exact houtside otherSlot hotherSlot.symm

/-- An interface-to-exterior edge of a union cannot come from a factor whose
whole support lies on the interface. -/
theorem sup_adj_interface_outside_iff_left
    {N Interface : Type*} (base extra : SimpleGraph N)
    (interfaceVertex : Interface → N)
    (hsupport : extra.support ⊆ Set.range interfaceVertex)
    (slot : Interface) {outside : N}
    (houtside : OutsideInterface interfaceVertex outside) :
    (base ⊔ extra).Adj (interfaceVertex slot) outside ↔
      base.Adj (interfaceVertex slot) outside := by
  rw [SimpleGraph.sup_adj]
  exact or_iff_left (extra_not_adj_interface_outside extra interfaceVertex
    hsupport slot houtside)

/-- The symmetric exterior-to-interface edge form. -/
theorem sup_adj_outside_interface_iff_left
    {N Interface : Type*} (base extra : SimpleGraph N)
    (interfaceVertex : Interface → N)
    (hsupport : extra.support ⊆ Set.range interfaceVertex)
    {outside : N} (houtside : OutsideInterface interfaceVertex outside)
    (slot : Interface) :
    (base ⊔ extra).Adj outside (interfaceVertex slot) ↔
      base.Adj outside (interfaceVertex slot) := by
  rw [SimpleGraph.sup_adj]
  exact or_iff_left (extra_not_adj_outside_interface extra interfaceVertex
    hsupport houtside slot)

/-- Adding a graph supported on the interface leaves the strictly exterior
graph definitionally unchanged up to extensional equality. -/
theorem exteriorGraph_sup_eq_left_of_right_support_subset_interface
    {N Interface : Type*} (base extra : SimpleGraph N)
    (interfaceVertex : Interface → N)
    (hsupport : extra.support ⊆ Set.range interfaceVertex) :
    exteriorGraph (base ⊔ extra) interfaceVertex =
      exteriorGraph base interfaceVertex := by
  ext left right
  simp only [exteriorGraph,
    GoertzelV24DeletionSensitivePortResidualFactorContraction.supportRestriction_adj,
    SimpleGraph.sup_adj]
  constructor
  · rintro ⟨hbase | hextra, hleftOutside, hrightOutside⟩
    · exact ⟨hbase, hleftOutside, hrightOutside⟩
    · have hleftSupport : left ∈ extra.support := ⟨right, hextra⟩
      rcases hsupport hleftSupport with ⟨slot, hslot⟩
      exact (hleftOutside slot hslot.symm).elim
  · rintro ⟨hbase, hleftOutside, hrightOutside⟩
    exact ⟨Or.inl hbase, hleftOutside, hrightOutside⟩

/-- The full exterior-attachment proposition is unchanged by an internal
interface graph. -/
theorem exists_exteriorConnection_sup_iff_left
    {N Interface : Type*} (base extra : SimpleGraph N)
    (interfaceVertex : Interface → N)
    (hsupport : extra.support ⊆ Set.range interfaceVertex)
    (left right : Interface) :
    (∃ entry exit : N,
        OutsideInterface interfaceVertex entry ∧
        OutsideInterface interfaceVertex exit ∧
        (base ⊔ extra).Adj (interfaceVertex left) entry ∧
        (exteriorGraph (base ⊔ extra) interfaceVertex).Reachable entry exit ∧
        (base ⊔ extra).Adj exit (interfaceVertex right)) ↔
      ∃ entry exit : N,
        OutsideInterface interfaceVertex entry ∧
        OutsideInterface interfaceVertex exit ∧
        base.Adj (interfaceVertex left) entry ∧
        (exteriorGraph base interfaceVertex).Reachable entry exit ∧
        base.Adj exit (interfaceVertex right) := by
  rw [exteriorGraph_sup_eq_left_of_right_support_subset_interface base extra
    interfaceVertex hsupport]
  constructor
  · rintro ⟨entry, exit, hentryOutside, hexitOutside, hentry, hreach, hexit⟩
    exact ⟨entry, exit, hentryOutside, hexitOutside,
      (sup_adj_interface_outside_iff_left base extra interfaceVertex hsupport
        left hentryOutside).1 hentry,
      hreach,
      (sup_adj_outside_interface_iff_left base extra interfaceVertex hsupport
        hexitOutside right).1 hexit⟩
  · rintro ⟨entry, exit, hentryOutside, hexitOutside, hentry, hreach, hexit⟩
    exact ⟨entry, exit, hentryOutside, hexitOutside,
      (sup_adj_interface_outside_iff_left base extra interfaceVertex hsupport
        left hentryOutside).2 hentry,
      hreach,
      (sup_adj_outside_interface_iff_left base extra interfaceVertex hsupport
        hexitOutside right).2 hexit⟩

/-- The Boolean update is semantically exact: it presents precisely the
interface contraction of the union whenever the added adjacency table is
exact and the added graph is supported on the interface. -/
theorem addInterfaceAdjacency_exact_step_iff
    {N Interface : Type*} (base extra : SimpleGraph N)
    (interfaceVertex : Interface → N)
    (hsupport : extra.support ⊆ Set.range interfaceVertex)
    (adjacency : Interface → Interface → Bool)
    (hadjacency : ∀ left right,
      adjacency left right = true ↔
        extra.Adj (interfaceVertex left) (interfaceVertex right))
    (left right : Interface) :
    InterfaceExteriorFactoredStep
        (addInterfaceAdjacency
          (exactInterfaceExteriorCode base interfaceVertex) adjacency)
        left right ↔
      InterfaceExteriorStep (base ⊔ extra) interfaceVertex left right := by
  classical
  unfold InterfaceExteriorFactoredStep addInterfaceAdjacency
    InterfaceExteriorStep exactInterfaceExteriorCode
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  rw [hadjacency left right, SimpleGraph.sup_adj,
    exists_exteriorConnection_sup_iff_left base extra interfaceVertex
      hsupport left right]

end GoertzelV24InterfaceDeletionComponentFactorUpdate

end Mettapedia.GraphTheory.FourColor
