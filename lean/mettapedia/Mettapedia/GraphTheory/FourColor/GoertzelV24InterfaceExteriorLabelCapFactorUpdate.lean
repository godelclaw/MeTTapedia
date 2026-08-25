import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceExteriorLabelCapFactor
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceDeletionComponentFactorUpdate

/-!
# Updating exterior label caps by an interface-supported graph

Adjoining a graph supported wholly on the represented interface changes two
finite rows: direct interface adjacency and literal interface presence.  It
does not change a strictly exterior component, any interface-to-exterior
incidence, or the distinct labels carried by such a component.

This file packages that observation as an exact executable update of the
weighted deletion-stable factor.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24InterfaceExteriorLabelCapFactorUpdate

open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceDeletionComponentFactorUpdate
open GoertzelV24InterfaceExteriorLabelCapFactor
open SimpleGraph

/-- Add literal interface adjacency and presence while retaining the exact
strict-exterior component data. -/
def addInterfaceAdjacencyAndPresence {Interface Incidence : Type*} {cap : Nat}
    (code : BoundedInterfaceExteriorLabelCapCode Interface Incidence cap)
    (adjacency : Interface → Interface → Bool)
    (addedPresent : Interface → Bool) :
    BoundedInterfaceExteriorLabelCapCode Interface Incidence cap where
  connectivity := addInterfaceAdjacency code.connectivity adjacency
  interfacePresent slot := code.interfacePresent slot || addedPresent slot
  incidencePresent := code.incidencePresent
  incidenceConnected := code.incidenceConnected
  incidenceCap := code.incidenceCap

/-- An interface-supported graph contributes no new live incidence into the
strict exterior. -/
theorem exteriorIncidencePresent_sup_iff_left
    {N Interface Incidence : Type*} (base extra : SimpleGraph N)
    (interfaceVertex : Interface → N)
    (hsupport : extra.support ⊆ Set.range interfaceVertex)
    (incidenceSlot : Incidence → Interface)
    (incidenceVertex : Incidence → N) (incidence : Incidence) :
    ExteriorIncidencePresent (base ⊔ extra) interfaceVertex incidenceSlot
        incidenceVertex incidence ↔
      ExteriorIncidencePresent base interfaceVertex incidenceSlot
        incidenceVertex incidence := by
  unfold ExteriorIncidencePresent
  constructor
  · rintro ⟨houtside, hadj⟩
    exact ⟨houtside,
      (sup_adj_interface_outside_iff_left base extra interfaceVertex hsupport
        (incidenceSlot incidence) houtside).1 hadj⟩
  · rintro ⟨houtside, hadj⟩
    exact ⟨houtside,
      (sup_adj_interface_outside_iff_left base extra interfaceVertex hsupport
        (incidenceSlot incidence) houtside).2 hadj⟩

/-- The label support of every entered exterior component is unchanged by an
interface-supported graph. -/
theorem exteriorIncidenceLabelSupport_sup_eq_left
    {N Interface Incidence Label : Type*}
    [Fintype N] [DecidableEq N] [Fintype Label] [DecidableEq Label]
    (base extra : SimpleGraph N) (interfaceVertex : Interface → N)
    (hsupport : extra.support ⊆ Set.range interfaceVertex)
    (incidenceSlot : Incidence → Interface)
    (incidenceVertex : Incidence → N) (label : N → Label)
    (incidence : Incidence) :
    exteriorIncidenceLabelSupport (base ⊔ extra) interfaceVertex
        incidenceSlot incidenceVertex label incidence =
      exteriorIncidenceLabelSupport base interfaceVertex incidenceSlot
        incidenceVertex label incidence := by
  classical
  ext value
  rw [mem_exteriorIncidenceLabelSupport_iff,
    mem_exteriorIncidenceLabelSupport_iff,
    exteriorIncidencePresent_sup_iff_left base extra interfaceVertex hsupport
      incidenceSlot incidenceVertex incidence,
    exteriorGraph_sup_eq_left_of_right_support_subset_interface base extra
      interfaceVertex hsupport]

/-- Exactness of the weighted update.  The local graph may change only
interface adjacency and the explicit presence predicate; every exterior row
is preserved. -/
theorem addInterfaceAdjacencyAndPresence_exact_code_eq
    {N Interface Incidence Label : Type*}
    [Fintype N] [DecidableEq N] [Fintype Label] [DecidableEq Label]
    (base extra : SimpleGraph N) (interfaceVertex : Interface → N)
    (hsupport : extra.support ⊆ Set.range interfaceVertex)
    (basePresent extraPresent : N → Prop)
    [DecidablePred basePresent] [DecidablePred extraPresent]
    (incidenceSlot : Incidence → Interface)
    (incidenceVertex : Incidence → N) (label : N → Label)
    (adjacency : Interface → Interface → Bool)
    (hadjacency : ∀ left right,
      adjacency left right = true ↔
        extra.Adj (interfaceVertex left) (interfaceVertex right))
    (cap : Nat := 5) :
    addInterfaceAdjacencyAndPresence
        (exactInterfaceExteriorLabelCapCode base interfaceVertex basePresent
          incidenceSlot incidenceVertex label cap)
        adjacency (fun slot => decide (extraPresent (interfaceVertex slot))) =
      exactInterfaceExteriorLabelCapCode (base ⊔ extra) interfaceVertex
        (fun vertex => basePresent vertex ∨ extraPresent vertex)
        incidenceSlot incidenceVertex label cap := by
  apply BoundedInterfaceExteriorLabelCapCode.ext
  · exact addInterfaceAdjacency_exact_code_eq base extra interfaceVertex
      hsupport adjacency hadjacency
  · funext slot
    apply Bool.eq_iff_iff.mpr
    simp [addInterfaceAdjacencyAndPresence,
      exactInterfaceExteriorLabelCapCode]
  · funext incidence
    apply Bool.eq_iff_iff.mpr
    simp only [addInterfaceAdjacencyAndPresence,
      exactInterfaceExteriorLabelCapCode, decide_eq_true_eq]
    exact (exteriorIncidencePresent_sup_iff_left base extra interfaceVertex
      hsupport incidenceSlot incidenceVertex incidence).symm
  · funext first second
    apply Bool.eq_iff_iff.mpr
    simp only [addInterfaceAdjacencyAndPresence,
      exactInterfaceExteriorLabelCapCode, decide_eq_true_eq]
    rw [exteriorIncidencePresent_sup_iff_left base extra interfaceVertex
        hsupport incidenceSlot incidenceVertex first,
      exteriorIncidencePresent_sup_iff_left base extra interfaceVertex
        hsupport incidenceSlot incidenceVertex second,
      exteriorGraph_sup_eq_left_of_right_support_subset_interface base extra
        interfaceVertex hsupport]
  · funext incidence
    apply Fin.ext
    simp only [addInterfaceAdjacencyAndPresence,
      exactInterfaceExteriorLabelCapCode]
    rw [exteriorIncidenceLabelSupport_sup_eq_left base extra interfaceVertex
      hsupport incidenceSlot incidenceVertex label incidence]

end GoertzelV24InterfaceExteriorLabelCapFactorUpdate

end Mettapedia.GraphTheory.FourColor
