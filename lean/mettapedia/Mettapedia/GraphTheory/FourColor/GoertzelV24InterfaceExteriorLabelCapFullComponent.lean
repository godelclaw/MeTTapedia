import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceExteriorLabelCapFactorForgetWeightExact

/-!
# Recover full component caps from an interface/exterior label factor

A weighted interface/exterior code stores labels in strict-exterior
components, while represented interface coordinates carry their own labels.
Forgetting the entire interface turns both kinds into the atoms of one finite
component calculation.  This file packages that calculation and proves its
literal graph semantics.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24InterfaceExteriorLabelCapFullComponent

open GoertzelV24DeletionSensitivePortResidualFactorContraction
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceDeletionComponentFactorForgetExterior
open GoertzelV24InterfaceExteriorLabelCapFactor
open GoertzelV24InterfaceExteriorLabelCapFactorForget
open GoertzelV24InterfaceExteriorLabelCapFactorForgetExact
open GoertzelV24InterfaceExteriorLabelCapFactorForgetWeightExact
open SimpleGraph

/-- The empty retained interface. -/
def emptyRetainedCoordinate {Interface : Type*} :
    Fin 0 → Option Interface :=
  fun empty => Fin.elim0 empty

/-- Forget every represented coordinate and read the capped weight of the
resulting full component rooted at one interface slot. -/
def interfaceExteriorLabelCapFullComponent
    {Interface Incidence : Type*}
    [Fintype Interface] [DecidableEq Interface]
    [Fintype Incidence] [LinearOrder Incidence]
    (code : BoundedInterfaceExteriorLabelCapCode Interface Incidence cap)
    (incidenceSlot : Incidence → Interface) (source : Interface) :
    Fin (cap + 1) :=
  exteriorLabelCapContractionComponentCap code emptyRetainedCoordinate
    incidenceSlot (.inl source)

/-- Distinct ambient labels in the full graph component rooted at one
represented coordinate. -/
noncomputable def fullComponentLabelSupport
    {N Interface Label : Type*}
    [Fintype N] [DecidableEq N] [Fintype Label] [DecidableEq Label]
    (graph : SimpleGraph N) (interfaceVertex : Interface → N)
    (label : N → Label) (source : Interface) : Finset Label := by
  classical
  exact ((Finset.univ.filter fun vertex =>
    graph.Reachable (interfaceVertex source) vertex).image label)

/-- A graph has no vertices named by an empty interface, so its strict
exterior relative to that interface is the whole graph. -/
@[simp] theorem exteriorGraph_emptyInterface
    {N : Type*} (graph : SimpleGraph N) :
    exteriorGraph graph (fun empty : Fin 0 => Fin.elim0 empty) = graph := by
  ext left right
  simp [exteriorGraph, supportRestriction_adj, OutsideInterface]

/-- On an exact code, forgetting the entire interface computes the capped
number of distinct labels in the literal full component of the source slot.

The label-injectivity premise is deliberately local to that component.  It is
the precise condition under which unit weights on interface coordinates and
stored weights on exterior components add without duplication. -/
theorem interfaceExteriorLabelCapFullComponent_exact
    {N Interface Incidence Label : Type*}
    [Fintype N] [DecidableEq N]
    [Fintype Interface] [DecidableEq Interface]
    [Fintype Incidence] [LinearOrder Incidence]
    [Fintype Label] [DecidableEq Label]
    (graph : SimpleGraph N)
    (interfaceVertex : Interface → N)
    (present : N → Prop) [DecidablePred present]
    (incidenceSlot : Incidence → Interface)
    (incidenceVertex : Incidence → N)
    (label : N → Label)
    (hinterfacePresent : ∀ slot,
      interfaceVertex slot ∈ graph.support → present (interfaceVertex slot))
    (hincidenceComplete : ∀ slot outside,
      OutsideInterface interfaceVertex outside →
        graph.Adj (interfaceVertex slot) outside →
        ∃ incidence,
          incidenceSlot incidence = slot ∧ incidenceVertex incidence = outside)
    (source : Interface)
    (hsource : present (interfaceVertex source))
    (hinterfaceInjective : Function.Injective interfaceVertex)
    (hlabelInjective : Set.InjOn label
      {vertex | graph.Reachable (interfaceVertex source) vertex}) :
    (interfaceExteriorLabelCapFullComponent
      (exactInterfaceExteriorLabelCapCode graph interfaceVertex present
        incidenceSlot incidenceVertex label cap)
      incidenceSlot source).val =
      min (fullComponentLabelSupport graph interfaceVertex label source).card
        cap := by
  classical
  let code := exactInterfaceExteriorLabelCapCode graph interfaceVertex present
    incidenceSlot incidenceVertex label cap
  let emptyVertex : Fin 0 → N := fun empty => Fin.elim0 empty
  let emptyRetain : Fin 0 → Option Interface := emptyRetainedCoordinate
  have hsome : ∀ retained slot, emptyRetain retained = some slot →
      interfaceVertex slot = emptyVertex retained := by
    intro retained
    exact Fin.elim0 retained
  have hnone : ∀ retained, emptyRetain retained = none →
      emptyVertex retained ∉ graph.support := by
    intro retained
    exact Fin.elim0 retained
  have hatomPresent :
      exteriorLabelCapContractionAtomPresent code emptyRetain
          (.inl source) = true := by
    simp [code, emptyRetain, emptyRetainedCoordinate,
      exteriorLabelCapContractionAtomPresent,
      codeSurvivesPartialRetained, hsource]
  have hcap :=
    exteriorLabelCapContractionComponentCap_val_eq_literalLabelSupport
      graph interfaceVertex emptyVertex emptyRetain hsome hnone incidenceSlot
      incidenceVertex label code rfl
      (by
        intro slot hsupport
        exact (exactInterfaceExteriorLabelCapCode_interfacePresent_iff graph
          interfaceVertex present incidenceSlot incidenceVertex label slot
            cap).2 (hinterfacePresent slot hsupport))
      (fun incidence =>
        exactInterfaceExteriorLabelCapCode_incidencePresent_iff graph
          interfaceVertex present incidenceSlot incidenceVertex label incidence
            cap)
      (fun first second =>
        exactInterfaceExteriorLabelCapCode_incidenceConnected_iff graph
          interfaceVertex present incidenceSlot incidenceVertex label first
            second cap)
      hincidenceComplete
      (fun incidence =>
        exactInterfaceExteriorLabelCapCode_incidenceCap_val graph
          interfaceVertex present incidenceSlot incidenceVertex label incidence
            cap)
      (.inl source) hatomPresent hinterfaceInjective
      (by
        simpa [emptyVertex, exteriorLabelCapContractionAtomVertex] using
          hlabelInjective)
  simpa [interfaceExteriorLabelCapFullComponent, code, emptyRetain, emptyVertex,
    exteriorLabelCapContractionLiteralLabelSupport,
    exteriorLabelCapContractionAtomVertex, fullComponentLabelSupport] using hcap

end GoertzelV24InterfaceExteriorLabelCapFullComponent

end Mettapedia.GraphTheory.FourColor
