import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularFrontierMenu

/-!
# Finite cap-connectivity profiles for Menu-B states

The source profile contains the connectivity pairing of the tracked strand
germs.  At a good CAP5 interface, a majority/singleton pair has four active
cap ports.  This file makes its component partition an explicit finite
profile and proves Addendum VII's Menu-B condition is decided by that profile.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularFrontierMenu

open SimpleGraph
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebRadialComponents

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

/-- The active cap ports of one selected color pair.  This subtype is the
literal finite carrier on which the component coordinate of the source
profile is evaluated. -/
abbrev AnnularFrontierActivePairPort
    (data : AnnularBoundaryData G outerCount)
    (coloring : G.EdgeColoring Color) (first second : Color) :=
  {inner : Fin 5 // inner ∈ cap5ActiveSupport first second
    (data.innerBoundaryWord coloring)}

/-- The selected-pair component containing one active cap port. -/
noncomputable def annularFrontierActivePairPortComponent
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (coloring : G.EdgeColoring Color) (first second : Color)
    (port : AnnularFrontierActivePairPort data coloring first second) :
    (colorPairSupportGraph coloring first second).ConnectedComponent :=
  (colorPairSupportGraph coloring first second).connectedComponentMk
    ⟨data.innerStub port.1,
      innerStub_mem_colorPairGraph_support_of_mem_activeSupport
        data hdata coloring first second port.1 port.2⟩

/-- The canonical component of an active cap port genuinely contains that
port's inner stub. -/
theorem annularFrontierActivePairPortComponent_contains
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (coloring : G.EdgeColoring Color) (first second : Color)
    (port : AnnularFrontierActivePairPort data coloring first second) :
    ComponentContainsInnerStub data coloring first second
      (annularFrontierActivePairPortComponent data hdata coloring first second port)
      port.1 := by
  let vertex : ColorPairSupportVertex coloring first second :=
    ⟨data.innerStub port.1,
      innerStub_mem_colorPairGraph_support_of_mem_activeSupport
        data hdata coloring first second port.1 port.2⟩
  refine ⟨vertex, ?_, rfl⟩
  change vertex ∈
    ((colorPairSupportGraph coloring first second).connectedComponentMk vertex).supp
  exact (ConnectedComponent.mem_supp_iff
    ((colorPairSupportGraph coloring first second).connectedComponentMk vertex) vertex).mpr rfl

/-- Any component known to contain an active cap port is the port's canonical
component.  This is the bridge from existential graph components to the
finite profile coordinate. -/
theorem annularFrontierActivePairPortComponent_eq_of_contains
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (coloring : G.EdgeColoring Color) (first second : Color)
    (port : AnnularFrontierActivePairPort data coloring first second)
    (component : (colorPairSupportGraph coloring first second).ConnectedComponent)
    (hcontains : ComponentContainsInnerStub data coloring first second component port.1) :
    annularFrontierActivePairPortComponent data hdata coloring first second port = component := by
  rcases hcontains with ⟨vertex, hvertexComponent, hvertexEq⟩
  have hvertexCanonical :
      (⟨data.innerStub port.1,
        innerStub_mem_colorPairGraph_support_of_mem_activeSupport
          data hdata coloring first second port.1 port.2⟩ :
        ColorPairSupportVertex coloring first second) = vertex := by
    apply Subtype.ext
    exact hvertexEq.symm
  change
    (colorPairSupportGraph coloring first second).connectedComponentMk
      ⟨data.innerStub port.1,
        innerStub_mem_colorPairGraph_support_of_mem_activeSupport
          data hdata coloring first second port.1 port.2⟩ = component
  rw [hvertexCanonical]
  exact (ConnectedComponent.mem_supp_iff component vertex).mp hvertexComponent

/-- The finite connectivity coordinate of the source profile: ordered active
cap-port pairs lying in the same selected-pair component. -/
noncomputable def annularFrontierPairConnectionProfile
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (coloring : G.EdgeColoring Color) (first second : Color) :
    Finset
      (AnnularFrontierActivePairPort data coloring first second ×
        AnnularFrontierActivePairPort data coloring first second) := by
  classical
  exact Finset.univ.filter fun ports =>
    annularFrontierActivePairPortComponent data hdata coloring first second ports.1 =
      annularFrontierActivePairPortComponent data hdata coloring first second ports.2

/-- Membership in the finite connectivity profile is exactly equality of the
two actual selected-pair components. -/
theorem mem_annularFrontierPairConnectionProfile_iff
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (coloring : G.EdgeColoring Color) (first second : Color)
    (ports : AnnularFrontierActivePairPort data coloring first second ×
      AnnularFrontierActivePairPort data coloring first second) :
    ports ∈ annularFrontierPairConnectionProfile data hdata coloring first second ↔
      annularFrontierActivePairPortComponent data hdata coloring first second ports.1 =
        annularFrontierActivePairPortComponent data hdata coloring first second ports.2 := by
  classical
  simp [annularFrontierPairConnectionProfile]

/-- Addendum VII in finite-profile form: Menu B for a selected pair holds
exactly when two active cap ports are separated by its component profile. -/
theorem annularFrontierMenuBForPair_iff_exists_not_mem_connectionProfile
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (coloring : G.EdgeColoring Color) (first second : Color) :
    AnnularFrontierMenuBForPair data coloring first second ↔
      ∃ left right : AnnularFrontierActivePairPort data coloring first second,
        (left, right) ∉
          annularFrontierPairConnectionProfile data hdata coloring first second := by
  constructor
  · rintro ⟨leftComponent, rightComponent, hcomponents,
      ⟨leftInner, hleftContains⟩, ⟨rightInner, hrightContains⟩⟩
    have hleftActive : leftInner ∈ cap5ActiveSupport first second
        (data.innerBoundaryWord coloring) :=
      mem_activeSupport_of_componentContainsInnerStub
        data hdata coloring first second leftComponent leftInner hleftContains
    have hrightActive : rightInner ∈ cap5ActiveSupport first second
        (data.innerBoundaryWord coloring) :=
      mem_activeSupport_of_componentContainsInnerStub
        data hdata coloring first second rightComponent rightInner hrightContains
    let left : AnnularFrontierActivePairPort data coloring first second :=
      ⟨leftInner, hleftActive⟩
    let right : AnnularFrontierActivePairPort data coloring first second :=
      ⟨rightInner, hrightActive⟩
    refine ⟨left, right, ?_⟩
    intro hconnected
    have hcomponentEq :=
      (mem_annularFrontierPairConnectionProfile_iff
        data hdata coloring first second (left, right)).mp hconnected
    have hleftEq :
        annularFrontierActivePairPortComponent data hdata coloring first second left =
          leftComponent :=
      annularFrontierActivePairPortComponent_eq_of_contains
        data hdata coloring first second left leftComponent hleftContains
    have hrightEq :
        annularFrontierActivePairPortComponent data hdata coloring first second right =
          rightComponent :=
      annularFrontierActivePairPortComponent_eq_of_contains
        data hdata coloring first second right rightComponent hrightContains
    exact hcomponents (hleftEq.symm.trans (hcomponentEq.trans hrightEq))
  · rintro ⟨left, right, hseparated⟩
    refine ⟨annularFrontierActivePairPortComponent data hdata coloring first second left,
      annularFrontierActivePairPortComponent data hdata coloring first second right,
      ?_, ⟨left.1,
        annularFrontierActivePairPortComponent_contains
          data hdata coloring first second left⟩,
      ⟨right.1,
        annularFrontierActivePairPortComponent_contains
          data hdata coloring first second right⟩⟩
    intro hcomponents
    apply hseparated
    exact (mem_annularFrontierPairConnectionProfile_iff
      data hdata coloring first second (left, right)).mpr hcomponents

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The active-port carrier has the same finite cardinality as the literal
pair support on the good inner word. -/
theorem annularFrontierActivePairPort_card
    (data : AnnularBoundaryData G outerCount)
    (coloring : G.EdgeColoring Color) (first second : Color) :
    Fintype.card (AnnularFrontierActivePairPort data coloring first second) =
      (cap5ActiveSupport first second (data.innerBoundaryWord coloring)).card := by
  simp [AnnularFrontierActivePairPort]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A source Menu-B state has a witnessed pair whose connectivity profile is
on exactly four active cap ports. -/
theorem AnnularFrontierMenuBState.exists_fourPort_connectionProfile
    (data : AnnularBoundaryData G outerCount)
    (coloring : G.EdgeColoring Color)
    (hmenu : AnnularFrontierMenuBState data coloring) :
    ∃ majority singleton : Color,
      Fintype.card (AnnularFrontierActivePairPort data coloring majority singleton) = 4 ∧
        AnnularFrontierMenuBForPair data coloring majority singleton := by
  rcases hmenu.exists_majorityPair_activeSupport_card with
    ⟨majority, singleton, hcard, hpair⟩
  refine ⟨majority, singleton, ?_, hpair⟩
  rw [annularFrontierActivePairPort_card]
  exact hcard

end

end GoertzelV24AnnularFrontierMenu

end Mettapedia.GraphTheory.FourColor
