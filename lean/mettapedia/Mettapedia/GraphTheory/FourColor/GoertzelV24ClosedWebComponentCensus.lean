import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebInnerTouching

/-!
# The component-level closed-web strand census

This module connects Addendum XXI's arithmetic strand ledger to actual
connected components of the three selected Tait-pair support graphs.

The three nonzero color pairs are represented in both orientations.  This is
a transparent double cover of the manuscript's unoriented ledger, chosen so
that `(a,b)` and `(b,a)` remain in their native dependent Lean graph types
without casts.  A boundary endpoint incidence is a boundary stub together
with one of the four oriented pairs that selects its nonzero edge color.
Thus the five inner stubs contribute twenty oriented incidences, while an
outer boundary of size `n` contributes `4 * n`; dividing by the harmless
orientation double cover recovers the manuscript's `10` and `2 * n`.

Under total closure every component is inner-touching.  Since selected-pair
components have maximum degree two, an outer endpoint and its chosen inner
endpoint determine the whole boundary of their component.  Consequently the
map from outer incidences to chosen inner incidences is injective.  At five
outer stubs its domain and codomain both have cardinality twenty, so it is also
surjective; no component can then contain two distinct inner endpoints.

This is a generated endpoint census of the proof's own three interface
graphs, not a configuration catalogue.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebComponentCensus

open SimpleGraph
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebSelectedEdgeStructure
open GoertzelV24ClosedWebRadialComponents
open GoertzelV24ClosedWebInnerTouching

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

/-- The six orientations of the three unordered pairs of nonzero Tait
colors. -/
inductive TaitPairIndex
  | redBlue
  | blueRed
  | redPurple
  | purpleRed
  | bluePurple
  | purpleBlue
  deriving DecidableEq

instance : Fintype TaitPairIndex where
  elems := {TaitPairIndex.redBlue, TaitPairIndex.blueRed,
    TaitPairIndex.redPurple, TaitPairIndex.purpleRed,
    TaitPairIndex.bluePurple, TaitPairIndex.purpleBlue}
  complete pair := by cases pair <;> simp

namespace TaitPairIndex

/-- First color in the canonical orientation of a pair. -/
def firstColor : TaitPairIndex → Color
  | redBlue => red
  | blueRed => blue
  | redPurple => red
  | purpleRed => purple
  | bluePurple => blue
  | purpleBlue => purple

/-- Second color in the canonical orientation of a pair. -/
def secondColor : TaitPairIndex → Color
  | redBlue => blue
  | blueRed => red
  | redPurple => purple
  | purpleRed => red
  | bluePurple => purple
  | purpleBlue => blue

/-- An oriented pair selects a boundary edge color. -/
def Selects (pair : TaitPairIndex) (color : Color) : Prop :=
  color = pair.firstColor ∨ color = pair.secondColor

instance (pair : TaitPairIndex) (color : Color) :
    Decidable (pair.Selects color) := by
  unfold Selects
  infer_instance

/-- Each indexed orientation is a valid pair of distinct nonzero Tait
colors. -/
theorem valid (pair : TaitPairIndex) :
    ValidColorPair pair.firstColor pair.secondColor := by
  cases pair with
  | redBlue => exact ⟨red_ne_zero, blue_ne_zero, red_ne_blue⟩
  | blueRed => exact ⟨blue_ne_zero, red_ne_zero, red_ne_blue.symm⟩
  | redPurple => exact ⟨red_ne_zero, purple_ne_zero, red_ne_purple⟩
  | purpleRed => exact ⟨purple_ne_zero, red_ne_zero, red_ne_purple.symm⟩
  | bluePurple => exact ⟨blue_ne_zero, purple_ne_zero, blue_ne_purple⟩
  | purpleBlue => exact ⟨purple_ne_zero, blue_ne_zero, blue_ne_purple.symm⟩

/-- Every nonzero Tait color occurs in exactly four of the six oriented
color pairs. -/
theorem selected_card_eq_four (color : Color) (hcolor : color ≠ 0) :
    Fintype.card {pair : TaitPairIndex // pair.Selects color} = 4 := by
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero color hcolor with
    rfl | rfl | rfl <;> decide

end TaitPairIndex

noncomputable local instance colorPairGraphNeighborSetFintype
    (C : G.EdgeColoring Color) (first second : Color) (vertex : V) :
    Fintype ((colorPairGraph C first second).neighborSet vertex) := by
  classical
  exact Subtype.fintype _

noncomputable local instance colorPairSupportGraphNeighborSetFintype
    (C : G.EdgeColoring Color) (first second : Color)
    (vertex : ColorPairSupportVertex C first second) :
    Fintype ((colorPairSupportGraph C first second).neighborSet vertex) := by
  classical
  exact Subtype.fintype _

/-- Inner boundary endpoint incidences, grouped by canonical color pair. -/
abbrev InnerEnd
    (data : AnnularBoundaryData G outerCount)
    (C : G.EdgeColoring Color) :=
  Σ pair : TaitPairIndex,
    {inner : Fin 5 //
      pair.Selects (C (data.innerBoundaryEdge inner))}

/-- The same inner incidences grouped first by boundary stub. -/
private abbrev InnerEndByStub
    (data : AnnularBoundaryData G outerCount)
    (C : G.EdgeColoring Color) :=
  Σ inner : Fin 5,
    {pair : TaitPairIndex //
      pair.Selects (C (data.innerBoundaryEdge inner))}

/-- Transpose the two finite indices in the inner endpoint ledger. -/
private def innerEndByPairEquivByStub
    (data : AnnularBoundaryData G outerCount)
    (C : G.EdgeColoring Color) :
    InnerEnd data C ≃ InnerEndByStub data C where
  toFun endpoint := ⟨endpoint.2.1, ⟨endpoint.1, endpoint.2.2⟩⟩
  invFun endpoint := ⟨endpoint.2.1, ⟨endpoint.1, endpoint.2.2⟩⟩
  left_inv endpoint := by
    rcases endpoint with ⟨pair, inner, hselected⟩
    rfl
  right_inv endpoint := by
    rcases endpoint with ⟨inner, pair, hselected⟩
    rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The five inner stubs contribute exactly twenty oriented bichromatic
strand ends, the double cover of the manuscript's ten unoriented ends. -/
theorem innerEnd_card_eq_twenty
    (data : AnnularBoundaryData G outerCount)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C) :
    Fintype.card (InnerEnd data C) = 20 := by
  rw [Fintype.card_congr (innerEndByPairEquivByStub data C),
    Fintype.card_sigma]
  have hfiber : ∀ inner : Fin 5,
      Fintype.card
        {pair : TaitPairIndex //
          pair.Selects (C (data.innerBoundaryEdge inner))} = 4 := by
    intro inner
    exact TaitPairIndex.selected_card_eq_four _
      (hC (data.innerBoundaryEdge inner))
  simp_rw [hfiber]
  simp

/-- Outer boundary endpoint incidences, grouped by canonical color pair. -/
abbrev OuterEnd
    (data : AnnularBoundaryData G outerCount)
    (C : G.EdgeColoring Color) :=
  Σ pair : TaitPairIndex,
    {outer : Fin outerCount //
      pair.Selects (C (data.outerBoundaryEdge outer))}

/-- The same outer incidences grouped first by boundary stub. -/
private abbrev OuterEndByStub
    (data : AnnularBoundaryData G outerCount)
    (C : G.EdgeColoring Color) :=
  Σ outer : Fin outerCount,
    {pair : TaitPairIndex //
      pair.Selects (C (data.outerBoundaryEdge outer))}

/-- Transpose the two finite indices in the outer endpoint ledger. -/
private def outerEndByPairEquivByStub
    (data : AnnularBoundaryData G outerCount)
    (C : G.EdgeColoring Color) :
    OuterEnd data C ≃ OuterEndByStub data C where
  toFun endpoint := ⟨endpoint.2.1, ⟨endpoint.1, endpoint.2.2⟩⟩
  invFun endpoint := ⟨endpoint.2.1, ⟨endpoint.1, endpoint.2.2⟩⟩
  left_inv endpoint := by
    rcases endpoint with ⟨pair, outer, hselected⟩
    rfl
  right_inv endpoint := by
    rcases endpoint with ⟨outer, pair, hselected⟩
    rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- An outer boundary of size `n` contributes exactly `4 * n` oriented
bichromatic strand ends, the double cover of the manuscript's `2 * n`. -/
theorem outerEnd_card_eq_four_times_outerCount
    (data : AnnularBoundaryData G outerCount)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C) :
    Fintype.card (OuterEnd data C) = 4 * outerCount := by
  rw [Fintype.card_congr (outerEndByPairEquivByStub data C),
    Fintype.card_sigma]
  have hfiber : ∀ outer : Fin outerCount,
      Fintype.card
        {pair : TaitPairIndex //
          pair.Selects (C (data.outerBoundaryEdge outer))} = 4 := by
    intro outer
    exact TaitPairIndex.selected_card_eq_four _
      (hC (data.outerBoundaryEdge outer))
  simp_rw [hfiber]
  simp [mul_comm]

/-- An indexed-pair inner incidence as a support-graph vertex. -/
def innerEndVertex
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (endpoint : InnerEnd data C) :
    ColorPairSupportVertex C endpoint.1.firstColor endpoint.1.secondColor := by
  refine ⟨data.innerStub endpoint.2.1, ?_⟩
  apply ((colorPairGraph C endpoint.1.firstColor endpoint.1.secondColor).degree_pos_iff_mem_support
    (data.innerStub endpoint.2.1)).mp
  rw [AnnularBoundaryData.colorPairGraph_degree_innerStub
    data hdata C endpoint.1.firstColor endpoint.1.secondColor endpoint.2.1]
  have hselected := endpoint.2.2
  simp only [TaitPairIndex.Selects] at hselected
  simp [hselected]

/-- An indexed-pair outer incidence as a support-graph vertex. -/
def outerEndVertex
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (endpoint : OuterEnd data C) :
    ColorPairSupportVertex C endpoint.1.firstColor endpoint.1.secondColor := by
  refine ⟨data.outerStub endpoint.2.1, ?_⟩
  apply ((colorPairGraph C endpoint.1.firstColor endpoint.1.secondColor).degree_pos_iff_mem_support
    (data.outerStub endpoint.2.1)).mp
  rw [AnnularBoundaryData.colorPairGraph_degree_outerStub
    data hdata C endpoint.1.firstColor endpoint.1.secondColor endpoint.2.1]
  have hselected := endpoint.2.2
  simp only [TaitPairIndex.Selects] at hselected
  simp [hselected]

/-- A component tagged by which indexed orientation of a color pair it
belongs to. -/
abbrev PairComponent (C : G.EdgeColoring Color) :=
  Σ pair : TaitPairIndex,
    (colorPairSupportGraph C pair.firstColor pair.secondColor).ConnectedComponent

/-- Component containing an inner endpoint incidence. -/
def innerEndComponent
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (endpoint : InnerEnd data C) :
    PairComponent C :=
  ⟨endpoint.1,
    (colorPairSupportGraph C endpoint.1.firstColor endpoint.1.secondColor).connectedComponentMk
      (innerEndVertex data hdata C endpoint)⟩

/-- Component containing an outer endpoint incidence. -/
def outerEndComponent
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (endpoint : OuterEnd data C) :
    PairComponent C :=
  ⟨endpoint.1,
    (colorPairSupportGraph C endpoint.1.firstColor endpoint.1.secondColor).connectedComponentMk
      (outerEndVertex data hdata C endpoint)⟩

/-- If an inner endpoint incidence is known to lie in a component, its
canonically constructed support vertex names exactly that component. -/
theorem innerEndComponent_eq_of_contains
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (endpoint : InnerEnd data C)
    (component :
      (colorPairSupportGraph C endpoint.1.firstColor
        endpoint.1.secondColor).ConnectedComponent)
    (hcontains : ComponentContainsInnerStub data C
      endpoint.1.firstColor endpoint.1.secondColor component endpoint.2.1) :
    innerEndComponent data hdata C endpoint = ⟨endpoint.1, component⟩ := by
  rcases hcontains with ⟨vertex, hvertexComponent, hvertexEq⟩
  have hvertexCanonical : innerEndVertex data hdata C endpoint = vertex := by
    apply Subtype.ext
    exact hvertexEq.symm
  have hcomponentEq :
      (colorPairSupportGraph C endpoint.1.firstColor
        endpoint.1.secondColor).connectedComponentMk vertex = component :=
    (ConnectedComponent.mem_supp_iff component vertex).mp hvertexComponent
  change
    (⟨endpoint.1,
      (colorPairSupportGraph C endpoint.1.firstColor
        endpoint.1.secondColor).connectedComponentMk
          (innerEndVertex data hdata C endpoint)⟩ : PairComponent C) =
      ⟨endpoint.1, component⟩
  rw [hvertexCanonical, hcomponentEq]

/-- An explicit inner endpoint incidence exists in every indexed-pair
component under the source's total-closure, inner-touching semantics. -/
theorem exists_innerEnd_with_component
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color)
    (hinnerTouching : EveryColorPairComponentInnerTouching data C)
    (pair : TaitPairIndex)
    (component :
      (colorPairSupportGraph C pair.firstColor pair.secondColor).ConnectedComponent) :
    ∃ endpoint : InnerEnd data C,
      innerEndComponent data hdata C endpoint = ⟨pair, component⟩ := by
  rcases hinnerTouching pair.firstColor pair.secondColor pair.valid component with
    ⟨inner, vertex, hvertexComponent, hvertexEq⟩
  have hactive : inner ∈ cap5ActiveSupport
      pair.firstColor pair.secondColor (data.innerBoundaryWord C) :=
    mem_activeSupport_of_componentContainsInnerStub
      data hdata C pair.firstColor pair.secondColor component inner
        ⟨vertex, hvertexComponent, hvertexEq⟩
  have hselected : pair.Selects (C (data.innerBoundaryEdge inner)) := by
    simpa [TaitPairIndex.Selects, cap5ActiveSupport,
      AnnularBoundaryData.innerBoundaryWord, cap5BoundaryWordOfEdges] using
        hactive
  let endpoint : InnerEnd data C := ⟨pair, ⟨inner, hselected⟩⟩
  refine ⟨endpoint, ?_⟩
  exact innerEndComponent_eq_of_contains data hdata C endpoint component
    ⟨vertex, hvertexComponent, hvertexEq⟩

/-- Choose the index of an inner endpoint of a component. -/
noncomputable def chosenInnerIndex
    (data : AnnularBoundaryData G outerCount) (_hdata : data.WellFormed)
    (C : G.EdgeColoring Color)
    (hinnerTouching : EveryColorPairComponentInnerTouching data C)
    (pair : TaitPairIndex)
    (component :
      (colorPairSupportGraph C pair.firstColor pair.secondColor).ConnectedComponent) :
    Fin 5 :=
  Classical.choose
    (hinnerTouching pair.firstColor pair.secondColor pair.valid component)

theorem chosenInnerIndex_contains
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color)
    (hinnerTouching : EveryColorPairComponentInnerTouching data C)
    (pair : TaitPairIndex)
    (component :
      (colorPairSupportGraph C pair.firstColor pair.secondColor).ConnectedComponent) :
    ComponentContainsInnerStub data C pair.firstColor pair.secondColor
      component (chosenInnerIndex data hdata C hinnerTouching pair component) :=
  Classical.choose_spec
    (hinnerTouching pair.firstColor pair.secondColor pair.valid component)

/-- Choose the inner endpoint of a component.  The pair index is preserved
definitionally.  The choice is used only for the finite injection argument;
no geometric claim depends on which endpoint is chosen when an inner--inner
component is hypothetically present. -/
noncomputable def chosenInnerEnd
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color)
    (hinnerTouching : EveryColorPairComponentInnerTouching data C)
    (pair : TaitPairIndex)
    (component :
      (colorPairSupportGraph C pair.firstColor pair.secondColor).ConnectedComponent) :
    InnerEnd data C :=
  ⟨pair, ⟨chosenInnerIndex data hdata C hinnerTouching pair component, by
    have hactive := mem_activeSupport_of_componentContainsInnerStub
      data hdata C pair.firstColor pair.secondColor component
        (chosenInnerIndex data hdata C hinnerTouching pair component)
        (chosenInnerIndex_contains data hdata C hinnerTouching pair component)
    simpa [TaitPairIndex.Selects, cap5ActiveSupport,
      AnnularBoundaryData.innerBoundaryWord, cap5BoundaryWordOfEdges] using
        hactive⟩⟩

theorem chosenInnerEnd_component
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color)
    (hinnerTouching : EveryColorPairComponentInnerTouching data C)
    (pair : TaitPairIndex)
    (component :
      (colorPairSupportGraph C pair.firstColor pair.secondColor).ConnectedComponent) :
    innerEndComponent data hdata C
        (chosenInnerEnd data hdata C hinnerTouching pair component) =
      ⟨pair, component⟩ := by
  apply innerEndComponent_eq_of_contains
  exact chosenInnerIndex_contains data hdata C hinnerTouching pair component

/-- Send each outer endpoint incidence to a chosen inner endpoint in its own
connected component. -/
noncomputable def outerToInnerEnd
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color)
    (hinnerTouching : EveryColorPairComponentInnerTouching data C)
    (endpoint : OuterEnd data C) : InnerEnd data C :=
  chosenInnerEnd data hdata C hinnerTouching endpoint.1
    (outerEndComponent data hdata C endpoint).2

theorem outerToInnerEnd_component
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color)
    (hinnerTouching : EveryColorPairComponentInnerTouching data C)
    (endpoint : OuterEnd data C) :
    innerEndComponent data hdata C
        (outerToInnerEnd data hdata C hinnerTouching endpoint) =
      outerEndComponent data hdata C endpoint := by
  exact chosenInnerEnd_component data hdata C hinnerTouching endpoint.1
    (outerEndComponent data hdata C endpoint).2

/-- Distinct outer endpoint incidences cannot choose the same inner endpoint.
If they did, they would lie in the same maximum-degree-two component; that
component already has the chosen inner endpoint and therefore has room for
only one outer boundary endpoint. -/
theorem outerToInnerEnd_injective
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (hinnerTouching : EveryColorPairComponentInnerTouching data C) :
    Function.Injective
      (outerToInnerEnd data hdata C hinnerTouching) := by
  classical
  intro leftEndpoint rightEndpoint himages
  have hpairs : leftEndpoint.1 = rightEndpoint.1 := by
    have houtputPairs := congrArg
      (fun endpoint : InnerEnd data C => endpoint.1) himages
    simpa [outerToInnerEnd, chosenInnerEnd] using houtputPairs
  rcases leftEndpoint with ⟨pair, leftOuter⟩
  rcases rightEndpoint with ⟨rightPair, rightOuter⟩
  dsimp at hpairs
  subst rightPair
  let leftEndpoint : OuterEnd data C := ⟨pair, leftOuter⟩
  let rightEndpoint : OuterEnd data C := ⟨pair, rightOuter⟩
  let leftComponent :=
    (colorPairSupportGraph C pair.firstColor pair.secondColor).connectedComponentMk
      (outerEndVertex data hdata C leftEndpoint)
  let rightComponent :=
    (colorPairSupportGraph C pair.firstColor pair.secondColor).connectedComponentMk
      (outerEndVertex data hdata C rightEndpoint)
  have hcomponentsSigma :
      outerEndComponent data hdata C leftEndpoint =
        outerEndComponent data hdata C rightEndpoint := by
    calc
      outerEndComponent data hdata C leftEndpoint =
          innerEndComponent data hdata C
            (outerToInnerEnd data hdata C hinnerTouching leftEndpoint) :=
        (outerToInnerEnd_component
          data hdata C hinnerTouching leftEndpoint).symm
      _ = innerEndComponent data hdata C
            (outerToInnerEnd data hdata C hinnerTouching rightEndpoint) := by
        apply congrArg (innerEndComponent data hdata C)
        simpa [leftEndpoint, rightEndpoint] using himages
      _ = outerEndComponent data hdata C rightEndpoint :=
        outerToInnerEnd_component
          data hdata C hinnerTouching rightEndpoint
  have hcomponents : leftComponent = rightComponent := by
    change (⟨pair, leftComponent⟩ : PairComponent C) =
      ⟨pair, rightComponent⟩ at hcomponentsSigma
    exact eq_of_heq (Sigma.ext_iff.mp hcomponentsSigma).2
  let innerEndpoint : InnerEnd data C :=
    chosenInnerEnd data hdata C hinnerTouching pair leftComponent
  let innerVertex : ColorPairSupportVertex C pair.firstColor pair.secondColor :=
    innerEndVertex data hdata C innerEndpoint
  let leftVertex : ColorPairSupportVertex C pair.firstColor pair.secondColor :=
    outerEndVertex data hdata C leftEndpoint
  let rightVertex : ColorPairSupportVertex C pair.firstColor pair.secondColor :=
    outerEndVertex data hdata C rightEndpoint
  have hinnerComponent : innerVertex ∈ leftComponent.supp := by
    rcases chosenInnerIndex_contains
        data hdata C hinnerTouching pair leftComponent with
      ⟨vertex, hvertexComponent, hvertexEq⟩
    have hvertexCanonical : innerVertex = vertex := by
      apply Subtype.ext
      exact hvertexEq.symm
    simpa [hvertexCanonical]
  have hleftComponent : leftVertex ∈ leftComponent.supp := by
    exact ConnectedComponent.connectedComponentMk_mem
  have hrightComponent : rightVertex ∈ leftComponent.supp := by
    have hrightOwn : rightVertex ∈ rightComponent.supp :=
      ConnectedComponent.connectedComponentMk_mem
    rwa [← hcomponents] at hrightOwn
  have hinnerLeft : innerVertex ≠ leftVertex := by
    intro heq
    apply hdata.inner_outer_stub_disjoint
      (chosenInnerIndex data hdata C hinnerTouching pair leftComponent)
      leftOuter.1
    exact congrArg Subtype.val heq
  have hendpointCases :=
    boundaryStub_eq_start_or_finish_of_mem_component
      data hdata C hC pair.valid leftComponent innerVertex leftVertex
      rightVertex hinnerComponent hleftComponent hrightComponent hinnerLeft
      (Or.inl ⟨chosenInnerIndex data hdata C hinnerTouching pair leftComponent,
        rfl⟩)
      (Or.inr ⟨leftOuter.1, rfl⟩)
      (Or.inr ⟨rightOuter.1, rfl⟩)
  have houterIndices : leftOuter.1 = rightOuter.1 := by
    rcases hendpointCases with hrightInner | hrightLeft
    · exfalso
      apply hdata.inner_outer_stub_disjoint
        (chosenInnerIndex data hdata C hinnerTouching pair leftComponent)
        rightOuter.1
      calc
        data.innerStub
            (chosenInnerIndex data hdata C hinnerTouching pair leftComponent) =
            innerVertex.1 := rfl
        _ = rightVertex.1 := congrArg Subtype.val hrightInner.symm
        _ = data.outerStub rightOuter.1 := rfl
    · apply data.outerStub.injective
      calc
        data.outerStub leftOuter.1 = leftVertex.1 := rfl
        _ = rightVertex.1 := congrArg Subtype.val hrightLeft.symm
        _ = data.outerStub rightOuter.1 := rfl
  exact Sigma.ext_iff.mpr
    ⟨rfl, heq_of_eq (Subtype.ext houterIndices)⟩

/-- At the sharp boundary `outerCount = 5`, the outer-to-inner endpoint map
is surjective because both oriented finite endpoint ledgers have cardinality
twenty. -/
theorem outerToInnerEnd_surjective_at_five
    (data : AnnularBoundaryData G 5) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (hinnerTouching : EveryColorPairComponentInnerTouching data C) :
    Function.Surjective
      (outerToInnerEnd data hdata C hinnerTouching) := by
  have hcard : Fintype.card (OuterEnd data C) =
      Fintype.card (InnerEnd data C) := by
    rw [outerEnd_card_eq_four_times_outerCount data C hC,
      innerEnd_card_eq_twenty data C hC]
  exact ((Fintype.bijective_iff_injective_and_card
    (outerToInnerEnd data hdata C hinnerTouching)).mpr
      ⟨outerToInnerEnd_injective data hdata C hC hinnerTouching,
        hcard⟩).2

/-- For one indexed color-pair orientation, the five-by-five endpoint
bijection rules
out an inner--inner component. -/
theorem noComponentHasTwoDistinctInnerStubs_at_indexedPair
    (data : AnnularBoundaryData G 5) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (hinnerTouching : EveryColorPairComponentInnerTouching data C)
    (pair : TaitPairIndex) :
    NoComponentHasTwoDistinctInnerStubs
      data C pair.firstColor pair.secondColor := by
  classical
  intro component firstInner secondInner
    hfirstContains hsecondContains
  have hfirstActive : firstInner ∈ cap5ActiveSupport
      pair.firstColor pair.secondColor (data.innerBoundaryWord C) :=
    mem_activeSupport_of_componentContainsInnerStub
      data hdata C pair.firstColor pair.secondColor component firstInner
        hfirstContains
  have hfirstSelected :
      pair.Selects (C (data.innerBoundaryEdge firstInner)) := by
    simpa [TaitPairIndex.Selects, cap5ActiveSupport,
      AnnularBoundaryData.innerBoundaryWord, cap5BoundaryWordOfEdges] using
        hfirstActive
  have hsecondActive : secondInner ∈ cap5ActiveSupport
      pair.firstColor pair.secondColor (data.innerBoundaryWord C) :=
    mem_activeSupport_of_componentContainsInnerStub
      data hdata C pair.firstColor pair.secondColor component secondInner
        hsecondContains
  have hsecondSelected :
      pair.Selects (C (data.innerBoundaryEdge secondInner)) := by
    simpa [TaitPairIndex.Selects, cap5ActiveSupport,
      AnnularBoundaryData.innerBoundaryWord, cap5BoundaryWordOfEdges] using
        hsecondActive
  let firstEndpoint : InnerEnd data C :=
    ⟨pair, ⟨firstInner, hfirstSelected⟩⟩
  let secondEndpoint : InnerEnd data C :=
    ⟨pair, ⟨secondInner, hsecondSelected⟩⟩
  obtain ⟨outerEndpoint, houterMaps⟩ :=
    outerToInnerEnd_surjective_at_five
      data hdata C hC hinnerTouching firstEndpoint
  have houterPair : outerEndpoint.1 = pair := by
    have hpairImage := congrArg
      (fun endpoint : InnerEnd data C => endpoint.1) houterMaps
    simpa [outerToInnerEnd, chosenInnerEnd, firstEndpoint] using hpairImage
  rcases outerEndpoint with ⟨outerPair, outer⟩
  dsimp at houterPair
  subst outerPair
  let outerEndpoint : OuterEnd data C := ⟨pair, outer⟩
  let firstVertex : ColorPairSupportVertex C pair.firstColor pair.secondColor :=
    innerEndVertex data hdata C firstEndpoint
  let secondVertex : ColorPairSupportVertex C pair.firstColor pair.secondColor :=
    innerEndVertex data hdata C secondEndpoint
  let outerVertex : ColorPairSupportVertex C pair.firstColor pair.secondColor :=
    outerEndVertex data hdata C outerEndpoint
  have hfirstComponent : firstVertex ∈ component.supp := by
    rcases hfirstContains with ⟨vertex, hvertexComponent, hvertexEq⟩
    have hvertexCanonical : firstVertex = vertex := by
      apply Subtype.ext
      exact hvertexEq.symm
    simpa [hvertexCanonical]
  have hsecondComponent : secondVertex ∈ component.supp := by
    rcases hsecondContains with ⟨vertex, hvertexComponent, hvertexEq⟩
    have hvertexCanonical : secondVertex = vertex := by
      apply Subtype.ext
      exact hvertexEq.symm
    simpa [hvertexCanonical]
  have houterComponentSigma :
      outerEndComponent data hdata C outerEndpoint =
        (⟨pair, component⟩ : PairComponent C) := by
    calc
      outerEndComponent data hdata C outerEndpoint =
          innerEndComponent data hdata C
            (outerToInnerEnd data hdata C hinnerTouching outerEndpoint) :=
        (outerToInnerEnd_component
          data hdata C hinnerTouching outerEndpoint).symm
      _ = innerEndComponent data hdata C firstEndpoint := by
        apply congrArg (innerEndComponent data hdata C)
        simpa [outerEndpoint] using houterMaps
      _ = (⟨pair, component⟩ : PairComponent C) :=
        innerEndComponent_eq_of_contains
          data hdata C firstEndpoint component hfirstContains
  have houterComponentEq :
      (colorPairSupportGraph C pair.firstColor pair.secondColor).connectedComponentMk
          outerVertex = component := by
    change (⟨pair,
      (colorPairSupportGraph C pair.firstColor pair.secondColor).connectedComponentMk
        outerVertex⟩ : PairComponent C) =
          ⟨pair, component⟩ at houterComponentSigma
    exact eq_of_heq (Sigma.ext_iff.mp houterComponentSigma).2
  have houterComponent : outerVertex ∈ component.supp := by
    have hown : outerVertex ∈
        ((colorPairSupportGraph C pair.firstColor pair.secondColor).connectedComponentMk
          outerVertex).supp :=
      ConnectedComponent.connectedComponentMk_mem
    rwa [houterComponentEq] at hown
  have hfirstOuter : firstVertex ≠ outerVertex := by
    intro heq
    apply hdata.inner_outer_stub_disjoint firstInner outer.1
    exact congrArg Subtype.val heq
  have hendpointCases :=
    boundaryStub_eq_start_or_finish_of_mem_component
      data hdata C hC pair.valid component firstVertex outerVertex
      secondVertex hfirstComponent houterComponent hsecondComponent
      hfirstOuter (Or.inl ⟨firstInner, rfl⟩)
      (Or.inr ⟨outer.1, rfl⟩) (Or.inl ⟨secondInner, rfl⟩)
  rcases hendpointCases with hsecondFirst | hsecondOuter
  · apply data.innerStub.injective
    calc
      data.innerStub firstInner = firstVertex.1 := rfl
      _ = secondVertex.1 := congrArg Subtype.val hsecondFirst.symm
      _ = data.innerStub secondInner := rfl
  · exfalso
    apply hdata.inner_outer_stub_disjoint secondInner outer.1
    calc
      data.innerStub secondInner = secondVertex.1 := rfl
      _ = outerVertex.1 := congrArg Subtype.val hsecondOuter
      _ = data.outerStub outer.1 := rfl

/-- Every valid color-pair orientation is one of the six indexed pairs. -/
theorem noColorPairComponentHasTwoDistinctInnerStubs_at_five
    (data : AnnularBoundaryData G 5) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (hinnerTouching : EveryColorPairComponentInnerTouching data C) :
    NoColorPairComponentHasTwoDistinctInnerStubs data C := by
  intro first second hpair
  rcases hpair with ⟨hfirstNonzero, hsecondNonzero, hfirstSecond⟩
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero first hfirstNonzero with
    rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero second hsecondNonzero with
      rfl | rfl | rfl
  · exact (hfirstSecond rfl).elim
  · exact noComponentHasTwoDistinctInnerStubs_at_indexedPair
      data hdata C hC hinnerTouching .redBlue
  · exact noComponentHasTwoDistinctInnerStubs_at_indexedPair
      data hdata C hC hinnerTouching .redPurple
  · exact noComponentHasTwoDistinctInnerStubs_at_indexedPair
      data hdata C hC hinnerTouching .blueRed
  · exact (hfirstSecond rfl).elim
  · exact noComponentHasTwoDistinctInnerStubs_at_indexedPair
      data hdata C hC hinnerTouching .bluePurple
  · exact noComponentHasTwoDistinctInnerStubs_at_indexedPair
      data hdata C hC hinnerTouching .purpleRed
  · exact noComponentHasTwoDistinctInnerStubs_at_indexedPair
      data hdata C hC hinnerTouching .purpleBlue
  · exact (hfirstSecond rfl).elim

/-- At five outer stubs, total-closure inner-touching semantics alone derive
the all-radial component anatomy for all three color pairs. -/
theorem everyColorPairComponentRadial_at_five_of_innerTouching
    (data : AnnularBoundaryData G 5) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (hinnerTouching : EveryColorPairComponentInnerTouching data C) :
    EveryColorPairComponentRadial data C := by
  exact everyColorPairComponentRadial_of_innerTouching_of_noTwoInner
    data hdata C hC hinnerTouching
      (noColorPairComponentHasTwoDistinctInnerStubs_at_five
        data hdata C hC hinnerTouching)

/-- Source-facing Addendum XXI conclusion: at the five-stub boundary, a
totally closed web with a good inner word has a singleton color pair whose
support is exactly two radial paths.  No radiality premise remains. -/
theorem exists_singletonPair_two_radialPaths_at_five_of_goodWord_of_innerTouching
    (data : AnnularBoundaryData G 5) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (hgood : CAP5BoundaryWordHasColoredBlock311
      (data.innerBoundaryWord C))
    (hinnerTouching : EveryColorPairComponentInnerTouching data C) :
    ∃ majority singletonFirst singletonSecond : Color,
      IsTaitColorTriple majority singletonFirst singletonSecond ∧
      ∃ firstComponent secondComponent :
          (colorPairSupportGraph C singletonFirst singletonSecond).ConnectedComponent,
        firstComponent ≠ secondComponent ∧
        ∃ firstPath : ComponentRadialPath
            data C singletonFirst singletonSecond firstComponent,
          ∃ secondPath : ComponentRadialPath
              data C singletonFirst singletonSecond secondComponent,
            firstPath.path.toSubgraph.verts ∪
                secondPath.path.toSubgraph.verts = Set.univ := by
  exact exists_singletonPair_two_radialPaths_of_goodWord_of_allRadial
    data hdata C hC hgood
      (everyColorPairComponentRadial_at_five_of_innerTouching
        data hdata C hC hinnerTouching)

end GoertzelV24ClosedWebComponentCensus

end Mettapedia.GraphTheory.FourColor
