import Mettapedia.GraphTheory.FourColor.CyclicCutSaturation

/-!
# Rooted, order-preserving saturation of cyclic cuts

Arbitrary saturation chooses components independently and can destroy a
nested family of shores.  This file develops the monotone alternative.  Fix
one exterior root, retain its component in every complementary shore, and
flip back.  The resulting filled shores grow monotonically, while their
complements are connected by construction.

The construction is graph-theoretic.  Its intended consumer is a nested
family of planar cycle push-off cuts.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace RootedCutSaturation

open GoertzelV24CyclicThreeCutConnectedSides
open SimpleGraph

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- An induced reachable component is connected. -/
theorem induce_inducedReachableSide_connected
    (side : V → Prop) (root : V) (hroot : side root) :
    (G.induce (inducedReachableSide G side root hroot)).Connected := by
  let sideGraph := G.induce side
  let component := sideGraph.connectedComponentMk ⟨root, hroot⟩
  let componentEquiv :
      {vertex // inducedReachableSide G side root hroot vertex} ≃
        {vertex : {point // side point} // vertex ∈ component} :=
    { toFun := fun vertex =>
        ⟨⟨vertex.1, vertex.2.choose⟩,
          ConnectedComponent.sound vertex.2.choose_spec |>.symm⟩
      invFun := fun vertex =>
        ⟨vertex.1.1, vertex.1.2,
          ConnectedComponent.exact vertex.2 |>.symm⟩
      left_inv := by intro vertex; apply Subtype.ext; rfl
      right_inv := by intro vertex; apply Subtype.ext; apply Subtype.ext; rfl }
  let componentIso :
      G.induce (inducedReachableSide G side root hroot) ≃g
        component.toSimpleGraph :=
    { toEquiv := componentEquiv
      map_rel_iff' := Iff.rfl }
  exact componentIso.connected_iff.mpr component.connected_toSimpleGraph

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Reachable components are monotone in their allowed vertex predicate. -/
theorem inducedReachableSide_mono
    {smaller larger : V → Prop}
    (hsub : ∀ vertex, smaller vertex → larger vertex)
    (root : V) (hroot : smaller root) (vertex : V)
    (hvertex : inducedReachableSide G smaller root hroot vertex) :
    inducedReachableSide G larger root (hsub root hroot) vertex := by
  rcases hvertex with ⟨hsmall, hreachable⟩
  refine ⟨hsub vertex hsmall, ?_⟩
  let inclusion := G.induceHomOfLE hsub
  have hmapped := hreachable.map inclusion.toHom
  convert hmapped using 1 <;> apply Subtype.ext <;> rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A vertex of `side` never belongs to a component induced in its
complement. -/
theorem not_inducedReachableSide_complement_of_mem
    (side : V → Prop) (root : V) (hroot : ¬ side root)
    {vertex : V} (hvertex : side vertex) :
    ¬ inducedReachableSide G (fun point => ¬ side point) root hroot vertex := by
  intro hcomponent
  exact hcomponent.choose hvertex

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- If `side` is connected, then removing one connected component of its
complement leaves a connected graph.  Equivalently, filling every other
complementary component into `side` preserves connectedness. -/
theorem induce_complement_component_complement_connected
    (hconnected : G.Connected)
    (side : V → Prop)
    (hsideConnected : (G.induce side).Connected)
    (sideRoot outsideRoot : V) (hsideRoot : side sideRoot)
    (houtsideRoot : ¬ side outsideRoot) :
    (G.induce (fun vertex =>
      ¬ inducedReachableSide G (fun point => ¬ side point)
        outsideRoot houtsideRoot vertex)).Connected := by
  let outsideComponent :=
    inducedReachableSide G (fun point => ¬ side point)
      outsideRoot houtsideRoot
  let closure : V → Prop := fun vertex => ¬ outsideComponent vertex
  have hsideClosure : ∀ vertex, side vertex → closure vertex := by
    intro vertex hvertex
    exact not_inducedReachableSide_complement_of_mem
      side outsideRoot houtsideRoot hvertex
  have hclosureRoot : closure sideRoot := hsideClosure sideRoot hsideRoot
  let mainComponent :=
    inducedReachableSide G closure sideRoot hclosureRoot
  have hsideMain : ∀ vertex, side vertex → mainComponent vertex := by
    intro vertex hvertex
    apply inducedReachableSide_mono hsideClosure sideRoot hsideRoot vertex
    exact ⟨hvertex, hsideConnected.preconnected
      ⟨sideRoot, hsideRoot⟩ ⟨vertex, hvertex⟩⟩
  have hall : ∀ vertex, closure vertex → mainComponent vertex := by
    intro vertex hvertex
    by_contra hnotMain
    let otherComponent := inducedReachableSide G closure vertex hvertex
    have hotherVertex : otherComponent vertex :=
      inducedReachableSide_root closure vertex hvertex
    have hnotOtherRoot : ¬ otherComponent sideRoot := by
      intro hotherRoot
      apply hnotMain
      rcases hotherRoot with ⟨_hroot, hvertexRoot⟩
      exact ⟨hvertex, by
        simpa [mainComponent, otherComponent] using hvertexRoot.symm⟩
    rcases hconnected vertex sideRoot with ⟨ambientWalk⟩
    rcases exists_edgeCrossesVertexSide_of_walk_endpoint_sides
        otherComponent ambientWalk hotherVertex hnotOtherRoot with
      ⟨edge, _hedgeWalk, hcrossOther⟩
    rcases hcrossOther with
      ⟨inner, outer, hinnerEdge, houterEdge, hinnerOther, houterOther⟩
    have hverticesNe : inner ≠ outer := by
      intro heq
      exact houterOther (heq ▸ hinnerOther)
    have hedgePair : (edge : Sym2 V) = s(inner, outer) :=
      sym2_eq_mk_of_mem_of_mem_of_ne hinnerEdge houterEdge hverticesNe
    have hadj : G.Adj inner outer :=
      (SimpleGraph.mem_edgeSet G).1 (by simpa [hedgePair] using edge.2)
    have hinnerClosure : closure inner := inducedReachableSide_mem hinnerOther
    have houterNotClosure : ¬ closure outer := by
      intro houterClosure
      have hinducedAdj : (G.induce closure).Adj
          ⟨inner, hinnerClosure⟩ ⟨outer, houterClosure⟩ := hadj
      exact houterOther
        ⟨houterClosure, hinnerOther.choose_spec.trans hinducedAdj.reachable⟩
    have houterOutsideComponent : outsideComponent outer := by
      exact Classical.byContradiction (fun hnot => houterNotClosure hnot)
    by_cases hinnerSide : side inner
    · have hinnerMain := hsideMain inner hinnerSide
      apply hnotMain
      rcases hinnerMain with ⟨_hinnerClosure, hrootInner⟩
      rcases hinnerOther with ⟨_hinnerClosure', hvertexInner⟩
      exact ⟨hvertex, by
        simpa [mainComponent, otherComponent] using
          hrootInner.trans hvertexInner.symm⟩
    · apply hinnerClosure
      rcases houterOutsideComponent with ⟨houterNotSide, hrootOuter⟩
      refine ⟨hinnerSide, ?_⟩
      have hinducedAdj : (G.induce (fun point => ¬ side point)).Adj
          ⟨outer, houterNotSide⟩ ⟨inner, hinnerSide⟩ := hadj.symm
      exact hrootOuter.trans hinducedAdj.reachable
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨sideRoot, hclosureRoot⟩, ?_⟩
  intro vertex
  rcases hall vertex.1 vertex.2 with ⟨_hclosure, hreachable⟩
  simpa [closure, outsideComponent] using hreachable

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Connectedness of induced graphs depends only on the pointwise extension
of the vertex predicate. -/
theorem induce_connected_congr
    {first second : V → Prop}
    (heq : ∀ vertex, first vertex ↔ second vertex) :
    (G.induce first).Connected ↔ (G.induce second).Connected := by
  have hpred : first = second := funext fun vertex => propext (heq vertex)
  subst second
  exact Iff.rfl

/-- The component of a fixed exterior root after deleting the chosen side. -/
def exteriorComponent
    (side : V → Prop) (outsideRoot : V) (houtsideRoot : ¬ side outsideRoot) :
    V → Prop :=
  inducedReachableSide G (fun vertex => ¬ side vertex)
    outsideRoot houtsideRoot

/-- Fill every complementary component except the one containing the fixed
exterior root. -/
def closureSide
    (side : V → Prop) (outsideRoot : V) (houtsideRoot : ¬ side outsideRoot) :
    V → Prop :=
  fun vertex => ¬ exteriorComponent (G := G) side outsideRoot houtsideRoot vertex

theorem side_subset_closureSide
    (side : V → Prop) (outsideRoot : V) (houtsideRoot : ¬ side outsideRoot) :
    ∀ vertex, side vertex →
      closureSide (G := G) side outsideRoot houtsideRoot vertex := by
  intro vertex hvertex
  exact not_inducedReachableSide_complement_of_mem
    side outsideRoot houtsideRoot hvertex

/-- Rooted filling is monotone: nested raw sides give nested filled sides
when the same exterior root is used. -/
theorem closureSide_mono
    {smaller larger : V → Prop}
    (hsub : ∀ vertex, smaller vertex → larger vertex)
    (outsideRoot : V) (hrootLarger : ¬ larger outsideRoot) :
    ∀ vertex,
      closureSide (G := G) smaller outsideRoot
          (fun hsmall => hrootLarger (hsub outsideRoot hsmall)) vertex →
        closureSide (G := G) larger outsideRoot hrootLarger vertex := by
  intro vertex hsmallClosure hlargeComponent
  apply hsmallClosure
  apply inducedReachableSide_mono
      (smaller := fun point => ¬ larger point)
      (larger := fun point => ¬ smaller point)
      (fun _ hnotLarge hsmall => hnotLarge (hsub _ hsmall))
      outsideRoot hrootLarger vertex at hlargeComponent
  simpa [exteriorComponent, closureSide] using hlargeComponent

/-- The exact support of rooted saturation. -/
def edgeCut
    {oldEdgeCut : Finset G.edgeSet}
    (realization : CyclicEdgeCutRealization G oldEdgeCut)
    (outsideRoot : V) (houtsideRoot : ¬ realization.side outsideRoot) :
    Finset G.edgeSet :=
  realization.compl.reachableCycleComponentCut outsideRoot houtsideRoot

/-- Rooted saturation of a cyclic cut.  The supplied cycle pins which
complementary component is to remain exterior. -/
def realization
    {oldEdgeCut : Finset G.edgeSet}
    (old : CyclicEdgeCutRealization G oldEdgeCut)
    (outsideRoot : V) (houtsideRoot : ¬ old.side outsideRoot)
    (outsideCycle : G.Walk outsideRoot outsideRoot)
    (hcycle : outsideCycle.IsCycle)
    (hsupport : ∀ vertex, vertex ∈ outsideCycle.support → ¬ old.side vertex) :
    CyclicEdgeCutRealization G
      (edgeCut old outsideRoot houtsideRoot) :=
  (old.compl.reachableCycleComponentRealization
    outsideRoot houtsideRoot outsideCycle hcycle hsupport).compl

@[simp]
theorem realization_side
    {oldEdgeCut : Finset G.edgeSet}
    (old : CyclicEdgeCutRealization G oldEdgeCut)
    (outsideRoot : V) (houtsideRoot : ¬ old.side outsideRoot)
    (outsideCycle : G.Walk outsideRoot outsideRoot)
    (hcycle : outsideCycle.IsCycle)
    (hsupport : ∀ vertex, vertex ∈ outsideCycle.support → ¬ old.side vertex)
    (vertex : V) :
    (realization old outsideRoot houtsideRoot outsideCycle hcycle hsupport).side vertex ↔
      closureSide (G := G) old.side outsideRoot houtsideRoot vertex :=
  Iff.rfl

theorem edgeCut_subset
    {oldEdgeCut : Finset G.edgeSet}
    (old : CyclicEdgeCutRealization G oldEdgeCut)
    (outsideRoot : V) (houtsideRoot : ¬ old.side outsideRoot) :
    edgeCut old outsideRoot houtsideRoot ⊆ oldEdgeCut := by
  exact old.compl.reachableCycleComponentCut_subset
    outsideRoot houtsideRoot

theorem induce_closureSide_connected
    (hconnected : G.Connected)
    (side : V → Prop)
    (hsideConnected : (G.induce side).Connected)
    (sideRoot outsideRoot : V) (hsideRoot : side sideRoot)
    (houtsideRoot : ¬ side outsideRoot) :
    (G.induce (closureSide (G := G) side outsideRoot houtsideRoot)).Connected := by
  apply (induce_connected_congr (G := G)
    (first := fun vertex =>
      ¬ inducedReachableSide G (fun point => ¬ side point)
        outsideRoot houtsideRoot vertex)
    (second := closureSide (G := G) side outsideRoot houtsideRoot)
    (fun _ => Iff.rfl)).mp
  exact induce_complement_component_complement_connected
    hconnected side hsideConnected sideRoot outsideRoot
      hsideRoot houtsideRoot

theorem induce_complement_closureSide_connected
    (side : V → Prop) (outsideRoot : V)
    (houtsideRoot : ¬ side outsideRoot) :
    (G.induce (fun vertex =>
      ¬ closureSide (G := G) side outsideRoot houtsideRoot vertex)).Connected := by
  have hcomponent := induce_inducedReachableSide_connected
    (G := G) (fun vertex => ¬ side vertex) outsideRoot houtsideRoot
  exact (induce_connected_congr (G := G)
    (first := exteriorComponent (G := G) side outsideRoot houtsideRoot)
    (second := fun vertex =>
      ¬ closureSide (G := G) side outsideRoot houtsideRoot vertex)
    (fun vertex => by
      simp only [closureSide]
      exact ⟨fun hcomponent hnot => hnot hcomponent,
        fun hnot => Classical.byContradiction hnot⟩)).mp hcomponent

/-- A width-bounded connected cut obtained by rooted saturation.  Besides
the standard `ConnectedAtWidth` receipt, the returned equalities retain the
exact edge set and side predicate of the rooted construction.  This
provenance is what lets a family saturated at one exterior root inherit the
nesting of its unsaturated sides. -/
theorem exists_connectedAtWidth
    (hconnected : G.Connected)
    {oldEdgeCut : Finset G.edgeSet}
    (old : CyclicEdgeCutRealization G oldEdgeCut)
    (hsideConnected : (G.induce old.side).Connected)
    (outsideRoot : V) (houtsideRoot : ¬ old.side outsideRoot)
    (outsideCycle : G.Walk outsideRoot outsideRoot)
    (hcycle : outsideCycle.IsCycle)
    (hsupport : ∀ vertex, vertex ∈ outsideCycle.support → ¬ old.side vertex)
    (bound : Nat) (hcard : oldEdgeCut.card ≤ bound) :
    ∃ connected : CyclicEdgeCutRealization.ConnectedAtWidth G bound,
      connected.edgeCut = edgeCut old outsideRoot houtsideRoot ∧
      ∀ vertex,
        connected.realization.side vertex ↔
          closureSide (G := G) old.side outsideRoot houtsideRoot vertex := by
  rcases old.hinside_cycle with
    ⟨sideRoot, hsideRoot, _insideCycle, _hinsideCycle, _hinsideSupport⟩
  refine ⟨
    { edgeCut := edgeCut old outsideRoot houtsideRoot
      realization := realization old outsideRoot houtsideRoot
        outsideCycle hcycle hsupport
      card_le := (Finset.card_le_card
        (edgeCut_subset old outsideRoot houtsideRoot)).trans hcard
      side_connected := ?_
      complement_connected := ?_ }, rfl, fun _ => Iff.rfl⟩
  · change (G.induce
      (closureSide (G := G) old.side outsideRoot houtsideRoot)).Connected
    exact induce_closureSide_connected hconnected old.side hsideConnected
      sideRoot outsideRoot hsideRoot houtsideRoot
  · change (G.induce (fun vertex =>
      ¬ closureSide (G := G) old.side outsideRoot houtsideRoot vertex)).Connected
    exact induce_complement_closureSide_connected
      old.side outsideRoot houtsideRoot

end


end RootedCutSaturation

end Mettapedia.GraphTheory.FourColor
