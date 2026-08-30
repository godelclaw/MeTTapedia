import Mettapedia.GraphTheory.FourColor.GoertzelV24PortTangleKempeEndpoints

/-!
# The primal graph of one physical port-tangle Kempe web

The common-web carrier has active darts as vertices.  Its vertex wires do
not traverse a primal edge, while its interior-edge wires do.  This file
contracts the former wires: for one fixed colour pair, the primal Kempe graph
has the tangle vertices as its vertices and precisely the active interior
edges as its edges.

The main result is an exact connectivity equivalence.  Two active darts lie
in the same physical common-web component if and only if their base vertices
are connected in the primal Kempe graph.  Thus simple primal paths may be
chosen without changing components, and paths chosen in distinct components
are automatically vertex-disjoint.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24PortTanglePrimalKempeGraph

open SimpleGraph
open GoertzelV24HexagonPairingTargetAwareBoundary
open GoertzelV24PortTangleGluing
open GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24PortTangleCommonKempeWeb
open GoertzelV24PortTangleKempeEndpoints
open GoertzelV24PortTangleCutParity

universe u

variable {V I P : Type u}
  [Fintype V] [Fintype I] [Fintype P]
  [DecidableEq V] [DecidableEq I] [DecidableEq P]

noncomputable section

/-- The primal graph of the selected physical bichromatic web.  Its edges
are exactly the interior tangle edges carrying one of the selected colours.
Boundary ports are terminals and therefore contribute no primal edge. -/
def primalKempeGraph
    (T : PortTangle V I P) (coloring : Coloring T)
    (pair : TaitColorPair) : SimpleGraph V where
  Adj first second :=
    ∃ dart : I,
      pairActiveDart coloring pair (Sum.inl dart) ∧
        ((T.vert (Sum.inl dart) = first ∧
            T.vert (Sum.inl (T.alpha dart)) = second) ∨
          (T.vert (Sum.inl dart) = second ∧
            T.vert (Sum.inl (T.alpha dart)) = first))
  symm := ⟨by
    rintro first second ⟨dart, hactive, hforward | hreverse⟩
    · exact ⟨dart, hactive, Or.inr hforward⟩
    · exact ⟨dart, hactive, Or.inl hreverse⟩⟩
  loopless := ⟨by
    rintro vertex ⟨dart, _hactive, hforward | hreverse⟩
    · exact T.no_self_loops dart (hforward.1.trans hforward.2.symm)
    · exact T.no_self_loops dart (hreverse.1.trans hreverse.2.symm)⟩

noncomputable local instance primalKempeGraphAdjDecidable
    (T : PortTangle V I P) (coloring : Coloring T)
    (pair : TaitColorPair) :
    DecidableRel (primalKempeGraph T coloring pair).Adj :=
  Classical.decRel _

/-- Interior darts are determined by their ordered endpoint pair.  Literal
vertex shores cut from a simple graph have this property; an abstract port
tangle with parallel interior edges need not. -/
def InteriorEndpointInjective (T : PortTangle V I P) : Prop :=
  ∀ first second : I,
    T.vert (Sum.inl first) = T.vert (Sum.inl second) →
    T.vert (Sum.inl (T.alpha first)) =
      T.vert (Sum.inl (T.alpha second)) →
    first = second

theorem primalKempeGraph_adj_of_active_interior
    (T : PortTangle V I P) (coloring : Coloring T)
    (pair : TaitColorPair) (dart : I)
    (hactive : pairActiveDart coloring pair (Sum.inl dart)) :
    (primalKempeGraph T coloring pair).Adj
      (T.vert (Sum.inl dart))
      (T.vert (Sum.inl (T.alpha dart))) := by
  exact ⟨dart, hactive, Or.inl ⟨rfl, rfl⟩⟩

/-- At a vertex carrying no active boundary port, the selected primal Kempe
graph has degree exactly two, provided parallel interior darts are excluded. -/
theorem primalKempeGraph_degree_eq_two_of_no_active_port_at
    (T : PortTangle V I P) (hcubic : IsCubic T)
    (hendpoint : InteriorEndpointInjective T)
    (coloring : Coloring T) (hproper : IsProper coloring)
    (pair : TaitColorPair) (vertex : V)
    (hnoPort : ∀ port : P, T.vert (Sum.inr port) = vertex →
      ¬pairActiveDart coloring pair (Sum.inr port)) :
    (primalKempeGraph T coloring pair).degree vertex = 2 := by
  classical
  have hcard := card_activeDartsAt_eq_two
    T hcubic coloring hproper pair vertex
  rcases Finset.card_eq_two.mp hcard with
    ⟨first, second, hfirstSecond, hactiveSet⟩
  have hfirstMem : first ∈ activeDartsAt T coloring pair vertex := by
    rw [hactiveSet]
    simp
  have hsecondMem : second ∈ activeDartsAt T coloring pair vertex := by
    rw [hactiveSet]
    simp
  have hfirstData :=
    (mem_activeDartsAt_iff T coloring pair vertex first).1 hfirstMem
  have hsecondData :=
    (mem_activeDartsAt_iff T coloring pair vertex second).1 hsecondMem
  have hfirstInterior : ∃ interior : I, first = Sum.inl interior := by
    rcases hfirst : first with firstInterior | firstPort
    · exact ⟨firstInterior, rfl⟩
    · exact False.elim
        (hnoPort firstPort
          (by simpa [hfirst] using hfirstData.1)
          (by simpa [hfirst] using hfirstData.2))
  rcases hfirstInterior with ⟨firstInterior, rfl⟩
  have hsecondInterior : ∃ interior : I, second = Sum.inl interior := by
    rcases hsecond : second with secondInterior | secondPort
    · exact ⟨secondInterior, rfl⟩
    · exact False.elim
        (hnoPort secondPort
          (by simpa [hsecond] using hsecondData.1)
          (by simpa [hsecond] using hsecondData.2))
  rcases hsecondInterior with ⟨secondInterior, rfl⟩
  have hfirstSelected :
      pairActiveDart coloring pair (Sum.inl firstInterior) := by
    exact hfirstData.2
  have hsecondSelected :
      pairActiveDart coloring pair (Sum.inl secondInterior) := by
    exact hsecondData.2
  let firstNeighbor := T.vert (Sum.inl (T.alpha firstInterior))
  let secondNeighbor := T.vert (Sum.inl (T.alpha secondInterior))
  have hfirstAdj : (primalKempeGraph T coloring pair).Adj
      vertex firstNeighbor := by
    have hadj := primalKempeGraph_adj_of_active_interior
      T coloring pair firstInterior hfirstSelected
    rw [hfirstData.1] at hadj
    exact hadj
  have hsecondAdj : (primalKempeGraph T coloring pair).Adj
      vertex secondNeighbor := by
    have hadj := primalKempeGraph_adj_of_active_interior
      T coloring pair secondInterior hsecondSelected
    rw [hsecondData.1] at hadj
    exact hadj
  have hneighborNe : firstNeighbor ≠ secondNeighbor := by
    intro heq
    have hinteriorEq : firstInterior = secondInterior :=
      hendpoint firstInterior secondInterior
        (hfirstData.1.trans hsecondData.1.symm)
        heq
    exact hfirstSecond (congrArg Sum.inl hinteriorEq)
  have hneighbors :
      (primalKempeGraph T coloring pair).neighborFinset vertex =
        {firstNeighbor, secondNeighbor} := by
    ext neighbor
    constructor
    · intro hneighbor
      have hadj : (primalKempeGraph T coloring pair).Adj vertex neighbor := by
        simpa using hneighbor
      rcases hadj with ⟨dart, hactive, hforward | hreverse⟩
      · have hdartMem : Sum.inl dart ∈
            activeDartsAt T coloring pair vertex :=
          (mem_activeDartsAt_iff T coloring pair vertex _).2
            ⟨hforward.1, hactive⟩
        rw [hactiveSet] at hdartMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hdartMem
        rcases hdartMem with hdart | hdart
        · have hdart' : dart = firstInterior := by
            simpa using hdart
          subst dart
          simp [firstNeighbor, hforward.2]
        · have hdart' : dart = secondInterior := by
            simpa using hdart
          subst dart
          simp [secondNeighbor, hforward.2]
      · have hactiveAlpha : pairActiveDart coloring pair
            (Sum.inl (T.alpha dart)) :=
          (pairActiveDart_alpha_iff T coloring pair dart).2 hactive
        have halphaMem : Sum.inl (T.alpha dart) ∈
            activeDartsAt T coloring pair vertex :=
          (mem_activeDartsAt_iff T coloring pair vertex _).2
            ⟨hreverse.2, hactiveAlpha⟩
        rw [hactiveSet] at halphaMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at halphaMem
        rcases halphaMem with halpha | halpha
        · have halpha' : T.alpha dart = firstInterior := by
            simpa using halpha
          have hneighborEq : neighbor = firstNeighbor := by
            calc
              neighbor = T.vert (Sum.inl dart) := hreverse.1.symm
              _ = T.vert (Sum.inl (T.alpha firstInterior)) := by
                rw [← halpha', T.alpha_involutive]
              _ = firstNeighbor := rfl
          simp [hneighborEq]
        · have halpha' : T.alpha dart = secondInterior := by
            simpa using halpha
          have hneighborEq : neighbor = secondNeighbor := by
            calc
              neighbor = T.vert (Sum.inl dart) := hreverse.1.symm
              _ = T.vert (Sum.inl (T.alpha secondInterior)) := by
                rw [← halpha', T.alpha_involutive]
              _ = secondNeighbor := rfl
          simp [hneighborEq]
    · intro hneighbor
      simp only [Finset.mem_insert, Finset.mem_singleton] at hneighbor
      rcases hneighbor with rfl | rfl
      · simpa using hfirstAdj
      · simpa using hsecondAdj
  rw [← (primalKempeGraph T coloring pair).card_neighborFinset_eq_degree,
    hneighbors]
  simp [hneighborNe]

/-- Active darts at one tangle vertex lie in the same physical component. -/
theorem kempeConnected_of_active_of_vert_eq
    (T : PortTangle V I P) (coloring : Coloring T)
    (pair : TaitColorPair) {first second : I ⊕ P}
    (hfirst : pairActiveDart coloring pair first)
    (hsecond : pairActiveDart coloring pair second)
    (hvert : T.vert first = T.vert second) :
    KempeConnected T coloring pair first second := by
  exact Relation.EqvGen.rel _ _ ⟨hfirst, hsecond, Or.inl hvert⟩

/-- Crossing an active interior edge is one physical common-web step. -/
theorem kempeConnected_interior_alpha
    (T : PortTangle V I P) (coloring : Coloring T)
    (pair : TaitColorPair) (dart : I)
    (hactive : pairActiveDart coloring pair (Sum.inl dart)) :
    KempeConnected T coloring pair
      (Sum.inl dart) (Sum.inl (T.alpha dart)) := by
  have hactiveAlpha :
      pairActiveDart coloring pair (Sum.inl (T.alpha dart)) :=
    (pairActiveDart_alpha_iff T coloring pair dart).2 hactive
  exact Relation.EqvGen.rel _ _
    ⟨hactive, hactiveAlpha, Or.inr ⟨dart, rfl, rfl⟩⟩

/-- One local common-web wire projects either to equality of primal vertices
or to one edge of the primal Kempe graph. -/
theorem kempeStep_primal_reachable
    (T : PortTangle V I P) (coloring : Coloring T)
    (pair : TaitColorPair) {first second : I ⊕ P}
    (hstep : GoertzelV24PortTangleCommonKempeWeb.KempeStep
      T coloring pair first second) :
    (primalKempeGraph T coloring pair).Reachable
      (T.vert first) (T.vert second) := by
  rcases hstep with ⟨hfirst, _hsecond, hvert | ⟨dart, rfl, rfl⟩⟩
  · rw [hvert]
  · exact (primalKempeGraph_adj_of_active_interior
      T coloring pair dart hfirst).reachable

/-- A physical dart-web connection projects to primal connectivity. -/
theorem kempeConnected_primal_reachable
    (T : PortTangle V I P) (coloring : Coloring T)
    (pair : TaitColorPair) {first second : I ⊕ P}
    (hconnected : KempeConnected T coloring pair first second) :
    (primalKempeGraph T coloring pair).Reachable
      (T.vert first) (T.vert second) := by
  induction hconnected with
  | rel first second hstep =>
      exact kempeStep_primal_reachable T coloring pair hstep
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond

/-- Lift one primal Kempe edge from an active dart based at its first
endpoint to an active dart based at its second endpoint. -/
theorem exists_kempeConnected_over_primalAdj
    (T : PortTangle V I P) (coloring : Coloring T)
    (pair : TaitColorPair) {first : I ⊕ P} {target : V}
    (hfirst : pairActiveDart coloring pair first)
    (hadj : (primalKempeGraph T coloring pair).Adj
      (T.vert first) target) :
    ∃ second : I ⊕ P,
      pairActiveDart coloring pair second ∧
        T.vert second = target ∧
        KempeConnected T coloring pair first second := by
  rcases hadj with ⟨dart, hactive, hforward | hreverse⟩
  · let second : I ⊕ P := Sum.inl (T.alpha dart)
    have hactiveSecond : pairActiveDart coloring pair second :=
      (pairActiveDart_alpha_iff T coloring pair dart).2 hactive
    have htoDart : KempeConnected T coloring pair first (Sum.inl dart) :=
      kempeConnected_of_active_of_vert_eq T coloring pair
        hfirst hactive hforward.1.symm
    have hacross := kempeConnected_interior_alpha
      T coloring pair dart hactive
    exact ⟨second, hactiveSecond, hforward.2,
      Relation.EqvGen.trans _ _ _ htoDart hacross⟩
  · let second : I ⊕ P := Sum.inl dart
    have hactiveAlpha :
        pairActiveDart coloring pair (Sum.inl (T.alpha dart)) :=
      (pairActiveDart_alpha_iff T coloring pair dart).2 hactive
    have htoAlpha : KempeConnected T coloring pair first
        (Sum.inl (T.alpha dart)) :=
      kempeConnected_of_active_of_vert_eq T coloring pair
        hfirst hactiveAlpha hreverse.2.symm
    have hacross := (kempeConnected_interior_alpha
      T coloring pair dart hactive).symm
    exact ⟨second, hactive, hreverse.1,
      Relation.EqvGen.trans _ _ _ htoAlpha hacross⟩

/-- Every primal path starting at an active dart can be lifted to a physical
common-web connection ending over the final primal vertex. -/
theorem exists_kempeConnected_over_primalReachable
    (T : PortTangle V I P) (coloring : Coloring T)
    (pair : TaitColorPair) {first : I ⊕ P} {target : V}
    (hfirst : pairActiveDart coloring pair first)
    (hreachable : (primalKempeGraph T coloring pair).Reachable
      (T.vert first) target) :
    ∃ second : I ⊕ P,
      pairActiveDart coloring pair second ∧
        T.vert second = target ∧
        KempeConnected T coloring pair first second := by
  rw [reachable_iff_reflTransGen] at hreachable
  induction hreachable with
  | refl => exact ⟨first, hfirst, rfl, Relation.EqvGen.refl _⟩
  | @tail middle target hprefix hadj ih =>
      rcases ih with ⟨middleDart, hmiddleActive, hmiddleVert,
        hfirstMiddle⟩
      have hadj' : (primalKempeGraph T coloring pair).Adj
          (T.vert middleDart) target := by
        rw [hmiddleVert]
        exact hadj
      rcases exists_kempeConnected_over_primalAdj
          T coloring pair hmiddleActive hadj' with
        ⟨targetDart, htargetActive, htargetVert, hmiddleTarget⟩
      exact ⟨targetDart, htargetActive, htargetVert,
        Relation.EqvGen.trans _ _ _ hfirstMiddle hmiddleTarget⟩

/-- **Exact primal/common-web connectivity equivalence.**  For active darts,
contracting vertex wires loses no component information. -/
theorem kempeConnected_iff_primal_reachable
    (T : PortTangle V I P) (coloring : Coloring T)
    (pair : TaitColorPair) {first second : I ⊕ P}
    (hfirst : pairActiveDart coloring pair first)
    (hsecond : pairActiveDart coloring pair second) :
    KempeConnected T coloring pair first second ↔
      (primalKempeGraph T coloring pair).Reachable
        (T.vert first) (T.vert second) := by
  constructor
  · exact kempeConnected_primal_reachable T coloring pair
  · intro hreachable
    rcases exists_kempeConnected_over_primalReachable
        T coloring pair hfirst hreachable with
      ⟨targetDart, htargetActive, htargetVert, hfirstTarget⟩
    have htargetSecond := kempeConnected_of_active_of_vert_eq
      T coloring pair htargetActive hsecond htargetVert
    exact Relation.EqvGen.trans _ _ _ hfirstTarget htargetSecond

/-- Common-web connectivity between active darts gives reachability in the
finite active-web graph.  This is the direction needed below without importing
the downstream physical-closure layer. -/
theorem activeWeb_reachable_of_kempeConnected
    (T : PortTangle V I P) (coloring : Coloring T)
    (pair : TaitColorPair)
    (first second : ActiveDart T coloring pair)
    (hconnected : KempeConnected T coloring pair first.1 second.1) :
    (activeWeb T coloring pair).Reachable first second := by
  let R : (I ⊕ P) → (I ⊕ P) → Prop := fun x y =>
    (pairActiveDart coloring pair x ↔ pairActiveDart coloring pair y) ∧
      ∀ (hx : pairActiveDart coloring pair x)
        (hy : pairActiveDart coloring pair y),
        (activeWeb T coloring pair).Reachable ⟨x, hx⟩ ⟨y, hy⟩
  have hR : Equivalence R := by
    constructor
    · intro x
      exact ⟨Iff.rfl, fun hx hy => by simpa using
        (SimpleGraph.Reachable.refl
          (⟨x, hx⟩ : ActiveDart T coloring pair))⟩
    · intro x y hxy
      exact ⟨hxy.1.symm, fun hy hx => (hxy.2 hx hy).symm⟩
    · intro x y z hxy hyz
      refine ⟨hxy.1.trans hyz.1, ?_⟩
      intro hx hz
      have hy : pairActiveDart coloring pair y := hxy.1.mp hx
      exact (hxy.2 hx hy).trans (hyz.2 hy hz)
  have hstep : ∀ x y, KempeStep T coloring pair x y → R x y := by
    intro x y hxy
    refine ⟨iff_of_true hxy.1 hxy.2.1, ?_⟩
    intro hx hy
    by_cases heq : x = y
    · subst y
      simpa using
        (SimpleGraph.Reachable.refl
          (⟨x, hx⟩ : ActiveDart T coloring pair))
    · rw [reachable_iff_reflTransGen]
      exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl
        ⟨by simpa using heq, hxy⟩
  have hEqv : Relation.EqvGen R first.1 second.1 :=
    Relation.EqvGen.mono hstep hconnected
  exact (hR.eqvGen_iff.mp hEqv).2 first.2 second.2

/-- If one physical component has no boundary port, its contraction to the
selected primal graph is a graph of cycles. -/
theorem primalKempeComponent_isCycles_of_boundaryFree
    (T : PortTangle V I P) (hcubic : IsCubic T)
    (hendpoint : InteriorEndpointInjective T)
    (coloring : Coloring T) (hproper : IsProper coloring)
    (pair : TaitColorPair) (root : ActiveDart T coloring pair)
    (hboundaryFree : componentPortDarts T coloring pair root = ∅) :
    ((primalKempeGraph T coloring pair).connectedComponentMk
      (T.vert root.1)).toSimpleGraph.IsCycles := by
  classical
  let primal := primalKempeGraph T coloring pair
  let component := primal.connectedComponentMk (T.vert root.1)
  intro vertex _hneighbors
  have hreach : primal.Reachable (T.vert root.1) vertex.1 :=
    component.reachable_of_mem_supp rfl vertex.2
  have hnoPort : ∀ port : P, T.vert (Sum.inr port) = vertex.1 →
      ¬pairActiveDart coloring pair (Sum.inr port) := by
    intro port hvert hactive
    let portDart : ActiveDart T coloring pair :=
      ⟨Sum.inr port, hactive⟩
    have hreachPort : primal.Reachable
        (T.vert root.1) (T.vert (Sum.inr port)) := by
      rw [hvert]
      exact hreach
    have hconnected : KempeConnected T coloring pair root.1 (Sum.inr port) :=
      (kempeConnected_iff_primal_reachable
        T coloring pair root.2 hactive).2 hreachPort
    have hwebReach : (activeWeb T coloring pair).Reachable root portDart :=
      activeWeb_reachable_of_kempeConnected
        T coloring pair root portDart hconnected
    have hmem : portDart ∈ (activeComponent T coloring pair root).supp := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff,
        SimpleGraph.ConnectedComponent.eq]
      exact hwebReach.symm
    let inComponent : activeComponent T coloring pair root :=
      ⟨portDart, hmem⟩
    have hportMem : inComponent ∈
        componentPortDarts T coloring pair root := by
      simp only [componentPortDarts, Finset.mem_filter, Finset.mem_univ,
        true_and, IsPortActiveDart]
      exact ⟨port, rfl⟩
    rw [hboundaryFree] at hportMem
    simp at hportMem
  have hparentDegree : primal.degree vertex.1 = 2 :=
    primalKempeGraph_degree_eq_two_of_no_active_port_at
      T hcubic hendpoint coloring hproper pair vertex.1 hnoPort
  let neighborEquiv : component.toSimpleGraph.neighborSet vertex ≃
      primal.neighborSet vertex.1 :=
    { toFun := fun neighbor =>
        ⟨neighbor.1.1,
          (component.toSimpleGraph_adj vertex.2 neighbor.1.2).1 neighbor.2⟩
      invFun := fun neighbor => by
        have hmem : neighbor.1 ∈ component.supp :=
          (component.mem_supp_congr_adj neighbor.2).mp vertex.2
        exact ⟨⟨neighbor.1, hmem⟩,
          (component.toSimpleGraph_adj vertex.2 hmem).2 neighbor.2⟩
      left_inv := fun neighbor => by
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv := fun neighbor => by
        apply Subtype.ext
        rfl }
  calc
    (component.toSimpleGraph.neighborSet vertex).ncard =
        Fintype.card (component.toSimpleGraph.neighborSet vertex) :=
      (Set.fintypeCard_eq_ncard _).symm
    _ = Fintype.card (primal.neighborSet vertex.1) :=
      Fintype.card_congr neighborEquiv
    _ = primal.degree vertex.1 :=
      primal.card_neighborSet_eq_degree vertex.1
    _ = 2 := hparentDegree

/-- A boundary-free physical component yields a simple cycle in the selected
primal graph through the base vertex of the chosen active dart. -/
theorem exists_primalKempeCycle_of_boundaryFree
    (T : PortTangle V I P) (hcubic : IsCubic T)
    (hendpoint : InteriorEndpointInjective T)
    (coloring : Coloring T) (hproper : IsProper coloring)
    (pair : TaitColorPair) (root : ActiveDart T coloring pair)
    (hboundaryFree : componentPortDarts T coloring pair root = ∅) :
    ∃ walk : (primalKempeGraph T coloring pair).Walk
        (T.vert root.1) (T.vert root.1),
      walk.IsCycle := by
  classical
  let primal := primalKempeGraph T coloring pair
  let component := primal.connectedComponentMk (T.vert root.1)
  let rootInComponent : component := ⟨T.vert root.1, rfl⟩
  have hcycles : component.toSimpleGraph.IsCycles :=
    primalKempeComponent_isCycles_of_boundaryFree
      T hcubic hendpoint coloring hproper pair root hboundaryFree
  have hrootNeighbors :
      (component.toSimpleGraph.neighborSet rootInComponent).Nonempty := by
    rcases hroot : root.1 with interior | port
    · have hadjParent : primal.Adj
          (T.vert root.1) (T.vert (Sum.inl (T.alpha interior))) := by
        have hadj := primalKempeGraph_adj_of_active_interior
          T coloring pair interior (hroot ▸ root.2)
        simpa [primal, hroot] using hadj
      have hneighborMem : T.vert (Sum.inl (T.alpha interior)) ∈
          component.supp :=
        component.mem_supp_of_adj_mem_supp rfl hadjParent
      let neighborInComponent : component :=
        ⟨T.vert (Sum.inl (T.alpha interior)), hneighborMem⟩
      exact ⟨neighborInComponent,
        (component.toSimpleGraph_adj rfl hneighborMem).2 hadjParent⟩
    · let portDart : ActiveDart T coloring pair :=
        ⟨Sum.inr port, hroot ▸ root.2⟩
      let rootInActive : activeComponent T coloring pair root := ⟨root, rfl⟩
      have hportMem : rootInActive ∈
          componentPortDarts T coloring pair root := by
        simp only [componentPortDarts, Finset.mem_filter, Finset.mem_univ,
          true_and, IsPortActiveDart]
        exact ⟨port, hroot⟩
      rw [hboundaryFree] at hportMem
      simp at hportMem
  rcases hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
      (c := component.toSimpleGraph.connectedComponentMk rootInComponent)
      (v := rootInComponent) rfl hrootNeighbors with
    ⟨walk, hwalk, _hsupport⟩
  refine ⟨(walk.map component.toSimpleGraph_hom).copy rfl rfl, ?_⟩
  simpa only [SimpleGraph.Walk.isCycle_copy] using
    hwalk.map Subtype.val_injective

/-- A physical common-web component supplies a simple path between the base
vertices of any two of its active darts. -/
theorem exists_primalKempePath
    (T : PortTangle V I P) (coloring : Coloring T)
    (pair : TaitColorPair) {first second : I ⊕ P}
    (hfirst : pairActiveDart coloring pair first)
    (hsecond : pairActiveDart coloring pair second)
    (hconnected : KempeConnected T coloring pair first second) :
    ∃ path : (primalKempeGraph T coloring pair).Walk
        (T.vert first) (T.vert second),
      path.IsPath := by
  exact ((kempeConnected_iff_primal_reachable
    T coloring pair hfirst hsecond).1 hconnected).exists_isPath

/-- Walks which start in two distinct physical common-web components have
disjoint primal edge lists.  A shared edge would give a shared endpoint;
prefixes of the two walks would then connect the two roots in the primal
Kempe graph, hence in the exact dart web. -/
theorem walk_edges_disjoint_of_not_kempeConnected
    (T : PortTangle V I P) (coloring : Coloring T)
    (pair : TaitColorPair) {first second : I ⊕ P}
    (hfirst : pairActiveDart coloring pair first)
    (hsecond : pairActiveDart coloring pair second)
    (hnotConnected : ¬KempeConnected T coloring pair first second)
    {firstTarget secondTarget : V}
    (firstWalk : (primalKempeGraph T coloring pair).Walk
      (T.vert first) firstTarget)
    (secondWalk : (primalKempeGraph T coloring pair).Walk
      (T.vert second) secondTarget) :
    firstWalk.edges.Disjoint secondWalk.edges := by
  rw [List.disjoint_left]
  intro edge hfirstEdge hsecondEdge
  induction edge using Sym2.inductionOn with
  | _ left right =>
      have hleftFirst : left ∈ firstWalk.support :=
        firstWalk.fst_mem_support_of_mem_edges hfirstEdge
      have hleftSecond : left ∈ secondWalk.support :=
        secondWalk.fst_mem_support_of_mem_edges hsecondEdge
      have hfirstReach : (primalKempeGraph T coloring pair).Reachable
          (T.vert first) left :=
        ⟨firstWalk.takeUntil left hleftFirst⟩
      have hsecondReach : (primalKempeGraph T coloring pair).Reachable
          (T.vert second) left :=
        ⟨secondWalk.takeUntil left hleftSecond⟩
      apply hnotConnected
      exact (kempeConnected_iff_primal_reachable
        T coloring pair hfirst hsecond).2
          (hfirstReach.trans hsecondReach.symm)

end

end GoertzelV24PortTanglePrimalKempeGraph

end Mettapedia.GraphTheory.FourColor
