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

theorem primalKempeGraph_adj_of_active_interior
    (T : PortTangle V I P) (coloring : Coloring T)
    (pair : TaitColorPair) (dart : I)
    (hactive : pairActiveDart coloring pair (Sum.inl dart)) :
    (primalKempeGraph T coloring pair).Adj
      (T.vert (Sum.inl dart))
      (T.vert (Sum.inl (T.alpha dart))) := by
  exact ⟨dart, hactive, Or.inl ⟨rfl, rfl⟩⟩

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
