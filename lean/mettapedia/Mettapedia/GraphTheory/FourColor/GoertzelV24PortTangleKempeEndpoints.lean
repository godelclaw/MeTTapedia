import Mettapedia.GraphTheory.FourColor.GoertzelV24FinitePathEndpointCount
import Mettapedia.GraphTheory.FourColor.GoertzelV24PortTangleCommonKempeWeb
import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Two-ended components of a finite cubic port-tangle Kempe web

This file connects the literal common-web relation to the finite path endpoint
count.  The active darts at each cubic vertex form a pair.  Pairing those two
darts at the vertex and pairing the two halves of every interior edge gives a
graph in which ports have degree one and interior darts have degree two.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24PortTangleKempeEndpoints

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

open SimpleGraph
open GoertzelV24PortTangleGluing
open GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24PortTangleCutParity
open GoertzelV24HexagonPairingTargetAwareBoundary
open GoertzelV24PortTangleCommonKempeWeb
open GoertzelV24FinitePathEndpointCount

universe u

variable {V I P : Type u}
  [Fintype V] [Fintype I] [Fintype P]
  [DecidableEq V] [DecidableEq I] [DecidableEq P]

private instance pairActiveDartDecidable
    (T : PortTangle V I P) (coloring : Coloring T)
    (pair : TaitColorPair) (dart : I ⊕ P) :
    Decidable (pairActiveDart coloring pair dart) := by
  unfold pairActiveDart pairActiveColor Color.twoColor
  infer_instance

/-- Active darts incident with one vertex. -/
def activeDartsAt (T : PortTangle V I P) (coloring : Coloring T)
    (pair : TaitColorPair) (vertex : V) : Finset (I ⊕ P) :=
  (dartsAt T vertex).filter fun dart => pairActiveDart coloring pair dart

@[simp] theorem mem_activeDartsAt_iff
    (T : PortTangle V I P) (coloring : Coloring T)
    (pair : TaitColorPair) (vertex : V) (dart : I ⊕ P) :
    dart ∈ activeDartsAt T coloring pair vertex ↔
      T.vert dart = vertex ∧ pairActiveDart coloring pair dart := by
  simp [activeDartsAt, dartsAt]

/-- Exactly two darts at a proper cubic vertex carry either colour of a fixed
Tait pair. -/
theorem card_activeDartsAt_eq_two
    (T : PortTangle V I P) (hcubic : IsCubic T)
    (coloring : Coloring T) (hproper : IsProper coloring)
    (pair : TaitColorPair) (vertex : V) :
    (activeDartsAt T coloring pair vertex).card = 2 := by
  have hcard := hcubic vertex
  rcases Finset.card_eq_three.mp hcard with
    ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hset⟩
  have hfirstMem : first ∈ dartsAt T vertex := by rw [hset]; simp
  have hsecondMem : second ∈ dartsAt T vertex := by rw [hset]; simp
  have hthirdMem : third ∈ dartsAt T vertex := by rw [hset]; simp
  have hfirstVert : T.vert first = vertex := by
    simpa [dartsAt] using hfirstMem
  have hsecondVert : T.vert second = vertex := by
    simpa [dartsAt] using hsecondMem
  have hthirdVert : T.vert third = vertex := by
    simpa [dartsAt] using hthirdMem
  have hfirstNonzero := hproper.1 first
  have hsecondNonzero := hproper.1 second
  have hthirdNonzero := hproper.1 third
  have hcolorFirstSecond : coloring.color first ≠ coloring.color second :=
    hproper.2 first second (hfirstVert.trans hsecondVert.symm) hfirstSecond
  have hcolorFirstThird : coloring.color first ≠ coloring.color third :=
    hproper.2 first third (hfirstVert.trans hthirdVert.symm) hfirstThird
  have hcolorSecondThird : coloring.color second ≠ coloring.color third :=
    hproper.2 second third (hsecondVert.trans hthirdVert.symm) hsecondThird
  rw [activeDartsAt, hset]
  simp only [Finset.filter_insert, Finset.filter_singleton]
  cases pair <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero
      (coloring.color first) hfirstNonzero with hfirst | hfirst | hfirst <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero
      (coloring.color second) hsecondNonzero with hsecond | hsecond | hsecond <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero
      (coloring.color third) hthirdNonzero with hthird | hthird | hthird <;>
    simp_all [pairActiveDart, pairActiveColor, Color.twoColor,
      TaitColorPair.colors, red, blue, purple]

/-- Active darts as a finite carrier. -/
abbrev ActiveDart (T : PortTangle V I P) (coloring : Coloring T)
    (pair : TaitColorPair) :=
  {dart : I ⊕ P // pairActiveDart coloring pair dart}

/-- Every active dart has a unique other active dart at its vertex. -/
theorem existsUnique_vertexPartner
    (T : PortTangle V I P) (hcubic : IsCubic T)
    (coloring : Coloring T) (hproper : IsProper coloring)
    (pair : TaitColorPair)
    (dart : ActiveDart T coloring pair) :
    ∃! other : ActiveDart T coloring pair,
      other ≠ dart ∧ T.vert other.1 = T.vert dart.1 := by
  have hdartMem :
      dart.1 ∈ activeDartsAt T coloring pair (T.vert dart.1) :=
    (mem_activeDartsAt_iff T coloring pair _ _).2 ⟨rfl, dart.2⟩
  have hcard := card_activeDartsAt_eq_two T hcubic coloring hproper pair
    (T.vert dart.1)
  rcases Finset.card_eq_two.mp hcard with ⟨first, second, hne, hset⟩
  have hdartCases : dart.1 = first ∨ dart.1 = second := by
    rw [hset] at hdartMem
    simpa [eq_comm] using hdartMem
  rcases hdartCases with hfirst | hsecond
  · have hsecondMem : second ∈ activeDartsAt T coloring pair (T.vert dart.1) := by
      rw [hset]
      simp
    have hsecondData :=
      (mem_activeDartsAt_iff T coloring pair _ second).1 hsecondMem
    let other : ActiveDart T coloring pair := ⟨second, hsecondData.2⟩
    refine ⟨other, ?_, ?_⟩
    · constructor
      · intro heq
        have : second = first := by
          simpa [other, hfirst] using congrArg Subtype.val heq
        exact hne this.symm
      · exact hsecondData.1
    · intro candidate hcand
      apply Subtype.ext
      have hcandMem :
          candidate.1 ∈ activeDartsAt T coloring pair (T.vert dart.1) :=
        (mem_activeDartsAt_iff T coloring pair _ _).2
          ⟨hcand.2, candidate.2⟩
      rw [hset] at hcandMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcandMem
      rcases hcandMem with hcandFirst | hcandSecond
      · exfalso
        apply hcand.1
        apply Subtype.ext
        exact hcandFirst.trans hfirst.symm
      · exact hcandSecond
  · have hfirstMem : first ∈ activeDartsAt T coloring pair (T.vert dart.1) := by
      rw [hset]
      simp
    have hfirstData :=
      (mem_activeDartsAt_iff T coloring pair _ first).1 hfirstMem
    let other : ActiveDart T coloring pair := ⟨first, hfirstData.2⟩
    refine ⟨other, ?_, ?_⟩
    · constructor
      · intro heq
        have : first = second := by
          simpa [other, hsecond] using congrArg Subtype.val heq
        exact hne this
      · exact hfirstData.1
    · intro candidate hcand
      apply Subtype.ext
      have hcandMem :
          candidate.1 ∈ activeDartsAt T coloring pair (T.vert dart.1) :=
        (mem_activeDartsAt_iff T coloring pair _ _).2
          ⟨hcand.2, candidate.2⟩
      rw [hset] at hcandMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcandMem
      rcases hcandMem with hcandFirst | hcandSecond
      · exact hcandFirst
      · exfalso
        apply hcand.1
        apply Subtype.ext
        exact hcandSecond.trans hsecond.symm

/-- The unique other active dart at the same cubic vertex. -/
noncomputable def vertexPartner
    (T : PortTangle V I P) (hcubic : IsCubic T)
    (coloring : Coloring T) (hproper : IsProper coloring)
    (pair : TaitColorPair)
    (dart : ActiveDart T coloring pair) : ActiveDart T coloring pair :=
  Classical.choose
    (existsUnique_vertexPartner T hcubic coloring hproper pair dart)

theorem vertexPartner_spec
    (T : PortTangle V I P) (hcubic : IsCubic T)
    (coloring : Coloring T) (hproper : IsProper coloring)
    (pair : TaitColorPair)
    (dart : ActiveDart T coloring pair) :
    vertexPartner T hcubic coloring hproper pair dart ≠ dart ∧
      T.vert (vertexPartner T hcubic coloring hproper pair dart).1 =
        T.vert dart.1 :=
  (Classical.choose_spec
    (existsUnique_vertexPartner T hcubic coloring hproper pair dart)).1

theorem eq_vertexPartner_of_ne_of_vert_eq
    (T : PortTangle V I P) (hcubic : IsCubic T)
    (coloring : Coloring T) (hproper : IsProper coloring)
    (pair : TaitColorPair)
    (dart other : ActiveDart T coloring pair)
    (hne : other ≠ dart) (hvert : T.vert other.1 = T.vert dart.1) :
    other = vertexPartner T hcubic coloring hproper pair dart :=
  (Classical.choose_spec
    (existsUnique_vertexPartner T hcubic coloring hproper pair dart)).2
      other ⟨hne, hvert⟩

/-- The active dart across the interior edge containing `dart`. -/
def edgePartner
    (T : PortTangle V I P) (coloring : Coloring T)
    (pair : TaitColorPair) (dart : I)
    (hactive : pairActiveDart coloring pair (Sum.inl dart)) :
    ActiveDart T coloring pair :=
  ⟨Sum.inl (T.alpha dart),
    (pairActiveDart_alpha_iff T coloring pair dart).2 hactive⟩

theorem kempeStep_symm
    (T : PortTangle V I P) (coloring : Coloring T)
    (pair : TaitColorPair) {first second : I ⊕ P}
    (hstep : KempeStep T coloring pair first second) :
    KempeStep T coloring pair second first := by
  rcases hstep with ⟨hfirst, hsecond, hvertex | ⟨dart, rfl, rfl⟩⟩
  · exact ⟨hsecond, hfirst, Or.inl hvertex.symm⟩
  · refine ⟨hsecond, hfirst, Or.inr ⟨T.alpha dart, rfl, ?_⟩⟩
    simp [T.alpha_involutive]

/-- The finite undirected graph of the physical bichromatic web.  Its vertices
are active darts; its edges alternately cross a cubic vertex or an interior
edge. -/
def activeWeb
    (T : PortTangle V I P) (coloring : Coloring T)
    (pair : TaitColorPair) :
    SimpleGraph (ActiveDart T coloring pair) where
  Adj first second :=
    first ≠ second ∧ KempeStep T coloring pair first.1 second.1
  symm := ⟨by
    intro first second h
    exact ⟨Ne.symm h.1, kempeStep_symm T coloring pair h.2⟩⟩
  loopless := ⟨by
    intro dart h
    exact h.1 rfl⟩

theorem activeWeb_adj_port_iff
    (T : PortTangle V I P) (hcubic : IsCubic T)
    (coloring : Coloring T) (hproper : IsProper coloring)
    (pair : TaitColorPair) (port : P)
    (hactive : pairActiveDart coloring pair (Sum.inr port))
    (other : ActiveDart T coloring pair) :
    (activeWeb T coloring pair).Adj ⟨Sum.inr port, hactive⟩ other ↔
      other = vertexPartner T hcubic coloring hproper pair
        ⟨Sum.inr port, hactive⟩ := by
  constructor
  · rintro ⟨hne, _, _, hvertex | hedge⟩
    · exact eq_vertexPartner_of_ne_of_vert_eq T hcubic coloring hproper pair
        _ other hne.symm hvertex.symm
    · rcases hedge with ⟨dart, hfalse, _⟩
      cases hfalse
  · intro heq
    subst other
    have hspec := vertexPartner_spec T hcubic coloring hproper pair
      ⟨Sum.inr port, hactive⟩
    exact ⟨hspec.1.symm, hactive,
      (vertexPartner T hcubic coloring hproper pair
        ⟨Sum.inr port, hactive⟩).2,
      Or.inl hspec.2.symm⟩

theorem activeWeb_adj_interior_iff
    (T : PortTangle V I P) (hcubic : IsCubic T)
    (coloring : Coloring T) (hproper : IsProper coloring)
    (pair : TaitColorPair) (dart : I)
    (hactive : pairActiveDart coloring pair (Sum.inl dart))
    (other : ActiveDart T coloring pair) :
    (activeWeb T coloring pair).Adj ⟨Sum.inl dart, hactive⟩ other ↔
      other = vertexPartner T hcubic coloring hproper pair
          ⟨Sum.inl dart, hactive⟩ ∨
        other = edgePartner T coloring pair dart hactive := by
  constructor
  · rintro ⟨hne, _, _, hvertex | hedge⟩
    · exact Or.inl
        (eq_vertexPartner_of_ne_of_vert_eq T hcubic coloring hproper pair
          _ other hne.symm hvertex.symm)
    · rcases hedge with ⟨edge, hedge, hother⟩
      have hedgeEq : edge = dart := by simpa using hedge.symm
      subst edge
      exact Or.inr (Subtype.ext hother)
  · rintro (heq | heq)
    · subst other
      have hspec := vertexPartner_spec T hcubic coloring hproper pair
        ⟨Sum.inl dart, hactive⟩
      exact ⟨hspec.1.symm, hactive,
        (vertexPartner T hcubic coloring hproper pair
          ⟨Sum.inl dart, hactive⟩).2,
        Or.inl hspec.2.symm⟩
    · subst other
      refine ⟨?_, hactive,
        (edgePartner T coloring pair dart hactive).2,
        Or.inr ⟨dart, rfl, rfl⟩⟩
      intro heq
      have halpha : T.alpha dart = dart := by
        simpa [edgePartner] using (congrArg Subtype.val heq).symm
      exact T.alpha_fixfree dart halpha

theorem vertexPartner_ne_edgePartner
    (T : PortTangle V I P) (hcubic : IsCubic T)
    (coloring : Coloring T) (hproper : IsProper coloring)
    (pair : TaitColorPair) (dart : I)
    (hactive : pairActiveDart coloring pair (Sum.inl dart)) :
    vertexPartner T hcubic coloring hproper pair
        ⟨Sum.inl dart, hactive⟩ ≠
      edgePartner T coloring pair dart hactive := by
  intro heq
  have hvertex := (vertexPartner_spec T hcubic coloring hproper pair
    ⟨Sum.inl dart, hactive⟩).2
  have : T.vert (Sum.inl (T.alpha dart)) = T.vert (Sum.inl dart) := by
    simpa [edgePartner] using
      (congrArg (fun active => T.vert active.1) heq).symm.trans hvertex
  exact T.no_self_loops dart this.symm

noncomputable instance activeDartFintype
    (T : PortTangle V I P) (coloring : Coloring T)
    (pair : TaitColorPair) : Fintype (ActiveDart T coloring pair) :=
  Fintype.ofFinite _

noncomputable instance activeWebAdjDecidable
    (T : PortTangle V I P) (coloring : Coloring T)
    (pair : TaitColorPair) : DecidableRel (activeWeb T coloring pair).Adj :=
  Classical.decRel _

/-- An active port has exactly one neighbour in the web: its partner at the
same cubic vertex. -/
theorem activeWeb_degree_port_eq_one
    (T : PortTangle V I P) (hcubic : IsCubic T)
    (coloring : Coloring T) (hproper : IsProper coloring)
    (pair : TaitColorPair) (port : P)
    (hactive : pairActiveDart coloring pair (Sum.inr port)) :
    (activeWeb T coloring pair).degree ⟨Sum.inr port, hactive⟩ = 1 := by
  classical
  rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
  refine ⟨vertexPartner T hcubic coloring hproper pair
      ⟨Sum.inr port, hactive⟩, ?_, ?_⟩
  · exact (activeWeb_adj_port_iff T hcubic coloring hproper pair
      port hactive _).2 rfl
  · intro other hother
    exact (activeWeb_adj_port_iff T hcubic coloring hproper pair
      port hactive other).1 hother

/-- An active interior dart has exactly two neighbours in the web: its partner
at the vertex and its partner across the interior edge. -/
theorem activeWeb_degree_interior_eq_two
    (T : PortTangle V I P) (hcubic : IsCubic T)
    (coloring : Coloring T) (hproper : IsProper coloring)
    (pair : TaitColorPair) (dart : I)
    (hactive : pairActiveDart coloring pair (Sum.inl dart)) :
    (activeWeb T coloring pair).degree ⟨Sum.inl dart, hactive⟩ = 2 := by
  classical
  have hneighbors :
      (activeWeb T coloring pair).neighborFinset
          ⟨Sum.inl dart, hactive⟩ =
        {vertexPartner T hcubic coloring hproper pair
            ⟨Sum.inl dart, hactive⟩,
          edgePartner T coloring pair dart hactive} := by
    ext other
    rw [SimpleGraph.mem_neighborFinset,
      activeWeb_adj_interior_iff T hcubic coloring hproper pair
        dart hactive other]
    simp
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hneighbors]
  simp [vertexPartner_ne_edgePartner T hcubic coloring hproper pair dart hactive]

/-- Active boundary darts are exactly the degree-one vertices of the common
web; active interior darts have degree two. -/
def IsPortActiveDart
    (dart : ActiveDart (T : PortTangle V I P) coloring pair) : Prop :=
  ∃ port : P, dart.1 = Sum.inr port

theorem activeWeb_degree_eq_one_iff_isPort
    (T : PortTangle V I P) (hcubic : IsCubic T)
    (coloring : Coloring T) (hproper : IsProper coloring)
    (pair : TaitColorPair)
    (dart : ActiveDart T coloring pair) :
    (activeWeb T coloring pair).degree dart = 1 ↔
      IsPortActiveDart dart := by
  classical
  rcases dart with ⟨dart, hactive⟩
  rcases dart with interior | port
  · constructor
    · intro hone
      have htwo := activeWeb_degree_interior_eq_two T hcubic coloring hproper
        pair interior hactive
      omega
    · rintro ⟨port, hfalse⟩
      cases hfalse
  · constructor
    · intro _
      exact ⟨port, rfl⟩
    · intro _
      exact activeWeb_degree_port_eq_one T hcubic coloring hproper pair
        port hactive

/-- The connected component of one active dart in the physical web. -/
abbrev activeComponent
    (T : PortTangle V I P) (coloring : Coloring T)
    (pair : TaitColorPair) (root : ActiveDart T coloring pair) :=
  (activeWeb T coloring pair).connectedComponentMk root

noncomputable instance activeComponentFintype
    (T : PortTangle V I P) (coloring : Coloring T)
    (pair : TaitColorPair) (root : ActiveDart T coloring pair) :
    Fintype (activeComponent T coloring pair root) :=
  Fintype.ofFinite _

noncomputable instance activeComponentAdjDecidable
    (T : PortTangle V I P) (coloring : Coloring T)
    (pair : TaitColorPair) (root : ActiveDart T coloring pair) :
    DecidableRel (activeComponent T coloring pair root).toSimpleGraph.Adj :=
  Classical.decRel _

/-- Boundary darts lying in the component of `root`. -/
noncomputable def componentPortDarts
    (T : PortTangle V I P) (coloring : Coloring T)
    (pair : TaitColorPair) (root : ActiveDart T coloring pair) :
    Finset (activeComponent T coloring pair root) := by
  classical
  exact Finset.univ.filter fun dart => IsPortActiveDart dart.1

/-- Passing to a connected component of the web does not remove any neighbour,
so it preserves every vertex degree. -/
theorem activeComponent_degree_eq
    (T : PortTangle V I P) (coloring : Coloring T)
    (pair : TaitColorPair) (root : ActiveDart T coloring pair)
    (dart : activeComponent T coloring pair root) :
    (activeComponent T coloring pair root).toSimpleGraph.degree dart =
      (activeWeb T coloring pair).degree dart.1 := by
  let graph := activeWeb T coloring pair
  let component := activeComponent T coloring pair root
  let neighbors : component.toSimpleGraph.neighborSet dart ≃
      graph.neighborSet dart.1 :=
    { toFun := fun other =>
        ⟨other.1.1,
          (component.toSimpleGraph_adj dart.2 other.1.2).1 other.2⟩
      invFun := fun other => by
        have hmem : other.1 ∈ component.supp :=
          (component.mem_supp_congr_adj other.2).mp dart.2
        exact ⟨⟨other.1, hmem⟩,
          (component.toSimpleGraph_adj dart.2 hmem).2 other.2⟩
      left_inv := fun other => by
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv := fun other => by
        apply Subtype.ext
        rfl }
  rw [← component.toSimpleGraph.card_neighborSet_eq_degree,
    ← graph.card_neighborSet_eq_degree]
  exact Fintype.card_congr neighbors

theorem activeComponent_degree_eq_one_iff_isPort
    (T : PortTangle V I P) (hcubic : IsCubic T)
    (coloring : Coloring T) (hproper : IsProper coloring)
    (pair : TaitColorPair) (root : ActiveDart T coloring pair)
    (dart : activeComponent T coloring pair root) :
    (activeComponent T coloring pair root).toSimpleGraph.degree dart = 1 ↔
      IsPortActiveDart dart.1 := by
  rw [activeComponent_degree_eq T coloring pair root dart]
  exact activeWeb_degree_eq_one_iff_isPort T hcubic coloring hproper pair dart.1

/-- **Two-ended common-web theorem.**  Every physical bichromatic component
that meets the boundary contains exactly two active boundary darts. -/
theorem card_componentPortDarts_eq_two
    (T : PortTangle V I P) (hcubic : IsCubic T)
    (coloring : Coloring T) (hproper : IsProper coloring)
    (pair : TaitColorPair) (port : P)
    (hactive : pairActiveDart coloring pair (Sum.inr port)) :
    (componentPortDarts T coloring pair
      ⟨Sum.inr port, hactive⟩).card = 2 := by
  classical
  let root : ActiveDart T coloring pair := ⟨Sum.inr port, hactive⟩
  let component := activeComponent T coloring pair root
  have hdegree (dart : component) :
      component.toSimpleGraph.degree dart = 1 ∨
        component.toSimpleGraph.degree dart = 2 := by
    rw [activeComponent_degree_eq T coloring pair root dart]
    rcases dart.1 with ⟨dart, hdartActive⟩
    rcases dart with interior | boundary
    · exact Or.inr (activeWeb_degree_interior_eq_two T hcubic coloring
        hproper pair interior hdartActive)
    · exact Or.inl (activeWeb_degree_port_eq_one T hcubic coloring
        hproper pair boundary hdartActive)
  let rootInComponent : component := ⟨root, rfl⟩
  have hrootDegree : component.toSimpleGraph.degree rootInComponent = 1 := by
    rw [activeComponent_degree_eq T coloring pair root rootInComponent]
    exact activeWeb_degree_port_eq_one T hcubic coloring hproper pair
      port hactive
  have hendpoints := card_degreeOneVertices_eq_two component.toSimpleGraph
    component.connected_toSimpleGraph hdegree rootInComponent hrootDegree
  have hidentify :
      componentPortDarts T coloring pair root =
        degreeOneVertices component.toSimpleGraph := by
    ext dart
    rw [mem_degreeOneVertices_iff]
    simp only [componentPortDarts, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (activeComponent_degree_eq_one_iff_isPort T hcubic coloring hproper
      pair root dart).symm
  rw [hidentify]
  exact hendpoints

/-- A physical bichromatic component with no boundary dart is a graph of
cycles.  The statement is deliberately about the exact active-dart web:
contracting its vertex wires to obtain an ambient primal cycle is a separate
geometric operation. -/
theorem activeComponent_isCycles_of_componentPortDarts_eq_empty
    (T : PortTangle V I P) (hcubic : IsCubic T)
    (coloring : Coloring T) (hproper : IsProper coloring)
    (pair : TaitColorPair) (root : ActiveDart T coloring pair)
    (hboundaryFree : componentPortDarts T coloring pair root = ∅) :
    (activeComponent T coloring pair root).toSimpleGraph.IsCycles := by
  intro dart _hneighbors
  calc
    ((activeComponent T coloring pair root).toSimpleGraph.neighborSet
        dart).ncard =
        Fintype.card
          ((activeComponent T coloring pair root).toSimpleGraph.neighborSet
            dart) := (Set.fintypeCard_eq_ncard _).symm
    _ = (activeComponent T coloring pair root).toSimpleGraph.degree dart :=
      (activeComponent T coloring pair root).toSimpleGraph
        |>.card_neighborSet_eq_degree dart
    _ = (activeWeb T coloring pair).degree dart.1 :=
      activeComponent_degree_eq T coloring pair root dart
    _ = 2 := by
      rcases hdart : dart.1.1 with interior | port
      · let interiorDart : ActiveDart T coloring pair :=
          ⟨Sum.inl interior, hdart ▸ dart.1.2⟩
        have hinteriorDart : interiorDart = dart.1 := by
          apply Subtype.ext
          exact hdart.symm
        rw [← hinteriorDart]
        exact activeWeb_degree_interior_eq_two T hcubic coloring hproper
          pair interior (hdart ▸ dart.1.2)
      · have hport : dart ∈ componentPortDarts T coloring pair root := by
          simp only [componentPortDarts, Finset.mem_filter, Finset.mem_univ,
            true_and, IsPortActiveDart]
          exact ⟨port, hdart⟩
        rw [hboundaryFree] at hport
        simp at hport

/-- A boundary-free physical bichromatic component contains a simple closed
walk through its chosen root. -/
theorem exists_activeComponent_cycle_of_componentPortDarts_eq_empty
    (T : PortTangle V I P) (hcubic : IsCubic T)
    (coloring : Coloring T) (hproper : IsProper coloring)
    (pair : TaitColorPair) (root : ActiveDart T coloring pair)
    (hboundaryFree : componentPortDarts T coloring pair root = ∅) :
    ∃ walk : (activeComponent T coloring pair root).toSimpleGraph.Walk
        (⟨root, rfl⟩ : activeComponent T coloring pair root)
        (⟨root, rfl⟩ : activeComponent T coloring pair root),
      walk.IsCycle := by
  let component := activeComponent T coloring pair root
  let rootInComponent : component := ⟨root, rfl⟩
  have hcycles : component.toSimpleGraph.IsCycles :=
    activeComponent_isCycles_of_componentPortDarts_eq_empty
      T hcubic coloring hproper pair root hboundaryFree
  have hrootDegree : component.toSimpleGraph.degree rootInComponent = 2 := by
    rw [activeComponent_degree_eq T coloring pair root rootInComponent]
    change (activeWeb T coloring pair).degree root = 2
    rcases hdart : root.1 with interior | port
    · let interiorDart : ActiveDart T coloring pair :=
        ⟨Sum.inl interior, hdart ▸ root.2⟩
      have hinteriorDart : interiorDart = root := by
        apply Subtype.ext
        exact hdart.symm
      rw [← hinteriorDart]
      exact activeWeb_degree_interior_eq_two T hcubic coloring hproper
        pair interior (hdart ▸ root.2)
    · have hport : rootInComponent ∈
          componentPortDarts T coloring pair root := by
        simp only [componentPortDarts, Finset.mem_filter, Finset.mem_univ,
          true_and, IsPortActiveDart]
        exact ⟨port, hdart⟩
      rw [hboundaryFree] at hport
      simp at hport
  have hrootNeighbors :
      (component.toSimpleGraph.neighborSet rootInComponent).Nonempty := by
    rcases (component.toSimpleGraph.degree_pos_iff_exists_adj
        rootInComponent).1 (by omega) with ⟨neighbor, hadj⟩
    exact ⟨neighbor, hadj⟩
  rcases hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
      (c := component.toSimpleGraph.connectedComponentMk rootInComponent)
      (v := rootInComponent) rfl hrootNeighbors with
    ⟨walk, hwalk, _hsupport⟩
  exact ⟨walk, hwalk⟩

end GoertzelV24PortTangleKempeEndpoints

end Mettapedia.GraphTheory.FourColor
