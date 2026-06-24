import Mathlib.Combinatorics.SimpleGraph.Paths

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

variable {V : Type*}

/-- An edge crosses a vertex-side predicate when its two endpoints occur on opposite sides.
This is the graph-theoretic edge-cut predicate, independent of any planar embedding. -/
def EdgeCrossesVertexSide (G : SimpleGraph V) (side : V → Prop) (e : G.edgeSet) : Prop :=
  ∃ u v : V, u ∈ (e : Sym2 V) ∧ v ∈ (e : Sym2 V) ∧ side u ∧ ¬ side v

/-- A walk from one side of a vertex cut to the other must use a crossing edge.  This is the
pure graph-theoretic separator lemma needed below the planar/Jordan CAP5 argument. -/
theorem exists_edgeCrossesVertexSide_of_walk_endpoint_sides
    {G : SimpleGraph V} (side : V → Prop) {u v : V}
    (p : G.Walk u v) (hu : side u) (hv : ¬ side v) :
    ∃ e : G.edgeSet, (e : Sym2 V) ∈ p.edges ∧ EdgeCrossesVertexSide G side e := by
  induction p with
  | nil =>
      exact (hv hu).elim
  | @cons u' v' w' hadj p ih =>
      by_cases hv' : side v'
      · rcases ih hv' hv with ⟨e, heEdges, hcross⟩
        exact ⟨e, by simp [Walk.edges_cons, heEdges], hcross⟩
      · let e : G.edgeSet := ⟨s(u', v'), hadj⟩
        refine ⟨e, by simp [e], ?_⟩
        refine ⟨u', v', by simp [e], by simp [e], hu, hv'⟩

/-- Crossing a vertex-side predicate is invariant under swapping the two sides. -/
theorem edgeCrossesVertexSide_compl (G : SimpleGraph V) (side : V → Prop) (e : G.edgeSet) :
    EdgeCrossesVertexSide G (fun v => ¬ side v) e ↔ EdgeCrossesVertexSide G side e := by
  classical
  constructor
  · rintro ⟨u, v, hu, hv, hnotSide, hnotNotSide⟩
    exact ⟨v, u, hv, hu, by_contra fun h => hnotNotSide h, hnotSide⟩
  · rintro ⟨u, v, hu, hv, hside, hnotSide⟩
    exact ⟨v, u, hv, hu, hnotSide, fun h => h hside⟩

/-- An edge that does not cross a side predicate preserves that side between any two listed
endpoints.  This is the local graph fact that turns an exact crossing-edge classification into
the side-preservation interface used by cyclic-cut realization data. -/
theorem not_edgeCrossesVertexSide_iff_forall_side_iff
    (G : SimpleGraph V) (side : V → Prop) (e : G.edgeSet) :
    (¬ EdgeCrossesVertexSide G side e) ↔
      ∀ u v : V, u ∈ (e : Sym2 V) → v ∈ (e : Sym2 V) → (side u ↔ side v) := by
  constructor
  · intro hnotCross u v hu hv
    constructor
    · intro hsu
      by_contra hsv
      exact hnotCross ⟨u, v, hu, hv, hsu, hsv⟩
    · intro hsv
      by_contra hsu
      exact hnotCross ⟨v, u, hv, hu, hsv, hsu⟩
  · intro hpreserve hcross
    rcases hcross with ⟨u, v, hu, hv, hsu, hsv⟩
    exact hsv ((hpreserve u v hu hv).1 hsu)

/-- An unordered pair with two distinct listed members is exactly the unordered pair of those
members. -/
theorem sym2_eq_mk_of_mem_of_mem_of_ne
    {u v : V} {e : Sym2 V} (hu : u ∈ e) (hv : v ∈ e) (hne : u ≠ v) :
    e = s(u, v) := by
  rcases Sym2.mem_iff_exists.1 hu with ⟨w, rfl⟩
  rw [Sym2.mem_iff] at hv
  rcases hv with hv | hv
  · exact (hne hv.symm).elim
  · rw [hv]

/-- A side-crossing graph edge gives a one-edge walk whose edge list is exactly that edge.  This
is the local graph fact needed to convert a Jordan/path-separation statement into exact
crossing-edge equality. -/
theorem exists_walk_edges_eq_singleton_of_edge_endpoint_sides
    {G : SimpleGraph V} {side : V → Prop} {e : G.edgeSet} {u v : V}
    (hu : u ∈ (e : Sym2 V)) (hv : v ∈ (e : Sym2 V))
    (hsu : side u) (hsv : ¬ side v) :
    ∃ p : G.Walk u v, p.edges = [(e : Sym2 V)] := by
  have hne : u ≠ v := fun huv => hsv (huv ▸ hsu)
  have heq : (e : Sym2 V) = s(u, v) :=
    sym2_eq_mk_of_mem_of_mem_of_ne hu hv hne
  have hadj : G.Adj u v :=
    (SimpleGraph.mem_edgeSet G).1 (by simpa [heq] using e.property)
  refine ⟨Walk.cons hadj Walk.nil, ?_⟩
  simp [Walk.edges_cons, heq]

/-- A graph contains a cycle entirely on one side of a vertex-side predicate. -/
def HasCycleOnSide (G : SimpleGraph V) (side : V → Prop) : Prop :=
  ∃ u : V, side u ∧ ∃ p : G.Walk u u, p.IsCycle ∧ ∀ v, v ∈ p.support → side v

/-- A cycle contained on one side remains contained after weakening that side predicate. -/
theorem HasCycleOnSide.mono {G : SimpleGraph V} {side₁ side₂ : V → Prop}
    (hside : ∀ v, side₁ v → side₂ v)
    (hcycle : HasCycleOnSide G side₁) :
    HasCycleOnSide G side₂ := by
  rcases hcycle with ⟨u, hu, p, hpcycle, hpside⟩
  exact ⟨u, hside u hu, p, hpcycle, fun v hv => hside v (hpside v hv)⟩

/-- A small cyclic edge cut: the finite edge cut induced by a vertex-side predicate has size at
most four, and both sides contain a cycle.  The CAP5 annulus argument should eventually construct
this from the planar/Jordan separator data. -/
structure SmallCyclicEdgeCut (G : SimpleGraph V) where
  edgeCut : Finset G.edgeSet
  side : V → Prop
  hcut_eq : ∀ e : G.edgeSet, e ∈ edgeCut ↔ EdgeCrossesVertexSide G side e
  hcard_le_four : edgeCut.card <= 4
  hinside_cycle : HasCycleOnSide G side
  houtside_cycle : HasCycleOnSide G (fun v => ¬ side v)

theorem SmallCyclicEdgeCut.card_le_four {G : SimpleGraph V} (cut : SmallCyclicEdgeCut G) :
    cut.edgeCut.card <= 4 :=
  cut.hcard_le_four

theorem SmallCyclicEdgeCut.edge_mem_iff {G : SimpleGraph V} (cut : SmallCyclicEdgeCut G)
    (e : G.edgeSet) :
    e ∈ cut.edgeCut ↔ EdgeCrossesVertexSide G cut.side e :=
  cut.hcut_eq e

/-- The same cyclic cut with the chosen side complemented.  The edge support and cardinality are
unchanged; the inside/outside cycle witnesses swap. -/
def SmallCyclicEdgeCut.compl {G : SimpleGraph V} (cut : SmallCyclicEdgeCut G) :
    SmallCyclicEdgeCut G where
  edgeCut := cut.edgeCut
  side := fun v => ¬ cut.side v
  hcut_eq := fun e =>
    (cut.hcut_eq e).trans (edgeCrossesVertexSide_compl G cut.side e).symm
  hcard_le_four := cut.hcard_le_four
  hinside_cycle := cut.houtside_cycle
  houtside_cycle :=
    HasCycleOnSide.mono (fun _ hv hnot => hnot hv) cut.hinside_cycle

@[simp]
theorem SmallCyclicEdgeCut.compl_edgeCut {G : SimpleGraph V} (cut : SmallCyclicEdgeCut G) :
    cut.compl.edgeCut = cut.edgeCut :=
  rfl

@[simp]
theorem SmallCyclicEdgeCut.compl_card {G : SimpleGraph V} (cut : SmallCyclicEdgeCut G) :
    cut.compl.edgeCut.card = cut.edgeCut.card :=
  rfl

/-- Realization data for a finite edge support as a cyclic edge cut.  This is the natural
target for planar/Jordan separator constructions: give the vertex side, prove exact crossing-edge
equality, and provide cycles on both sides.  A separate cardinality proof turns it into a
`SmallCyclicEdgeCut`. -/
structure CyclicEdgeCutRealization (G : SimpleGraph V) (edgeCut : Finset G.edgeSet) where
  side : V → Prop
  hcut_eq : ∀ e : G.edgeSet, e ∈ edgeCut ↔ EdgeCrossesVertexSide G side e
  hinside_cycle : HasCycleOnSide G side
  houtside_cycle : HasCycleOnSide G (fun v => ¬ side v)

/-- Build a small cyclic edge cut from realization data plus the cardinality bound. -/
def CyclicEdgeCutRealization.toSmallCyclicEdgeCut
    {G : SimpleGraph V} {edgeCut : Finset G.edgeSet}
    (realization : CyclicEdgeCutRealization G edgeCut)
    (hcard : edgeCut.card <= 4) :
    SmallCyclicEdgeCut G where
  edgeCut := edgeCut
  side := realization.side
  hcut_eq := realization.hcut_eq
  hcard_le_four := hcard
  hinside_cycle := realization.hinside_cycle
  houtside_cycle := realization.houtside_cycle

/-- Forget the cardinality bound from a bundled small cyclic edge cut, retaining the exact
realization data for its finite edge support. -/
def SmallCyclicEdgeCut.toCyclicEdgeCutRealization
    {G : SimpleGraph V} (cut : SmallCyclicEdgeCut G) :
    CyclicEdgeCutRealization G cut.edgeCut where
  side := cut.side
  hcut_eq := cut.hcut_eq
  hinside_cycle := cut.hinside_cycle
  houtside_cycle := cut.houtside_cycle

/-- Reindex a bundled small cyclic edge cut as realization data for an equal finite support.
This is the bridge needed when a planar/Jordan argument naturally returns a `SmallCyclicEdgeCut`
and an equality with a candidate support rather than constructing `CyclicEdgeCutRealization`
directly. -/
def SmallCyclicEdgeCut.toCyclicEdgeCutRealization_of_edgeCut_eq
    {G : SimpleGraph V} (cut : SmallCyclicEdgeCut G) {edgeCut : Finset G.edgeSet}
    (h : cut.edgeCut = edgeCut) :
    CyclicEdgeCutRealization G edgeCut := by
  rw [← h]
  exact cut.toCyclicEdgeCutRealization

@[simp]
theorem CyclicEdgeCutRealization.toSmallCyclicEdgeCut_edgeCut
    {G : SimpleGraph V} {edgeCut : Finset G.edgeSet}
    (realization : CyclicEdgeCutRealization G edgeCut)
    (hcard : edgeCut.card <= 4) :
    (realization.toSmallCyclicEdgeCut hcard).edgeCut = edgeCut :=
  rfl

/-- Complement the chosen side in a cyclic-cut realization without changing the finite edge
support. -/
def CyclicEdgeCutRealization.compl
    {G : SimpleGraph V} {edgeCut : Finset G.edgeSet}
    (realization : CyclicEdgeCutRealization G edgeCut) :
    CyclicEdgeCutRealization G edgeCut where
  side := fun v => ¬ realization.side v
  hcut_eq := fun e =>
    (realization.hcut_eq e).trans (edgeCrossesVertexSide_compl G realization.side e).symm
  hinside_cycle := realization.houtside_cycle
  houtside_cycle :=
    HasCycleOnSide.mono (fun _ hv hnot => hnot hv) realization.hinside_cycle

@[simp]
theorem CyclicEdgeCutRealization.compl_toSmallCyclicEdgeCut_edgeCut
    {G : SimpleGraph V} {edgeCut : Finset G.edgeSet}
    (realization : CyclicEdgeCutRealization G edgeCut)
    (hcard : edgeCut.card <= 4) :
    ((realization.compl).toSmallCyclicEdgeCut hcard).edgeCut =
      (realization.toSmallCyclicEdgeCut hcard).edgeCut :=
  rfl

/-- Existence form for the manuscript's forbidden small cyclic edge cut. -/
def HasCyclicEdgeCutOfSizeAtMostFour (G : SimpleGraph V) : Prop :=
  ∃ cut : SmallCyclicEdgeCut G, cut.edgeCut.card <= 4

/-- Realization data plus a size bound gives the corresponding small cyclic-edge-cut existence
form. -/
theorem CyclicEdgeCutRealization.hasCyclicEdgeCutOfSizeAtMostFour
    {G : SimpleGraph V} {edgeCut : Finset G.edgeSet}
    (realization : CyclicEdgeCutRealization G edgeCut)
    (hcard : edgeCut.card <= 4) :
    HasCyclicEdgeCutOfSizeAtMostFour G :=
  ⟨realization.toSmallCyclicEdgeCut hcard, hcard⟩

/-- A realized cyclic cut intersects every walk joining the two sides.  The planar CAP5 layer can
use this as the graph-facing separator property after it supplies the vertex side and crossing-edge
equality. -/
theorem CyclicEdgeCutRealization.exists_mem_edgeCut_of_walk_endpoint_sides
    {G : SimpleGraph V} {edgeCut : Finset G.edgeSet}
    (realization : CyclicEdgeCutRealization G edgeCut)
    {u v : V} (p : G.Walk u v) (hu : realization.side u) (hv : ¬ realization.side v) :
    ∃ e : G.edgeSet, e ∈ edgeCut ∧ (e : Sym2 V) ∈ p.edges := by
  rcases exists_edgeCrossesVertexSide_of_walk_endpoint_sides realization.side p hu hv with
    ⟨e, heEdges, hcross⟩
  exact ⟨e, (realization.hcut_eq e).2 hcross, heEdges⟩

/-- A walk that avoids a realized cyclic cut cannot change sides.  This is the graph-facing
form of separation that the planar/Jordan layer can use after constructing the side predicate and
the exact cut support. -/
theorem CyclicEdgeCutRealization.side_iff_of_forall_not_mem_edgeCut_of_walk
    {G : SimpleGraph V} {edgeCut : Finset G.edgeSet}
    (realization : CyclicEdgeCutRealization G edgeCut)
    {u v : V} (p : G.Walk u v)
    (havoid : ∀ e : G.edgeSet, e ∈ edgeCut → (e : Sym2 V) ∉ p.edges) :
    realization.side u ↔ realization.side v := by
  constructor
  · intro hu
    by_contra hv
    rcases realization.exists_mem_edgeCut_of_walk_endpoint_sides p hu hv with
      ⟨e, hecut, heEdges⟩
    exact havoid e hecut heEdges
  · intro hv
    by_contra hu
    rcases realization.exists_mem_edgeCut_of_walk_endpoint_sides p.reverse hv hu with
      ⟨e, hecut, heReverseEdges⟩
    exact havoid e hecut (by simpa [Walk.edges_reverse] using heReverseEdges)

/-- Path-separation constructor for cyclic-edge-cut realization data.  If the listed finite
support consists of side-crossing edges, and every walk crossing the side contains a listed edge,
then the listed support is exactly the edge cut induced by the side.  This is the graph-level
interface a planar/Jordan argument should prove for the CAP5 separator candidate. -/
def CyclicEdgeCutRealization.of_walk_separator
    {G : SimpleGraph V} {edgeCut : Finset G.edgeSet} (side : V → Prop)
    (hcut_crosses :
      ∀ e : G.edgeSet, e ∈ edgeCut → EdgeCrossesVertexSide G side e)
    (hwalk_separator :
      ∀ {u v : V} (p : G.Walk u v), side u → ¬ side v →
        ∃ e : G.edgeSet, e ∈ edgeCut ∧ (e : Sym2 V) ∈ p.edges)
    (hinside_cycle : HasCycleOnSide G side)
    (houtside_cycle : HasCycleOnSide G (fun v => ¬ side v)) :
    CyclicEdgeCutRealization G edgeCut where
  side := side
  hcut_eq := by
    intro e
    constructor
    · exact hcut_crosses e
    · intro hcross
      rcases hcross with ⟨u, v, hu, hv, hsu, hsv⟩
      rcases exists_walk_edges_eq_singleton_of_edge_endpoint_sides
          (G := G) (side := side) (e := e) hu hv hsu hsv with
        ⟨p, hpEdges⟩
      rcases hwalk_separator p hsu hsv with ⟨e', he'cut, he'edges⟩
      have heq : e' = e := by
        apply Subtype.ext
        simpa [hpEdges] using he'edges
      simpa [heq] using he'cut
  hinside_cycle := hinside_cycle
  houtside_cycle := houtside_cycle

/-- Avoidance-side constructor for cyclic-edge-cut realization data.  If every walk avoiding the
listed finite support stays on the same side, while every listed edge really crosses the side,
then the listed support is exactly the side edge cut.  This is often the most natural output of a
planar/Jordan separation argument. -/
def CyclicEdgeCutRealization.of_walk_avoid_side_invariant
    {G : SimpleGraph V} {edgeCut : Finset G.edgeSet} (side : V → Prop)
    (hcut_crosses :
      ∀ e : G.edgeSet, e ∈ edgeCut → EdgeCrossesVertexSide G side e)
    (hwalk_invariant :
      ∀ {u v : V} (p : G.Walk u v),
        (∀ e : G.edgeSet, e ∈ edgeCut → (e : Sym2 V) ∉ p.edges) →
        (side u ↔ side v))
    (hinside_cycle : HasCycleOnSide G side)
    (houtside_cycle : HasCycleOnSide G (fun v => ¬ side v)) :
    CyclicEdgeCutRealization G edgeCut :=
  CyclicEdgeCutRealization.of_walk_separator side hcut_crosses
    (by
      intro u v p hu hv
      by_contra hnone
      have havoid :
          ∀ e : G.edgeSet, e ∈ edgeCut → (e : Sym2 V) ∉ p.edges := by
        intro e hecut heEdges
        exact hnone ⟨e, hecut, heEdges⟩
      exact hv ((hwalk_invariant p havoid).1 hu))
    hinside_cycle houtside_cycle

/-- Local edge-classification constructor for cyclic-edge-cut realization data.  If the listed
finite support consists of side-crossing edges, and every unlisted edge has both endpoints on the
same side, then the listed support is exactly the side edge cut. -/
def CyclicEdgeCutRealization.of_edge_side_classification
    {G : SimpleGraph V} {edgeCut : Finset G.edgeSet} (side : V → Prop)
    (hcut_crosses :
      ∀ e : G.edgeSet, e ∈ edgeCut → EdgeCrossesVertexSide G side e)
    (hnoncut_preserves :
      ∀ e : G.edgeSet, e ∉ edgeCut →
        ∀ u v : V, u ∈ (e : Sym2 V) → v ∈ (e : Sym2 V) → (side u ↔ side v))
    (hinside_cycle : HasCycleOnSide G side)
    (houtside_cycle : HasCycleOnSide G (fun v => ¬ side v)) :
    CyclicEdgeCutRealization G edgeCut where
  side := side
  hcut_eq := by
    intro e
    constructor
    · exact hcut_crosses e
    · intro hcross
      by_contra hnot
      rcases hcross with ⟨u, v, hu, hv, hsu, hsv⟩
      exact hsv ((hnoncut_preserves e hnot u v hu hv).1 hsu)
  hinside_cycle := hinside_cycle
  houtside_cycle := houtside_cycle

/-- Exact crossing-edge constructor for cyclic-edge-cut realization data.  It is enough to show
that the listed finite support crosses the side, and every unlisted edge does not cross it. -/
def CyclicEdgeCutRealization.of_edge_crossing_classification
    {G : SimpleGraph V} {edgeCut : Finset G.edgeSet} (side : V → Prop)
    (hcut_crosses :
      ∀ e : G.edgeSet, e ∈ edgeCut → EdgeCrossesVertexSide G side e)
    (hnoncut_not_crosses :
      ∀ e : G.edgeSet, e ∉ edgeCut → ¬ EdgeCrossesVertexSide G side e)
    (hinside_cycle : HasCycleOnSide G side)
    (houtside_cycle : HasCycleOnSide G (fun v => ¬ side v)) :
    CyclicEdgeCutRealization G edgeCut :=
  CyclicEdgeCutRealization.of_edge_side_classification side hcut_crosses
    (fun e hnot =>
      (not_edgeCrossesVertexSide_iff_forall_side_iff G side e).1
        (hnoncut_not_crosses e hnot))
    hinside_cycle houtside_cycle

/-- Exact crossing classification already gives the graph-facing separator theorem: every walk
whose endpoints lie on opposite sides contains one of the listed crossing edges. -/
theorem exists_mem_edgeCut_of_walk_endpoint_sides_of_edge_crossing_classification
    {G : SimpleGraph V} {edgeCut : Finset G.edgeSet} (side : V → Prop)
    (hnoncut_not_crosses :
      ∀ e : G.edgeSet, e ∉ edgeCut → ¬ EdgeCrossesVertexSide G side e)
    {u v : V} (p : G.Walk u v) (hu : side u) (hv : ¬ side v) :
    ∃ e : G.edgeSet, e ∈ edgeCut ∧ (e : Sym2 V) ∈ p.edges := by
  rcases exists_edgeCrossesVertexSide_of_walk_endpoint_sides side p hu hv with
    ⟨e, heEdges, hcross⟩
  by_cases hecut : e ∈ edgeCut
  · exact ⟨e, hecut, heEdges⟩
  · exact (hnoncut_not_crosses e hecut hcross).elim

/-- The graph-facing separator statement is equivalent to exact non-crossing of every unlisted
edge.  This removes a layer of conditional bookkeeping from the CAP5 route: proving that every
walk between opposite sides hits the listed support is the same local edge-classification target
as proving that no edge outside the support crosses the side. -/
theorem forall_walk_hits_edgeCut_iff_noncrossing_outside_edgeCut
    {G : SimpleGraph V} {edgeCut : Finset G.edgeSet} (side : V → Prop) :
    (∀ {u v : V} (p : G.Walk u v), side u → ¬ side v →
        ∃ e : G.edgeSet, e ∈ edgeCut ∧ (e : Sym2 V) ∈ p.edges) ↔
      (∀ e : G.edgeSet, e ∉ edgeCut → ¬ EdgeCrossesVertexSide G side e) := by
  constructor
  · intro hwalk e hnot hcross
    rcases hcross with ⟨u, v, hu, hv, hsu, hsv⟩
    rcases exists_walk_edges_eq_singleton_of_edge_endpoint_sides
        (G := G) (side := side) (e := e) hu hv hsu hsv with
      ⟨p, hpEdges⟩
    rcases hwalk p hsu hsv with ⟨e', he'cut, he'edges⟩
    have heq : e' = e := by
      apply Subtype.ext
      simpa [hpEdges] using he'edges
    exact hnot (by simpa [heq] using he'cut)
  · intro hnoncut u v p hu hv
    exact exists_mem_edgeCut_of_walk_endpoint_sides_of_edge_crossing_classification
      side hnoncut p hu hv

theorem SmallCyclicEdgeCut.exists_mem_edgeCut_of_walk_endpoint_sides
    {G : SimpleGraph V} (cut : SmallCyclicEdgeCut G)
    {u v : V} (p : G.Walk u v) (hu : cut.side u) (hv : ¬ cut.side v) :
    ∃ e : G.edgeSet, e ∈ cut.edgeCut ∧ (e : Sym2 V) ∈ p.edges :=
  cut.toCyclicEdgeCutRealization.exists_mem_edgeCut_of_walk_endpoint_sides p hu hv

theorem SmallCyclicEdgeCut.side_iff_of_forall_not_mem_edgeCut_of_walk
    {G : SimpleGraph V} (cut : SmallCyclicEdgeCut G)
    {u v : V} (p : G.Walk u v)
    (havoid : ∀ e : G.edgeSet, e ∈ cut.edgeCut → (e : Sym2 V) ∉ p.edges) :
    cut.side u ↔ cut.side v :=
  cut.toCyclicEdgeCutRealization.side_iff_of_forall_not_mem_edgeCut_of_walk p havoid

/-- Obstruction hypothesis used by the CAP5 exceptional-annulus branch: there is no cyclic edge
cut of size at most four. -/
def NoCyclicEdgeCutOfSizeAtMostFour (G : SimpleGraph V) : Prop :=
  ¬ HasCyclicEdgeCutOfSizeAtMostFour G

theorem SmallCyclicEdgeCut.hasCyclicEdgeCutOfSizeAtMostFour
    {G : SimpleGraph V} (cut : SmallCyclicEdgeCut G) :
    HasCyclicEdgeCutOfSizeAtMostFour G :=
  ⟨cut, cut.hcard_le_four⟩

theorem NoCyclicEdgeCutOfSizeAtMostFour.not_smallCyclicEdgeCut
    {G : SimpleGraph V} (h : NoCyclicEdgeCutOfSizeAtMostFour G)
    (cut : SmallCyclicEdgeCut G) :
    False :=
  h cut.hasCyclicEdgeCutOfSizeAtMostFour

theorem NoCyclicEdgeCutOfSizeAtMostFour.not_cyclicEdgeCutRealization_card_le_four
    {G : SimpleGraph V} (h : NoCyclicEdgeCutOfSizeAtMostFour G)
    {edgeCut : Finset G.edgeSet} (realization : CyclicEdgeCutRealization G edgeCut)
    (hcard : edgeCut.card <= 4) :
    False :=
  h (realization.hasCyclicEdgeCutOfSizeAtMostFour hcard)

/-- A graph has cyclic edge-connectivity at least `k` when every cyclic edge cut has at least
`k` edges. -/
def CyclicEdgeConnectivityAtLeast (G : SimpleGraph V) (k : Nat) : Prop :=
  ∀ cut : SmallCyclicEdgeCut G, k <= cut.edgeCut.card

/-- The four-color minimal-counterexample hypothesis usually needed by the CAP5 annulus
argument: no cyclic edge cut of size at most four. -/
def CyclicallyFiveEdgeConnected (G : SimpleGraph V) : Prop :=
  CyclicEdgeConnectivityAtLeast G 5

theorem CyclicallyFiveEdgeConnected.noCyclicEdgeCutOfSizeAtMostFour
    {G : SimpleGraph V} (h : CyclicallyFiveEdgeConnected G) :
    NoCyclicEdgeCutOfSizeAtMostFour G := by
  intro hcut
  rcases hcut with ⟨cut, hcard⟩
  exact Nat.not_succ_le_self 4 (le_trans (h cut) hcard)

theorem NoCyclicEdgeCutOfSizeAtMostFour.cyclicallyFiveEdgeConnected
    {G : SimpleGraph V} (h : NoCyclicEdgeCutOfSizeAtMostFour G) :
    CyclicallyFiveEdgeConnected G := by
  intro cut
  by_contra hnot
  exact h ⟨cut, Nat.lt_succ_iff.mp (lt_of_not_ge hnot)⟩

theorem cyclicallyFiveEdgeConnected_iff_noCyclicEdgeCutOfSizeAtMostFour
    {G : SimpleGraph V} :
    CyclicallyFiveEdgeConnected G ↔ NoCyclicEdgeCutOfSizeAtMostFour G :=
  ⟨CyclicallyFiveEdgeConnected.noCyclicEdgeCutOfSizeAtMostFour,
    NoCyclicEdgeCutOfSizeAtMostFour.cyclicallyFiveEdgeConnected⟩

theorem CyclicallyFiveEdgeConnected.not_smallCyclicEdgeCut_card_le_four
    {G : SimpleGraph V} (h : CyclicallyFiveEdgeConnected G)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card <= 4) :
    False :=
  h.noCyclicEdgeCutOfSizeAtMostFour ⟨cut, hcard⟩

end Mettapedia.GraphTheory.FourColor
