import Mettapedia.GraphTheory.FourColor.Theorem49TargetSubspace

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-!
# CDL-style flow layer for the Goertzel 4CP route

The latest benxiv 4CP manuscript phrases the new route in terms of
`F2^2`-flows and a local CDL-goodness condition.  This file gives that
language a small Lean surface over the existing FourColor color algebra and
Kirchhoff-incidence API.
-/

/-- An `F2^2` graph flow: the incident edge-values sum to zero at every vertex. -/
def IsGraphFlow (G : SimpleGraph V) [Fintype G.edgeSet] (x : G.edgeSet → Color) : Prop :=
  ∀ v : V, vertexKirchhoffSum G x v = 0

/-- Local CDL-goodness for the canonical cubic-vertex gadget: the incident edge
triple is not the all-zero pattern.  On cubic graphs this is the manuscript's
"not CDL-bad at the vertex" condition. -/
def IsCDLGoodAtVertex (G : SimpleGraph V) [Fintype G.edgeSet]
    (x : G.edgeSet → Color) (v : V) : Prop :=
  ∃ e ∈ incidentEdgeFinset G v, x e ≠ 0

/-- A CDL-good flow on all vertices.  For disk patches, later files should use
the same local predicate restricted to the patch's interior vertices. -/
def IsCDLGoodFlow (G : SimpleGraph V) [Fintype G.edgeSet]
    (x : G.edgeSet → Color) : Prop :=
  IsGraphFlow G x ∧ ∀ v : V, IsCDLGoodAtVertex G x v

/-- A nowhere-zero graph flow.  On a bridgeless cubic graph, this is the
flow-side form of a Tait coloring used by the manuscript. -/
def IsNowhereZeroFlow (G : SimpleGraph V) [Fintype G.edgeSet]
    (x : G.edgeSet → Color) : Prop :=
  IsGraphFlow G x ∧ ∀ e : G.edgeSet, x e ≠ 0

/-- A named cubic incidence package: the incident edges at `v` are exactly
`e1`, `e2`, and `e3`, with no duplicates. -/
def IsIncidentEdgeTriple (G : SimpleGraph V) [Fintype G.edgeSet] (v : V)
    (e1 e2 e3 : G.edgeSet) : Prop :=
  incidentEdgeFinset G v = {e1, e2, e3} ∧ e1 ≠ e2 ∧ e1 ≠ e3 ∧ e2 ≠ e3

/-- A lightweight cubic-incidence hypothesis: every vertex has its incident
edge-set explicitly enumerated by three distinct edges. -/
def HasCubicIncidentEdgeTriples (G : SimpleGraph V) [Fintype G.edgeSet] : Prop :=
  ∀ v : V, ∃ e1 e2 e3 : G.edgeSet, IsIncidentEdgeTriple G v e1 e2 e3

/-- Local Kirchhoff law for the three incident edge-values at a cubic vertex. -/
def IsLocalKirchhoffTriple (a b c : Color) : Prop :=
  a + b + c = 0

/-- The canonical local CDL-bad pattern: all three incident values are zero. -/
def IsLocalCDLBadTriple (a b c : Color) : Prop :=
  a = 0 ∧ b = 0 ∧ c = 0

/-- The canonical local CDL-good condition: the incident triple is not all-zero. -/
def IsLocalCDLGoodTriple (a b c : Color) : Prop :=
  a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0

/-- The local nowhere-zero condition needed by a Tait-flow interpretation. -/
def IsLocalNowhereZeroTriple (a b c : Color) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0

/-- Local Tait condition for a cubic vertex: the three incident colors are
nonzero and pairwise distinct. -/
def IsLocalTaitTriple (a b c : Color) : Prop :=
  IsLocalNowhereZeroTriple a b c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c

theorem isGraphFlow_iff {G : SimpleGraph V} [Fintype G.edgeSet]
    {x : G.edgeSet → Color} :
    IsGraphFlow G x ↔ ∀ v : V, vertexKirchhoffSum G x v = 0 :=
  Iff.rfl

theorem incidentEdgeFinset_nonempty_of_hasCubicIncidentEdgeTriples {G : SimpleGraph V}
    [Fintype G.edgeSet] (hG : HasCubicIncidentEdgeTriples G) (v : V) :
    (incidentEdgeFinset G v).Nonempty := by
  rcases hG v with ⟨e1, _e2, _e3, hincident⟩
  refine ⟨e1, ?_⟩
  rw [hincident.1]
  simp

theorem hasCubicIncidentEdgeTriples_of_incidentEdgeFinset_card_eq_three
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3) :
    HasCubicIncidentEdgeTriples G := by
  intro v
  rcases Finset.card_eq_three.mp (hcard v) with ⟨e1, e2, e3, h12, h13, h23, hset⟩
  exact ⟨e1, e2, e3, hset, h12, h13, h23⟩

theorem incidentEdgeFinset_card_eq_three_of_hasCubicIncidentEdgeTriples
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (hG : HasCubicIncidentEdgeTriples G) (v : V) :
    (incidentEdgeFinset G v).card = 3 := by
  rcases hG v with ⟨e1, e2, e3, hset, h12, h13, h23⟩
  rw [hset]
  simp [h12, h13, h23]

theorem hasCubicIncidentEdgeTriples_iff_incidentEdgeFinset_card_eq_three
    {G : SimpleGraph V} [Fintype G.edgeSet] :
    HasCubicIncidentEdgeTriples G ↔ ∀ v : V, (incidentEdgeFinset G v).card = 3 := by
  constructor
  · exact incidentEdgeFinset_card_eq_three_of_hasCubicIncidentEdgeTriples
  · exact hasCubicIncidentEdgeTriples_of_incidentEdgeFinset_card_eq_three

theorem isLocalCDLGoodTriple_iff_not_bad {a b c : Color} :
    IsLocalCDLGoodTriple a b c ↔ ¬ IsLocalCDLBadTriple a b c := by
  constructor
  · intro hgood hbad
    rcases hbad with ⟨ha, hb, hc⟩
    rcases hgood with ha_ne | hb_ne | hc_ne
    · exact ha_ne ha
    · exact hb_ne hb
    · exact hc_ne hc
  · intro hnot
    by_cases ha : a = 0
    · by_cases hb : b = 0
      · by_cases hc : c = 0
        · exact False.elim (hnot ⟨ha, hb, hc⟩)
        · exact Or.inr (Or.inr hc)
      · exact Or.inr (Or.inl hb)
    · exact Or.inl ha

theorem localKirchhoff_zero_same (c : Color) :
    IsLocalKirchhoffTriple 0 c c := by
  simp [IsLocalKirchhoffTriple]

theorem localCDLGood_zero_same_of_ne_zero {c : Color} (hc : c ≠ 0) :
    IsLocalCDLGoodTriple 0 c c := by
  exact Or.inr (Or.inl hc)

theorem not_localNowhereZero_zero_left (b c : Color) :
    ¬ IsLocalNowhereZeroTriple 0 b c := by
  intro h
  exact h.1 rfl

theorem isLocalNowhereZeroTriple_of_tait {a b c : Color}
    (h : IsLocalTaitTriple a b c) :
    IsLocalNowhereZeroTriple a b c :=
  h.1

/-- Over `F₂²`, a local Tait triple at a cubic vertex automatically satisfies
Kirchhoff's law.  This is the local algebra behind the manuscript's Tait-flow
translation. -/
theorem isLocalKirchhoffTriple_of_tait {a b c : Color}
    (h : IsLocalTaitTriple a b c) :
    IsLocalKirchhoffTriple a b c := by
  rcases h with ⟨hnz, hab, hac, hbc⟩
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero a hnz.1 with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero b hnz.2.1 with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero c hnz.2.2 with rfl | rfl | rfl <;>
    simp [IsLocalKirchhoffTriple, red, blue, purple] at *

/-- Over `F2^2`, the local Kirchhoff law plus nowhere-zero values forces the
three colors at a cubic vertex to be pairwise distinct. -/
theorem isLocalTaitTriple_of_kirchhoff_nowhereZero {a b c : Color}
    (hK : IsLocalKirchhoffTriple a b c)
    (hnz : IsLocalNowhereZeroTriple a b c) :
    IsLocalTaitTriple a b c := by
  refine ⟨hnz, ?_, ?_, ?_⟩
  · intro hab
    have hsum : a + b + c = 0 := by
      simpa [IsLocalKirchhoffTriple] using hK
    have hc0 : c = 0 := by
      have hsum' : a + a + c = 0 := by
        simpa [hab] using hsum
      simpa [color_add_self] using hsum'
    exact hnz.2.2 hc0
  · intro hac
    have hsum : a + b + c = 0 := by
      simpa [IsLocalKirchhoffTriple] using hK
    have hsum' : c + b + c = 0 := by
      simpa [hac] using hsum
    have hb0 : b = 0 := by
      calc
        b = 0 + b := by simp
        _ = (c + c) + b := by rw [color_add_self]
        _ = c + b + c := by abel
        _ = 0 := hsum'
    exact hnz.2.1 hb0
  · intro hbc
    have hsum : a + b + c = 0 := by
      simpa [IsLocalKirchhoffTriple] using hK
    have hsum' : a + c + c = 0 := by
      simpa [hbc] using hsum
    have ha0 : a = 0 := by
      calc
        a = a + 0 := by simp
        _ = a + (c + c) := by rw [color_add_self]
        _ = a + c + c := by abel
        _ = 0 := hsum'
    exact hnz.1 ha0

/-- Graph-level local form of the Tait-flow direction: at a cubic vertex whose
incident edge-set is explicitly enumerated, a nowhere-zero graph flow produces
a local Tait triple on those three edges. -/
theorem isLocalTaitTriple_of_nowhereZeroFlow_at_incidentTriple {G : SimpleGraph V}
    [Fintype G.edgeSet] {x : G.edgeSet → Color} {v : V} {e1 e2 e3 : G.edgeSet}
    (hincident : IsIncidentEdgeTriple G v e1 e2 e3)
    (hx : IsNowhereZeroFlow G x) :
    IsLocalTaitTriple (x e1) (x e2) (x e3) := by
  apply isLocalTaitTriple_of_kirchhoff_nowhereZero
  · have hv := hx.1 v
    unfold vertexKirchhoffSum at hv
    rw [hincident.1] at hv
    simpa [IsLocalKirchhoffTriple, hincident.2.1, hincident.2.2.1, hincident.2.2.2,
      add_assoc] using hv
  · exact ⟨hx.2 e1, hx.2 e2, hx.2 e3⟩

/-- Graph-level local form of the Tait-coloring direction: at a cubic vertex
whose incident edge-set is explicitly enumerated, an edge coloring using only
nonzero `F₂²` colors produces three nonzero, pairwise distinct local values. -/
theorem isLocalTaitTriple_of_taitEdgeColoring_at_incidentTriple {G : SimpleGraph V}
    [Fintype G.edgeSet] {C : G.EdgeColoring Color} {v : V} {e1 e2 e3 : G.edgeSet}
    (hincident : IsIncidentEdgeTriple G v e1 e2 e3)
    (hC : IsTaitEdgeColoring G C) :
    IsLocalTaitTriple (C e1) (C e2) (C e3) := by
  have he1_mem : e1 ∈ incidentEdgeFinset G v := by
    rw [hincident.1]
    simp
  have he2_mem : e2 ∈ incidentEdgeFinset G v := by
    rw [hincident.1]
    simp
  have he3_mem : e3 ∈ incidentEdgeFinset G v := by
    rw [hincident.1]
    simp
  have he1v : v ∈ (e1 : Sym2 V) := by
    simpa [incidentEdgeFinset] using he1_mem
  have he2v : v ∈ (e2 : Sym2 V) := by
    simpa [incidentEdgeFinset] using he2_mem
  have he3v : v ∈ (e3 : Sym2 V) := by
    simpa [incidentEdgeFinset] using he3_mem
  have h12 : C e1 ≠ C e2 := by
    exact C.valid ((SimpleGraph.lineGraph_adj_iff_exists).2
      ⟨hincident.2.1, ⟨v, he1v, he2v⟩⟩)
  have h13 : C e1 ≠ C e3 := by
    exact C.valid ((SimpleGraph.lineGraph_adj_iff_exists).2
      ⟨hincident.2.2.1, ⟨v, he1v, he3v⟩⟩)
  have h23 : C e2 ≠ C e3 := by
    exact C.valid ((SimpleGraph.lineGraph_adj_iff_exists).2
      ⟨hincident.2.2.2, ⟨v, he2v, he3v⟩⟩)
  exact ⟨⟨hC e1, hC e2, hC e3⟩, h12, h13, h23⟩

/-- A Tait edge coloring induces the local Kirchhoff equation at an explicitly
enumerated cubic vertex. -/
theorem isLocalKirchhoffTriple_of_taitEdgeColoring_at_incidentTriple {G : SimpleGraph V}
    [Fintype G.edgeSet] {C : G.EdgeColoring Color} {v : V} {e1 e2 e3 : G.edgeSet}
    (hincident : IsIncidentEdgeTriple G v e1 e2 e3)
    (hC : IsTaitEdgeColoring G C) :
    IsLocalKirchhoffTriple (C e1) (C e2) (C e3) := by
  exact isLocalKirchhoffTriple_of_tait
    (isLocalTaitTriple_of_taitEdgeColoring_at_incidentTriple hincident hC)

/-- Vertex-sum form of the local Tait-flow translation: if the incident
edge-set at `v` is exactly `e1,e2,e3`, then a Tait edge coloring has zero
Kirchhoff sum at `v`. -/
theorem vertexKirchhoffSum_eq_zero_of_taitEdgeColoring_at_incidentTriple
    {G : SimpleGraph V} [Fintype G.edgeSet] {C : G.EdgeColoring Color}
    {v : V} {e1 e2 e3 : G.edgeSet}
    (hincident : IsIncidentEdgeTriple G v e1 e2 e3)
    (hC : IsTaitEdgeColoring G C) :
    vertexKirchhoffSum G C v = 0 := by
  unfold vertexKirchhoffSum
  rw [hincident.1]
  simpa [IsLocalKirchhoffTriple, hincident.2.1, hincident.2.2.1, hincident.2.2.2,
    add_assoc] using
    (isLocalKirchhoffTriple_of_taitEdgeColoring_at_incidentTriple hincident hC)

/-- Graph-level Tait-flow direction, phrased with the explicit cubic-incidence
package used by the local API: a Tait edge coloring satisfies Kirchhoff's law
at every vertex. -/
theorem isGraphFlow_of_taitEdgeColoring_of_hasCubicIncidentEdgeTriples
    {G : SimpleGraph V} [Fintype G.edgeSet] {C : G.EdgeColoring Color}
    (hG : HasCubicIncidentEdgeTriples G) (hC : IsTaitEdgeColoring G C) :
    IsGraphFlow G C := by
  intro v
  rcases hG v with ⟨e1, e2, e3, hincident⟩
  exact vertexKirchhoffSum_eq_zero_of_taitEdgeColoring_at_incidentTriple hincident hC

/-- A Tait edge coloring is a nowhere-zero `F₂²` graph flow once every vertex
has the expected cubic incident triple. -/
theorem isNowhereZeroFlow_of_taitEdgeColoring_of_hasCubicIncidentEdgeTriples
    {G : SimpleGraph V} [Fintype G.edgeSet] {C : G.EdgeColoring Color}
    (hG : HasCubicIncidentEdgeTriples G) (hC : IsTaitEdgeColoring G C) :
    IsNowhereZeroFlow G C := by
  exact ⟨isGraphFlow_of_taitEdgeColoring_of_hasCubicIncidentEdgeTriples hG hC, hC⟩

/-- Converse local-to-global edge-coloring step: in a nowhere-zero `F₂²` flow
on a graph with explicit cubic incident triples, adjacent line-graph vertices
(i.e. incident graph edges) have distinct values. -/
theorem edge_values_ne_of_nowhereZeroFlow_of_hasCubicIncidentEdgeTriples
    {G : SimpleGraph V} [Fintype G.edgeSet] {x : G.edgeSet → Color}
    (hG : HasCubicIncidentEdgeTriples G) (hx : IsNowhereZeroFlow G x)
    {e f : G.edgeSet} (hadj : G.lineGraph.Adj e f) :
    x e ≠ x f := by
  rcases (SimpleGraph.lineGraph_adj_iff_exists).1 hadj with ⟨hef, v, hev, hfv⟩
  rcases hG v with ⟨e1, e2, e3, hincident⟩
  have he_mem : e ∈ incidentEdgeFinset G v := by
    simpa [incidentEdgeFinset] using hev
  have hf_mem : f ∈ incidentEdgeFinset G v := by
    simpa [incidentEdgeFinset] using hfv
  rw [hincident.1] at he_mem hf_mem
  have htrip := isLocalTaitTriple_of_nowhereZeroFlow_at_incidentTriple hincident hx
  rcases htrip with ⟨_hnz, h12, h13, h23⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at he_mem hf_mem
  rcases he_mem with rfl | rfl | rfl
  · rcases hf_mem with rfl | rfl | rfl
    · exact (hef rfl).elim
    · exact h12
    · exact h13
  · rcases hf_mem with rfl | rfl | rfl
    · exact fun h => h12 h.symm
    · exact (hef rfl).elim
    · exact h23
  · rcases hf_mem with rfl | rfl | rfl
    · exact fun h => h13 h.symm
    · exact fun h => h23 h.symm
    · exact (hef rfl).elim

/-- Package a nowhere-zero `F₂²` flow as a proper edge coloring. -/
def edgeColoringOfNowhereZeroFlow
    {G : SimpleGraph V} [Fintype G.edgeSet] (x : G.edgeSet → Color)
    (hG : HasCubicIncidentEdgeTriples G) (hx : IsNowhereZeroFlow G x) :
    G.EdgeColoring Color :=
  SimpleGraph.Coloring.mk x
    (fun hadj => edge_values_ne_of_nowhereZeroFlow_of_hasCubicIncidentEdgeTriples hG hx hadj)

/-- The edge coloring obtained from a nowhere-zero `F₂²` flow is Tait: all
edge-values are nonzero. -/
theorem isTaitEdgeColoring_edgeColoringOfNowhereZeroFlow
    {G : SimpleGraph V} [Fintype G.edgeSet] {x : G.edgeSet → Color}
    (hG : HasCubicIncidentEdgeTriples G) (hx : IsNowhereZeroFlow G x) :
    IsTaitEdgeColoring G (edgeColoringOfNowhereZeroFlow x hG hx) := by
  intro e
  exact hx.2 e

/-- Nowhere-zero `F₂²` flows produce Tait edge colorings under the explicit
cubic-incidence hypothesis. -/
theorem exists_taitEdgeColoring_of_nowhereZeroFlow_of_hasCubicIncidentEdgeTriples
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (hG : HasCubicIncidentEdgeTriples G) (x : G.edgeSet → Color)
    (hx : IsNowhereZeroFlow G x) :
    ∃ C : G.EdgeColoring Color, IsTaitEdgeColoring G C := by
  exact ⟨edgeColoringOfNowhereZeroFlow x hG hx,
    isTaitEdgeColoring_edgeColoringOfNowhereZeroFlow hG hx⟩

/-- Existence-level Tait/flow reformulation for the explicit cubic-incidence
API: Tait edge colorings are equivalent to nowhere-zero `F₂²` graph flows. -/
theorem exists_taitEdgeColoring_iff_exists_nowhereZeroFlow_of_hasCubicIncidentEdgeTriples
    {G : SimpleGraph V} [Fintype G.edgeSet] (hG : HasCubicIncidentEdgeTriples G) :
    (∃ C : G.EdgeColoring Color, IsTaitEdgeColoring G C) ↔
      ∃ x : G.edgeSet → Color, IsNowhereZeroFlow G x := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, isNowhereZeroFlow_of_taitEdgeColoring_of_hasCubicIncidentEdgeTriples hG hC⟩
  · rintro ⟨x, hx⟩
    exact exists_taitEdgeColoring_of_nowhereZeroFlow_of_hasCubicIncidentEdgeTriples hG x hx

/-- Tait/flow reformulation using the finite incidence-cardinality form of
cubicity. -/
theorem exists_taitEdgeColoring_iff_exists_nowhereZeroFlow_of_incidentEdgeFinset_card_eq_three
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3) :
    (∃ C : G.EdgeColoring Color, IsTaitEdgeColoring G C) ↔
      ∃ x : G.edgeSet → Color, IsNowhereZeroFlow G x := by
  exact exists_taitEdgeColoring_iff_exists_nowhereZeroFlow_of_hasCubicIncidentEdgeTriples
    (hasCubicIncidentEdgeTriples_of_incidentEdgeFinset_card_eq_three hcard)

/-- The canonical CDL-good local condition is weaker than local nowhere-zero:
the Kirchhoff triple `(0, red, red)` is CDL-good and sums to zero, but still
has a zero edge-value. -/
theorem localCDLGoodKirchhoff_not_nowhereZero_red :
    IsLocalKirchhoffTriple 0 red red ∧
      IsLocalCDLGoodTriple 0 red red ∧
      ¬ IsLocalNowhereZeroTriple 0 red red := by
  exact
    ⟨localKirchhoff_zero_same red,
      localCDLGood_zero_same_of_ne_zero red_ne_zero,
      not_localNowhereZero_zero_left red red⟩

theorem exists_localCDLGoodKirchhoff_not_nowhereZero :
    ∃ a b c : Color,
      IsLocalKirchhoffTriple a b c ∧
        IsLocalCDLGoodTriple a b c ∧
        ¬ IsLocalNowhereZeroTriple a b c := by
  exact ⟨0, red, red, localCDLGoodKirchhoff_not_nowhereZero_red⟩

/-- Thus the local implication from canonical CDL-good Kirchhoff triples to
nowhere-zero triples is false without an additional hypothesis. -/
theorem not_forall_localCDLGoodKirchhoff_implies_nowhereZero :
    ¬ (∀ a b c : Color,
      IsLocalKirchhoffTriple a b c →
      IsLocalCDLGoodTriple a b c →
      IsLocalNowhereZeroTriple a b c) := by
  intro h
  exact localCDLGoodKirchhoff_not_nowhereZero_red.2.2
    (h 0 red red
      localCDLGoodKirchhoff_not_nowhereZero_red.1
      localCDLGoodKirchhoff_not_nowhereZero_red.2.1)

theorem isGraphFlow_of_mem_kirchhoffSubmodule_univ {G : SimpleGraph V}
    [Fintype V] [Fintype G.edgeSet] {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G Finset.univ) :
    IsGraphFlow G x := by
  intro v
  exact hx v (by simp)

theorem mem_kirchhoffSubmodule_univ_of_isGraphFlow {G : SimpleGraph V}
    [Fintype V] [Fintype G.edgeSet] {x : G.edgeSet → Color}
    (hx : IsGraphFlow G x) :
    x ∈ kirchhoffSubmodule G Finset.univ := by
  intro v _hv
  exact hx v

theorem isCDLGoodAtVertex_of_nowhereZero {G : SimpleGraph V} [Fintype G.edgeSet]
    {x : G.edgeSet → Color} {v : V}
    (hincident : (incidentEdgeFinset G v).Nonempty)
    (hnz : ∀ e : G.edgeSet, x e ≠ 0) :
    IsCDLGoodAtVertex G x v := by
  rcases hincident with ⟨e, he⟩
  exact ⟨e, he, hnz e⟩

theorem isCDLGoodFlow_of_nowhereZeroFlow {G : SimpleGraph V} [Fintype G.edgeSet]
    {x : G.edgeSet → Color}
    (hincident : ∀ v : V, (incidentEdgeFinset G v).Nonempty)
    (hx : IsNowhereZeroFlow G x) :
    IsCDLGoodFlow G x := by
  exact ⟨hx.1, fun v => isCDLGoodAtVertex_of_nowhereZero (hincident v) hx.2⟩

/-- For the canonical all-zero-bad CDL gadget, a Tait edge coloring is a
CDL-good flow under the same explicit cubic-incidence hypothesis. -/
theorem isCDLGoodFlow_of_taitEdgeColoring_of_hasCubicIncidentEdgeTriples
    {G : SimpleGraph V} [Fintype G.edgeSet] {C : G.EdgeColoring Color}
    (hG : HasCubicIncidentEdgeTriples G) (hC : IsTaitEdgeColoring G C) :
    IsCDLGoodFlow G C := by
  exact isCDLGoodFlow_of_nowhereZeroFlow
    (incidentEdgeFinset_nonempty_of_hasCubicIncidentEdgeTriples hG)
    (isNowhereZeroFlow_of_taitEdgeColoring_of_hasCubicIncidentEdgeTriples hG hC)

/-- The CDL formulation used here keeps the nonzero condition explicit:
Tait edge colorings are equivalent to flows that are both CDL-good and
nowhere-zero.  This deliberately does not identify CDL-goodness alone with
nowhere-zero. -/
theorem
    exists_taitEdgeColoring_iff_exists_cdlGood_nowhereZeroFlow_of_hasCubicIncidentEdgeTriples
    {G : SimpleGraph V} [Fintype G.edgeSet] (hG : HasCubicIncidentEdgeTriples G) :
    (∃ C : G.EdgeColoring Color, IsTaitEdgeColoring G C) ↔
      ∃ x : G.edgeSet → Color, IsCDLGoodFlow G x ∧ IsNowhereZeroFlow G x := by
  constructor
  · rintro ⟨C, hC⟩
    have hx := isNowhereZeroFlow_of_taitEdgeColoring_of_hasCubicIncidentEdgeTriples hG hC
    exact ⟨C, isCDLGoodFlow_of_taitEdgeColoring_of_hasCubicIncidentEdgeTriples hG hC, hx⟩
  · rintro ⟨x, _hgood, hx⟩
    exact exists_taitEdgeColoring_of_nowhereZeroFlow_of_hasCubicIncidentEdgeTriples hG x hx

/-- CDL-safe Tait/flow reformulation using finite incidence cardinality: the
flow side includes both CDL-goodness and nowhere-zeroness. -/
theorem
    exists_taitEdgeColoring_iff_exists_cdlGood_nowhereZeroFlow_of_incidentEdgeFinset_card_eq_three
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3) :
    (∃ C : G.EdgeColoring Color, IsTaitEdgeColoring G C) ↔
      ∃ x : G.edgeSet → Color, IsCDLGoodFlow G x ∧ IsNowhereZeroFlow G x := by
  exact exists_taitEdgeColoring_iff_exists_cdlGood_nowhereZeroFlow_of_hasCubicIncidentEdgeTriples
    (hasCubicIncidentEdgeTriples_of_incidentEdgeFinset_card_eq_three hcard)

theorem zeroChain_isGraphFlow (G : SimpleGraph V) [Fintype G.edgeSet] :
    IsGraphFlow G (zeroChain : G.edgeSet → Color) := by
  intro v
  simp [vertexKirchhoffSum, zeroChain]

theorem not_isCDLGoodAtVertex_zeroChain (G : SimpleGraph V) [Fintype G.edgeSet]
    (v : V) :
    ¬ IsCDLGoodAtVertex G (zeroChain : G.edgeSet → Color) v := by
  intro h
  rcases h with ⟨e, _he, hne⟩
  exact hne rfl

theorem zeroChain_not_isCDLGoodFlow_of_nonempty_incident (G : SimpleGraph V)
    [Fintype G.edgeSet]
    (hincident : ∃ v : V, (incidentEdgeFinset G v).Nonempty) :
    ¬ IsCDLGoodFlow G (zeroChain : G.edgeSet → Color) := by
  intro hgood
  rcases hincident with ⟨v, _hv⟩
  exact not_isCDLGoodAtVertex_zeroChain G v (hgood.2 v)

end Mettapedia.GraphTheory.FourColor
