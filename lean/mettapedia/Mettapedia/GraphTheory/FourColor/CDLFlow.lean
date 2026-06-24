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
