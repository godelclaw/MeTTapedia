import Mettapedia.GraphTheory.Kempe.Boundary

/-!
# Small instances of the boundary notions

The definitions of `Kempe.Boundary` are not degenerate:

* **a connected fibre** — the single edge `K₂` with three colours and one
  boundary vertex: `FibreConnected` holds;
* **a disconnected fibre and a transparent colouring** — the net (a triangle
  with one pendant vertex at each corner, the pendants forming the boundary).
  The colouring `(0,1,2 | 0,2,1)` is transparent relative to the pendants, so no
  switch avoiding them applies to it; the colouring `(2,0,1 | 0,2,1)` has the
  same boundary word and differs from it, so `FibreConnected` fails.  The same
  frozen colouring cannot be moved to a colouring with another colour at a
  corner, so completability with the pendants fixed fails as well;
* **a non-transparent colouring with an interior Kempe cycle** — a four-cycle
  with one pendant boundary vertex, coloured `0,1,0,1` around the cycle and `2`
  on the pendant: the `{0,1}`-component is the whole four-cycle, which avoids
  the boundary.
-/

namespace Mettapedia.GraphTheory.Kempe.BoundaryExamples

open SimpleGraph Relation
open Mettapedia.Combinatorics.Reconfiguration

/-! ## A connected fibre -/

/-- The single edge. -/
abbrev edge : SimpleGraph (Fin 2) := ⊤

/-- Local Kempe reachability with one endpoint of an edge fixed, three
colours: the free endpoint takes either colour other than the fixed one, and a
single switch on it passes between them. -/
theorem edge_fibreConnected : edge.FibreConnected (Fin 3) {0} := by
  intro C D hCD
  have h0 : C 0 = D 0 := Coloring.boundaryWord_eq_iff.1 hCD 0 rfl
  by_cases h1 : C 1 = D 1
  · have : C = D := by
      ext v : 1
      fin_cases v
      · exact h0
      · exact h1
    subst this
    exact ReflTransGen.refl
  · apply ReflTransGen.single
    have hmem : (1 : Fin 2) ∈ C.bicoloredSet (C 1) (D 1) := Or.inl rfl
    let K := (C.bicoloredSubgraph (C 1) (D 1)).connectedComponentMk ⟨1, hmem⟩
    have hC01 : C 0 ≠ C 1 := C.valid (by decide : edge.Adj 0 1)
    have hD01 : D 0 ≠ D 1 := D.valid (by decide : edge.Adj 0 1)
    have h0K : (0 : Fin 2) ∉ C.kempeComponentSet (C 1) (D 1) K := by
      intro h
      rcases C.mem_bicoloredSet_of_mem_kempeComponentSet h with h' | h'
      · exact hC01 h'
      · exact hD01 (h0 ▸ h')
    refine ⟨C 1, D 1, K, ?_, ?_⟩
    · rw [Set.disjoint_singleton_right]
      exact h0K
    · ext v : 1
      fin_cases v
      · change D 0 = C.swapOnKempeComponent (C 1) (D 1) K 0
        rw [C.swapOnKempeComponent_apply_of_not_mem h0K]
        exact h0.symm
      · change D 1 = C.swapOnKempeComponent (C 1) (D 1) K 1
        rw [C.swapOnKempeComponent_apply_of_mem (C.mem_kempeComponentSet_self hmem)]
        simp

/-! ## The net: a transparent, frozen colouring and a disconnected fibre -/

/-- Adjacency of the net: triangle `0,1,2`, pendants `3` at `2`, `4` at `1`,
`5` at `0`. -/
def netAdj (i j : Fin 6) : Bool :=
  (i, j) ∈ [(0, 1), (1, 0), (0, 2), (2, 0), (1, 2), (2, 1),
    (2, 3), (3, 2), (1, 4), (4, 1), (0, 5), (5, 0)]

def net : SimpleGraph (Fin 6) where
  Adj i j := netAdj i j = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel net.Adj := fun i j => inferInstanceAs (Decidable (netAdj i j = true))

/-- The pendants. -/
def pendants : Set (Fin 6) := {3, 4, 5}

instance (v : Fin 6) : Decidable (v ∈ pendants) :=
  inferInstanceAs (Decidable (v = 3 ∨ v = 4 ∨ v = 5))

def netC : Fin 6 → Fin 3
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 2 | 5 => 1

def netD : Fin 6 → Fin 3
  | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 1

def netColoringC : net.Coloring (Fin 3) :=
  Coloring.mk netC (by intro u v; revert u v; decide)

def netColoringD : net.Coloring (Fin 3) :=
  Coloring.mk netD (by intro u v; revert u v; decide)

/-- One step along an edge inside a two-colour component. -/
private theorem net_step {a b : Fin 3} {K : (netColoringC.bicoloredSubgraph a b).ConnectedComponent}
    {u : Fin 6} (hu : u ∈ netColoringC.kempeComponentSet a b K) (w : Fin 6)
    (h : net.Adj u w ∧ (netC w = a ∨ netC w = b)) :
    w ∈ netColoringC.kempeComponentSet a b K :=
  netColoringC.mem_kempeComponentSet_of_adj hu h.1 h.2

/-- **The colouring `C` of the net is transparent relative to the pendants**:
every two-colour component reaches a pendant within two edges. -/
theorem netColoringC_isTransparent : netColoringC.IsTransparent pendants := by
  intro a b hab K
  obtain ⟨v, hv, rfl⟩ := netColoringC.exists_eq_mk_of_kempeComponent K
  have hmem := netColoringC.mem_kempeComponentSet_self hv
  have hv' : netC v = a ∨ netC v = b := hv
  fin_cases a <;> fin_cases b <;> fin_cases v <;> (try simp at hab) <;>
    first
    | exact absurd hv' (by decide)
    | exact ⟨_, hmem, by decide⟩
    | exact ⟨3, net_step hmem 3 (by decide), by decide⟩
    | exact ⟨4, net_step hmem 4 (by decide), by decide⟩
    | exact ⟨5, net_step hmem 5 (by decide), by decide⟩
    | exact ⟨3, net_step (net_step hmem 2 (by decide)) 3 (by decide), by decide⟩
    | exact ⟨4, net_step (net_step hmem 1 (by decide)) 4 (by decide), by decide⟩
    | exact ⟨5, net_step (net_step hmem 0 (by decide)) 5 (by decide), by decide⟩

theorem netColorings_same_word :
    netColoringC.boundaryWord pendants = netColoringD.boundaryWord pendants := by
  apply Coloring.boundaryWord_eq_iff.2
  intro v hv
  rcases hv with rfl | rfl | rfl <;> rfl

theorem netColorings_ne : netColoringC ≠ netColoringD := by
  intro h
  have h0 : netC 0 = netD 0 := congrArg (fun C : net.Coloring (Fin 3) => C 0) h
  exact absurd h0 (by decide)

/-- **A disconnected fibre.**  The net with its pendants fixed does not satisfy
LKR_in: the transparent colouring `C` is frozen, and `D` shares its word. -/
theorem net_not_fibreConnected : ¬ net.FibreConnected (Fin 3) pendants := by
  intro h
  have hpath := h netColoringC netColoringD netColorings_same_word
  exact netColorings_ne
    (netColoringC_isTransparent.eq_of_reflTransGen subset_rfl hpath).symm

/-- With the pendants fixed, the frozen colouring cannot reach a colouring with
colour `2` at corner `0`, although `D` is one. -/
theorem net_not_completable :
    ¬ Completable (net.KempeStepAvoiding pendants)
      {C : net.Coloring (Fin 3) | C 0 = 2} := by
  intro h
  obtain ⟨y, hy, hpath⟩ := h netColoringC
  rw [netColoringC_isTransparent.eq_of_reflTransGen subset_rfl hpath] at hy
  have hy' : netC 0 = 2 := hy
  exact absurd hy' (by decide)

/-! ## An interior Kempe cycle -/

/-- A four-cycle `0,1,2,3` with a pendant `4` at `0`. -/
def cycAdj (i j : Fin 5) : Bool :=
  (i, j) ∈ [(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2), (3, 0), (0, 3), (0, 4), (4, 0)]

def cyclePendant : SimpleGraph (Fin 5) where
  Adj i j := cycAdj i j = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel cyclePendant.Adj := fun i j =>
  inferInstanceAs (Decidable (cycAdj i j = true))

def cycC : Fin 5 → Fin 3
  | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 1 | 4 => 2

def cycleColoring : cyclePendant.Coloring (Fin 3) :=
  Coloring.mk cycC (by intro u v; revert u v; decide)

/-- The `{0,1}`-component of vertex `1`. -/
def cycleComponent : (cycleColoring.bicoloredSubgraph 0 1).ConnectedComponent :=
  (cycleColoring.bicoloredSubgraph 0 1).connectedComponentMk ⟨1, Or.inr rfl⟩

/-- The component contains the whole four-cycle. -/
theorem cycleComponent_contains_cycle :
    ∀ v : Fin 5, v ≠ 4 → v ∈ cycleColoring.kempeComponentSet 0 1 cycleComponent := by
  have h1 : (1 : Fin 5) ∈ cycleColoring.kempeComponentSet 0 1 cycleComponent :=
    cycleColoring.mem_kempeComponentSet_self _
  have h0 := cycleColoring.mem_kempeComponentSet_of_adj h1
    (by decide : cyclePendant.Adj 1 0) (Or.inl rfl)
  have h2 := cycleColoring.mem_kempeComponentSet_of_adj h1
    (by decide : cyclePendant.Adj 1 2) (Or.inl rfl)
  have h3 := cycleColoring.mem_kempeComponentSet_of_adj h2
    (by decide : cyclePendant.Adj 2 3) (Or.inr rfl)
  intro v hv
  fin_cases v
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact absurd rfl hv

/-- **An interior Kempe cycle.**  The colouring is not transparent relative to
the pendant: its `{0,1}`-component (the four-cycle) avoids it. -/
theorem cycleColoring_not_isTransparent : ¬ cycleColoring.IsTransparent {4} := by
  intro h
  obtain ⟨v, hvK, hv⟩ := h 0 1 (by decide) cycleComponent
  rw [Set.mem_singleton_iff] at hv
  subst hv
  have h4 : cycC 4 = 0 ∨ cycC 4 = 1 :=
    cycleColoring.mem_bicoloredSet_of_mem_kempeComponentSet hvK
  exact absurd h4 (by decide)

/-- Accordingly, the interior switch moves the colouring while fixing the
pendant. -/
theorem cycleColoring_interior_switch :
    cyclePendant.KempeStepAvoiding {4} cycleColoring
        (cycleColoring.swapOnKempeComponent 0 1 cycleComponent) ∧
      cycleColoring.swapOnKempeComponent 0 1 cycleComponent ≠ cycleColoring := by
  have hdisj : Disjoint (cycleColoring.kempeComponentSet 0 1 cycleComponent) {4} := by
    rw [Set.disjoint_singleton_right]
    intro h4
    have h4' : cycC 4 = 0 ∨ cycC 4 = 1 :=
      cycleColoring.mem_bicoloredSet_of_mem_kempeComponentSet h4
    exact absurd h4' (by decide)
  refine ⟨kempeStepAvoiding_swapOnKempeComponent _ _ _ _ hdisj, fun h => ?_⟩
  have h1 : cycleColoring.swapOnKempeComponent 0 1 cycleComponent 1 = cycleColoring 1 :=
    congrArg (fun C : cyclePendant.Coloring (Fin 3) => C 1) h
  rw [cycleColoring.swapOnKempeComponent_apply_of_mem
    (cycleComponent_contains_cycle 1 (by decide))] at h1
  have h1' : Equiv.swap (0 : Fin 3) 1 (cycC 1) = cycC 1 := h1
  exact absurd h1' (by decide)

end Mettapedia.GraphTheory.Kempe.BoundaryExamples
