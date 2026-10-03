import Mettapedia.GraphTheory.FourColor.KempeChainCertificate
import Mettapedia.GSLT.Core.NonFactorization
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Current boundary Kempe partitions do not determine their own evolution

Three ports of a four-cycle have the same colours and the same boundary
connectivity for every colour pair in two proper colourings. Switching
the component of the same pair at the same port gives different new
boundary connectivity. One invisible interior switch joins the two inputs.

Thus the current word and all current pair partitions are not sufficient
for a deterministic quotient of rooted component switching. This does not
exclude a relation retaining its concrete witnesses or silent preparation.
-/

namespace Mettapedia.GraphTheory.FourColor.KempeBoundaryObservation

open SimpleGraph KempeChainCertificate Mettapedia.GSLT.Core.NonFactorization

variable {V P α : Type*} {G : SimpleGraph V}

local instance [DecidableEq α] (C : G.Coloring α) (a b : α) (v : V) :
    Decidable (v ∈ C.bicoloredSet a b) :=
  inferInstanceAs (Decidable (C v = a ∨ C v = b))

/-- Actual connectivity in the selected two-colour induced subgraph. -/
def PairConnected (C : G.Coloring α) (a b : α) (u v : V) : Prop :=
  ∃ hu : u ∈ C.bicoloredSet a b, ∃ hv : v ∈ C.bicoloredSet a b,
    (C.bicoloredSubgraph a b).Reachable ⟨u, hu⟩ ⟨v, hv⟩

instance [Fintype V] [DecidableEq V] [DecidableEq α] [DecidableRel G.Adj]
    (C : G.Coloring α) (a b : α) (u v : V) : Decidable (PairConnected C a b u v) := by
  unfold PairConnected
  infer_instance

/-- Retain the complete boundary word and every current two-colour partition. -/
def view (ports : P → V) (C : G.Coloring α) :
    (P → α) × (α → α → P → P → Prop) :=
  (C ∘ ports, fun a b i j => PairConnected C a b (ports i) (ports j))

/-- A boundary-rooted operation includes the inactive-root identity case. -/
noncomputable def rootedSwitch [DecidableEq α] (C : G.Coloring α) (a b : α) (root : V) :
    G.Coloring α :=
  if h : root ∈ C.bicoloredSet a b then
    C.swapOnKempeComponent a b ((C.bicoloredSubgraph a b).connectedComponentMk ⟨root, h⟩)
  else C

noncomputable def rootedSwitch_step [DecidableEq α] (C : G.Coloring α) (a b : α) (root : V)
    (h : root ∈ C.bicoloredSet a b) : Step C (rootedSwitch C a b root) := by
  rw [rootedSwitch, dite_eq_left h]
  exact .switch _ _ _ _

open Classical in
/-- The current pair partition does determine the immediate colour change. -/
theorem rootedSwitch_apply [DecidableEq α] (C : G.Coloring α) (a b : α) (root v : V) :
    rootedSwitch C a b root v =
      if PairConnected C a b root v then Equiv.swap a b (C v) else C v := by
  classical
  by_cases hr : root ∈ C.bicoloredSet a b
  · rw [rootedSwitch, dite_eq_left hr]
    let K := (C.bicoloredSubgraph a b).connectedComponentMk ⟨root, hr⟩
    have same : v ∈ C.kempeComponentSet a b K ↔ PairConnected C a b root v := by
      constructor
      · rintro ⟨hv, heq⟩
        exact ⟨hr, hv, ConnectedComponent.exact heq.symm⟩
      · rintro ⟨_, hv, path⟩
        exact ⟨hv, (ConnectedComponent.sound path).symm⟩
    by_cases hv : PairConnected C a b root v
    · rw [ite_eq_left hv]
      exact C.swapOnKempeComponent_apply_of_mem (same.mpr hv)
    · rw [ite_eq_right hv]
      exact C.swapOnKempeComponent_apply_of_not_mem (fun h => hv (same.mp h))
  · rw [rootedSwitch, dite_eq_right hr]
    have hn : ¬ PairConnected C a b root v := fun h => hr h.choose
    simp only [ite_eq_right hn]

/-- For arbitrary graphs and palettes the word after one rooted switch factors
through the current summary. Iterating this fact would also need a valid
update of the partitions, which the square below disproves. -/
theorem word_update_factors [DecidableEq α] (ports : P → V) (a b : α) (root : P) :
    Factors (view (G := G) ports)
      (fun C => fun i => rootedSwitch C a b (ports root) (ports i)) := by
  classical
  refine ⟨fun s i => if s.2 a b root i then Equiv.swap a b (s.1 i) else s.1 i, ?_⟩
  intro C
  funext i
  exact (rootedSwitch_apply C a b (ports root) (ports i)).symm

namespace Square

def graph : SimpleGraph (Fin 4) where
  Adj u v := (u.val + 1) % 4 = v.val ∨ (v.val + 1) % 4 = u.val
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide +kernel⟩

instance : DecidableRel graph.Adj := by unfold graph; infer_instance

def ports : Fin 3 → Fin 4 := fun i => i.castSucc

def values : Fin 4 → Fin 4 → Fin 4
  | 0 => ![0, 1, 2, 1]
  | 1 => ![0, 1, 2, 3]
  | 2 => ![2, 1, 2, 1]
  | 3 => ![2, 1, 2, 3]

theorem proper : ∀ s u v, graph.Adj u v → values s u ≠ values s v := by decide +kernel

def state (s : Fin 4) : graph.Coloring (Fin 4) := .mk (values s) (fun h => proper s _ _ h)

theorem initial_word : ∀ i, state 0 (ports i) = state 1 (ports i) := by decide +kernel

theorem initial_pairs : ∀ a b i j,
    PairConnected (state 0) a b (ports i) (ports j) ↔
      PairConnected (state 1) a b (ports i) (ports j) := by decide +kernel

theorem same_view : view ports (state 0) = view ports (state 1) := by
  apply Prod.ext
  · exact funext initial_word
  · funext a b i j
    exact propext (initial_pairs a b i j)

private theorem switch_singleton (s t a b root : Fin 4)
    (active : state s root = a ∨ state s root = b)
    (closed : ∀ v, graph.Adj root v → ¬ (state s v = a ∨ state s v = b))
    (answer : ∀ v, state t v = if v = root then Equiv.swap a b (state s v) else state s v) :
    rootedSwitch (state s) a b root = state t := by
  have ha : root ∈ (state s).bicoloredSet a b := active
  rw [rootedSwitch, dite_eq_left ha]
  apply DFunLike.ext
  intro v
  rw [(state s).swap_apply_of_chain a b _ [root] (by simp)
    (by simpa using active) (by
      intro x hx y hxy hy
      have he : x = root := by simpa using hx
      subst x
      exact (closed y hxy hy).elim)
    (by simp) ((state s).mem_kempeComponentSet_self active) v]
  simpa using (answer v).symm

theorem hidden_switch : rootedSwitch (state 0) 1 3 3 = state 1 :=
  switch_singleton 0 1 1 3 3 (by decide) (by decide +kernel) (by decide +kernel)

theorem left_switch : rootedSwitch (state 0) 0 2 0 = state 2 :=
  switch_singleton 0 2 0 2 0 (by decide) (by decide +kernel) (by decide +kernel)

theorem right_switch : rootedSwitch (state 1) 0 2 0 = state 3 :=
  switch_singleton 1 3 0 2 0 (by decide) (by decide +kernel) (by decide +kernel)

theorem after_word : ∀ i, state 2 (ports i) = state 3 (ports i) := by decide +kernel

theorem after_disconnected : ¬ PairConnected (state 2) 2 3 (ports 0) (ports 2) := by
  decide +kernel

theorem after_connected : PairConnected (state 3) 2 3 (ports 0) (ports 2) := by
  decide +kernel

theorem different_after : view ports (state 2) ≠ view ports (state 3) := by
  intro h
  have hp := congrArg (fun s => s.2 2 3 0 2) h
  exact after_disconnected (Eq.mpr hp after_connected)

/-- A genuine boundary-labelled switch cannot be updated from the current
boundary word and pair partitions alone. -/
theorem no_deterministic_update :
    ¬ Factors (view ports) (fun C : graph.Coloring (Fin 4) => view ports (rootedSwitch C 0 2 0)) := by
  apply NonTrivialFiber.not_factors
  refine ⟨state 0, state 1, same_view, ?_⟩
  simpa only [left_switch, right_switch] using different_after

/-- The lost distinction affects boundary colours after just two specified
commands, not merely an auxiliary partition recorded by the observer. -/
theorem no_two_step_word_update :
    ¬ Factors (view ports) (fun C : graph.Coloring (Fin 4) => fun i : Fin 3 =>
      rootedSwitch (rootedSwitch C 0 2 0) 2 3 0 (ports i)) := by
  classical
  apply NonTrivialFiber.not_factors
  refine ⟨state 0, state 1, same_view, ?_⟩
  intro h
  have he := congrFun h 2
  simp only [left_switch, right_switch] at he
  rw [rootedSwitch_apply, rootedSwitch_apply] at he
  have hno : ¬ PairConnected (state 2) 2 3 0 (ports 2) := after_disconnected
  have hyes : PairConnected (state 3) 2 3 0 (ports 2) := after_connected
  simp only [hno, hyes, ite_false, ite_true] at he
  have hn : (2 : Fin 4) ≠ 3 := by decide
  change (2 : Fin 4) = Equiv.swap 2 3 2 at he
  rw [Equiv.swap_apply_left] at he
  exact hn he

/-- The indistinguishable inputs are physically connected by one switch
that does not change a port colour. -/
theorem hidden_history : Nonempty (History (state 0) (state 1)) := by
  have h := rootedSwitch_step (state 0) 1 3 3 (by decide)
  rw [hidden_switch] at h
  exact ⟨.cons h (.refl _)⟩

/-- Retaining a concrete silent-preparation witness permits the other
observed outcome, with two actual component switches. -/
theorem prepared_history : Nonempty (History (state 0) (state 3)) := by
  have first := rootedSwitch_step (state 0) 1 3 3 (by decide)
  have second := rootedSwitch_step (state 1) 0 2 0 (by decide)
  rw [hidden_switch] at first
  rw [right_switch] at second
  exact ⟨.cons first (.cons second (.refl _))⟩

end Square
end Mettapedia.GraphTheory.FourColor.KempeBoundaryObservation
