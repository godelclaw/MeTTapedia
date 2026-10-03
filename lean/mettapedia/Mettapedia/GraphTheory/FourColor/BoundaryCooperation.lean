import Mettapedia.GraphTheory.FourColor.AdjacentHiddenObstruction
import Mettapedia.GraphTheory.Kempe.HomProjection

/-!
# An exact unbounded boundary-cooperation cost

Replace each boundary leaf of the adjacent-hidden-vertex obstruction by `r`
independent copies. Moving the retained core vertex requires permission to
change at least `r` boundary vertices during the history. A uniform repair
achieves this budget and restores the full boundary at its endpoint.

The lower bound rules out a constant bound on the number of participating
context vertices for this contract. The upper bound has a short uniform proof:
an unbounded affected region does not imply an unbounded proof description.
The family has degree-one leaves and unbounded core degrees; it does not
satisfy the geometric hypotheses of a minimal Four Colour counterexample.
-/

namespace Mettapedia.GraphTheory.FourColor.BoundaryCooperation

open SimpleGraph Relation KempeChainCertificate

abbrev Vertex (r : ℕ) := Fin 3 ⊕ (Fin 6 × Fin r)

theorem card_vertices (r : ℕ) : Fintype.card (Vertex r) = 3 + 6 * r := by
  simp [Vertex]

def index {r : ℕ} : Vertex r → Fin 9
  | .inl v => ⟨v.val, by omega⟩
  | .inr (g, _) => ⟨3 + g.val, by omega⟩

/-- The same triangle, with `r` copies of each of its six leaves. -/
def graph (r : ℕ) : SimpleGraph (Vertex r) := AdjacentHiddenObstruction.graph.comap index

def projection (r : ℕ) : graph r →g AdjacentHiddenObstruction.graph where
  toFun := index
  map_rel' := fun h => h

def state (r : ℕ) (s : Fin 4) : (graph r).Coloring (Fin 4) :=
  (AdjacentHiddenObstruction.state s).comp (projection r)

@[simp] theorem state_apply {r : ℕ} (s : Fin 4) (v : Vertex r) :
    state r s v = AdjacentHiddenObstruction.state s (index v) := rfl

/-- Only leaves in `allowed` may cooperate; every other leaf stays fixed. -/
def fixedBoundary {r : ℕ} (allowed : Finset (Fin 6 × Fin r)) : Set (Vertex r)
  | .inl _ => False
  | .inr p => p ∉ allowed

def pick {r : ℕ} (choice : Fin 6 → Fin r) (v : Fin 9) : Vertex r :=
  if h : v.val < 3 then .inl ⟨v.val, h⟩
  else .inr (⟨v.val - 3, by omega⟩, choice ⟨v.val - 3, by omega⟩)

@[simp] theorem index_pick {r : ℕ} (choice : Fin 6 → Fin r) (v : Fin 9) :
    index (pick choice v) = v := by
  apply Fin.ext
  unfold pick
  split
  · rfl
  · simp only [index]; omega

@[simp] theorem pick_core {r : ℕ} (choice : Fin 6 → Fin r) (v : Fin 3) :
    pick choice (index (.inl v : Vertex r)) = .inl v := by
  simp [pick, index, v.isLt]

/-- One representative from each leaf group realizes the small obstruction. -/
def pickHom {r : ℕ} (choice : Fin 6 → Fin r) : AdjacentHiddenObstruction.graph →g graph r where
  toFun := pick choice
  map_rel' := by
    intro v w h
    change AdjacentHiddenObstruction.graph.Adj (index (pick choice v)) (index (pick choice w))
    simpa using h

@[simp] theorem state_comp_pick {r : ℕ} (choice : Fin 6 → Fin r) (s : Fin 4) :
    (state r s).comp (pickHom choice) = AdjacentHiddenObstruction.state s := by
  apply DFunLike.ext
  intro v
  change AdjacentHiddenObstruction.state s (index (pick choice v)) = AdjacentHiddenObstruction.state s v
  rw [index_pick]

/-- If every leaf group retains a protected representative, no core vertex
can move. Unprotected leaves may still move; the whole state need not freeze. -/
theorem core_fixed {r : ℕ} (allowed : Finset (Fin 6 × Fin r))
    (spared : ∀ g : Fin 6, ∃ i : Fin r, (g, i) ∉ allowed)
    (D : (graph r).Coloring (Fin 4))
    (path : ReflTransGen ((graph r).KempeStepAvoiding (fixedBoundary allowed)) (state r 0) D)
    (v : Fin 3) : D (.inl v) = state r 0 (.inl v) := by
  classical
  choose choice good using spared
  have keeps : AdjacentHiddenObstruction.boundary ⊆ (pickHom choice) ⁻¹' fixedBoundary allowed := by
    intro x hx
    have ge : 3 ≤ x.val := hx
    change pick choice x ∈ fixedBoundary allowed
    rw [pick, dite_eq_right (show ¬ x.val < 3 by omega)]
    exact good _
  have projected := kempe_path_comp (pickHom choice) path
  have small := ReflTransGen.mono (fun _ _ h => h.mono keeps) _ _ projected
  rw [state_comp_pick] at small
  have fixed := AdjacentHiddenObstruction.frozen.eq_of_reflTransGen subset_rfl small
  have atCore := DFunLike.congr_fun fixed (index (.inl v : Vertex r))
  change D (pick choice (index (.inl v : Vertex r))) = _ at atCore
  simpa only [pick_core, state_apply] using atCore

private theorem spared_of_card_lt {r : ℕ} (allowed : Finset (Fin 6 × Fin r))
    (small : allowed.card < r) (g : Fin 6) : ∃ i : Fin r, (g, i) ∉ allowed := by
  have injective : Function.Injective (fun i : Fin r => (g, i)) := fun _ _ h => (Prod.mk.inj h).2
  have size : (Finset.univ.image (fun i : Fin r => (g, i))).card = r := by
    rw [Finset.card_image_of_injective _ injective]
    simp
  obtain ⟨p, hp, outside⟩ := Finset.exists_mem_notMem_of_card_lt_card (small.trans_eq size.symm)
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  exact ⟨i, outside⟩

/-- Any history moving the retained third corner must have at least `r`
distinct boundary vertices available for temporary change. -/
theorem boundary_lower_bound {r : ℕ} (allowed : Finset (Fin 6 × Fin r))
    (D : (graph r).Coloring (Fin 4))
    (path : ReflTransGen ((graph r).KempeStepAvoiding (fixedBoundary allowed)) (state r 0) D)
    (moves : D (.inl 2) ≠ state r 0 (.inl 2)) : r ≤ allowed.card := by
  by_contra h
  exact moves (core_fixed allowed (spared_of_card_lt allowed (by omega)) D path 2)

/-- The repair only needs the copies of the original leaf `3`. -/
def repairBudget (r : ℕ) : Finset (Fin 6 × Fin r) :=
  Finset.univ.image (fun i : Fin r => ((0 : Fin 6), i))

@[simp] theorem repairBudget_card (r : ℕ) : (repairBudget r).card = r := by
  rw [repairBudget, Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)]
  simp

@[simp] theorem mem_repairBudget {r : ℕ} (g : Fin 6) (i : Fin r) :
    (g, i) ∈ repairBudget r ↔ g = 0 := by
  simp [repairBudget, Prod.mk.injEq, eq_comm]

private theorem phase (r : ℕ) (s t a b : Fin 4)
    (fixed : ∀ v ∈ AdjacentHiddenObstruction.fixedContext,
      AdjacentHiddenObstruction.state s v = AdjacentHiddenObstruction.state t v)
    (pair : ∀ v, AdjacentHiddenObstruction.state t v = AdjacentHiddenObstruction.state s v ∨
      AdjacentHiddenObstruction.state t v = Equiv.swap a b (AdjacentHiddenObstruction.state s v)) :
    ReflTransGen ((graph r).KempeStepAvoiding (fixedBoundary (repairBudget r)))
      (state r s) (state r t) := by
  apply (state r s).avoiding_of_pointwise_swap (state r t) a b (fixedBoundary (repairBudget r))
  · intro v hv
    cases v with
    | inl v => exact hv.elim
    | inr p =>
      obtain ⟨g, i⟩ := p
      change (g, i) ∉ repairBudget r at hv
      have hn : g ≠ 0 := by simpa only [mem_repairBudget] using hv
      apply fixed
      change 4 ≤ 3 + g.val
      have hg : g.val ≠ 0 := fun h => hn (Fin.ext h)
      omega
  · intro v
    exact pair (index v)

/-- Three partial-transposition phases give an actual history for every `r`.
The middle phase may switch several disjoint leaf components. -/
theorem repair (r : ℕ) :
    ReflTransGen ((graph r).KempeStepAvoiding (fixedBoundary (repairBudget r)))
      (state r 0) (state r 3) := by
  have first := phase r 0 1 0 1 (by decide +kernel) (by decide +kernel)
  have middle := phase r 1 2 0 2 (by decide +kernel) (by decide +kernel)
  have last := phase r 2 3 1 2 (by decide +kernel) (by decide +kernel)
  exact first.trans (middle.trans last)

/-- The temporary cooperation restores the entire boundary word. -/
theorem boundary_restored (r : ℕ) (p : Fin 6 × Fin r) :
    state r 0 (.inr p) = state r 3 (.inr p) := by
  apply AdjacentHiddenObstruction.same_boundary
  change 3 ≤ 3 + p.1.val
  omega

/-- The abstract operation still hides only the same two adjacent corners. -/
abbrev retained (r : ℕ) : Set (Vertex r) := ({.inl 0, .inl 1} : Set (Vertex r))ᶜ

/-- For every width, a single retained component switch produces the target
restriction. The endpoints have the full extensions explicitly given above. -/
theorem retained_switch (r : ℕ) :
    ((graph r).induce (retained r)).KempeStepAvoiding
      (Subtype.val ⁻¹' fixedBoundary ∅)
      ((state r 0).restrictInduce (retained r)) ((state r 3).restrictInduce (retained r)) := by
  apply KempeIndependentLift.single_vertex (⟨.inl 2, by simp [retained]⟩ : retained r)
  · intro x hx
    obtain ⟨v, hv⟩ := x
    cases v with
    | inl c =>
      fin_cases c
      · exact (hv (by simp)).elim
      · exact (hv (by simp)).elim
      · exact (hx (Subtype.ext rfl)).elim
    | inr p => exact boundary_restored r p
  · change ¬ False
    exact not_false

/-- Every successful fixed-permission repair requires at least the exhibited
budget. This counts vertices, not proof length or stored interface bits. -/
theorem repair_budget_optimal {r : ℕ} (allowed : Finset (Fin 6 × Fin r))
    (path : ReflTransGen ((graph r).KempeStepAvoiding (fixedBoundary allowed))
      (state r 0) (state r 3)) : (repairBudget r).card ≤ allowed.card := by
  rw [repairBudget_card]
  exact boundary_lower_bound allowed _ path (by change (0 : Fin 4) ≠ 1; decide)

/-- There is no bound independent of width on the permitted cooperating
boundary vertices, even though one uniform repair proves every width. -/
theorem no_uniform_budget :
    ¬ ∃ k : ℕ, ∀ r : ℕ, ∃ allowed : Finset (Fin 6 × Fin r), allowed.card ≤ k ∧
      ReflTransGen ((graph r).KempeStepAvoiding (fixedBoundary allowed))
        (state r 0) (state r 3) := by
  rintro ⟨k, repairs⟩
  obtain ⟨allowed, size, path⟩ := repairs (k + 1)
  have bound := repair_budget_optimal allowed path
  rw [repairBudget_card] at bound
  omega

theorem repair_history (r : ℕ) : Nonempty (History (state r 0) (state r 3)) :=
  nonempty_history_iff.mpr (ReflTransGen.mono (fun _ _ h => h.kempeStep) _ _ (repair r))

end Mettapedia.GraphTheory.FourColor.BoundaryCooperation
