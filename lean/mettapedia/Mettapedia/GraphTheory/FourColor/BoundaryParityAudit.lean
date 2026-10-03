import Mettapedia.GraphTheory.Kempe.BoundaryParity
import Mettapedia.GraphTheory.FourColor.ComponentDetachAudit

/-!
# Fixed-region obstruction and two successful enlargements

Each of two vertices in the retained exterior has a pentagonal neighbour
walk. Neither singleton can ever be an entire two-colour component in any
proper four-colouring. Both vertices nevertheless belong to each of the
two larger regions detached by the supplied physical repairs. Thus those
repairs use strictly larger regions and reconstruct whole-graph colourings.
-/

namespace SimpleGraph.KempeDetachParity

open KempeDetachExample

def seed (j : Fin 2) : Fin 155 := if j = 0 then 74 else 105
def neighbourCycle (j : Fin 2) : List (Fin 155) :=
  if j = 0 then [14,72,76,59,109,14] else [89,148,152,143,145,89]

theorem cycle_nonempty : ∀ j, neighbourCycle j ≠ [] := by decide +kernel
theorem cycle_chain : ∀ j, (neighbourCycle j).IsChain graph.Adj := by decide +kernel
theorem cycle_endpoints : ∀ j,
    (neighbourCycle j).head (cycle_nonempty j) =
      (neighbourCycle j).getLast (cycle_nonempty j) := by decide +kernel
theorem cycle_length : ∀ j, (neighbourCycle j).length = 6 := by decide +kernel

theorem cycle_neighbours : ∀ j, ∀ v ∈ neighbourCycle j, v ≠ seed j ∧ graph.Adj (seed j) v := by
  have h : ∀ j, (neighbourCycle j).all (fun v => decide (v ≠ seed j ∧ graph.Adj (seed j) v)) = true := by
    decide +kernel
  exact fun j v hv => of_decide_eq_true (List.all_eq_true.mp (h j) v hv)

def walk (j : Fin 2) : graph.Walk
    ((neighbourCycle j).head (cycle_nonempty j))
    ((neighbourCycle j).head (cycle_nonempty j)) :=
  (Walk.ofSupport (neighbourCycle j) (cycle_nonempty j) (cycle_chain j)).copy
    rfl (cycle_endpoints j).symm

theorem walk_support (j : Fin 2) : (walk j).support = neighbourCycle j := by
  simp only [walk, Walk.support_copy, Walk.support_ofSupport]

theorem walk_external (j : Fin 2) : ∀ v ∈ (walk j).support,
    v ∈ KempeBoundaryParity.outside graph {seed j} := by
  intro v hv
  obtain ⟨ne, edge⟩ := cycle_neighbours j v (by simpa only [walk_support] using hv)
  exact ⟨ne, seed j, rfl, edge⟩

theorem walk_odd (j : Fin 2) : Odd (walk j).length := by
  have h := (walk j).length_support
  rw [walk_support, cycle_length] at h
  have len : (walk j).length = 5 := by omega
  rw [len]
  decide

/-- No preparation history can isolate either fixed singleton. -/
theorem singleton_ne_component (j : Fin 2) (C : graph.Coloring (Fin 4))
    (a b : Fin 4) (different : a ≠ b)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) :
    C.kempeComponentSet a b K ≠ {seed j} :=
  KempeBoundaryParity.component_ne_of_odd_walk _ (walk j) (walk_external j)
    (walk_odd j) C a b different K

theorem seed_retained : ∀ i j, seed j ∈ trace i 1 := by decide +kernel
theorem selected_distinct : ∀ i, (0 : Fin 4) ≠ secondColour i 1 := by decide +kernel

/-- Any closed region retaining the seed must absorb a pentagon vertex. -/
theorem enlargement_absorbs_neighbour (j : Fin 2) (C : graph.Coloring (Fin 4))
    (a b : Fin 4) (different : a ≠ b) (T : Set (Fin 155))
    (retained : seed j ∈ T) (closed : KempeBoundaryParity.Closed C a b T) :
    ∃ v ∈ neighbourCycle j, v ∈ T := by
  have inclusion : ({seed j} : Set (Fin 155)) ⊆ T := by
    intro v hv
    have hv' : v = seed j := hv
    simpa only [hv'] using retained
  simpa only [walk_support] using
    KempeBoundaryParity.absorb_odd_walk _ T inclusion (walk j) (walk_external j)
      (walk_odd j) C a b different closed

/-- Both actual detachment histories enlarge each obstructed singleton. -/
theorem strictly_larger (i j : Fin 2) :
    ({seed j} : Set (Fin 155)) ⊂
      (before i 1).kempeComponentSet 0 (secondColour i 1) (component i 1) := by
  apply Set.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro v hv
    have hv' : v = seed j := hv
    subst v
    exact (component_iff i 1 (all_closed i 1) _).mpr (seed_retained i j)
  · exact Ne.symm (singleton_ne_component j (before i 1) 0 (secondColour i 1)
      (selected_distinct i) (component i 1))

/-- The enlarged component participates in a physical repair admitting
literal whole-graph reconstruction. Both facts refer to the same history. -/
theorem enlarged_repair (i j : Fin 2) :
    ({seed j} : Set (Fin 155)) ⊂
      (before i 1).kempeComponentSet 0 (secondColour i 1) (component i 1) ∧
    state (stage i 3) ∈ graph.KempeClosure (state 0) ∧
    ∃ F : ambient.Coloring (Fin 4), ∀ v,
      F (includeExterior v) = state (stage i 3) v :=
  ⟨strictly_larger i j, physical_history i, completed i, reconstructed i⟩

end SimpleGraph.KempeDetachParity

open Lean Elab Command SimpleGraph
run_cmd do
  let env ← getEnv
  let roots := [``KempeBoundaryParity.outside_two_colorable,
    ``KempeBoundaryParity.not_closed_of_odd_walk, ``KempeBoundaryParity.component_ne_of_odd_walk,
    ``KempeBoundaryParity.absorb_odd_walk,
    ``KempeDetachParity.cycle_chain, ``KempeDetachParity.cycle_neighbours,
    ``KempeDetachParity.walk_external, ``KempeDetachParity.walk_odd,
    ``KempeDetachParity.singleton_ne_component, ``KempeDetachParity.enlargement_absorbs_neighbour,
    ``KempeDetachParity.strictly_larger,
    ``KempeDetachParity.enlarged_repair]
  let consumers := [``KempeDetachParity.singleton_ne_component,
    ``KempeDetachParity.strictly_larger, ``KempeDetachParity.enlarged_repair]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.WheelRepairData, `FourColor.ExceptionalRepairData]
  let mut all : NameSet := {}
  for root in roots do
    let mut todo := [root]
    let mut seen : NameSet := {}
    while !todo.isEmpty do
      let name := todo.head!
      todo := todo.tail!
      if !seen.contains name then
        seen := seen.insert name
        all := all.insert name
        if forbidden.any (·.isPrefixOf name) then
          throwError m!"Forbidden dependency in {root}: {name}"
        if let some info := env.find? name then
          todo := info.getUsedConstantsAsSet.toList ++ todo
    if consumers.contains root then
      unless seen.contains ``KempeBoundaryParity.component_ne_of_odd_walk do
        throwError m!"Missing boundary-parity theorem in {root}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Boundary parity: {roots.length} roots; {all.toList.length} declarations."
