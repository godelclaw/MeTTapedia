import Mettapedia.GraphTheory.Kempe.RouteProjection
import Lean.Util.CollectAxioms

/-!
# A triangular mesh consumes bichromatic route projection

The twenty-one vertices form a width-five triangular mesh. Its corners
are pairwise nonadjacent. Each original triangle edge is instead a
five-edge alternating path. The general route theorem therefore projects
every fixed-pair phase to a proper colouring of the three corners.

The larger spherical examples and their short-cycle census are separate
program evidence. No assertion about arbitrary mixed-pair histories or
geometric coverage is made here.
-/

namespace SimpleGraph.KempeOddMesh

def edges : List (Fin 21 × Fin 21) := [(0,3),(0,4),(1,19),(1,20),(2,10),(2,11),(3,4),(3,5),(3,12),(4,5),(4,6),(5,6),(5,7),(5,12),(5,13),(6,7),(6,8),(7,8),(7,9),(7,13),(7,14),(8,9),(8,10),(9,10),(9,11),(9,14),(9,15),(10,11),(11,15),(12,13),(12,16),(13,14),(13,16),(13,17),(14,15),(14,17),(14,18),(15,18),(16,17),(16,19),(17,18),(17,19),(17,20),(18,20),(19,20)]

def graph : SimpleGraph (Fin 21) where
  Adj u v := (u,v) ∈ edges ∨ (v,u) ∈ edges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by intro v; revert v; decide +kernel⟩

instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

def colours (v : Fin 21) : Fin 4 :=
  ([0,1,2,1,2,3,0,1,2,3,0,1,0,2,0,2,1,3,1,0,2] : List (Fin 4)).get ⟨v.val, v.isLt⟩

theorem proper : ∀ u v, graph.Adj u v → colours u ≠ colours v := by decide +kernel
def initial : graph.Coloring (Fin 4) := .mk colours (fun h => proper _ _ h)

def corner (v : Fin 3) : Fin 21 := v.castLE (by decide)
def triangle : (⊤ : SimpleGraph (Fin 3)).Coloring (Fin 4) :=
  .mk (fun v => v.castLE (by decide)) (by
    intro u v h eq
    exact h (Fin.ext (congrArg (fun x : Fin 4 => x.val) eq)))

theorem corner_colours : ∀ v, initial (corner v) = triangle v := by decide +kernel
theorem corners_nonadjacent : ∀ u v, ¬ graph.Adj (corner u) (corner v) := by decide +kernel

def routeList (u v : Fin 3) : List (Fin 21) :=
  if u = 0 ∧ v = 1 then [0,3,12,16,19,1]
  else if u = 1 ∧ v = 0 then [1,19,16,12,3,0]
  else if u = 1 ∧ v = 2 then [1,20,18,15,11,2]
  else if u = 2 ∧ v = 1 then [2,11,15,18,20,1]
  else if u = 2 ∧ v = 0 then [2,10,8,6,4,0]
  else if u = 0 ∧ v = 2 then [0,4,6,8,10,2]
  else [corner u]

theorem route_nonempty : ∀ u v, routeList u v ≠ [] := by decide +kernel
theorem route_chain : ∀ u v, (routeList u v).IsChain graph.Adj := by decide +kernel
theorem route_head : ∀ u v, (routeList u v).head (route_nonempty u v) = corner u := by decide +kernel
theorem route_last : ∀ u v, (routeList u v).getLast (route_nonempty u v) = corner v := by decide +kernel
theorem route_colours : ∀ u v x, x ∈ routeList u v →
    initial x = triangle u ∨ initial x = triangle v := by decide +kernel

def route (u v : Fin 3) : graph.Walk (corner u) (corner v) :=
  (Walk.ofSupport (routeList u v) (route_nonempty u v) (route_chain u v)).copy
    (route_head u v) (route_last u v)

theorem route_support (u v : Fin 3) : (route u v).support = routeList u v := by
  simp only [route, Walk.support_copy, Walk.support_ofSupport]

theorem phase_projects (D : graph.Coloring (Fin 4)) {a b : Fin 4}
    (history : Relation.ReflTransGen (KempePairHistory.Step a b) initial D) :
    ∃ F : (⊤ : SimpleGraph (Fin 3)).Coloring (Fin 4),
      (∀ v, F v = D (corner v)) ∧
      ∀ v, F v = triangle v ∨ F v = Equiv.swap a b (triangle v) := by
  apply KempeRouteProjection.project_phase corner triangle initial D corner_colours
    (fun u v _ => ⟨route u v, fun x hx => route_colours u v x (by simpa only [route_support] using hx)⟩)
    history

end SimpleGraph.KempeOddMesh

open Lean Elab Command SimpleGraph
run_cmd do
  let env ← getEnv
  let roots := [``KempeRouteProjection.changed_along_walk,
    ``KempeRouteProjection.routed_endpoints_ne, ``KempeRouteProjection.project_phase,
    ``KempeOddMesh.proper, ``KempeOddMesh.corners_nonadjacent,
    ``KempeOddMesh.route_chain, ``KempeOddMesh.route_colours, ``KempeOddMesh.phase_projects]
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
    if root == ``KempeOddMesh.phase_projects then
      unless seen.contains ``KempeRouteProjection.project_phase do
        throwError "Missing general route projection theorem"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Odd mesh: {roots.length} roots; {all.toList.length} declarations."
