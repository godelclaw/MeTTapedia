import Mettapedia.GraphTheory.Kempe.CliqueLift
import Lean.Util.CollectAxioms

/-!
# Icosahedral clique filling: geometry and Kempe lifting

Removing one face leaves a nine-vertex interior attached along a triangle.
The finite incidence checks feed the general clique-attachment theorem;
repair lifting quantifies over all starting colourings and all retained
histories. This module does not assert planar geometry for the larger
source examples, whose oriented sphere reconstruction is program checked.
-/

namespace SimpleGraph.KempeCliqueFill

open Relation KempeIndependentLift

def edges : List (Fin 12 × Fin 12) := [(0,1),(0,2),(0,7),(0,8),(0,11),(1,2),(1,3),(1,6),(1,8),(2,5),(2,6),(2,11),(3,4),(3,6),(3,8),(3,9),(4,5),(4,6),(4,9),(4,10),(5,6),(5,10),(5,11),(7,8),(7,9),(7,10),(7,11),(8,9),(9,10),(10,11)]

def graph : SimpleGraph (Fin 12) where
  Adj u v := (u,v) ∈ edges ∨ (v,u) ∈ edges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by intro v; revert v; decide +kernel⟩

instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

def hidden : Finset (Fin 12) := Finset.univ.filter (3 ≤ ·.val)
def seam : Set (Fin 12) := {v | v.val < 3}

theorem seam_clique : graph.IsClique seam := by
  change ∀ x : Fin 12, x.val < 3 → ∀ y : Fin 12, y.val < 3 → x ≠ y → graph.Adj x y
  decide +kernel

theorem seam_retained : seam ⊆ (↑hidden)ᶜ := by
  change ∀ x : Fin 12, x.val < 3 → x ∉ hidden
  decide +kernel

theorem attachment : ∀ x ∈ hidden, ∀ y, y ∉ hidden → graph.Adj x y → y ∈ seam := by
  change ∀ x ∈ hidden, ∀ y, y ∉ hidden → graph.Adj x y → y.val < 3
  decide +kernel

def colours (v : Fin 12) : Fin 4 :=
  ([0,1,2,0,1,0,3,1,2,3,2,3] : List (Fin 4)).get ⟨v.val, v.isLt⟩

theorem colours_proper : ∀ x y, graph.Adj x y → colours x ≠ colours y := by
  decide +kernel

theorem degree_five : ∀ x, (Finset.univ.filter (graph.Adj x)).card = 5 := by
  decide +kernel

/-- Every retained pair history lifts from every existing cap colouring. -/
theorem repair_lifts {α : Type*} [DecidableEq α]
    (C : graph.Coloring α) (D : (graph.induce (↑hidden)ᶜ).Coloring α)
    (path : ReflTransGen (PairStep (graph.induce (↑hidden)ᶜ) ∅)
      (C.restrictInduce (↑hidden)ᶜ) D) :
    ∃ E : graph.Coloring α, E.restrictInduce (↑hidden)ᶜ = D ∧ E ∈ graph.KempeClosure C := by
  obtain ⟨E, hE, history⟩ :=
    (KempeCliqueLift.history_iff hidden seam ∅ seam_clique seam_retained
      (Set.empty_subset _) attachment C D).mp (by simpa using path)
  exact ⟨E, hE, ReflTransGen.mono (fun _ _ step => step.kempeStep) _ _ history⟩

end SimpleGraph.KempeCliqueFill

open Lean Elab Command SimpleGraph
run_cmd do
  let env ← getEnv
  let roots := [``KempeCliqueLift.uniform_on_clique, ``KempeCliqueLift.lift_pair,
    ``KempeCliqueLift.lifts_steps, ``KempeCliqueLift.history_iff,
    ``KempeCliqueFill.seam_clique, ``KempeCliqueFill.attachment,
    ``KempeCliqueFill.colours_proper, ``KempeCliqueFill.degree_five,
    ``KempeCliqueFill.repair_lifts]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.WheelRepairData,
    `FourColor.ExceptionalRepairData]
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
    if root == ``KempeCliqueFill.repair_lifts then
      unless seen.contains ``KempeCliqueLift.history_iff do
        throwError "Missing general clique history theorem"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Clique filling: {roots.length} roots; {all.toList.length} declarations."
