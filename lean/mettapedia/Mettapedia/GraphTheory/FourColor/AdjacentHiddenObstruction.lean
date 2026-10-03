import Mettapedia.GraphTheory.Kempe.TwoVertexFibre
import Mettapedia.GraphTheory.FourColor.KempeChainCertificate

/-!
# Extendable moves need not lift across adjacent hidden vertices

A triangle with two leaves at each corner gives a four-colour example.
Hide two adjacent corners and protect all six leaves. The retained third
corner admits a component switch whose target extends to a full colouring.
The initial full colouring is nevertheless frozen with that context fixed.

Allowing one leaf to change temporarily repairs the obstruction in three
physical switches, restoring every leaf at the endpoint. Thus endpoint
support alone does not justify composing boundary-fixed repair laws beyond
the independent-hidden-set theorem. This example has degree-one leaves;
no minimal-counterexample geometry or universal impossibility is asserted.
-/

namespace Mettapedia.GraphTheory.FourColor.AdjacentHiddenObstruction

open SimpleGraph Relation KempeChainCertificate
open Mettapedia.Combinatorics.Reconfiguration

/-- Triangle `0,1,2`, leaves `3,6` at `0`, `4,7` at `1`, `5,8` at `2`. -/
def graph : SimpleGraph (Fin 9) where
  Adj u v := (u, v) ∈ [(0, 1), (1, 0), (1, 2), (2, 1), (2, 0), (0, 2),
    (0, 3), (3, 0), (1, 4), (4, 1), (2, 5), (5, 2),
    (0, 6), (6, 0), (1, 7), (7, 1), (2, 8), (8, 2)]
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩

instance : DecidableRel graph.Adj := by unfold graph; infer_instance

abbrev hidden : Finset (Fin 9) := {0, 1}
abbrev retained : Set (Fin 9) := (↑hidden)ᶜ
def boundary : Set (Fin 9) := {v | 3 ≤ v.val}
def fixedContext : Set (Fin 9) := {v | 4 ≤ v.val}

instance (v : Fin 9) : Decidable (v ∈ boundary) := inferInstanceAs (Decidable (3 ≤ v.val))
instance (v : Fin 9) : Decidable (v ∈ fixedContext) := inferInstanceAs (Decidable (4 ≤ v.val))

theorem hidden_adjacent : graph.Adj 0 1 := by decide +kernel

def values : Fin 4 → Fin 9 → Fin 4
  | 0 => ![0, 2, 1, 1, 0, 2, 3, 3, 3]
  | 1 => ![1, 2, 0, 0, 0, 2, 3, 3, 3]
  | 2 => ![1, 2, 0, 2, 0, 2, 3, 3, 3]
  | 3 => ![2, 1, 0, 1, 0, 2, 3, 3, 3]

theorem proper : ∀ s u v, graph.Adj u v → values s u ≠ values s v := by decide +kernel

def state (s : Fin 4) : graph.Coloring (Fin 4) := .mk (values s) (fun h => proper s _ _ h)

/-- Both full endpoints have exactly the same protected word. -/
theorem same_boundary : ∀ v ∈ boundary, state 0 v = state 3 v := by decide +kernel

/-- Every active vertex reaches a protected leaf in at most two edges.
This checks local paths, not a table of colouring histories. -/
private theorem leaf_paths : ∀ a b : Fin 4, a ≠ b → ∀ v : Fin 9,
    (state 0 v = a ∨ state 0 v = b) →
    ∃ w : Fin 9, w ∈ boundary ∧ (state 0 w = a ∨ state 0 w = b) ∧
      (w = v ∨ graph.Adj v w ∨ ∃ u : Fin 9,
        graph.Adj v u ∧ (state 0 u = a ∨ state 0 u = b) ∧ graph.Adj u w) := by
  decide +kernel

/-- All nontrivial full components meet the protected context. -/
theorem frozen : (state 0).IsTransparent boundary := by
  intro a b hab K
  obtain ⟨v, hv, rfl⟩ := (state 0).exists_eq_mk_of_kempeComponent K
  have hmem := (state 0).mem_kempeComponentSet_self hv
  obtain ⟨w, hwB, hw, path⟩ := leaf_paths a b hab v hv
  refine ⟨w, ?_, hwB⟩
  rcases path with rfl | edge | ⟨u, vu, hu, uw⟩
  · exact hmem
  · exact (state 0).mem_kempeComponentSet_of_adj hmem edge hw
  · exact (state 0).mem_kempeComponentSet_of_adj
      ((state 0).mem_kempeComponentSet_of_adj hmem vu hu) uw hw

/-- The retained move is an actual single-component switch, not merely a
proper target or an arbitrary abstract relation. -/
theorem retained_switch :
    (graph.induce retained).KempeStepAvoiding (Subtype.val ⁻¹' boundary)
      ((state 0).restrictInduce retained) ((state 3).restrictInduce retained) :=
  KempeIndependentLift.single_vertex (⟨2, by decide⟩ : retained)
    (by decide +kernel) _ (by change ¬ (2 : Fin 9) ∈ boundary; decide +kernel)

/-- Every fibre of this restriction is connected, for any palette. Thus the
failure below is genuinely a step-lifting failure, not a disconnected fibre. -/
theorem fibres_connected {α : Type*} [DecidableEq α] :
    FibresConnected (graph.KempeStepAvoiding (α := α) retained)
      (fun C : graph.Coloring α => C.restrictInduce retained) := by
  intro C D equal
  simpa only [retained, hidden, Finset.coe_insert, Finset.coe_singleton] using
    KempeTwoVertexFibre.fibre_path 0 1 C D (fun x hx0 hx1 =>
      DFunLike.congr_fun equal ⟨x, by simp [retained, hidden, hx0, hx1]⟩)

/-- Even after restricting the reduced moves to genuinely extendable targets,
this particular one admits no lift with the context fixed. -/
theorem no_lift (E : graph.Coloring (Fin 4))
    (target : E.restrictInduce retained = (state 3).restrictInduce retained) :
    ¬ ReflTransGen (graph.KempeStepAvoiding boundary) (state 0) E := by
  intro path
  have eq := frozen.eq_of_reflTransGen subset_rfl path
  have atTwo := DFunLike.congr_fun target (⟨2, by decide⟩ : retained)
  rw [eq] at atTwo
  exact absurd atTwo (by decide +kernel)

/-- On-image step lifting fails for this adjacent hidden pair. -/
theorem not_lifts_image :
    ¬ LiftsSteps (graph.KempeStepAvoiding (α := Fin 4) boundary)
      (ImageStep ((graph.induce retained).KempeStepAvoiding (Subtype.val ⁻¹' boundary))
        (fun C : graph.Coloring (Fin 4) => C.restrictInduce retained))
      (fun C : graph.Coloring (Fin 4) => C.restrictInduce retained) := by
  intro lift
  obtain ⟨E, target, path⟩ := lift (state 0) _ ⟨retained_switch, state 3, rfl⟩
  exact no_lift E target path

/-- Endpoint extension also fails to justify the joint-operation fibration
once the independent-set hypothesis is removed. -/
theorem not_lifts_joint_image :
    ¬ LiftsSteps (graph.KempeStepAvoiding (α := Fin 4) boundary)
      (ImageStep (KempeIndependentLift.PairStep (graph.induce retained)
          (Subtype.val ⁻¹' boundary))
        (fun C : graph.Coloring (Fin 4) => C.restrictInduce retained))
      (fun C : graph.Coloring (Fin 4) => C.restrictInduce retained) := by
  intro lift
  have pair : KempeIndependentLift.PairStep (graph.induce retained)
      (Subtype.val ⁻¹' boundary) ((state 0).restrictInduce retained)
      ((state 3).restrictInduce retained) :=
    ⟨⟨0, 1, by decide +kernel⟩, fun x hx => same_boundary x hx⟩
  obtain ⟨E, target, path⟩ := lift (state 0) _ ⟨pair, state 3, rfl⟩
  exact no_lift E target path

private theorem chain_step (s t a b : Fin 4) (v : Fin 9) (chain : List (Fin 9))
    (active : state s v = a ∨ state s v = b)
    (member : v ∈ chain) (linked : chain.IsChain graph.Adj)
    (colours : ∀ x ∈ chain, state s x = a ∨ state s x = b)
    (closed : ∀ x ∈ chain, ∀ y, graph.Adj x y →
      (state s y = a ∨ state s y = b) → y ∈ chain)
    (avoids : ∀ x ∈ chain, x ∉ fixedContext)
    (answer : ∀ x, state t x = if x ∈ chain then Equiv.swap a b (state s x) else state s x) :
    graph.KempeStepAvoiding fixedContext (state s) (state t) := by
  let K := ((state s).bicoloredSubgraph a b).connectedComponentMk ⟨v, active⟩
  have hv := (state s).mem_kempeComponentSet_self active
  refine ⟨a, b, K, ?_, ?_⟩
  · exact Set.disjoint_left.mpr fun x hx hxB =>
      avoids x (((state s).kempe_component_iff_mem_chain a b K chain linked colours closed
        member hv x).mp hx) hxB
  · apply DFunLike.ext
    intro x
    rw [(state s).swap_apply_of_chain a b K chain linked colours closed member hv x]
    exact answer x

/-- Three physical switches repair the target while only leaf `3` is allowed
to change temporarily. Every other boundary leaf stays fixed at every step. -/
theorem repair_steps :
    graph.KempeStepAvoiding fixedContext (state 0) (state 1) ∧
    graph.KempeStepAvoiding fixedContext (state 1) (state 2) ∧
    graph.KempeStepAvoiding fixedContext (state 2) (state 3) := by
  refine ⟨?_, ?_, ?_⟩
  · exact chain_step 0 1 0 1 0 [2, 0, 3] (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact chain_step 1 2 0 2 3 [3] (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact chain_step 2 3 1 2 0 [1, 0, 3] (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem repaired : ReflTransGen (graph.KempeStepAvoiding fixedContext) (state 0) (state 3) :=
  ((ReflTransGen.single repair_steps.1).tail repair_steps.2.1).tail repair_steps.2.2

/-- The repaired sequence uses the same proof-relevant physical route semantics
as the compositional reductions. The endpoint restores the full boundary. -/
theorem repaired_history : Nonempty (History (state 0) (state 3)) :=
  nonempty_history_iff.mpr
    (ReflTransGen.mono (fun _ _ h => h.kempeStep) _ _ repaired)

end Mettapedia.GraphTheory.FourColor.AdjacentHiddenObstruction
