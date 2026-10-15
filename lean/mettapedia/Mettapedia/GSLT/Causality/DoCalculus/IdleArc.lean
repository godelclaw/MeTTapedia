import Mettapedia.GSLT.Causality.DoCalculus.Identification

/-!
# An intervention that reaches neither the outcome nor a covariate

Edges `U → A`, `U → B`, `U → C`, and `A → C`, with latent set `{U}`.
`A` and `B` are c-neighbors, so the bow search and the c-component hedge
both see a hedge. No directed path runs from `A` to `B`, so
`P(B | do(A))` is the observational marginal `P(B)`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.ProbabilityTheory.BayesianNetworks
open Mettapedia.ProbabilityTheory.BayesianNetworks.FiniteDSeparation

inductive Idle
  | u
  | a
  | b
  | c
  deriving DecidableEq

instance : Fintype Idle where
  elems := {Idle.u, Idle.a, Idle.b, Idle.c}
  complete := by intro vertex; cases vertex <;> simp

/-- `U → A`, `U → B`, `U → C`, and `A → C`. -/
def idleGraph : DirectedGraph Idle where
  edges source target :=
    (source = Idle.u ∧ target = Idle.a) ∨
    (source = Idle.u ∧ target = Idle.b) ∨
    (source = Idle.u ∧ target = Idle.c) ∨
    (source = Idle.a ∧ target = Idle.c)

instance : DecidableRel idleGraph.edges := fun _ _ => by
  unfold idleGraph
  infer_instance

def idleL : Finset Idle := {Idle.u}
def idleA : Finset Idle := {Idle.a}
def idleB : Finset Idle := {Idle.b}
def idleEnum : List Idle := [Idle.u, Idle.a, Idle.b, Idle.c]

theorem idle_parents_fail :
    parentsIn idleGraph idleA (∅ : Finset Idle) (∅ : Finset Idle) = false := by
  decide

theorem idle_delete_fail :
    deleteOK idleGraph idleB idleA (∅ : Finset Idle) = false := by
  decide

theorem idle_no_front_mediator :
    findVertex idleEnum (fun v =>
      outsideQuery idleL idleB idleA v &&
        frontDoorReady idleGraph idleA {v} idleB) = none := by
  decide

theorem idle_no_napkin :
    findNapkin idleGraph idleEnum idleL idleB idleA = none := by
  decide

theorem idle_no_singleton_backdoor :
    findVertex idleEnum (fun v =>
      outsideQuery idleL idleB idleA v &&
        backDoorReady idleGraph idleA {v} idleB) = none := by
  decide

/-- `A` reaches `A` and `C`, and neither is `B`. -/
theorem idle_misses_forward :
    missesForward idleGraph idleA (idleB ∪ (∅ : Finset Idle)) = true := by
  decide

/-- The bow search still finds the c-neighbor pair `(B, A)`. -/
theorem idle_bow_pair :
    ((bowPair idleGraph idleEnum idleL idleB idleA).map fun hit => (hit.y, hit.x)) =
      some (Idle.b, Idle.a) := by
  decide

/-- The c-component hedge is real: trunk `{B, C}`, canopy `{A, B, C}`. -/
theorem idle_component_hedge :
    ((componentHedge idleGraph idleEnum idleL idleB idleA).map
      fun hedge => (hedge.trunk, hedge.canopy)) =
      some ({Idle.b, Idle.c}, {Idle.a, Idle.b, Idle.c}) := by
  decide

/-- Fuel 0 deletes the intervention inside `identifyRest`, before the c-component hedge. -/
theorem idle_identify_fuel0_is_marginal :
    identify idleGraph 0 idleEnum idleL idleB idleA (∅ : Finset Idle) =
      .doFree (deleteResult idleB (∅ : Finset Idle)) := by
  have hparents : ¬ parentsIn idleGraph idleA (∅ : Finset Idle) (∅ : Finset Idle) = true := by
    simp [idle_parents_fail]
  have hdelete : ¬ deleteOK idleGraph idleB idleA (∅ : Finset Idle) = true := by
    simp [idle_delete_fail]
  have hmiss : missesForward idleGraph idleA (idleB ∪ (∅ : Finset Idle)) = true :=
    idle_misses_forward
  unfold identify
  split
  · rw [if_neg hparents, if_neg hdelete]
    unfold identifyRest
    rw [if_pos hmiss]
  · rename_i hsucc
    cases hsucc

/-- `P(B | do(A))` is the do-free marginal `P(B)`, not the bow hedge. -/
theorem idle_identify_is_marginal :
    identify idleGraph 2 idleEnum idleL idleB idleA (∅ : Finset Idle) =
      .doFree (deleteResult idleB (∅ : Finset Idle)) ∧
    doFree (deleteResult idleB (∅ : Finset Idle)) = true := by
  refine ⟨?_, delete_result_doFree _ _⟩
  have hparents : ¬ parentsIn idleGraph idleA (∅ : Finset Idle) (∅ : Finset Idle) = true := by
    simp [idle_parents_fail]
  have hdelete : ¬ deleteOK idleGraph idleB idleA (∅ : Finset Idle) = true := by
    simp [idle_delete_fail]
  have hmiss : missesForward idleGraph idleA (idleB ∪ (∅ : Finset Idle)) = true :=
    idle_misses_forward
  unfold identify
  split
  · rename_i hzero
    cases hzero
  · rw [if_neg hparents, if_neg hdelete, if_pos (rfl : (∅ : Finset Idle) = ∅)]
    rw [idle_no_front_mediator, idle_no_napkin, idle_no_singleton_backdoor]
    rw [if_pos hmiss]

end Mettapedia.GSLT.Causality.DoCalculus
