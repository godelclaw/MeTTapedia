import MettapediaFourColor.ExceptionalCoreOrientation

/-!
# Local injectivity of the actual D1774 reading

A chain of facial corners at one vertex follows consecutive powers of its
actual vertex rotation. A chain no longer than the ambient degree cannot
repeat a neighbour. The generic argument is applied to each source core
star, establishing the local-injectivity prerequisite of the collision
argument in arXiv:2603.24880v1, Lemmas 9.1--9.2.
-/

namespace FourColor.ExceptionalCoreLocalInjectivity

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open ExceptionalPattern ExceptionalOverlap ExceptionalCore ExceptionalCoreOrientation

set_option maxRecDepth 32768

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
  [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (rotation : Data G)

/-- Uniform facial-chain law, independent of the configuration catalogue. -/
theorem corner_chain_injective (cyclic : rotation.IsVertexwiseCyclic)
    (v : V) {n : ℕ} (hn : 0 < n) (ns : Fin n → V)
    (adjacent : ∀ i, G.Adj v (ns i))
    (step : ∀ i (h : i + 1 < n),
      Corner rotation v (ns ⟨i, by omega⟩) (ns ⟨i + 1, h⟩))
    (bound : n ≤ G.degree v) : Function.Injective ns := by
  classical
  let d (i : Fin n) : G.Dart := ⟨(v, ns i), adjacent i⟩
  have ds (i : ℕ) (h : i + 1 < n) :
      rotation.vertexRotation (d ⟨i, by omega⟩) = d ⟨i + 1, h⟩ := by
    obtain ⟨_, _, eq⟩ := step i h
    exact eq
  have dp : ∀ i (h : i < n),
      (rotation.vertexRotation ^ i) (d ⟨0, hn⟩) = d ⟨i, h⟩ := by
    intro i
    induction i with
    | zero => intro h; rfl
    | succ i ih =>
      intro h
      rw [pow_succ', Equiv.Perm.mul_apply, ih (by omega)]
      exact ds i h
  let fiber : Finset G.Dart := Finset.univ.filter fun e => e.fst = v
  have hc : rotation.vertexRotation.IsCycleOn (fiber : Set G.Dart) := by
    simpa [fiber] using cyclic v
  have hcard : fiber.card = G.degree v := by
    change ({e : G.Dart | e.fst = v} : Finset G.Dart).card = G.degree v
    rw [G.dart_fst_fiber_card_eq_degree]
    exact (SimpleGraph.degree_instance_independent v _ _).symm
  have hbase : d ⟨0, hn⟩ ∈ fiber := by simp [fiber, d]
  intro i j hij
  have hd : d i = d j := by
    apply SimpleGraph.Dart.ext
    exact Prod.ext rfl hij
  have hp : (rotation.vertexRotation ^ i.val) (d ⟨0, hn⟩) =
      (rotation.vertexRotation ^ j.val) (d ⟨0, hn⟩) := by
    rw [dp i.val i.isLt, dp j.val j.isLt]
    exact hd
  have hm := (hc.pow_apply_eq_pow_apply hbase).mp hp
  have hi : i.val < fiber.card := by rw [hcard]; exact lt_of_lt_of_le i.isLt bound
  have hj : j.val < fiber.card := by rw [hcard]; exact lt_of_lt_of_le j.isLt bound
  change i.val % fiber.card = j.val % fiber.card at hm
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hm
  exact Fin.ext hm

/-- Keep the core interval in its source order. The separate turn theorem
checks consecutiveness against the full star, including ring neighbours. -/
def star (i : Fin 8) : List (Fin 8) :=
  (input.neighbors (i.natAdd 11)).filterMap fun v =>
    if h : 12 ≤ v ∧ v < 20 then some ⟨v - 12, by omega⟩ else none

def spoke (i : Fin 8) (p : Fin (star i).length) : Fin 8 := (star i).get p

theorem star_specs : ∀ i : Fin 8,
    0 < (star i).length ∧ (star i).length ≤ coreDegree i ∧
      ∀ j, core.Adj i j ↔ ∃ p, spoke i p = j := by decide +kernel

theorem star_steps : ∀ (i : Fin 8) (p q : Fin (star i).length),
    q.val = p.val + 1 → CoreTurn i (spoke i p) (spoke i q) := by decide +kernel

variable {rotation}

/-- Distinct neighbours of any core vertex remain distinct in the ambient
graph. This does not yet exclude collisions at distance three. -/
theorem joint_neighbor_injective (r : JointReading rotation)
    (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (i j k : Fin 8) (hij : core.Adj i j) (hik : core.Adj i k)
    (eq : r.core.map j = r.core.map k) : j = k := by
  obtain ⟨hn, hb, hs⟩ := star_specs i
  have inj : Function.Injective (fun p => r.core.map (spoke i p)) := by
    apply corner_chain_injective rotation cyclic (r.core.map i) hn
    · intro p
      exact r.core.map.map_adj ((hs _).mpr ⟨p, rfl⟩)
    · intro p hp
      exact joint_preserves_turns r tri i _ _ (star_steps i _ _ rfl)
    · rw [r.core.degree]
      exact hb
  obtain ⟨p, rfl⟩ := (hs j).mp hij
  obtain ⟨q, rfl⟩ := (hs k).mp hik
  exact congrArg (spoke i) (inj eq)

end FourColor.ExceptionalCoreLocalInjectivity
