import MettapediaFourColor.NearLinearCharge

/-!
# Deterministic traversal of oriented rule occurrences

Fixing one actual dart fixes the result of every permitted reversal or
rotation. A checked source trace therefore determines actual vertex images,
even when distant source vertices coincide in the ambient graph.

This is the local traversal principle of arXiv:2603.24880v1, Section 9.1,
also used by the source program's homomorphism search. The theorem concerns
actual dart operations; it does not trust that program's search result.
-/

namespace FourColor.RuleTraversal

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open NearLinearRuleData NearLinearCharge

inductive Move where
  | flip
  | next
  | previous
  deriving DecidableEq

abbrev State (r : Fin 84) := Vertex r × Vertex r
abbrev Trace (r : Fin 84) := List (Move × State r)

def Step (r : Fin 84) (op : Move) (p q : State r) : Prop :=
  match op with
  | .flip => q.1 = p.2 ∧ q.2 = p.1
  | .next => q.1 = p.1 ∧ Turn r p.1 p.2 q.2
  | .previous => q.1 = p.1 ∧ Turn r p.1 q.2 p.2

instance (r : Fin 84) (op : Move) (p q : State r) : Decidable (Step r op p q) := by
  cases op <;> unfold Step <;> infer_instance

def Valid (r : Fin 84) (p : State r) : Trace r → Prop
  | [] => True
  | (op, q) :: tail => (graph r).Adj q.1 q.2 ∧ Step r op p q ∧ Valid r q tail

instance (r : Fin 84) (p : State r) (trace : Trace r) : Decidable (Valid r p trace) := by
  induction trace generalizing p with
  | nil => exact isTrue trivial
  | cons head tail ih =>
      letI := ih head.2
      unfold Valid
      infer_instance

def lastState {r : Fin 84} (p : State r) : Trace r → State r
  | [] => p
  | (_, q) :: tail => lastState q tail

variable {V : Type*} {G : SimpleGraph V} (rotation : Data G)

def move (op : Move) (d : G.Dart) : G.Dart :=
  match op with
  | .flip => d.symm
  | .next => rotation.vertexRotation d
  | .previous => rotation.vertexRotation.symm d

def execute {r : Fin 84} (d : G.Dart) : Trace r → G.Dart
  | [] => d
  | (op, _) :: tail => execute (move rotation op d) tail

variable [G.LocallyFinite] {rotation} {r : Fin 84}

def imageDart (x : Occurrence rotation r) (p : State r)
    (hp : (graph r).Adj p.1 p.2) : G.Dart :=
  ⟨(x.vertex p.1, x.vertex p.2), x.edge p.1 p.2 hp⟩

theorem step_transport (x : Occurrence rotation r) (op : Move) (p q : State r)
    (hp : (graph r).Adj p.1 p.2) (hq : (graph r).Adj q.1 q.2)
    (h : Step r op p q) :
    move rotation op (imageDart x p hp) = imageDart x q hq := by
  rcases p with ⟨a, b⟩
  rcases q with ⟨c, d⟩
  cases op with
  | flip =>
      obtain ⟨rfl, rfl⟩ := h
      rfl
  | next =>
      obtain ⟨rfl, ht⟩ := h
      exact x.turn _ _ _ hp hq ht
  | previous =>
      obtain ⟨rfl, ht⟩ := h
      apply rotation.vertexRotation.injective
      change rotation.vertexRotation (rotation.vertexRotation.symm _) = _
      rw [Equiv.apply_symm_apply]
      exact (x.turn _ _ _ hq hp ht).symm

/-- A valid source construction path commutes with every actual occurrence.
The same occurrence supplies every intermediate image. -/
theorem trace_transport (x : Occurrence rotation r) (p : State r)
    (hp : (graph r).Adj p.1 p.2) (trace : Trace r) (h : Valid r p trace) :
    ∃ hend : (graph r).Adj (lastState p trace).1 (lastState p trace).2,
      execute rotation (imageDart x p hp) trace = imageDart x (lastState p trace) hend := by
  induction trace generalizing p with
  | nil => exact ⟨hp, rfl⟩
  | cons head tail ih =>
      obtain ⟨hq, hs, ht⟩ := h
      obtain ⟨hend, he⟩ := ih head.2 hq ht
      refine ⟨hend, ?_⟩
      change execute rotation (move rotation head.1 (imageDart x p hp)) tail = _
      rw [step_transport x head.1 p head.2 hp hq hs]
      exact he

end FourColor.RuleTraversal
