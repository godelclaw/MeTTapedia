import MettapediaFourColor.NearLinearDiamondData
import MettapediaFourColor.FacialPatchInduced

/-!
# Joint geometry for two four-triangle patches

D0051 and D0052 are from near-linear-4ct/reducible-configurations, revision
c2ce7a96e35256201526e2abb51a39d04a588b53, copyright 2026 Yuta Inoue (MIT).
The unaltered sources and licence are in tools/fourcolor/near-linear.

The fan and tripod have different internal graphs. One facial-interval
argument proves injectivity and adjacency reflection for both, retaining
the same vertices throughout all four triangles. The ambient degree bounds
may vary; their published degree profiles are particular consumers.
Completing the ten-port boundary and repairing colourings remain separate.
-/

namespace FourColor.FourTriangleCore

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open NearLinearDiamondData ExceptionalCoreOrientation ExceptionalOverlap

set_option maxRecDepth 32768

/-- Index zero is the fan D0051; index one is the tripod D0052. -/
def source : Fin 2 → String := ![
  "16 10\n11 5 8 9 13 12 7\n12 6 6 7 11 13 14 5\n13 7 10 15 16 14 12 11 9\n14 6 4 5 12 13 16 3\n15 5 2 16 13 10 1\n16 5 3 14 13 15 2\n",
  "16 10\n11 5 8 9 12 13 7\n12 6 10 16 14 13 11 9\n13 6 7 11 12 14 15 6\n14 7 3 4 15 13 12 16 2\n15 5 5 6 13 14 4\n16 5 2 14 12 10 1\n"]

def input (s : Fin 2) : Input 16 10 where
  source := source s
  valid := by fin_cases s <;> decide +kernel

def core (s : Fin 2) : SimpleGraph (Fin 6) :=
  (input s).graph.comap (fun i => i.natAdd 10)

instance (s : Fin 2) : DecidableRel (core s).Adj := by unfold core; infer_instance

def star : Fin 2 → Fin 6 → List (Fin 6) := ![
  ![[2, 1], [0, 2, 3], [4, 5, 3, 1, 0], [1, 2, 5], [5, 2], [3, 2, 4]],
  ![[1, 2], [5, 3, 2, 0], [0, 1, 3, 4], [4, 2, 1, 5], [2, 3], [3, 1]]]

def spoke (s : Fin 2) (i : Fin 6) (p : Fin (star s i).length) := (star s i).get p
def degree (s : Fin 2) (i : Fin 6) := (coreRow (source s) i.val).getD 1 0
def first : Fin 2 → Fin 4 → Fin 6 := ![![2, 2, 2, 2], ![1, 1, 2, 3]]
def second : Fin 2 → Fin 4 → Fin 6 := ![![4, 5, 3, 1], ![3, 2, 3, 1]]
def third : Fin 2 → Fin 4 → Fin 6 := ![![5, 3, 1, 0], ![2, 0, 4, 5]]

theorem star_specs : ∀ (s : Fin 2) (i : Fin 6),
    0 < (star s i).length ∧ (star s i).length < degree s i ∧
      ∀ j, (core s).Adj i j ↔ ∃ p, spoke s i p = j := by decide +kernel

/-- All prescribed degrees and every known core turn are read from the
complete source stars, including their boundary neighbours. -/
theorem source_stars : ∀ (s : Fin 2) (i : Fin 6),
    ((input s).internalStar (i.natAdd 10)).length = degree s i ∧
      ∀ p q : Fin (star s i).length, q.val = p.val + 1 →
        List.IsInfix [(spoke s i p).natAdd 10, (spoke s i q).natAdd 10]
          ((input s).internalStar (i.natAdd 10)) := by decide +kernel

theorem step_partition : ∀ (s : Fin 2) (i : Fin 6) (p q : Fin (star s i).length),
    q.val = p.val + 1 → ∃ k : Fin 4,
      (i = first s k ∧ spoke s i p = second s k ∧ spoke s i q = third s k) ∨
      (i = second s k ∧ spoke s i p = third s k ∧ spoke s i q = first s k) ∨
      (i = third s k ∧ spoke s i p = first s k ∧ spoke s i q = second s k) := by
  decide +kernel

theorem consecutive_adjacent : ∀ (s : Fin 2) (i : Fin 6) (p q : Fin (star s i).length),
    q.val = p.val + 1 → (core s).Adj (spoke s i p) (spoke s i q) := by decide +kernel

/-- Every distinct pair is adjacent or lies in one shared source star. -/
theorem short_pairs : ∀ (s : Fin 2) (i j : Fin 6), i ≠ j →
    (core s).Adj i j ∨ ∃ k, (core s).Adj k i ∧ (core s).Adj k j := by decide +kernel

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

structure Reading (s : Fin 2) (rotation : Data G) where
  map : core s →g G
  face : ∀ k : Fin 4,
    Corner rotation (map (first s k)) (map (second s k)) (map (third s k))

variable {s : Fin 2} {rotation : Data G} (r : Reading s rotation)

theorem turns (tri : Triangular rotation) (i : Fin 6) (p q : Fin (star s i).length)
    (next : q.val = p.val + 1) :
    Corner rotation (r.map i) (r.map (spoke s i p)) (r.map (spoke s i q)) := by
  obtain ⟨k, h | h | h⟩ := step_partition s i p q next
  · rcases h with ⟨hi, hp, hq⟩
    rw [hp, hq, hi]
    exact r.face k
  · rcases h with ⟨hi, hp, hq⟩
    rw [hp, hq, hi]
    exact Corner.rotate rotation tri (r.face k)
  · rcases h with ⟨hi, hp, hq⟩
    rw [hp, hq, hi]
    exact Corner.rotate rotation tri (Corner.rotate rotation tri (r.face k))

variable [Finite V]

theorem neighbors_injective
    (proper : ∀ i, (star s i).length < G.degree (r.map i))
    (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic) (i : Fin 6) :
    Function.Injective (fun p => r.map (spoke s i p)) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  apply ExceptionalCoreLocalInjectivity.corner_chain_injective rotation cyclic
    (r.map i) (star_specs s i).1
  · intro p
    exact r.map.map_adj ((star_specs s i).2.2 _ |>.mpr ⟨p, rfl⟩)
  · intro p hp
    exact turns r tri i _ _ rfl
  · exact le_of_lt (proper i)

/-- One proof excludes all collisions for both triangle-attachment shapes. -/
theorem injective
    (proper : ∀ i, (star s i).length < G.degree (r.map i))
    (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic) :
    Function.Injective r.map := by
  intro i j eq
  by_contra ne
  rcases short_pairs s i j ne with edge | ⟨k, hi, hj⟩
  · exact (r.map.map_adj edge).ne eq
  · obtain ⟨p, hp⟩ := (star_specs s k).2.2 i |>.mp hi
    obtain ⟨q, hq⟩ := (star_specs s k).2.2 j |>.mp hj
    have pq := neighbors_injective r proper tri cyclic k
      (show r.map (spoke s k p) = r.map (spoke s k q) by rw [hp, hq]; exact eq)
    exact ne (hp.symm.trans ((congrArg (spoke s k) pq).trans hq))

/-- Facial triangles also exclude every additional ambient core edge. -/
theorem reflects
    (proper : ∀ i, (star s i).length < G.degree (r.map i))
    (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (facial : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj c a →
      Corner rotation a b c ∨ Corner rotation a c b)
    (i j : Fin 6) (adj : G.Adj (r.map i) (r.map j)) : (core s).Adj i j := by
  classical
  have ne : i ≠ j := fun eq => adj.ne (congrArg r.map eq)
  rcases short_pairs s i j ne with edge | ⟨k, hi, hj⟩
  · exact edge
  · obtain ⟨p, rfl⟩ := (star_specs s k).2.2 i |>.mp hi
    obtain ⟨q, rfl⟩ := (star_specs s k).2.2 j |>.mp hj
    have successor (p q : Fin (star s k).length)
        (h : Corner rotation (r.map k) (r.map (spoke s k p)) (r.map (spoke s k q))) :
        q.val = p.val + 1 := by
      apply FacialPatchInduced.corner_chain_successor rotation cyclic (r.map k)
        (star_specs s k).1 (fun t => r.map (spoke s k t))
      · intro t
        exact r.map.map_adj ((star_specs s k).2.2 _ |>.mpr ⟨t, rfl⟩)
      · intro t ht
        exact turns r tri k _ _ rfl
      · exact proper k
      · exact h
    rcases facial _ _ _ (r.map.map_adj hi) adj (r.map.map_adj hj).symm with h | h
    · exact consecutive_adjacent s k p q (successor p q h)
    · exact (consecutive_adjacent s k q p (successor q p h)).symm

/-- Both exact source degree profiles meet the same interval hypotheses. -/
theorem source_profile_embedding (degrees : ∀ i, G.degree (r.map i) = degree s i)
    (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (facial : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj c a →
      Corner rotation a b c ∨ Corner rotation a c b) :
    Function.Injective r.map ∧ ∀ i j, G.Adj (r.map i) (r.map j) ↔ (core s).Adj i j := by
  have proper i : (star s i).length < G.degree (r.map i) := by
    rw [degrees]
    exact (star_specs s i).2.1
  exact ⟨injective r proper tri cyclic, fun i j =>
    ⟨reflects r proper tri cyclic facial i j, r.map.map_adj⟩⟩

end FourColor.FourTriangleCore
