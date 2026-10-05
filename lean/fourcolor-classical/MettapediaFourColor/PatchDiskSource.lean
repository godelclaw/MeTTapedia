import MettapediaFourColor.CyclicCoreStars
import MettapediaFourColor.InducedGraphRotation
import Mathlib.Data.Fintype.EquivFin

/-! # Source contracts for deleting a triangulated patch core

A source records cyclic core rows and short facial fans at the boundary.
The contract contains only source combinatorics. It does not assume an
ambient exterior, planarity of a deletion, or colouring repair.
-/

namespace FourColor.PatchDisk

open SimpleGraph Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open ExceptionalCoreOrientation ExceptionalOverlap

structure Source (n b : ℕ) [NeZero b] where
  graph : SimpleGraph (Fin (b + n))
  decAdj : DecidableRel graph.Adj
  boundary_size : 3 ≤ b
  core_size : 0 < n
  turn : Fin (b + n) → Fin (b + n) → Fin (b + n) → Prop
  core_nonempty : ∀ i, b ≤ i.val → ∃ j, graph.Adj i j
  core_predecessor : ∀ i j, b ≤ i.val → graph.Adj i j →
    ∃ k, graph.Adj i k ∧ turn i k j
  core_boundary_turn : ∀ i j k, turn i j k → j.val < b → k.val < b →
    k.val = (j.val + 1) % b
  fan : Fin b → List (Fin (b + n))
  fan_size : ∀ j, 3 ≤ (fan j).length
  fan_adjacent : ∀ j (i : Fin (fan j).length), graph.Adj (j.castAdd n) ((fan j).get i)
  fan_first : ∀ j, (fan j).get ⟨0, by have := fan_size j; omega⟩ = (j - 1).castAdd n
  fan_last : ∀ j, (fan j).get
    ⟨(fan j).length - 1, by have := fan_size j; omega⟩ = (j + 1).castAdd n
  fan_internal : ∀ j (i : Fin (fan j).length),
    0 < i.val → i.val + 1 < (fan j).length → b ≤ ((fan j).get i).val
  fan_chain : ∀ j, (fan j).IsChain (fun a c =>
    turn (j.castAdd n) c a ∨ turn c a (j.castAdd n) ∨ turn a (j.castAdd n) c)
  boundary_adjacent : ∀ j : Fin b, graph.Adj (j.castAdd n) ((j + 1).castAdd n)
  tip : Fin b → Fin (b + n)
  tip_core : ∀ j, b ≤ (tip j).val
  tip_adjacent : ∀ j, graph.Adj (tip j) (j.castAdd n)
  tip_turn : ∀ j, turn (tip j) (j.castAdd n) ((j + 1).castAdd n)
  core_dart_count : Nat.card {d : graph.Dart // b ≤ d.fst.val ∨ b ≤ d.snd.val} + 6 =
    6 * n + 2 * b

attribute [instance] Source.decAdj

variable {n b : ℕ} [NeZero b] {s : Source n b}
  {V : Type*} {G : SimpleGraph V} {data : Data G}

/-- Core injectivity and local neighbour injectivity allow boundary vertices
from different source stars to coincide. No boundary vertex enters the core. -/
structure Reading (s : Source n b) (data : Data G) where
  hom : s.graph →g G
  core_injective : Set.InjOn hom {i | b ≤ i.val}
  no_capture : ∀ a, ¬b ≤ a.val → hom a ∉ hom '' {i | b ≤ i.val}
  local_injective : ∀ i, b ≤ i.val → Set.InjOn hom (s.graph.neighborSet i)
  turn : ∀ i j k, s.turn i j k → Corner data (hom i) (hom k) (hom j)

/-- Preserved cyclic rows derive complete ambient stars. -/
theorem stars [Finite V] (f : s.graph →g G)
    (turn : ∀ i j k, s.turn i j k → Corner data (f i) (f k) (f j))
    (cyclic : data.IsVertexwiseCyclic) (i : Fin (b + n)) (hi : b ≤ i.val)
    (v : V) (edge : G.Adj (f i) v) : ∃ j, f j = v ∧ s.graph.Adj i j := by
  apply CyclicCoreStars.covers data cyclic f i (s.core_nonempty i hi) ?_ v edge
  intro j hj
  obtain ⟨k,hk,hturn⟩ := s.core_predecessor i j hi hj
  exact ⟨k,hk,turn i k j hturn⟩

/-- Exact prescribed core degrees turn star coverage into local injectivity. -/
theorem neighbours_injective [Fintype V] [DecidableRel G.Adj]
    (f : s.graph →g G)
    (turn : ∀ i j k, s.turn i j k → Corner data (f i) (f k) (f j))
    (cyclic : data.IsVertexwiseCyclic) (i : Fin (b + n)) (hi : b ≤ i.val)
    (degree : G.degree (f i) = s.graph.degree i) :
    Set.InjOn f (s.graph.neighborSet i) := by
  let g : s.graph.neighborSet i → G.neighborSet (f i) :=
    fun j => ⟨f j, f.map_rel j.property⟩
  have onto : Function.Surjective g := by
    intro v
    obtain ⟨j,eq,adj⟩ := stars f turn cyclic i hi v v.property
    exact ⟨⟨j,adj⟩, Subtype.ext eq⟩
  have cards : Fintype.card (s.graph.neighborSet i) =
      Fintype.card (G.neighborSet (f i)) := by
    simpa only [SimpleGraph.card_neighborSet_eq_degree] using degree.symm
  have inj := ((Fintype.bijective_iff_surjective_and_card g).mpr ⟨onto,cards⟩).1
  intro j hj k hk eq
  exact congrArg Subtype.val (inj (show g ⟨j,hj⟩ = g ⟨k,hk⟩ from Subtype.ext eq))

namespace Reading

variable (r : Reading s data)

theorem core_eq {i j : Fin (b + n)} (hi : b ≤ i.val) (eq : r.hom i = r.hom j) : i = j := by
  have hj : b ≤ j.val := by
    by_contra h
    exact r.no_capture j h ⟨i,hi,eq⟩
  exact r.core_injective hi hj eq

theorem core_stars [Finite V] (cyclic : data.IsVertexwiseCyclic)
    (i : Fin (b + n)) (hi : b ≤ i.val) (v : V) (edge : G.Adj (r.hom i) v) :
    ∃ j, r.hom j = v ∧ s.graph.Adj i j := stars r.hom r.turn cyclic i hi v edge

theorem corner [G.LocallyFinite] (tri : Triangular data) {a c d : Fin (b + n)}
    (h : s.turn a c d ∨ s.turn c d a ∨ s.turn d a c) :
    Corner data (r.hom a) (r.hom d) (r.hom c) := by
  rcases h with h | h | h
  · exact r.turn _ _ _ h
  · exact (r.turn _ _ _ h).rotate data tri
  · exact ((r.turn _ _ _ h).rotate data tri).rotate data tri

end Reading
end FourColor.PatchDisk
