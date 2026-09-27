import Mettapedia.GraphTheory.FourColor.TubeSlabEmbedding
import Mettapedia.GraphTheory.FourColor.SimpleGraphRotationSystem

/-!
# Cyclic frames in cubic graphs

A simple cyclic row determines three distinct outgoing darts at every row
vertex. Chords are allowed: proving that its third edges leave the row is
a separate geometric obligation.
-/

namespace Mettapedia.GraphTheory.FourColor.InducedCycleLayer

open ZigzagRing SimpleGraphDartRotation TubeSlab

variable (k : Nat) [NeZero k]

/-- Successor around the row, with its two alternating vertex classes. -/
def next : Vtx k → Vtx k
  | .inl i => .inr i
  | .inr i => .inl (i + 1)

def prev : Vtx k → Vtx k
  | .inl i => .inr (i - 1)
  | .inr i => .inl i

@[simp] theorem next_prev (v : Vtx k) : next k (prev k v) = v := by
  cases v <;> simp [next, prev]

@[simp] theorem prev_next (v : Vtx k) : prev k (next k v) = v := by
  cases v <;> simp [next, prev]

theorem next_ne_prev (hk : 2 ≤ k) (v : Vtx k) : next k v ≠ prev k v := by
  have hstep (i : Fin k) : i + 1 ≠ i := by
    intro h
    have h1 : (1 : Fin k) = 0 := add_left_cancel (show i + 1 = i + 0 by simpa using h)
    have hv := congrArg Fin.val h1
    simp only [Fin.val_one', Fin.val_zero] at hv
    rw [Nat.mod_eq_of_lt (by omega)] at hv
    omega
  cases v with
  | inl i =>
    intro h
    have he := congrArg (fun j : Fin k => j + 1) (Sum.inr.inj h)
    exact hstep i (by simpa using he)
  | inr i => exact fun h => hstep i (Sum.inl.inj h)

variable {V : Type*} {G : SimpleGraph V}

/-- A simple cycle in cyclic vertex order, allowing ambient chords. -/
structure Frame (G : SimpleGraph V) (k : Nat) [NeZero k] where
  vertex : Vtx k → V
  injective : Function.Injective vertex
  adjacent : ∀ v, G.Adj (vertex v) (vertex (next k v))

/-- Ring darts indexed by their vertex and the port/forward/backward slot. -/
def dartCoordinate : AllDart k ≃ Vtx k × Fin 3 where
  toFun
    | .inl (.inl (i, false)) => (.inl i, 1)
    | .inl (.inl (i, true)) => (.inr i, 2)
    | .inl (.inr (i, false)) => (.inr i, 1)
    | .inl (.inr (i, true)) => (.inl (i + 1), 2)
    | .inr v => (v, 0)
  invFun
    | (v, 0) => .inr v
    | (.inl i, 1) => .inl (.inl (i, false))
    | (.inr i, 1) => .inl (.inr (i, false))
    | (.inl i, 2) => .inl (.inr (i - 1, true))
    | (.inr i, 2) => .inl (.inl (i, true))
  left_inv := by
    rintro ((⟨i, _ | _⟩ | ⟨i, _ | _⟩) | (i | i)) <;> simp
  right_inv := by
    rintro ⟨i | i, j⟩ <;> fin_cases j <;> simp

namespace Frame

variable {k} (C : Frame G k)

theorem adjacent_prev (v : Vtx k) : G.Adj (C.vertex v) (C.vertex (prev k v)) := by
  simpa only [next_prev] using (C.adjacent (prev k v)).symm

variable [DecidableEq V] [G.LocallyFinite]
variable (hk : 2 ≤ k) (hG : G.IsRegularOfDegree 3)

include hk hG

/-- Cubicity constructs the third neighbour, rather than requiring a
displayed port at each cycle vertex. -/
theorem existsUnique_port (v : Vtx k) :
    ∃! p, G.Adj (C.vertex v) p ∧ p ≠ C.vertex (next k v) ∧ p ≠ C.vertex (prev k v) := by
  classical
  let candidates := ((G.neighborFinset (C.vertex v)).erase (C.vertex (next k v))).erase
    (C.vertex (prev k v))
  have hne := C.injective.ne (next_ne_prev k hk v)
  have hn : C.vertex (next k v) ∈ G.neighborFinset (C.vertex v) := by
    simpa using C.adjacent v
  have hp : C.vertex (prev k v) ∈ (G.neighborFinset (C.vertex v)).erase
      (C.vertex (next k v)) := by
    exact Finset.mem_erase.mpr ⟨hne.symm, by simpa using C.adjacent_prev v⟩
  have hc : candidates.card = 1 := by
    have h := hG.degree_eq (C.vertex v)
    change (G.neighborFinset (C.vertex v)).card = 3 at h
    have h₁ := Finset.card_erase_of_mem hn
    have h₂ := Finset.card_erase_of_mem hp
    dsimp only [candidates]
    omega
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc
  refine ⟨p, ?_, ?_⟩
  · have hm : p ∈ candidates := by simp [hp]
    simp only [candidates, Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hm
    exact ⟨hm.2.2, hm.2.1, hm.1⟩
  · intro q hq
    have hm : q ∈ candidates := by
      simp only [candidates, Finset.mem_erase, SimpleGraph.mem_neighborFinset]
      exact ⟨hq.2.2, hq.2.1, hq.1⟩
    simpa only [hp, Finset.mem_singleton] using hm

noncomputable def port (v : Vtx k) : V := Classical.choose (C.existsUnique_port hk hG v)

theorem port_spec (v : Vtx k) :
    G.Adj (C.vertex v) (C.port hk hG v) ∧
      C.port hk hG v ≠ C.vertex (next k v) ∧ C.port hk hG v ≠ C.vertex (prev k v) :=
  (Classical.choose_spec (C.existsUnique_port hk hG v)).1

theorem neighborFinset_eq (v : Vtx k) :
    G.neighborFinset (C.vertex v) =
      {C.port hk hG v, C.vertex (next k v), C.vertex (prev k v)} := by
  classical
  obtain ⟨hp, hpn, hpp⟩ := C.port_spec hk hG v
  have hnp := C.injective.ne (next_ne_prev k hk v)
  have hs : {C.port hk hG v, C.vertex (next k v), C.vertex (prev k v)} ⊆
      G.neighborFinset (C.vertex v) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · simpa using hp
    · simpa using C.adjacent v
    · simpa using C.adjacent_prev v
  apply (Finset.eq_of_subset_of_card_le hs ?_).symm
  have h := hG.degree_eq (C.vertex v)
  change (G.neighborFinset (C.vertex v)).card = 3 at h
  simp [h, hpn, hpp, hnp]

theorem adjacent_iff (v : Vtx k) (w : V) :
    G.Adj (C.vertex v) w ↔
      w = C.port hk hG v ∨ w = C.vertex (next k v) ∨ w = C.vertex (prev k v) := by
  rw [← SimpleGraph.mem_neighborFinset, C.neighborFinset_eq hk hG]
  simp

/-- The three actual outgoing darts at a row vertex. -/
noncomputable def star (v : Vtx k) : Fin 3 → G.Dart
  | 0 => ⟨(C.vertex v, C.port hk hG v), (C.port_spec hk hG v).1⟩
  | 1 => ⟨(C.vertex v, C.vertex (next k v)), C.adjacent v⟩
  | 2 => ⟨(C.vertex v, C.vertex (prev k v)), C.adjacent_prev v⟩

@[simp] theorem star_fst (v : Vtx k) (j : Fin 3) :
    (C.star hk hG v j).fst = C.vertex v := by
  fin_cases j <;> rfl

theorem star_injective : Function.Injective (fun p : Vtx k × Fin 3 => C.star hk hG p.1 p.2) := by
  rintro ⟨v, i⟩ ⟨w, j⟩ h
  have hv : v = w := C.injective (by
    simpa only [star_fst] using congrArg (fun d : G.Dart => d.fst) h)
  subst w
  have hs := congrArg (fun d : G.Dart => d.snd) h
  obtain ⟨_, hpn, hpp⟩ := C.port_spec hk hG v
  have hnp := C.injective.ne (next_ne_prev k hk v)
  fin_cases i <;> fin_cases j <;> simp_all [star]

theorem star_surjective_at (v : Vtx k) (d : G.Dart) (hd : d.fst = C.vertex v) :
    ∃ j, C.star hk hG v j = d := by
  have ha : G.Adj (C.vertex v) d.snd := hd ▸ d.adj
  rcases (C.adjacent_iff hk hG v d.snd).mp ha with h | h | h
  · exact ⟨0, by apply SimpleGraph.Dart.ext; exact Prod.ext hd.symm h.symm⟩
  · exact ⟨1, by apply SimpleGraph.Dart.ext; exact Prod.ext hd.symm h.symm⟩
  · exact ⟨2, by apply SimpleGraph.Dart.ext; exact Prod.ext hd.symm h.symm⟩

/-- Construct the ambient dart map from the cycle and its third edges. -/
noncomputable def embedding (d : AllDart k) : G.Dart :=
  C.star hk hG (dartCoordinate k d).1 (dartCoordinate k d).2

theorem embedding_injective : Function.Injective (C.embedding hk hG) :=
  (C.star_injective hk hG).comp (dartCoordinate k).injective

@[simp] theorem embedding_fst (d : AllDart k) :
    (C.embedding hk hG d).fst = C.vertex ((ring k).vertOf d) := by
  rw [embedding, star_fst]
  congr 1
  rcases d with (⟨i, _ | _⟩ | ⟨i, _ | _⟩) | (i | i) <;> rfl

theorem embedding_flip (d : ZigzagRing.Dart k) :
    (C.embedding hk hG (.inl d)).symm = C.embedding hk hG (.inl (flip k d)) := by
  rcases d with ⟨i, _ | _⟩ | ⟨i, _ | _⟩ <;>
    apply SimpleGraph.Dart.ext <;>
    simp [embedding, dartCoordinate, star, next, prev, ZigzagRing.flip, SimpleGraph.Dart.symm]

theorem embedding_covers (d : G.Dart) (hd : ∃ v, d.fst = C.vertex v) :
    ∃ x, C.embedding hk hG x = d := by
  obtain ⟨v, hv⟩ := hd
  obtain ⟨j, hj⟩ := C.star_surjective_at hk hG v d hv
  exact ⟨(dartCoordinate k).symm (v, j), by simpa [embedding] using hj⟩

end Frame
end Mettapedia.GraphTheory.FourColor.InducedCycleLayer
