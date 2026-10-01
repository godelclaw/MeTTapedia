import MettapediaFourColor.ExceptionalCoreLocalInjectivity

/-!
# Induced patch recognition from short paths and facial intervals

A proper interval of an actual cyclic vertex rotation can only contain a
facial corner between consecutive entries. If all ambient triangles are
facial, this controls extra edges between neighbours of a patch vertex.
For an injective homomorphism, that local control extends to every pair
joined by at most three source edges when ambient four-cycles have a chord.
-/

namespace FourColor.FacialPatchInduced

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open ExceptionalCoreOrientation

variable {V : Type*} {G : SimpleGraph V}

section Interval

variable [G.LocallyFinite] [Finite V] (rotation : Data G)

/-- A proper neighbour interval cannot acquire a wraparound facial corner.
The strict degree bound retains at least one omitted neighbour. -/
theorem corner_chain_successor (cyclic : rotation.IsVertexwiseCyclic)
    (v : V) {n : ℕ} (hn : 0 < n) (ns : Fin n → V)
    (adjacent : ∀ i, G.Adj v (ns i))
    (step : ∀ i (h : i + 1 < n),
      Corner rotation v (ns ⟨i, by omega⟩) (ns ⟨i + 1, h⟩))
    (bound : n < G.degree v) (i j : Fin n)
    (corner : Corner rotation v (ns i) (ns j)) : j.val = i.val + 1 := by
  classical
  let : Fintype V := Fintype.ofFinite V
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
  obtain ⟨_, _, he⟩ := corner
  have hp : (rotation.vertexRotation ^ (i.val + 1)) (d ⟨0, hn⟩) =
      (rotation.vertexRotation ^ j.val) (d ⟨0, hn⟩) := by
    rw [pow_succ', Equiv.Perm.mul_apply, dp i.val i.isLt, dp j.val j.isLt]
    exact he
  have hm := (hc.pow_apply_eq_pow_apply hbase).mp hp
  have hi : i.val + 1 < fiber.card := by rw [hcard]; omega
  have hj : j.val < fiber.card := by rw [hcard]; omega
  change (i.val + 1) % fiber.card = j.val % fiber.card at hm
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hm
  exact hm.symm

end Interval

/-- Local adjacency reflection suffices for a diameter-three patch if each
ambient four-cycle has a diagonal. Every vertex and edge is kept in the
same injective homomorphism throughout the argument. -/
theorem reflects_of_short_paths {W : Type*} {H : SimpleGraph W} (f : H →g G)
    (inj : Function.Injective f)
    (localReflect : ∀ k i j, H.Adj k i → H.Adj k j → G.Adj (f i) (f j) → H.Adj i j)
    (short : ∀ i j, i ≠ j → H.Adj i j ∨
      (∃ k, H.Adj i k ∧ H.Adj k j) ∨
      ∃ a b, H.Adj i a ∧ H.Adj a b ∧ H.Adj b j)
    (chord : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a ≠ c → b ≠ d → G.Adj a c ∨ G.Adj b d) :
    ∀ i j, G.Adj (f i) (f j) → H.Adj i j := by
  intro i j hij
  have ne : i ≠ j := fun eq => hij.ne (congrArg f eq)
  rcases short i j ne with h | ⟨k, hik, hkj⟩ | ⟨a, b, hia, hab, hbj⟩
  · exact h
  · exact localReflect k i j hik.symm hkj hij
  · by_cases hib : i = b
    · simpa only [hib] using hbj
    by_cases haj : a = j
    · simpa only [haj] using hia
    rcases chord (f i) (f a) (f b) (f j) (f.map_adj hia) (f.map_adj hab)
        (f.map_adj hbj) hij.symm (inj.ne hib) (inj.ne haj) with hib' | haj'
    · have hib'' := localReflect a i b hia.symm hab hib'
      exact localReflect b i j hib''.symm hbj hij
    · have haj'' := localReflect b a j hab.symm hbj haj'
      exact localReflect a i j hia.symm haj'' hij

end FourColor.FacialPatchInduced
