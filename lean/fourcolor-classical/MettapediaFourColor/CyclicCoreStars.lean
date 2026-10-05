import MettapediaFourColor.ExceptionalCoreOrientation

/-! # A cyclic source neighbourhood covers the ambient star

If every source neighbour has a predecessor whose corner is preserved, the
source image is closed under the ambient vertex rotation. Vertexwise
cyclicity then reaches every ambient neighbour. Neither injectivity nor a
degree equality is needed for this coverage statement.
-/

namespace FourColor.CyclicCoreStars

open SimpleGraph Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open ExceptionalCoreOrientation

theorem covers {A V : Type*} [Finite V] {P : SimpleGraph A} {G : SimpleGraph V}
    (data : Data G) (cyclic : data.IsVertexwiseCyclic) (f : P →g G) (i : A)
    (nonempty : ∃ j, P.Adj i j)
    (predecessor : ∀ j, P.Adj i j →
      ∃ k, P.Adj i k ∧ Corner data (f i) (f j) (f k))
    (v : V) (edge : G.Adj (f i) v) :
    ∃ j, f j = v ∧ P.Adj i j := by
  classical
  let : Fintype V := Fintype.ofFinite V
  obtain ⟨j, hj⟩ := nonempty
  let start : G.Dart := ⟨(f i, f j), f.map_rel hj⟩
  have powers : ∀ n : ℕ, ∃ k, ∃ hk : P.Adj i k,
      (data.vertexRotation ^ n) start = ⟨(f i, f k), f.map_rel hk⟩ := by
    intro n
    induction n with
    | zero => exact ⟨j, hj, rfl⟩
    | succ n ih =>
      obtain ⟨k, hk, hpow⟩ := ih
      obtain ⟨l, hl, _, _, step⟩ := predecessor k hk
      refine ⟨l, hl, ?_⟩
      rw [pow_succ', Equiv.Perm.mul_apply, hpow]
      exact step
  have same := (cyclic (f i)).2
    (show start.fst = f i from rfl)
    (show (⟨(f i, v), edge⟩ : G.Dart).fst = f i from rfl)
  obtain ⟨n, hn⟩ := same.exists_nat_pow_eq
  obtain ⟨k, hk, hpow⟩ := powers n
  rw [hn] at hpow
  exact ⟨k, (congrArg (fun d => d.snd) hpow).symm, hk⟩

end FourColor.CyclicCoreStars
