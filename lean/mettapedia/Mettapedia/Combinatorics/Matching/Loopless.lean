import Mettapedia.Combinatorics.Matching.Sum

/-!
# Removing loop weights from matching amplitudes

Perfect matchings contain no loops. Consequently an amplitude depends only on
weights whose two underlying vertices are distinct, and every weighting has a
canonical loop-free normalization with the same amplitudes.
-/

namespace MatchingLoopless

open Amplitude MatchingSum

variable {V C R : Type*} [Fintype V] [DecidableEq V] [CommSemiring R]

/-- Changing only weights above diagonal vertex pairs changes no amplitude. -/
theorem amplitude_ignore_loops (W W' : Sym2 (V × C) → R)
    (h : ∀ (x y : V) (a b : C), x ≠ y →
      W' s((x, a), (y, b)) = W s((x, a), (y, b)))
    (c : V → C) : amplitude W' c = amplitude W c := by
  rw [← pmSum_univ, ← pmSum_univ, pmSum, pmSum]
  refine Finset.sum_congr rfl fun σ hσ =>
    Finset.prod_congr rfl fun e he => ?_
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
  have hne : σ x ≠ x := (mem_pairingsOn.mp hσ).2.1 x hx
  exact h x (σ x) (c x) (c (σ x)) (fun hh => hne hh.symm)

/-- The loop-free normalization of a weighting. -/
noncomputable def deloop (W : Sym2 (V × C) → R) : Sym2 (V × C) → R :=
  fun e => if (Sym2.map Prod.fst e).IsDiag then 0 else W e

omit [Fintype V] in
lemma deloop_off {W : Sym2 (V × C) → R} {x y : V} (hxy : x ≠ y)
    (a b : C) : deloop W s((x, a), (y, b)) = W s((x, a), (y, b)) := by
  rw [deloop]
  exact if_neg (by simpa only [Sym2.map_mk, Sym2.mk_isDiag_iff] using hxy)

omit [Fintype V] in
lemma deloop_loop (W : Sym2 (V × C) → R) (x : V) (a b : C) :
    deloop W s((x, a), (x, b)) = 0 := by
  rw [deloop]
  exact if_pos (by simp only [Sym2.map_mk, Sym2.mk_isDiag_iff])

lemma amplitude_deloop (W : Sym2 (V × C) → R) (c : V → C) :
    amplitude (deloop W) c = amplitude W c :=
  amplitude_ignore_loops _ _ (fun _ _ a b hxy => deloop_off hxy a b) c

end MatchingLoopless
