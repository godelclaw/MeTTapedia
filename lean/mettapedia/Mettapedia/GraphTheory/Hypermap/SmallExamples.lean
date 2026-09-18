import Mettapedia.GraphTheory.Hypermap.Walkup.Basic

/-!
# Two hypermaps small enough to compute with

Every statement about hypermaps in this development is checked here against two
concrete maps before it is believed:

* `spherePair` — two darts, one edge, one vertex, two faces.  Planar.
* `torusTriple` — three darts, all three permutations equal to the same
  3-cycle.  Genus one, so **not** planar.

Having a genuinely non-planar example matters more than having a planar one.
A planarity predicate that everything satisfies is worthless, and so is a
Jordan-style predicate that nothing satisfies; `torusTriple` is the witness that
neither has happened here.

The orbit counts are proved rather than evaluated: `orbitCount` is a count of
quotient classes and is noncomputable, so the counting facts are obtained from
the complete-invariant lemma of `OrbitCountSplitting`, while everything that
*is* computable — the Walkup formula, the skipped permutations — is checked by
`decide`.

## What the Walkup checks establish

At `z = 0` the genus-one map has `edge 0 ≠ 0`, `node 0 ≠ 0`, `face 0 ≠ 0` (so
`z` is non-degenerate) and `0`, `node 0` share an edge cycle.  These are exactly
the conditions under which Walkup's transform is *allowed* to drop the genus,
and it does: `walkupE torusTriple 0` has identity edge permutation on two darts
and is planar.  So the genus-preservation hypothesis of `genus_WalkupE_eq` is
load-bearing, not decoration — and `skipEdgeFun` genuinely differs from naively
skipping `z` in `edge`, which the last check below pins down.
-/

namespace Mettapedia.GraphTheory

open Mettapedia.GraphTheory.FourColor

open Equiv Equiv.Perm
open GoertzelV24PermutationOrbitSurgery GoertzelV24WordReachability
open Mettapedia.GraphTheory.OrbitCountSplitting

namespace Hypermap

/-! ## A planar map on two darts -/

/-- One edge, one vertex, two faces: the sphere with a single edge drawn on it. -/
def spherePair : Hypermap (Fin 2) where
  edge := Equiv.swap 0 1
  node := Equiv.swap 0 1
  face := 1
  cancel3 := by decide

/-! ## A genus-one map on three darts -/

/-- The 3-cycle `0 ↦ 1 ↦ 2 ↦ 0`. -/
def cyc3 : Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2

/-- All three permutations are the same 3-cycle.  The composite law holds
because the cycle has order three. -/
def torusTriple : Hypermap (Fin 3) where
  edge := cyc3
  node := cyc3
  face := cyc3
  cancel3 := by decide

/-! ## Orbit counts

`orbitCount` is a count of quotient classes, hence noncomputable; these are
proved from the complete-invariant lemma with a one-point invariant. -/

theorem sameCycle_cyc3 (x y : Fin 3) : cyc3.SameCycle x y := by
  have h : ∃ n : Fin 3, (cyc3 ^ (n : ℕ)) x = y := by revert x y; decide
  obtain ⟨n, hn⟩ := h
  exact ⟨(n : ℕ), by rw [zpow_natCast]; exact hn⟩

theorem orbitCount_cyc3 : orbitCount cyc3 = 1 := by
  have h := orbitCount_eq_card_of_completeInvariant (σ := cyc3) (fun _ : Fin 3 => ())
    (fun x y => ⟨fun _ => rfl, fun _ => sameCycle_cyc3 x y⟩) (fun _ => ⟨0, rfl⟩)
  rw [h]
  simp

theorem sameCycle_swap01 (x y : Fin 2) : (Equiv.swap (0 : Fin 2) 1).SameCycle x y := by
  have h : ∃ n : Fin 2, ((Equiv.swap (0 : Fin 2) 1) ^ (n : ℕ)) x = y := by revert x y; decide
  obtain ⟨n, hn⟩ := h
  exact ⟨(n : ℕ), by rw [zpow_natCast]; exact hn⟩

theorem orbitCount_swap01 : orbitCount (Equiv.swap (0 : Fin 2) 1) = 1 := by
  have h := orbitCount_eq_card_of_completeInvariant (σ := Equiv.swap (0 : Fin 2) 1)
    (fun _ : Fin 2 => ()) (fun x y => ⟨fun _ => rfl, fun _ => sameCycle_swap01 x y⟩)
    (fun _ => ⟨0, rfl⟩)
  rw [h]
  simp

/-! ## The two maps are connected -/

theorem compCount_torusTriple : compCount torusTriple = 1 := by
  have hmem : cyc3 ∈ [cyc3, cyc3, cyc3] := List.mem_cons_self
  have hreach : ∀ x y : Fin 3, WordReachable [cyc3, cyc3, cyc3] x y := by
    intro x y
    obtain ⟨n, hn⟩ := exists_nat_pow_apply_eq (sameCycle_cyc3 x y)
    have h := wordReachable_pow hmem x n
    rwa [hn] at h
  have h := wordOrbitCount_eq_card_of_completeInvariant (L := [cyc3, cyc3, cyc3])
    (fun _ : Fin 3 => ()) (fun x y => ⟨fun _ => rfl, fun _ => hreach x y⟩) (fun _ => ⟨0, rfl⟩)
  show wordOrbitCount [cyc3, cyc3, cyc3] = 1
  rw [h]
  simp

theorem compCount_spherePair : compCount spherePair = 1 := by
  have hmem : (Equiv.swap (0 : Fin 2) 1) ∈ [Equiv.swap (0 : Fin 2) 1, Equiv.swap (0 : Fin 2) 1,
      (1 : Perm (Fin 2))] := List.mem_cons_self
  have hreach : ∀ x y : Fin 2, WordReachable [Equiv.swap (0 : Fin 2) 1,
      Equiv.swap (0 : Fin 2) 1, (1 : Perm (Fin 2))] x y := by
    intro x y
    obtain ⟨n, hn⟩ := exists_nat_pow_apply_eq (sameCycle_swap01 x y)
    have h := wordReachable_pow hmem x n
    rwa [hn] at h
  have h := wordOrbitCount_eq_card_of_completeInvariant
    (L := [Equiv.swap (0 : Fin 2) 1, Equiv.swap (0 : Fin 2) 1, (1 : Perm (Fin 2))])
    (fun _ : Fin 2 => ()) (fun x y => ⟨fun _ => rfl, fun _ => hreach x y⟩) (fun _ => ⟨0, rfl⟩)
  show wordOrbitCount [Equiv.swap (0 : Fin 2) 1, Equiv.swap (0 : Fin 2) 1,
    (1 : Perm (Fin 2))] = 1
  rw [h]
  simp

/-! ## Euler data, and the verdicts -/

theorem eulerLhs_spherePair : eulerLhs spherePair = 4 := by
  show orbitCount (Equiv.swap (0 : Fin 2) 1) + orbitCount (Equiv.swap (0 : Fin 2) 1)
    + orbitCount (1 : Perm (Fin 2)) = 4
  rw [orbitCount_swap01, PermSwapDecomposition.orbitCount_one]
  simp

theorem eulerRhs_spherePair : eulerRhs spherePair = 4 := by
  rw [eulerRhs_eq_card_add_two_mul_compCount, compCount_spherePair]
  simp

/-- **The two-dart map is planar.** -/
theorem planar_spherePair : Planar spherePair := by
  rw [planar_iff_eulerRhs_eq, eulerRhs_spherePair, eulerLhs_spherePair]

theorem eulerLhs_torusTriple : eulerLhs torusTriple = 3 := by
  show orbitCount cyc3 + orbitCount cyc3 + orbitCount cyc3 = 3
  rw [orbitCount_cyc3]

theorem eulerRhs_torusTriple : eulerRhs torusTriple = 5 := by
  rw [eulerRhs_eq_card_add_two_mul_compCount, compCount_torusTriple]
  simp

/-- **The three-dart map has genus one.** -/
theorem genus_torusTriple : genus torusTriple = 1 := by
  have h := even_genus torusTriple
  rw [eulerRhs_torusTriple, eulerLhs_torusTriple] at h
  omega

/-- **The three-dart map is not planar.**  This is the witness that `Planar` is
not vacuously true. -/
theorem not_planar_torusTriple : ¬ Planar torusTriple := by
  rw [planar_iff_genus_eq_zero, genus_torusTriple]
  omega

/-- The Euler defect of the genus-one map is `-2`: non-positive, as
`eulerDefect_nonpos` requires, and *not* `+2`. -/
theorem eulerDefect_torusTriple : eulerDefect torusTriple = -2 := by
  rw [eulerDefect, eulerLhs_torusTriple, eulerRhs_torusTriple]
  norm_num

/-! ## The Walkup construction, evaluated

Everything here is computable, so it is checked by the kernel rather than
argued. -/

/-- `z = 0` is non-degenerate in the genus-one map: none of the three
permutations fixes it. -/
example : torusTriple.edge 0 ≠ 0 ∧ torusTriple.node 0 ≠ 0 ∧ torusTriple.face 0 ≠ 0 := by decide

/-- Walkup's formula at `z = 0` in the genus-one map is the identity on the two
surviving darts: the 3-cycle of edges is cut down to two fixed points. -/
example : ∀ x : Fin 3, x ≠ 0 → skipEdgeFun torusTriple 0 x = x := by decide

/-- The punctured `node` and `face` permutations transpose the two survivors. -/
example : skipFun torusTriple.node 0 1 = 2 ∧ skipFun torusTriple.node 0 2 = 1 := by decide

/-- **The composite law, checked on the nose.**  This is `skipEdgeK` evaluated. -/
example : ∀ x : Fin 3, x ≠ 0 →
    skipFun torusTriple.node 0 (skipFun torusTriple.face 0 (skipEdgeFun torusTriple 0 x)) = x := by
  decide

/-- **Walkup's edge formula is not just "skip `z` in `edge`".**  On the
genus-one map the two differ, which is precisely the case where the transform
changes the genus. -/
example : skipEdgeFun torusTriple 0 1 ≠ skipFun torusTriple.edge 0 1 := by decide

/-- On a map where `z` is degenerate the two *do* agree, as Coq's
`glink_fp_skip_edge` says: here `face 0 = 0`. -/
example : spherePair.face 0 = 0 := by decide

example : ∀ x : Fin 2, x ≠ 0 → skipEdgeFun spherePair 0 x = skipFun spherePair.edge 0 x := by
  decide

/-- The carrier shrinks by exactly one. -/
example : Fintype.card {x : Fin 3 // x ≠ 0} + 1 = Fintype.card (Fin 3) :=
  card_subtype_ne_succ 0

end Hypermap

end Mettapedia.GraphTheory
