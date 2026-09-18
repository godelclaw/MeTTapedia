import Mettapedia.GraphTheory.Hypermap.Basic
import Mettapedia.GraphTheory.FourColor.MapEulerDefect

/-!
# Euler's relation for hypermaps: the defect never has the wrong sign, and is even

`Hypermap.lean` records the Euler defect of a hypermap without claiming either
of its two substantive properties.  This module proves both, for every finite
hypermap, with no planarity, connectivity or orientability hypothesis:

* `Hypermap.eulerLhs_le_eulerRhs` — the orbit total `E + N + F` never exceeds
  the dart count plus twice the component count;
* `Hypermap.even_genus` — the gap between them is even, so the *genus* is a
  genuine natural number and `eulerRhs = 2 * genus + eulerLhs` holds on the
  nose, with no truncation.

Everything else here is bookkeeping around those two: `Hypermap.genus`,
`Hypermap.eulerDefect_nonpos`, `Hypermap.eulerDefect_even`, and the
identification of `Hypermap.Planar` with vanishing genus.

## Where the content comes from

Both facts are already present in this development, in the edge-list
presentation: `MapEulerDefect.defect_eq_twice_handles` states that

    E + 2·C - V - F  =  2 · (number of handle-creating edges),

which is simultaneously a sign statement and a parity statement.  What was
missing was the translation between that presentation — a rotation together
with a *list of transpositions* — and the hypermap presentation, where the
second permutation is an arbitrary `edge` with no chosen factorisation.

The translation is the one lemma in `PermSwapDecomposition` below: every
permutation `τ` factors as a product of `card D - orbitCount τ` transpositions,
each of which transposes two points of a single `τ`-cycle.  The length count is
what turns the edge-list `E` into the dart count, and the cycle condition is
what keeps the connected components from changing: the transpositions connect
exactly what `τ` connects, neither more nor less.

The factorisation is built greedily: peel off `swap a (τ a)` for any point `a`
moved by `τ`.  That strictly shrinks the support and, by the split law
`orbitCount_swap_mul_of_sameCycle`, raises the orbit count by exactly one — so
the two bookkeeping invariants advance together, and the recursion terminates
at the identity, whose orbit count is the dart count.

## A note on the sign

`eulerDefect` is `eulerLhs - eulerRhs`, i.e. `(E + N + F) - (#darts + 2·C)`.
That quantity is `-2 · genus`: it is *non-positive*, vanishing exactly in the
planar case.  The positively-signed quantity is `eulerRhs - eulerLhs`.
-/

namespace Mettapedia.GraphTheory

open Mettapedia.GraphTheory.FourColor

open Equiv Equiv.Perm
open GoertzelV24PermutationOrbitSurgery GoertzelV24WordReachability
open GoertzelV24MapEulerBound

namespace PermSwapDecomposition

variable {D : Type*} [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/-- The identity has one orbit per dart. -/
theorem orbitCount_one : orbitCount (1 : Perm D) = Fintype.card D := by
  have hbij : Function.Bijective (Quotient.mk (SameCycle.setoid (1 : Perm D))) := by
    constructor
    · intro x y hxy
      have h : (1 : Perm D).SameCycle x y := Quotient.exact hxy
      obtain ⟨n, hn⟩ := h
      simpa using hn
    · intro q
      obtain ⟨x, hx⟩ := Quotient.exists_rep q
      exact ⟨x, hx⟩
  show Fintype.card (Quotient (SameCycle.setoid (1 : Perm D))) = Fintype.card D
  exact (Fintype.card_of_bijective hbij).symm

/-- **Cycle-respecting transposition factorisation.**  Every permutation is a
product of transpositions, each transposing two points of one of its own
cycles, and the number of factors is exactly `card D - orbitCount τ`.

The two extra clauses are what make the factorisation usable for Euler
counting: the length clause converts an edge count into a dart count, and the
same-cycle clause guarantees that the factors generate exactly the connectivity
that `τ` itself generates. -/
theorem exists_swapProduct_eq (τ : Perm D) :
    ∃ edges : List (D × D),
      (∀ e ∈ edges, e.1 ≠ e.2) ∧
        (∀ e ∈ edges, τ.SameCycle e.1 e.2) ∧
          swapProduct edges = τ ∧
            edges.length + orbitCount τ = Fintype.card D := by
  classical
  suffices hmain : ∀ n : ℕ, ∀ τ : Perm D, τ.support.card ≤ n →
      ∃ edges : List (D × D),
        (∀ e ∈ edges, e.1 ≠ e.2) ∧
          (∀ e ∈ edges, τ.SameCycle e.1 e.2) ∧
            swapProduct edges = τ ∧
              edges.length + orbitCount τ = Fintype.card D by
    exact hmain τ.support.card τ le_rfl
  intro n
  induction n with
  | zero =>
      intro τ hτ
      have hτ1 : τ = 1 := by
        rw [← Equiv.Perm.support_eq_empty_iff, ← Finset.card_eq_zero]
        omega
      subst hτ1
      exact ⟨[], by simp, by simp, rfl, by simp [orbitCount_one]⟩
  | succ n ih =>
      intro τ hτ
      by_cases hone : τ = 1
      · subst hone
        exact ⟨[], by simp, by simp, rfl, by simp [orbitCount_one]⟩
      · obtain ⟨a, ha⟩ : ∃ a : D, τ a ≠ a := by
          by_contra hcon
          exact hone (Equiv.ext fun x => not_not.mp fun h => hcon ⟨x, h⟩)
        have hab : a ≠ τ a := fun h => ha h.symm
        have hsame : τ.SameCycle a (τ a) := ⟨1, by simp⟩
        have hcount : orbitCount (Equiv.swap a (τ a) * τ) = orbitCount τ + 1 :=
          orbitCount_swap_mul_of_sameCycle τ hab hsame
        have hbsupp : τ (τ a) ≠ τ a := fun h => ha (τ.injective h)
        -- the peeled permutation fixes `a`, and moves nothing new
        have hsub : (Equiv.swap a (τ a) * τ).support ⊆ τ.support.erase a := by
          intro x hx
          rw [Equiv.Perm.mem_support] at hx
          have hxa : x ≠ a := by
            rintro rfl
            exact hx (by rw [Perm.mul_apply, Equiv.swap_apply_right])
          refine Finset.mem_erase.mpr ⟨hxa, Equiv.Perm.mem_support.mpr ?_⟩
          intro hfix
          apply hx
          have hxb : x ≠ τ a := by
            rintro rfl
            exact hbsupp hfix
          rw [Perm.mul_apply, hfix, Equiv.swap_apply_of_ne_of_ne hxa hxb]
        have hcard : (Equiv.swap a (τ a) * τ).support.card ≤ n := by
          have h1 : (Equiv.swap a (τ a) * τ).support.card ≤ (τ.support.erase a).card :=
            Finset.card_le_card hsub
          have h2 : (τ.support.erase a).card = τ.support.card - 1 :=
            Finset.card_erase_of_mem (Equiv.Perm.mem_support.mpr ha)
          have h3 : a ∈ τ.support := Equiv.Perm.mem_support.mpr ha
          have h4 : 0 < τ.support.card := Finset.card_pos.mpr ⟨a, h3⟩
          omega
        obtain ⟨edges, hne, hcyc, hprod, hlen⟩ := ih _ hcard
        refine ⟨(a, τ a) :: edges, ?_, ?_, ?_, ?_⟩
        · intro e he
          rcases List.mem_cons.mp he with rfl | he'
          · exact hab
          · exact hne e he'
        · intro e he
          rcases List.mem_cons.mp he with rfl | he'
          · exact hsame
          · exact sameCycle_of_swap_mul_sameCycle hsame (hcyc e he')
        · rw [swapProduct_cons, hprod]
          exact Equiv.swap_mul_self_mul _ _ _
        · rw [List.length_cons]
          omega

end PermSwapDecomposition

namespace Hypermap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The composite law, solved for the node permutation. -/
theorem face_mul_edge (H : Hypermap D) : H.face * H.edge = H.node⁻¹ := by
  have h : H.node * (H.face * H.edge) = 1 := by
    ext d
    show H.node (H.face (H.edge d)) = d
    exact H.cancel3 d
  exact eq_inv_of_mul_eq_one_right h

theorem orbitCount_face_mul_edge (H : Hypermap D) :
    orbitCount (H.face * H.edge) = orbitCount H.node := by
  rw [face_mul_edge, orbitCount_inv]

/-- **The factorisation does not change connectivity.**  Replacing the `edge`
permutation by a cycle-respecting transposition factorisation of it, and
dropping the `node` permutation (which the composite law determines), leaves
the component count of the map untouched. -/
theorem wordOrbitCount_face_swapGenerators (H : Hypermap D) {edges : List (D × D)}
    (hprod : swapProduct edges = H.edge)
    (hcyc : ∀ e ∈ edges, H.edge.SameCycle e.1 e.2) :
    wordOrbitCount (H.face :: swapGenerators edges) =
      wordOrbitCount [H.edge, H.node, H.face] := by
  have hEmem : H.edge ∈ [H.edge, H.node, H.face] := List.mem_cons_self
  have hNmem : H.node ∈ [H.edge, H.node, H.face] :=
    List.mem_cons_of_mem _ List.mem_cons_self
  have hFmem : H.face ∈ [H.edge, H.node, H.face] :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  refine le_antisymm ?_ ?_
  · -- the factorisation reaches everything the three permutations reach
    refine wordOrbitCount_le_of_le (fun u v huv => ?_)
    refine wordReachable_absorb ?_ huv
    have hE : ∀ z : D, WordReachable (H.face :: swapGenerators edges) z (H.edge z) := by
      intro z
      rw [← hprod]
      exact wordReachable_swapProduct H.face edges z
    have hF : ∀ z : D, WordReachable (H.face :: swapGenerators edges) z (H.face z) :=
      fun z => wordReachable_step List.mem_cons_self z
    intro g hg z
    rcases List.mem_cons.mp hg with rfl | hg1
    · exact hE z
    rcases List.mem_cons.mp hg1 with rfl | hg2
    · -- the node step is the reverse of a face step after an edge step
      have hback : H.face (H.edge (H.node z)) = z :=
        H.node.injective (H.cancel3 (H.node z))
      have hchain : WordReachable (H.face :: swapGenerators edges) (H.node z) z := by
        have h1 := hE (H.node z)
        have h2 := hF (H.edge (H.node z))
        rw [hback] at h2
        exact h1.trans h2
      exact hchain.symm
    rcases List.mem_cons.mp hg2 with rfl | hg3
    · exact hF z
    · simp at hg3
  · -- conversely each transposition joins two points of one `edge`-cycle
    refine wordOrbitCount_le_of_le (fun u v huv => ?_)
    refine wordReachable_absorb ?_ huv
    intro g hg z
    rcases List.mem_cons.mp hg with rfl | hg1
    · exact wordReachable_step hFmem z
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hg1
      have hjoin : WordReachable [H.edge, H.node, H.face] e.1 e.2 := by
        obtain ⟨k, hk⟩ := exists_nat_pow_apply_eq (hcyc e he)
        have := wordReachable_pow hEmem e.1 k
        rwa [hk] at this
      rcases eq_or_ne z e.1 with rfl | hz1
      · rw [Equiv.swap_apply_left]
        exact hjoin
      · rcases eq_or_ne z e.2 with rfl | hz2
        · rw [Equiv.swap_apply_right]
          exact hjoin.symm
        · rw [Equiv.swap_apply_of_ne_of_ne hz1 hz2]
          exact WordReachable.refl _ z

/-- **Euler's relation with an explicit remainder.**  For every hypermap the
dart count plus twice the component count exceeds the orbit total by an even
amount. -/
theorem exists_eulerRhs_eq (H : Hypermap D) :
    ∃ k : ℕ, eulerRhs H = 2 * k + eulerLhs H := by
  obtain ⟨edges, hne, hcyc, hprod, hlen⟩ :=
    PermSwapDecomposition.exists_swapProduct_eq H.edge
  refine ⟨MapEulerDefect.handles H.face edges, ?_⟩
  have hdef := MapEulerDefect.defect_eq_twice_handles H.face edges hne
  rw [MapEulerDefect.defect, hprod, orbitCount_face_mul_edge,
    wordOrbitCount_face_swapGenerators H hprod hcyc] at hdef
  unfold eulerRhs eulerLhs
  omega

/-- **Euler's inequality for hypermaps.**  `E + N + F ≤ #darts + 2·C`. -/
theorem eulerLhs_le_eulerRhs (H : Hypermap D) : eulerLhs H ≤ eulerRhs H := by
  obtain ⟨k, hk⟩ := exists_eulerRhs_eq H
  omega

/-- The genus: half the Euler gap.  `even_genus` below says the halving loses
nothing. -/
noncomputable def genus (H : Hypermap D) : ℕ := (eulerRhs H - eulerLhs H) / 2

/-- **The genus is a genuine natural number.**  No truncation occurs in the
genus formula: `#darts + 2·C = 2·genus + (E + N + F)` exactly. -/
theorem even_genus (H : Hypermap D) : eulerRhs H = 2 * genus H + eulerLhs H := by
  obtain ⟨k, hk⟩ := exists_eulerRhs_eq H
  unfold genus
  omega

/-- The Euler defect of `Hypermap.lean` is `-2 · genus`. -/
theorem eulerDefect_eq_neg_two_mul_genus (H : Hypermap D) :
    eulerDefect H = -2 * (genus H : ℤ) := by
  have h := even_genus H
  unfold eulerDefect
  omega

/-- **The defect never has the wrong sign.**  Note the direction: `eulerDefect`
is `eulerLhs - eulerRhs`, so it is non-positive, and vanishes exactly in the
planar case. -/
theorem eulerDefect_nonpos (H : Hypermap D) : eulerDefect H ≤ 0 := by
  rw [eulerDefect_eq_neg_two_mul_genus]
  have : (0 : ℤ) ≤ (genus H : ℤ) := Int.natCast_nonneg _
  omega

/-- **The defect is even**, so the genus is well defined. -/
theorem eulerDefect_even (H : Hypermap D) : Even (eulerDefect H) := by
  refine ⟨-(genus H : ℤ), ?_⟩
  rw [eulerDefect_eq_neg_two_mul_genus]
  ring

theorem planar_iff_genus_eq_zero (H : Hypermap D) : Planar H ↔ genus H = 0 := by
  unfold Planar
  rw [eulerDefect_eq_neg_two_mul_genus]
  omega

theorem planar_iff_eulerRhs_eq (H : Hypermap D) :
    Planar H ↔ eulerRhs H = eulerLhs H := by
  rw [planar_iff_genus_eq_zero]
  have h := even_genus H
  omega

/-! ## The rotation systems of this development

The dictionary of `Hypermap.lean` transports all of the above to
`RotationSystem`s without further work. -/

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem rotationSystem_eulerLhs_le_eulerRhs (RS : RotationSystem V E) :
    eulerLhs (ofRotationSystem RS) ≤ eulerRhs (ofRotationSystem RS) :=
  eulerLhs_le_eulerRhs _

theorem rotationSystem_eulerDefect_nonpos (RS : RotationSystem V E) :
    eulerDefect (ofRotationSystem RS) ≤ 0 :=
  eulerDefect_nonpos _

theorem rotationSystem_eulerDefect_even (RS : RotationSystem V E) :
    Even (eulerDefect (ofRotationSystem RS)) :=
  eulerDefect_even _

end Hypermap

end Mettapedia.GraphTheory
