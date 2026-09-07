import Mettapedia.GraphTheory.FourColor.PermutationFirstReturnRestriction
import Mettapedia.GraphTheory.FourColor.GoertzelV24MapEulerBound

/-!
# Planar edge extension preserves surviving boundary order

Euler equality is hereditary along an edge presentation. An edge inside
an existing component must split a face; merging faces inside that same
component would create positive genus, which later edges cannot remove.
Consequently, if marked darts start in one component and end on one face,
their first-return order is unchanged by planar edge extension. Neither
an intermediate single-face condition nor an order-preservation hypothesis
is supplied by the caller.
-/

namespace Mettapedia.GraphTheory.FourColor.PlanarMapBoundaryRestriction

open Equiv Equiv.Perm
open GoertzelV24PermutationOrbitSurgery GoertzelV24WordReachability
open GoertzelV24MapEulerBound GoertzelV24OrderedCutFaceReturnProfile
open PermutationFirstReturnRestriction

variable {D : Type*} [Fintype D] [DecidableEq D]

noncomputable section

/-- Genus-zero Euler equality for a rotation and an edge presentation;
isolated vertices and disconnected maps are included. -/
def PlaneEdges (rho : Perm D) (edges : List (D × D)) : Prop :=
  orbitCount rho + orbitCount (rho * swapProduct edges) =
    edges.length + 2 * wordOrbitCount (rho :: swapGenerators edges)

omit [Fintype D] in
theorem face_cons (rho : Perm D) (e : D × D) (rest : List (D × D)) :
    rho * swapProduct (e :: rest) =
      swap (rho e.1) (rho e.2) * (rho * swapProduct rest) := by
  rw [swapProduct_cons, ← mul_assoc, Equiv.mul_swap_eq_swap_mul, mul_assoc]

theorem componentCount_cons (rho : Perm D) (e : D × D) (rest : List (D × D)) :
    wordOrbitCount (rho :: swapGenerators (e :: rest)) =
      wordOrbitCount (swap e.1 e.2 :: rho :: swapGenerators rest) := by
  apply wordOrbitCount_eq_of_mem_iff
  intro g
  simp only [swapGenerators_cons, List.mem_cons]
  tauto

/-- Euler equality leaves no room for a face merge between points already
joined in the old map. The old map is itself planar. -/
theorem plane_tail_and_split (rho : Perm D) (e : D × D) (rest : List (D × D))
    (hne : ∀ edge ∈ e :: rest, edge.1 ≠ edge.2)
    (hplane : PlaneEdges rho (e :: rest)) :
    PlaneEdges rho rest ∧
      (WordReachable (rho :: swapGenerators rest) e.1 e.2 →
        (rho * swapProduct rest).SameCycle (rho e.1) (rho e.2)) := by
  let p := rho * swapProduct rest
  let L := rho :: swapGenerators rest
  have hab : rho e.1 ≠ rho e.2 := fun h => hne e List.mem_cons_self (rho.injective h)
  have hold := orbitCount_add_orbitCount_mul_swapProduct_le rho rest
    (fun edge he => hne edge (List.mem_cons_of_mem e he))
  change orbitCount rho + orbitCount p ≤ rest.length + 2 * wordOrbitCount L at hold
  unfold PlaneEdges at hplane ⊢
  rw [face_cons, componentCount_cons] at hplane
  change orbitCount rho + orbitCount (swap (rho e.1) (rho e.2) * p) =
    rest.length + 1 + 2 * wordOrbitCount (swap e.1 e.2 :: L) at hplane
  by_cases hc : WordReachable L e.1 e.2
  · have hcomp := wordOrbitCount_cons_swap_eq_of_reachable hc
    rw [hcomp] at hplane
    by_cases hs : p.SameCycle (rho e.1) (rho e.2)
    · have hf := orbitCount_swap_mul_of_sameCycle p hab hs
      rw [hf] at hplane
      refine ⟨?_, fun _ => hs⟩
      dsimp only [L, p] at *
      omega
    · have hf := orbitCount_swap_mul_of_not_sameCycle p hab hs
      omega
  · have hs : ¬ p.SameCycle (rho e.1) (rho e.2) := by
      intro hs
      have hh := wordReachable_of_sameCycle_mul rho rest hs
      have ha : WordReachable L e.1 (rho e.1) := wordReachable_step List.mem_cons_self _
      have hb : WordReachable L e.2 (rho e.2) := wordReachable_step List.mem_cons_self _
      exact hc (ha.trans (hh.trans hb.symm))
    have hf := orbitCount_swap_mul_of_not_sameCycle p hab hs
    have hcomp := wordOrbitCount_le_cons_swap_add_one L e.1 e.2
    refine ⟨?_, fun h => (hc h).elim⟩
    dsimp only [L, p] at *
    omega

/-- Every tail of a planar edge presentation is planar. -/
theorem plane_tail (rho : Perm D) (added base : List (D × D))
    (hne : ∀ e ∈ added ++ base, e.1 ≠ e.2)
    (hplane : PlaneEdges rho (added ++ base)) : PlaneEdges rho base := by
  induction added with
  | nil => exact hplane
  | cons e rest ih =>
    exact ih (fun f hf => hne f (List.mem_cons_of_mem _ hf))
      (plane_tail_and_split rho e (rest ++ base) hne hplane).1

/-- One planar edge extension preserves the order of any marked subset
of an old component, provided its marks lie on one new face. -/
theorem nextHit_face_cons (rho : Perm D) (e : D × D) (rest : List (D × D))
    (hit : D → Prop) (hne : ∀ edge ∈ e :: rest, edge.1 ≠ edge.2)
    (hplane : PlaneEdges rho (e :: rest))
    (hcomp : ∀ x y, hit x → hit y → WordReachable (rho :: swapGenerators rest) x y)
    (hface : ∀ x y, hit x → hit y →
      (rho * swapProduct (e :: rest)).SameCycle x y) :
    nextHitPerm (rho * swapProduct (e :: rest)) hit =
      nextHitPerm (rho * swapProduct rest) hit := by
  classical
  let p := rho * swapProduct rest
  let L := rho :: swapGenerators rest
  rw [face_cons] at hface ⊢
  by_cases hc : WordReachable L e.1 e.2
  · have hs := (plane_tail_and_split rho e rest hne hplane).2 hc
    apply nextHit_swap_mul_of_one_cycle p hit (rho e.1) (rho e.2) _ hface
    intro x y hx hy
    exact sameCycle_of_swap_mul_sameCycle hs (hface x y hx hy)
  · by_cases hex : ∃ r, hit r
    · obtain ⟨r, hr⟩ := hex
      let keep := WordReachable L r
      have hp (d : D) (hd : keep d) : keep (p d) :=
        hd.trans (wordReachable_of_sameCycle_mul rho rest ⟨1, by simp [p]⟩)
      apply nextHit_swap_mul_of_invariant p hit keep hp
        (fun d hd => hcomp r d hr hd) (rho e.1) (rho e.2)
      rintro ⟨ha, hb⟩
      have hsa : WordReachable L e.1 (rho e.1) := wordReachable_step List.mem_cons_self _
      have hsb : WordReachable L e.2 (rho e.2) := wordReachable_step List.mem_cons_self _
      exact hc (hsa.trans (ha.symm.trans (hb.trans hsb.symm)))
    · apply Equiv.ext
      intro x
      exact False.elim (hex ⟨x.1, x.2⟩)

/-- Planar edge extension cannot reorder a surviving marked face boundary
of one original component. Intermediate face conditions are derived. -/
theorem nextHit_face_extension (rho : Perm D) (added base : List (D × D))
    (hit : D → Prop) (hne : ∀ edge ∈ added ++ base, edge.1 ≠ edge.2)
    (hplane : PlaneEdges rho (added ++ base))
    (hcomp : ∀ x y, hit x → hit y → WordReachable (rho :: swapGenerators base) x y)
    (hface : ∀ x y, hit x → hit y →
      (rho * swapProduct (added ++ base)).SameCycle x y) :
    nextHitPerm (rho * swapProduct (added ++ base)) hit =
      nextHitPerm (rho * swapProduct base) hit := by
  induction added with
  | nil => rfl
  | cons e rest ih =>
    have hcomp' (x y : D) (hx : hit x) (hy : hit y) :
        WordReachable (rho :: swapGenerators (rest ++ base)) x y := by
      apply wordReachable_mono _ (hcomp x y hx hy)
      intro g hg
      simp only [swapGenerators, List.map_append, List.mem_cons, List.mem_append] at hg ⊢
      tauto
    have he := nextHit_face_cons rho e (rest ++ base) hit hne hplane hcomp' hface
    have hface' (x y : D) (hx : hit x) (hy : hit y) :
        (rho * swapProduct (rest ++ base)).SameCycle x y := by
      have hh := (nextHitPerm_sameCycle_iff
        (rho * swapProduct (e :: rest ++ base)) hit ⟨x, hx⟩ ⟨y, hy⟩).mpr (hface x y hx hy)
      simp only [List.cons_append] at hh
      rw [he] at hh
      exact (nextHitPerm_sameCycle_iff _ hit ⟨x, hx⟩ ⟨y, hy⟩).mp hh
    exact he.trans (ih (fun f hf => hne f (List.mem_cons_of_mem _ hf))
      (plane_tail_and_split rho e (rest ++ base) hne hplane).1 hface')

end
end Mettapedia.GraphTheory.FourColor.PlanarMapBoundaryRestriction
