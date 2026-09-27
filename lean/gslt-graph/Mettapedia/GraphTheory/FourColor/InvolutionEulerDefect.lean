import Mettapedia.GraphTheory.FourColor.OpenTangleEulerPresentation

/-!
# Presentation-independent Euler defect and edge deletion

The same involution has many edge lists. Its defect is independent of the
chosen list when every listed transposition stays inside a component of the
involution and the list has the correct length. Restricting to an invariant
set of edges cannot increase the defect.
-/

namespace Mettapedia.GraphTheory.FourColor.InvolutionEulerDefect

open Equiv Equiv.Perm
open GoertzelV24WordReachability GoertzelV24InvolutionEdgeList
open GoertzelV24MapEulerBound GoertzelV24PermutationOrbitSurgery
open GoertzelV24OrbitCountCongr GoertzelV24ConnectedMapEulerBound
open InvolutionRestrictionEdgeList VertexSideCappedComponents

noncomputable section
attribute [local instance] Classical.propDecidable
variable {D : Type*} [Fintype D] [DecidableEq D]

theorem presentation_reach (rho a : Perm D) (edges : List (D × D))
    (hp : swapProduct edges = a)
    (he : ∀ e ∈ edges, WordReachable [rho, a] e.1 e.2) (x y : D) :
    WordReachable (rho :: swapGenerators edges) x y ↔ WordReachable [rho, a] x y := by
  constructor
  · apply wordReachable_absorb
    intro g hg d
    rcases List.mem_cons.mp hg with rfl | hg
    · exact wordReachable_step List.mem_cons_self d
    obtain ⟨e, he', rfl⟩ := List.mem_map.mp hg
    by_cases h1 : d = e.1
    · subst d; simpa using he e he'
    by_cases h2 : d = e.2
    · subst d; simpa using (he e he').symm
    rw [swap_apply_of_ne_of_ne h1 h2]
    exact .refl _ _
  · apply wordReachable_absorb
    intro g hg d
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact wordReachable_step List.mem_cons_self d
    · simpa only [hp] using wordReachable_swapProduct rho edges d

theorem edgeList_reach (rho a : Perm D) (ha : Function.Involutive a) (x y : D) :
    WordReachable (rho :: swapGenerators (edgeList a)) x y ↔ WordReachable [rho, a] x y := by
  apply presentation_reach rho a _ (swapProduct_edgeList a ha)
  intro e he
  apply Quotient.exact (s := wordSetoid [rho, a])
  exact invariant_edgeList (Quotient.mk (wordSetoid [rho, a])) a
    (fun d => Quotient.sound (wordReachable_step (by simp) d).symm) e he

theorem presentation_count (rho a : Perm D) (edges : List (D × D))
    (hp : swapProduct edges = a)
    (he : ∀ e ∈ edges, WordReachable [rho, a] e.1 e.2) :
    wordOrbitCount (rho :: swapGenerators edges) = wordOrbitCount [rho, a] := by
  apply Nat.le_antisymm
  · exact wordOrbitCount_le_of_le (fun x y => (presentation_reach rho a edges hp he x y).mpr)
  · exact wordOrbitCount_le_of_le (fun x y => (presentation_reach rho a edges hp he x y).mp)

theorem edgeList_count (rho a : Perm D) (ha : Function.Involutive a) :
    wordOrbitCount (rho :: swapGenerators (edgeList a)) = wordOrbitCount [rho, a] := by
  apply Nat.le_antisymm
  · exact wordOrbitCount_le_of_le (fun x y => (edgeList_reach rho a ha x y).mpr)
  · exact wordOrbitCount_le_of_le (fun x y => (edgeList_reach rho a ha x y).mp)

/-- Four times total genus for a genuine ribbon graph. Boundary darts
fixed by the involution are not counted as internal edges. -/
def defect (rho a : Perm D) : Int :=
  (movedFinset a).card + 4 * (wordOrbitCount [rho, a] : Int) -
    2 * orbitCount rho - 2 * orbitCount (rho * a)

theorem defect_eq_presentation (rho a : Perm D) (ha : Function.Involutive a) :
    defect rho a = 2 * MapEulerDefect.defect rho (edgeList a) := by
  have hl := two_mul_length_edgeList_eq_card_movedFinset a ha
  have hl' : (2 : Int) * (edgeList a).length = (movedFinset a).card := by exact_mod_cast hl
  simp only [defect, MapEulerDefect.defect, edgeList_count rho a ha, swapProduct_edgeList a ha]
  omega

theorem defect_nonneg (rho a : Perm D) (ha : Function.Involutive a) : 0 ≤ defect rho a := by
  rw [defect_eq_presentation rho a ha]
  have h := MapEulerDefect.defect_nonneg rho (edgeList a) (edgeList_fst_ne_snd a)
  omega

theorem defect_restrict_le (rho a : Perm D) (ha : Function.Involutive a)
    (keep : D → Prop) (hk : ∀ d, keep (a d) ↔ keep d) :
    defect rho (restrict a ha keep hk) ≤ defect rho a := by
  let p := restrict a ha keep hk
  let q := restrict a ha (fun d => ¬ keep d) (fun d => not_congr (hk d))
  let es := edgeList q ++ edgeList p
  have hp : swapProduct es = a := by
    rw [swapProduct_append, swapProduct_edgeList _ (restrict_involutive _ _ _ _),
      swapProduct_edgeList _ (restrict_involutive _ _ _ _)]
    exact restrict_compl_mul a ha keep hk
  have he : ∀ e ∈ es, WordReachable [rho, a] e.1 e.2 := by
    intro e h
    apply Quotient.exact (s := wordSetoid [rho, a])
    have inv (k : D → Prop) (hka : ∀ d, k (a d) ↔ k d) (d : D) :
        Quotient.mk (wordSetoid [rho, a]) (restrict a ha k hka d) = Quotient.mk _ d := by
      rw [restrict_apply]
      split_ifs
      · exact Quotient.sound (wordReachable_step (by simp) d).symm
      · rfl
    rcases List.mem_append.mp h with h | h
    · exact invariant_edgeList _ q (inv _ _) e h
    · exact invariant_edgeList _ p (inv _ _) e h
  have hl : es.length = (edgeList a).length := by
    exact (List.length_append ..).trans (length_restrict_add_compl a ha keep hk)
  have heq : MapEulerDefect.defect rho es = MapEulerDefect.defect rho (edgeList a) := by
    simp only [MapEulerDefect.defect, hl, presentation_count rho a es hp he,
      edgeList_count rho a ha, hp, swapProduct_edgeList a ha]
  have hm := MapEulerDefect.defect_mono rho (edgeList q) (edgeList p) (edgeList_fst_ne_snd q)
  change MapEulerDefect.defect rho (edgeList p) ≤ MapEulerDefect.defect rho es at hm
  rw [heq] at hm
  dsimp only [p] at hm
  rw [defect_eq_presentation _ _ (restrict_involutive _ _ _ _), defect_eq_presentation _ _ ha]
  omega

end
end Mettapedia.GraphTheory.FourColor.InvolutionEulerDefect
