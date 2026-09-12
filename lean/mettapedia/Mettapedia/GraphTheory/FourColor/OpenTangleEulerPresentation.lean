import Mettapedia.GraphTheory.FourColor.VertexSideCappedComponents
import Mettapedia.GraphTheory.FourColor.MapEulerDefect
import Mettapedia.GraphTheory.FourColor.VertexAttachmentTransfer

/-!
# The Euler defect of an open tangle and its edge presentation

The provisional edge involution fixes boundary darts. Rotation orbits are
vertices only when the vertex fibers are cyclic and every vertex has a dart.
Under those hypotheses, word orbits are exactly the components of the actual
side multigraph. These identifications transport the generic handle-count
formula to open tangles, including disconnected ones and hidden components.
-/

namespace Mettapedia.GraphTheory.FourColor.OpenTangleEulerPresentation

open Equiv Equiv.Perm
open GoertzelV24OpenTangleComposition GoertzelV24CompositeSeamMultigraph
open GoertzelV24CompositeSeamCubic GoertzelV24CanonicalHubCyclicity
open GoertzelV24WordReachability GoertzelV24InvolutionEdgeList
open GoertzelV24MapEulerBound GoertzelV24PermutationOrbitSurgery
open GoertzelV24ConnectedMapEulerBound
open BoundarySmallCutViability OpenTangleMarkedFace OpenTangleReplacementEuler
open GoertzelV24BoundaryEssentialGluing.Multigraph

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V I B : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B]

def alpha (T : OpenTangleData V I B) : Perm (I ⊕ B) :=
  Equiv.sumCongr T.interiorAlpha (Equiv.refl B)

omit [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B] in
theorem alpha_involutive (T : OpenTangleData V I B) : Function.Involutive (alpha T) := by
  rintro (i | b)
  · exact congrArg Sum.inl (T.interiorAlpha_involutive i)
  · rfl

def generators (T : OpenTangleData V I B) : List (Perm (I ⊕ B)) :=
  T.rho :: swapGenerators (edgeList (alpha T))

omit [Fintype V] [DecidableEq V] in
theorem word_alpha (T : OpenTangleData V I B) (d : I ⊕ B) :
    WordReachable (generators T) d (alpha T d) := by
  have h := wordReachable_swapProduct T.rho (edgeList (alpha T)) d
  rwa [swapProduct_edgeList _ (alpha_involutive T)] at h

omit [Fintype V] [DecidableEq V] in
theorem word_same_vertex (T : OpenTangleData V I B) (hc : OpenRotationCyclic T)
    {x y : I ⊕ B} (h : T.vertOf x = T.vertOf y) : WordReachable (generators T) x y := by
  obtain ⟨n, hn⟩ := exists_nat_pow_apply_eq (hc x y h)
  simpa only [hn] using wordReachable_pow (L := generators T) List.mem_cons_self x n

theorem word_of_reach (T : OpenTangleData V I B) (hc : OpenRotationCyclic T)
    {u v : V} (h : (sideMultigraph T).Reach u v) :
    ∀ x y, T.vertOf x = u → T.vertOf y = v → WordReachable (generators T) x y := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro x y hx hy
    exact word_same_vertex T hc (hx.trans hy.symm)
  | head hs _ ih =>
    intro x y hx hy
    obtain ⟨i, hi, hi'⟩ := exists_interiorDart_of_sideStep T hs
    have hi0 : T.vertOf (.inl i) = _ := hi
    exact (word_same_vertex T hc (hx.trans hi0.symm)).trans
      ((word_alpha T (.inl i)).trans (ih (.inl (T.interiorAlpha i)) y hi' hy))

def component (T : OpenTangleData V I B) (d : I ⊕ B) :
    Quotient (componentSetoid (sideMultigraph T)) := Quotient.mk _ (T.vertOf d)

omit [Fintype V] [DecidableEq V] [Fintype I] [Fintype B] [DecidableEq B] in
theorem component_alpha (T : OpenTangleData V I B) (d : I ⊕ B) :
    component T (alpha T d) = component T d := by
  rcases d with i | b
  · apply Quotient.sound
    apply Relation.ReflTransGen.single
    refine ⟨sideEdgeOf T i, by simp, ?_⟩
    rcases sideMultigraph_ends T i with h | h
    · exact Or.inr ⟨h.1, h.2⟩
    · exact Or.inl ⟨h.1, h.2⟩
  · rfl

theorem word_iff_component (T : OpenTangleData V I B) (hc : OpenRotationCyclic T)
    (x y : I ⊕ B) : WordReachable (generators T) x y ↔ component T x = component T y := by
  constructor
  · exact VertexSideCappedComponents.invariant_word (component T) T.rho (alpha T)
      (fun d => congrArg (Quotient.mk _) (T.vert_rho d)) (component_alpha T)
  · intro h
    exact word_of_reach T hc (Quotient.exact h) x y rfl rfl

def componentEquiv (T : OpenTangleData V I B) (hc : OpenRotationCyclic T)
    (hs : Function.Surjective T.vertOf) :
    Quotient (wordSetoid (generators T)) ≃ Quotient (componentSetoid (sideMultigraph T)) :=
  Equiv.ofBijective (Quotient.lift (component T)
    (fun x y h => (word_iff_component T hc x y).mp h)) (by
      constructor
      · intro a b
        obtain ⟨x, rfl⟩ := Quotient.exists_rep a
        obtain ⟨y, rfl⟩ := Quotient.exists_rep b
        exact fun h => Quotient.sound ((word_iff_component T hc x y).mpr h)
      · intro q
        obtain ⟨v, rfl⟩ := Quotient.exists_rep q
        obtain ⟨d, hd⟩ := hs v
        exact ⟨Quotient.mk _ d, congrArg (Quotient.mk _) hd⟩)

theorem wordOrbitCount_eq_components (T : OpenTangleData V I B)
    (hc : OpenRotationCyclic T) (hs : Function.Surjective T.vertOf) :
    wordOrbitCount (generators T) = Nat.card (Quotient (componentSetoid (sideMultigraph T))) := by
  rw [wordOrbitCount, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (componentEquiv T hc hs)

omit [Fintype V] [DecidableEq V] in
theorem twice_edges (T : OpenTangleData V I B) :
    2 * (edgeList (alpha T)).length = Fintype.card I := by
  rw [two_mul_length_edgeList_eq_card_movedFinset _ (alpha_involutive T)]
  have he : movedFinset (alpha T) = Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩ := by
    ext d
    rcases d with i | b <;> simp [movedFinset, alpha, T.interiorAlpha_fixfree]
  rw [he, Finset.card_map, Finset.card_univ]

theorem orbitCount_eq_parts {D : Type*} [Fintype D] [DecidableEq D] (p : Perm D) :
    orbitCount p = p.partition.parts.card :=
  GoertzelV24FaceOrbitPartitionBridge.card_permOrbit_eq_card_partition_parts p

omit [Fintype V] [DecidableEq V] in
theorem face_count (T : OpenTangleData V I B) :
    orbitCount (T.rho * swapProduct (edgeList (alpha T))) =
      (openPhi T).partition.parts.card := by
  rw [swapProduct_edgeList _ (alpha_involutive T)]
  exact orbitCount_eq_parts (openPhi T)

def defect (T : OpenTangleData V I B) : Int :=
  4 * (Nat.card (Quotient (componentSetoid (sideMultigraph T))) : Int) - eulerMass T

/-- The two Euler bookkeepings agree, with the factor two coming from
counting interior darts instead of edges. -/
theorem defect_eq_twice (T : OpenTangleData V I B) (hc : OpenRotationCyclic T)
    (hs : Function.Surjective T.vertOf) :
    defect T = 2 * MapEulerDefect.defect T.rho (edgeList (alpha T)) := by
  have hv := orbitCount_rho_eq_card_vertex T hc hs
  have he := twice_edges T
  have he' : (2 : Int) * (edgeList (alpha T)).length = Fintype.card I := by exact_mod_cast he
  have hc' := wordOrbitCount_eq_components T hc hs
  unfold generators at hc'
  unfold defect eulerMass MapEulerDefect.defect
  rw [hc', hv, face_count]
  omega

theorem defect_nonneg (T : OpenTangleData V I B) (hc : OpenRotationCyclic T)
    (hs : Function.Surjective T.vertOf) : 0 ≤ defect T := by
  rw [defect_eq_twice T hc hs]
  have h := MapEulerDefect.defect_nonneg T.rho (edgeList (alpha T)) (edgeList_fst_ne_snd _)
  omega

end
end Mettapedia.GraphTheory.FourColor.OpenTangleEulerPresentation
