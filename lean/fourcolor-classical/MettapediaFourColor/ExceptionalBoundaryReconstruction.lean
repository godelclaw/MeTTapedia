import MettapediaFourColor.ExceptionalBoundaryOccurrence
import MettapediaFourColor.PatchBoundaryGluing

/-!
# Reconstructing colourings through the exceptional eleven-port completion

The actual pair of aligned exceptional occurrences supplies the geometry
needed by patch gluing. A genuine completion colouring that agrees with one
exterior assignment reconstructs a colouring of the full ambient dual.
Port identifications are retained through this single joint assignment.
Existence or Kempe repair of a compatible completion colouring is separate.
-/

namespace FourColor.ExceptionalBoundaryReconstruction

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24FaceOrbitIncidence
open ExceptionalCore ExceptionalBoundaryCompletion ExceptionalBoundaryOccurrence

set_option maxRecDepth 32768

def interior : Set (Fin 19) := {a | 11 ≤ a.val}

theorem interior_iff (a : Fin 19) : a ∈ interior ↔ ∃ i : Fin 8, a = i.natAdd 11 := by
  constructor
  · intro h
    exact ⟨⟨a.val - 11, by have := a.isLt; change 11 ≤ a.val at h; omega⟩,
      by apply Fin.ext; change a.val = 11 + (a.val - 11); exact (Nat.add_sub_of_le h).symm⟩
  · rintro ⟨i, rfl⟩
    change 11 ≤ 11 + i.val
    omega

theorem exterior_iff (a : Fin 19) : a ∉ interior ↔ ∃ p : Fin 11, a = p.castAdd 8 := by
  constructor
  · intro h
    exact ⟨⟨a.val, by change ¬ 11 ≤ a.val at h; omega⟩, by apply Fin.ext; rfl⟩
  · rintro ⟨p, rfl⟩
    exact Nat.not_le.mpr p.isLt

theorem source_spoke_adj : ∀ (i : Fin 8) (p : Fin (coreDegree i)),
    input.graph.Adj (i.natAdd 11) (fullSpoke i p) := by decide +kernel

noncomputable section

variable {W : Type*} [Fintype W] [DecidableEq W]
  {H : SimpleGraph W} [DecidableRel H.Adj]
  (original : Data H)
  (minimal : GoertzelV24TwoEdgeCutMinimality.GraphBackedVertexMinimalTaitCounterexample original)

variable (x y : ExceptionalPattern.Occurrence
    (MinimalExceptionalEmbedding.rotation original minimal))
  (aligned : y.vertex 0 = x.vertex 14)

theorem interior_image :
    sourceHom original minimal x y aligned '' interior = Set.range (coreVertex x) := by
  ext v
  constructor
  · rintro ⟨a, ha, he⟩
    obtain ⟨i, rfl⟩ := (interior_iff a).mp ha
    exact ⟨i, (source_core original minimal x y aligned i).symm.trans he⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.natAdd 11, (interior_iff _).mpr ⟨i, rfl⟩,
      source_core original minimal x y aligned i⟩

/-- Exact reconstruction fixing every exterior vertex. No independent choices
are substituted for agreement with the same exterior assignment. -/
theorem reconstruct {C : Type*} (inside : input.graph.Coloring C)
    (outside : OrbitFace original.toRotationSystem → C)
    (proper : ∀ {v w}, v ∉ Set.range (coreVertex x) → w ∉ Set.range (coreVertex x) →
      (MinimalExceptionalEmbedding.graph original minimal).Adj v w → outside v ≠ outside w)
    (agree : ∀ p : Fin 11, inside (p.castAdd 8) =
      outside (sourceHom original minimal x y aligned (p.castAdd 8))) :
    ∃ k : (MinimalExceptionalEmbedding.graph original minimal).Coloring C,
      (∀ a, k (sourceHom original minimal x y aligned a) = inside a) ∧
      ∀ v, v ∉ Set.range (coreVertex x) → k v = outside v := by
  classical
  let f := sourceHom original minimal x y aligned
  have img : f '' interior = Set.range (coreVertex x) :=
    interior_image original minimal x y aligned
  have inj : Set.InjOn f interior := by
    intro a ha b hb eq
    obtain ⟨i, rfl⟩ := (interior_iff a).mp ha
    obtain ⟨j, rfl⟩ := (interior_iff b).mp hb
    have eq' : coreVertex x i = coreVertex x j := by
      simpa only [f, source_core] using eq
    exact congrArg (fun i : Fin 8 => i.natAdd 11)
      (MinimalExceptionalEmbedding.source_core_injective original minimal x y aligned eq')
  have no_capture : ∀ a, a ∉ interior → f a ∉ f '' interior := by
    intro a ha
    obtain ⟨p, rfl⟩ := (exterior_iff a).mp ha
    rw [img]
    rintro ⟨i, hi⟩
    exact source_ring_outside original minimal x y aligned p i hi.symm
  have covers : ∀ a ∈ interior, ∀ v,
      (MinimalExceptionalEmbedding.graph original minimal).Adj (f a) v →
        ∃ b, input.graph.Adj a b ∧ f b = v := by
    intro a ha v adj
    obtain ⟨i, rfl⟩ := (interior_iff a).mp ha
    let reading : JointReading (MinimalExceptionalEmbedding.rotation original minimal) :=
      jointReading x (MinimalExceptionalEmbedding.triangular original minimal)
        (MinimalExceptionalEmbedding.cyclic original minimal) y aligned
    have adj' : (MinimalExceptionalEmbedding.graph original minimal).Adj (coreVertex x i) v := by
      simpa only [f, source_core] using adj
    obtain ⟨p, hp⟩ := star_covers reading
      (MinimalExceptionalEmbedding.triangular original minimal)
      (MinimalExceptionalEmbedding.cyclic original minimal) i adj'
    exact ⟨fullSpoke i p, source_spoke_adj i p, hp⟩
  obtain ⟨k, hk, hext⟩ := PatchBoundaryGluing.reconstruct f interior inj no_capture covers
    inside outside
    (by intro v w hv hw h; rw [img] at hv hw; exact proper hv hw h)
    (by intro a ha; obtain ⟨p, rfl⟩ := (exterior_iff a).mp ha; exact agree p)
  exact ⟨k, hk, by simpa only [img] using hext⟩

/-- The eleven joint observations exactly describe extension of a fixed
proper exterior assignment, even when boundary labels have equal images. -/
theorem extension_iff {C : Type*} (outside : OrbitFace original.toRotationSystem → C)
    (proper : ∀ {v w}, v ∉ Set.range (coreVertex x) → w ∉ Set.range (coreVertex x) →
      (MinimalExceptionalEmbedding.graph original minimal).Adj v w → outside v ≠ outside w) :
    (∃ k : (MinimalExceptionalEmbedding.graph original minimal).Coloring C,
      ∀ v, v ∉ Set.range (coreVertex x) → k v = outside v) ↔
    ∃ inside : input.graph.Coloring C, ∀ p : Fin 11, inside (p.castAdd 8) =
      outside (sourceHom original minimal x y aligned (p.castAdd 8)) := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k.comp (sourceHom original minimal x y aligned), ?_⟩
    intro p
    apply hk
    rintro ⟨i, hi⟩
    exact source_ring_outside original minimal x y aligned p i hi.symm
  · rintro ⟨inside, agree⟩
    obtain ⟨k, _, hext⟩ := reconstruct original minimal x y aligned inside outside proper agree
    exact ⟨k, hext⟩

end
end FourColor.ExceptionalBoundaryReconstruction
