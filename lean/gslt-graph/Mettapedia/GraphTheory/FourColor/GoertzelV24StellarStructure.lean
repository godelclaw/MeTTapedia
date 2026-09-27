import Mettapedia.GraphTheory.FourColor.GoertzelV24StellarEuler
import Mettapedia.GraphTheory.FourColor.GoertzelV24WordReachability

/-!
# Connectedness, looplessness, and the three vertices of a face

The remaining conclusions of the subdivision theorem, other than containment
of the original underlying graph, are statements about the two permutations
and need no graph layer.

* **Connectedness.**  Every new dart reaches an old dart in one or two steps,
  and an old step of the original map is one or two steps of the subdivision,
  since the subdivided rotation squares to the original rotation on old darts.
  So reachability of the original transports.
* **Looplessness.**  An old edge is a loop of the subdivision exactly when it
  was a loop before.  A new edge joins the vertex carrying `α d` to the vertex
  created inside the face, and those are never the same vertex, because old and
  rim darts never share a vertex.
* **Three distinct vertices.**  The face `{old d, apex d, rim (φ⁻¹ d)}` meets
  the vertex of `old d`, the vertex of `old (α d)` — the apex dart is spliced in
  there — and the new vertex of the face.  The first two differ exactly when
  the edge at `d` is not a loop, which is the source's own reason.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24StellarStructure

open Equiv Equiv.Perm
open GoertzelV24PermutationOrbitSurgery
open GoertzelV24StellarEuler
open GoertzelV24StellarSubdivision
open GoertzelV24WordReachability

variable {D : Type*} [Fintype D] [DecidableEq D] {σ α : Perm D}

/-- The generating pair of the subdivision. -/
def stellarGenerators (σ α : Perm D) : List (Perm (StellarDart D)) :=
  [stellarRotation σ α, stellarFlip α]

theorem rotation_mem_stellarGenerators (σ α : Perm D) :
    stellarRotation σ α ∈ stellarGenerators σ α := by
  simp [stellarGenerators]

theorem flip_mem_stellarGenerators (σ α : Perm D) :
    stellarFlip α ∈ stellarGenerators σ α := by
  simp [stellarGenerators]

/-! ## Connectedness -/

/-- An old step of the flip is one step of the subdivision. -/
theorem wordReachable_old_flip (v : D) :
    WordReachable (stellarGenerators σ α) (old v) (old (α v)) := by
  simpa using wordReachable_step (flip_mem_stellarGenerators σ α) (old v)

/-- An old step of the rotation is two steps of the subdivision: the apex dart
is spliced in between. -/
theorem wordReachable_old_rotation (hinv : ∀ d, α (α d) = d) (v : D) :
    WordReachable (stellarGenerators σ α) (old v) (old (σ v)) := by
  refine (wordReachable_step (rotation_mem_stellarGenerators σ α) (old v)).trans ?_
  have hstep :=
    wordReachable_step (rotation_mem_stellarGenerators σ α)
      (stellarRotation σ α (old v))
  rwa [stellarRotation_sq_old (σ := σ) hinv] at hstep

/-- Reachability in the original map transports to its old darts. -/
theorem wordReachable_old_of_wordReachable (hinv : ∀ d, α (α d) = d) {u v : D}
    (huv : WordReachable [σ, α] u v) :
    WordReachable (stellarGenerators σ α) (old u) (old v) := by
  induction huv with
  | refl => exact WordReachable.refl _ _
  | tail _huv hstep ih =>
      obtain ⟨g, hg, rfl⟩ := hstep
      rcases List.mem_cons.1 hg with rfl | hg
      · exact ih.trans (wordReachable_old_rotation hinv _)
      · rcases List.mem_cons.1 hg with rfl | hg
        · exact ih.trans (wordReachable_old_flip _)
        · exact absurd hg List.not_mem_nil

/-- Every dart of the subdivision reaches an old dart. -/
theorem wordReachable_old_of_stellarDart (x : StellarDart D) :
    ∃ d : D, WordReachable (stellarGenerators σ α) x (old d) := by
  rcases x with d | d | d
  · exact ⟨d, WordReachable.refl _ _⟩
  · refine ⟨(σ * α) d, ?_⟩
    simpa [Equiv.Perm.mul_apply] using
      wordReachable_step (rotation_mem_stellarGenerators σ α) (apex d)
  · refine ⟨(σ * α) d, ?_⟩
    refine (wordReachable_step (flip_mem_stellarGenerators σ α) (rim d)).trans ?_
    simp only [stellarFlip_rim]
    simpa [Equiv.Perm.mul_apply] using
      wordReachable_step (rotation_mem_stellarGenerators σ α) (apex d)

/-- **Connectedness is preserved.**  If every two darts of the map are
connected, so are every two darts of its subdivision. -/
theorem wordReachable_stellar (hinv : ∀ d, α (α d) = d)
    (hconnected : ∀ u v : D, WordReachable [σ, α] u v) :
    ∀ x y : StellarDart D, WordReachable (stellarGenerators σ α) x y := by
  intro x y
  obtain ⟨dx, hx⟩ := wordReachable_old_of_stellarDart (σ := σ) (α := α) x
  obtain ⟨dy, hy⟩ := wordReachable_old_of_stellarDart (σ := σ) (α := α) y
  refine (hx.trans ?_).trans (WordReachable.symm hy)
  exact wordReachable_old_of_wordReachable hinv (hconnected dx dy)

/-! ## Looplessness -/

/-- **Looplessness is preserved.**  Old edges are loops of the subdivision
exactly when they were loops before; new edges never are, since an old dart
and a rim dart never share a vertex. -/
theorem stellar_loopless (hinv : ∀ d, α (α d) = d)
    (hloopless : ∀ d, ¬ σ.SameCycle d (α d)) :
    ∀ x : StellarDart D,
      ¬ (stellarRotation σ α).SameCycle x (stellarFlip α x) := by
  rintro (d | d | d)
  · rw [stellarFlip_old]
    intro hsame
    exact hloopless d ((stellarRotation_sameCycle_old_iff hinv d (α d)).1 hsame)
  · rw [stellarFlip_apex]
    intro hsame
    have hold : (stellarRotation σ α).SameCycle (old (α d)) (apex d) :=
      stellarRotation_sameCycle_old_apex hinv d
    exact not_stellarRotation_sameCycle_old_rim hinv (α d) d (hold.trans hsame)
  · rw [stellarFlip_rim]
    intro hsame
    have hold : (stellarRotation σ α).SameCycle (old (α d)) (apex d) :=
      stellarRotation_sameCycle_old_apex hinv d
    exact not_stellarRotation_sameCycle_old_rim hinv (α d) d
      (hold.trans hsame.symm)

/-! ## Three distinct vertices at every face -/

/-- **Each face of the subdivision meets three distinct vertices.**  The face
through an old dart meets the vertex of that dart, the vertex of its flip —
where the apex dart is spliced in — and the new vertex created inside the old
face.  The first two are distinct exactly because the edge is not a loop. -/
theorem stellar_face_three_vertices (hinv : ∀ d, α (α d) = d)
    (hloopless : ∀ d, ¬ σ.SameCycle d (α d)) (d : D) :
    ¬ (stellarRotation σ α).SameCycle (old d) (apex d) ∧
      ¬ (stellarRotation σ α).SameCycle (old d) (rim ((σ * α)⁻¹ d)) ∧
      ¬ (stellarRotation σ α).SameCycle (apex d) (rim ((σ * α)⁻¹ d)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hsame
    have hold : (stellarRotation σ α).SameCycle (old (α d)) (apex d) :=
      stellarRotation_sameCycle_old_apex hinv d
    exact hloopless d
      ((stellarRotation_sameCycle_old_iff hinv d (α d)).1 (hsame.trans hold.symm))
  · exact not_stellarRotation_sameCycle_old_rim hinv d _
  · intro hsame
    have hold : (stellarRotation σ α).SameCycle (old (α d)) (apex d) :=
      stellarRotation_sameCycle_old_apex hinv d
    exact not_stellarRotation_sameCycle_old_rim hinv (α d) _ (hold.trans hsame)

/-! ## The old darts embed the original map

The old darts carry the original map's two relations faithfully: two old darts
share a vertex of the subdivision exactly when they shared one before, and they
share an edge exactly when they did before.  Old edges are therefore neither
merged nor split, and their endpoints are unchanged. -/

/-- Two old darts share an edge of the subdivision exactly when they shared one
before. -/
theorem stellarFlip_sameCycle_old_iff (hinv : ∀ d, α (α d) = d) (d e : D) :
    (stellarFlip α).SameCycle (old d) (old e) ↔ α.SameCycle d e := by
  rw [sameCycle_involutive_iff (stellarFlip_involutive hinv) (old e) (old d),
    sameCycle_involutive_iff hinv e d, stellarFlip_old]
  constructor
  · rintro (h | h)
    · exact Or.inl (Sum.inl_injective h)
    · exact Or.inr (Sum.inl_injective h)
  · rintro (h | h)
    · exact Or.inl (congrArg old h)
    · exact Or.inr (congrArg old h)

/-- **The old darts embed the original map.**  Both relations are preserved and
reflected, so no old vertex is split or merged and no old edge is lost. -/
theorem stellar_old_embedding (hinv : ∀ d, α (α d) = d) (d e : D) :
    ((stellarRotation σ α).SameCycle (old d) (old e) ↔ σ.SameCycle d e) ∧
      ((stellarFlip α).SameCycle (old d) (old e) ↔ α.SameCycle d e) :=
  ⟨stellarRotation_sameCycle_old_iff hinv d e, stellarFlip_sameCycle_old_iff hinv d e⟩

end GoertzelV24StellarStructure

end Mettapedia.GraphTheory.FourColor
