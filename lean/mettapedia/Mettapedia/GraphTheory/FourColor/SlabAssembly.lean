import Mettapedia.GraphTheory.FourColor.GeneralSlabEmbedding

/-!
# Serial assembly of actual embedded slabs

Two consecutive slabs determine their own seam matching from the complete
ambient boundary maps. Their union realizes the literal serial constructor,
including internal edge identities and vertex rotations. This is a geometric
assembly statement, independent of colouring support.
-/

namespace Mettapedia.GraphTheory.FourColor.TubeSlab.SlabOf

open GoertzelV24OpenTangleComposition TwoSidedOpenTangleData
open GoertzelV24RotationCutDartDecomposition

noncomputable section

universe u
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  {RS : RotationSystem.{u, u, u} V E} {k : ℕ} [NeZero k]
  {A I B J : Type*}
  {P : TwoSidedOpenTangleData A I (Fin k) (Fin k)}
  {Q : TwoSidedOpenTangleData B J (Fin k) (Fin k)}
  {inner : V → Prop} (S : SlabOf RS P inner)

/-- The embedding respects the actual cyclic order at vertices. -/
def RotationCompatible : Prop := ∀ d, RS.rho (S.ι d) = S.ι (P.rho d)

variable (T : SlabOf RS Q S.inner')

/-- Pairing read from the two complete maps to the same ambient cut. -/
def matching : Fin k ≃ Fin k := S.outEquiv.trans T.inEquiv.symm

theorem matching_mate (i : Fin k) :
    RS.alpha (S.ι (.inr (.inr i))) = T.ι (.inr (.inl (S.matching T i))) := by
  have h := congrArg (fun b : BoundaryDart RS S.inner' => b.1.1)
    (T.inEquiv.apply_symm_apply (S.outEquiv i))
  change RS.alpha (T.ι (.inr (.inl (S.matching T i)))) = S.ι (.inr (.inr i)) at h
  have hh := congrArg RS.alpha h
  rw [RS.alpha_involutive] at hh
  exact hh.symm

theorem matching_mate_symm (i : Fin k) :
    RS.alpha (T.ι (.inr (.inl i))) = S.ι (.inr (.inr ((S.matching T).symm i))) := by
  have h := congrArg RS.alpha (S.matching_mate T ((S.matching T).symm i))
  simpa only [RS.alpha_involutive, Equiv.apply_symm_apply] using h.symm

omit [NeZero k] in
theorem vertices_disjoint (a : A) (b : B) : S.vtx a ≠ T.vtx b := by
  intro h
  exact T.vtx_not_inner b (Or.inr ⟨a, h.symm⟩)

omit [NeZero k] in
theorem darts_disjoint (a : SlabDart P) (b : SlabDart Q) : S.ι a ≠ T.ι b := by
  intro h
  exact S.vertices_disjoint T _ _ ((S.vert_ι a).symm.trans
    ((congrArg RS.vertOf h).trans (T.vert_ι b)))

/-- The disjoint source vertices are the actual vertices of the two slabs. -/
def joinedVertex : A ⊕ B → V := Sum.elim S.vtx T.vtx

omit [NeZero k] in
theorem joinedVertex_injective : Function.Injective (S.joinedVertex T) := by
  rintro (a | b) (a' | b') h
  · exact congrArg Sum.inl (S.vtx_inj h)
  · exact (S.vertices_disjoint T a b' h).elim
  · exact (S.vertices_disjoint T a' b h.symm).elim
  · exact congrArg Sum.inr (T.vtx_inj h)

/-- Serial carrier reassociation changes no ambient dart. -/
def joinedDart : SlabDart (serialCompose P Q (S.matching T)) → RS.D :=
  Sum.elim S.ι T.ι ∘ serialDartEquiv.symm

theorem joinedDart_serial (d : SlabDart P ⊕ SlabDart Q) :
    S.joinedDart T (serialDartEquiv d) = Sum.elim S.ι T.ι d := by
  simp [joinedDart]

theorem joinedDart_injective : Function.Injective (S.joinedDart T) := by
  have hinj : Function.Injective (Sum.elim S.ι T.ι) := by
    rintro (a | b) (a' | b') h
    · exact congrArg Sum.inl (S.ι_inj h)
    · exact (S.darts_disjoint T a b' h).elim
    · exact (S.darts_disjoint T a' b h.symm).elim
    · exact congrArg Sum.inr (T.ι_inj h)
  exact hinj.comp serialDartEquiv.symm.injective

theorem joinedDart_vert (d : SlabDart (serialCompose P Q (S.matching T))) :
    RS.vertOf (S.joinedDart T d) =
      S.joinedVertex T ((serialCompose P Q (S.matching T)).vertOf d) := by
  rcases d with ((i | j) | (p | q)) | (p | q)
  · exact S.vert_ι (.inl i)
  · exact T.vert_ι (.inl j)
  · exact S.vert_ι (.inr (.inr p))
  · exact T.vert_ι (.inr (.inl q))
  · exact S.vert_ι (.inr (.inl p))
  · exact T.vert_ι (.inr (.inr q))

/-- The complete serial tangle is embedded in the original rotation system. -/
def assemble : SlabOf RS (serialCompose P Q (S.matching T)) inner where
  ι := S.joinedDart T
  vtx := S.joinedVertex T
  ι_inj := S.joinedDart_injective T
  vtx_inj := S.joinedVertex_injective T
  vtx_not_inner := by
    rintro (a | b) h
    · exact S.vtx_not_inner a h
    · exact T.vtx_not_inner b (Or.inl h)
  vert_ι := S.joinedDart_vert T
  alpha_interior := by
    rintro ((i | j) | (p | q))
    · exact S.alpha_interior i
    · exact T.alpha_interior j
    · exact S.matching_mate T p
    · exact S.matching_mate_symm T q
  in_inner := S.in_inner
  out_not_inner := fun i h => T.out_not_inner i (Or.inl h)
  out_not_slab := by
    rintro i (a | b) h
    · exact T.out_not_inner i (Or.inr ⟨a, h⟩)
    · exact T.out_not_slab i b h
  cubic_slab := by
    rintro d ⟨a | b, hv⟩
    · obtain ⟨x, hx⟩ := S.cubic_slab d ⟨a, hv⟩
      exact ⟨serialDartEquiv (.inl x), (S.joinedDart_serial T _).trans hx⟩
    · obtain ⟨x, hx⟩ := T.cubic_slab d ⟨b, hv⟩
      exact ⟨serialDartEquiv (.inr x), (S.joinedDart_serial T _).trans hx⟩
  boundary_inner := S.boundary_inner

theorem assemble_inner' : (S.assemble T).inner' = T.inner' := by
  funext v
  apply propext
  change (inner v ∨ ∃ w : A ⊕ B, v = S.joinedVertex T w) ↔
    (inner v ∨ ∃ a, v = S.vtx a) ∨ ∃ b, v = T.vtx b
  simp only [Sum.exists, joinedVertex, Sum.elim_inl, Sum.elim_inr]
  exact or_assoc.symm

theorem assemble_inEquiv : (S.assemble T).inEquiv = S.inEquiv := by
  ext i
  rfl

theorem assemble_rotationCompatible (hS : S.RotationCompatible)
    (hT : T.RotationCompatible) : (S.assemble T).RotationCompatible := by
  intro d
  obtain ⟨x, rfl⟩ := serialDartEquiv.surjective d
  change RS.rho (S.joinedDart T (serialDartEquiv x)) =
    S.joinedDart T ((serialCompose P Q (S.matching T)).rho (serialDartEquiv x))
  rw [S.joinedDart_serial]
  have hr : (serialCompose P Q (S.matching T)).rho (serialDartEquiv x) =
      serialDartEquiv ((Equiv.sumCongr P.rho Q.rho) x) := by
    change serialDartEquiv ((Equiv.sumCongr P.rho Q.rho)
      (serialDartEquiv.symm (serialDartEquiv x))) = _
    rw [Equiv.symm_apply_apply]
  rw [hr, S.joinedDart_serial]
  cases x with
  | inl x => exact hS x
  | inr x => exact hT x

/-- Use a prescribed seam only after identifying it with the actual one. -/
def assembleWith (m : Fin k ≃ Fin k) (hm : S.matching T = m) :
    SlabOf RS (serialCompose P Q m) inner := hm ▸ S.assemble T

theorem assembleWith_inner' (m : Fin k ≃ Fin k) (hm : S.matching T = m) :
    (S.assembleWith T m hm).inner' = T.inner' := by
  subst m
  exact S.assemble_inner' T

theorem assembleWith_input (m : Fin k ≃ Fin k) (hm : S.matching T = m) (i : Fin k) :
    (S.assembleWith T m hm).ι (.inr (.inl i)) = S.ι (.inr (.inl i)) := by
  subst m
  rfl

theorem assembleWith_output (m : Fin k ≃ Fin k) (hm : S.matching T = m) (i : Fin k) :
    (S.assembleWith T m hm).ι (.inr (.inr i)) = T.ι (.inr (.inr i)) := by
  subst m
  rfl

theorem assembleWith_rotationCompatible (m : Fin k ≃ Fin k) (hm : S.matching T = m)
    (hS : S.RotationCompatible) (hT : T.RotationCompatible) :
    (S.assembleWith T m hm).RotationCompatible := by
  subst m
  exact S.assemble_rotationCompatible T hS hT

end
end Mettapedia.GraphTheory.FourColor.TubeSlab.SlabOf
