import Mettapedia.GraphTheory.FourColor.SerialTangleSmallCutTransfer
import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenTangleBoundaryReindex

/-!
# Repartitioning an open boundary without changing the tangle

Retained and consumed ports are a partition of the existing boundary,
not a separate wire tangle. Reindexing may change which ports are called
left and right, while preserving the literal colouring problem exactly.
-/

namespace Mettapedia.GraphTheory.FourColor.TwoSidedBoundaryReindex

open GoertzelV24OpenTangleComposition TwoSidedOpenTangleData
open GoertzelV24RotationSpliceConstructor SerialTangleSmallCutTransfer

noncomputable section
variable {V I L R L' R' : Type*}

def split (T : OpenTangleData V I (L ⊕ R)) : TwoSidedOpenTangleData V I L R where
  interiorVert := T.interiorVert
  leftVert := fun p => T.boundaryVert (.inl p)
  rightVert := fun p => T.boundaryVert (.inr p)
  interiorAlpha := T.interiorAlpha
  interiorAlpha_involutive := T.interiorAlpha_involutive
  interiorAlpha_fixfree := T.interiorAlpha_fixfree
  rho := T.rho
  vert_rho := by
    have h : twoSidedOpenTangleVertOf T.interiorVert
        (fun p => T.boundaryVert (.inl p)) (fun p => T.boundaryVert (.inr p)) =
        T.vertOf := by funext d; rcases d with d | (p | p) <;> rfl
    intro d
    rw [h]
    exact T.vert_rho d
  interior_no_self_loops := T.interior_no_self_loops
  outer := T.outer

def reindex (T : TwoSidedOpenTangleData V I L R) (e : L' ⊕ R' ≃ L ⊕ R) :
    TwoSidedOpenTangleData V I L' R' := split ((asOpen T).reindexBoundary e)

def darts (e : L' ⊕ R' ≃ L ⊕ R) : I ⊕ (L' ⊕ R') ≃ I ⊕ (L ⊕ R) :=
  Equiv.sumCongr (Equiv.refl I) e

theorem vert_reindex (T : TwoSidedOpenTangleData V I L R)
    (e : L' ⊕ R' ≃ L ⊕ R) (d : I ⊕ (L' ⊕ R')) :
    (reindex T e).vertOf d = T.vertOf (darts e d) := by
  rcases d with d | (p | p)
  · rfl
  · change Sum.elim T.leftVert T.rightVert (e (.inl p)) = T.vertOf (.inr (e (.inl p)))
    cases e (.inl p) <;> rfl
  · change Sum.elim T.leftVert T.rightVert (e (.inr p)) = T.vertOf (.inr (e (.inr p)))
    cases e (.inr p) <;> rfl

theorem tait_pullback (T : TwoSidedOpenTangleData V I L R)
    (e : L' ⊕ R' ≃ L ⊕ R) (c : T.Coloring) :
    (reindex T e).IsTaitColoring (c ∘ darts e) ↔ T.IsTaitColoring c := by
  constructor
  · rintro ⟨hm, hp, hn⟩
    refine ⟨hm, ?_, ?_⟩
    · intro d f hv hd
      have hv' : (reindex T e).vertOf ((darts e).symm d) =
          (reindex T e).vertOf ((darts e).symm f) := by
        simpa only [vert_reindex, Equiv.apply_symm_apply] using hv
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
        hp hv' (fun he => hd ((darts e).symm.injective he))
    · intro d
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hn ((darts e).symm d)
  · rintro ⟨hm, hp, hn⟩
    refine ⟨hm, ?_, fun d => hn _⟩
    intro d f hv hd
    exact hp ((vert_reindex T e d).symm.trans (hv.trans (vert_reindex T e f)))
      (fun he => hd ((darts e).injective he))

def Accepts (T : TwoSidedOpenTangleData V I L R) (w : L ⊕ R → Color) : Prop :=
  ∃ c : T.Coloring, T.IsTaitColoring c ∧ ∀ b, c (.inr b) = w b

theorem accepts_iff (T : TwoSidedOpenTangleData V I L R) (x : L → Color) (y : R → Color) :
    Accepts T (Sum.elim x y) ↔ T.AcceptsBoundaryWords x y := by
  constructor
  · rintro ⟨c, hc, hb⟩
    exact ⟨c, hc, funext (fun p => hb (.inl p)), funext (fun p => hb (.inr p))⟩
  · rintro ⟨c, hc, hx, hy⟩
    refine ⟨c, hc, ?_⟩
    rintro (p | p)
    · exact congrFun hx p
    · exact congrFun hy p

theorem accepts_reindex (T : TwoSidedOpenTangleData V I L R)
    (e : L' ⊕ R' ≃ L ⊕ R) (w : L ⊕ R → Color) :
    Accepts (reindex T e) (w ∘ e) ↔ Accepts T w := by
  constructor
  · rintro ⟨c, hc, hb⟩
    have he : (c ∘ (darts e).symm) ∘ darts e = c := by
      funext d
      exact congrArg c ((darts e).symm_apply_apply d)
    refine ⟨c ∘ (darts e).symm, (tait_pullback T e _).mp ?_, ?_⟩
    · rwa [he]
    · intro b
      simpa [Function.comp_def, darts] using hb (e.symm b)
  · rintro ⟨c, hc, hb⟩
    exact ⟨c ∘ darts e, (tait_pullback T e c).mpr hc, fun b => hb (e b)⟩

end
end Mettapedia.GraphTheory.FourColor.TwoSidedBoundaryReindex
