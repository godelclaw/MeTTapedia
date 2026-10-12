import Mettapedia.GSLT.Logic.RelativePushoutFunctor

/-!
# Complete relative-pushout candidates under full category comparisons

The comparison acts on a candidate's apex, both legs and its descent map.
Fullness and faithfulness transport all three mediator equations and their
uniqueness. Preservation also requires object surjectivity, so every target
competitor is covered, rather than only competitors already in the image.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.GSLT.RelativePushout

open _root_.CategoryTheory

universe u v u' v'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable (F : C ⥤ D) [F.Full] [F.Faithful]
variable {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

theorem reflects_relativePushout (candidate : Candidate f g h i)
    (mapped : IsRelativePushout (mapCandidate F candidate)) : IsRelativePushout candidate := by
  intro other
  obtain ⟨mediator, equations, unique⟩ := mapped (mapCandidate F other)
  change F.obj candidate.apex ⟶ F.obj other.apex at mediator
  dsimp only [mapCandidate, Candidate.Mediates] at equations unique ⊢
  refine ⟨F.preimage mediator, ?_, ?_⟩
  · refine ⟨F.map_injective ?_, F.map_injective ?_, F.map_injective ?_⟩
    · simpa only [F.map_comp, F.map_preimage] using equations.1
    · simpa only [F.map_comp, F.map_preimage] using equations.2.1
    · simpa only [F.map_comp, F.map_preimage] using equations.2.2
  · intro alternative laws
    apply F.map_injective
    rw [F.map_preimage]
    apply unique
    exact ⟨by simpa only [F.map_comp] using congrArg F.map laws.1,
      by simpa only [F.map_comp] using congrArg F.map laws.2.1,
      by simpa only [F.map_comp] using congrArg F.map laws.2.2⟩

theorem preserves_relativePushout (objects : Function.Surjective F.obj)
    (candidate : Candidate f g h i) (universal : IsRelativePushout candidate) :
    IsRelativePushout (mapCandidate F candidate) := by
  intro other
  rcases other with ⟨otherApex, otherInl, otherInr, otherDown,
    otherComm, otherLeft, otherRight⟩
  obtain ⟨apex, rfl⟩ := objects otherApex
  let lifted : Candidate f g h i :=
    { apex := apex
      inl := F.preimage otherInl
      inr := F.preimage otherInr
      down := F.preimage otherDown
      comm := F.map_injective (by simpa only [F.map_comp, F.map_preimage] using otherComm)
      fac_left := F.map_injective (by simpa only [F.map_comp, F.map_preimage] using otherLeft)
      fac_right := F.map_injective (by simpa only [F.map_comp, F.map_preimage] using otherRight) }
  obtain ⟨mediator, equations, unique⟩ := universal lifted
  dsimp only [mapCandidate, Candidate.Mediates] at equations unique ⊢
  refine ⟨F.map mediator, ?_, ?_⟩
  · exact ⟨by simpa only [lifted, F.map_comp, F.map_preimage] using congrArg F.map equations.1,
      by simpa only [lifted, F.map_comp, F.map_preimage] using congrArg F.map equations.2.1,
      by simpa only [lifted, F.map_comp, F.map_preimage] using congrArg F.map equations.2.2⟩
  · intro alternative laws
    have same : F.preimage alternative = mediator := by
      apply unique
      refine ⟨F.map_injective ?_, F.map_injective ?_, F.map_injective ?_⟩
      · simpa only [lifted, F.map_comp, F.map_preimage] using laws.1
      · simpa only [lifted, F.map_comp, F.map_preimage] using laws.2.1
      · simpa only [lifted, F.map_comp, F.map_preimage] using laws.2.2
    simpa only [F.map_preimage] using congrArg F.map same

theorem relativePushout_iff_mapped (objects : Function.Surjective F.obj)
    (candidate : Candidate f g h i) :
    IsRelativePushout candidate ↔ IsRelativePushout (mapCandidate F candidate) :=
  ⟨preserves_relativePushout F objects candidate, reflects_relativePushout F candidate⟩

end Mettapedia.GSLT.RelativePushout
