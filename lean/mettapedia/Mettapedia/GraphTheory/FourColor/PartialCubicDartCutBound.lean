import Mettapedia.GraphTheory.FourColor.PartialCubicDartBoundary

/-!
# Cut bounds before global injectivity

Only unpaired slots whose endpoints actually leave the realized image can
contribute to its cut. This remains true when a partial diagram identifies
vertices, allowing cut conditions to exclude such identifications.
-/

namespace Mettapedia.GraphTheory.FourColor.PartialCubicDartSeparation.Realization

open _root_.SimpleGraph GoertzelV24CubicSmallBoundaryCycle

noncomputable section
variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {P : Diagram W} (F : Realization P G)

omit [DecidableEq W] [DecidableEq V] [DecidableRel G.Adj] in
theorem card_imageSide_le : Fintype.card {v // F.imageSide v} ≤ Fintype.card W := by
  classical
  apply Fintype.card_le_of_surjective (fun w => (⟨F.vertex w, ⟨w, rfl⟩⟩ : {v // F.imageSide v}))
  rintro ⟨v, w, rfl⟩
  exact ⟨w, rfl⟩

omit [DecidableEq W] [DecidableEq V] in
theorem crossing_card_le_of_internal (allowed : Unpaired (P := P) → Prop)
    [DecidablePred allowed]
    (hinternal : ∀ p, ¬ allowed p → F.imageSide (F.dart p.1).snd) :
    Fintype.card (CrossingSideDart G F.imageSide) ≤ Fintype.card {p // allowed p} := by
  classical
  let f : CrossingSideDart G F.imageSide → {p // allowed p} := fun d =>
    ⟨F.crossingIndex d, by
      by_contra hn
      have hh := hinternal (F.crossingIndex d) hn
      rw [F.crossingIndex_dart] at hh
      exact d.2.2 hh⟩
  apply Fintype.card_le_of_injective f
  intro a b he
  exact F.crossingIndex_injective (congrArg Subtype.val he)

end
end Mettapedia.GraphTheory.FourColor.PartialCubicDartSeparation.Realization
