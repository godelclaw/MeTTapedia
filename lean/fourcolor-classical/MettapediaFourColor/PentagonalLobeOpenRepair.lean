import MettapediaFourColor.PentagonalLobeTreeGeometry
import MettapediaFourColor.PhysicalKempeBoundary

/-! # Joint repair in an ordinary open exterior

The boundary relation retains whole exterior colourings. Its exact physical
support supplies the same repair used by the serial interface, and genuine
witnesses reconstruct a colouring of the closed sewing.
-/

namespace FourColor.PentagonalLobePatch.Tangle

open Mettapedia.GraphTheory.FourColor
open GoertzelV24OpenTangleComposition GoertzelV24TwoEdgeCutMinimality
open GoertzelV24PortTangleGluing GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24PortTangleCutParity GoertzelV24PhysicalKempeNoncrossingClosure
open GoertzelV24HexagonPairingTargetAwareBoundary

noncomputable section
universe u
variable {W J B : Type u}
  [Fintype W] [DecidableEq W] [Fintype J] [DecidableEq J]
  [Fintype B] [DecidableEq B]
  (outside : OpenTangleData W J B) (seam : Fin 6 ≃ B)

abbrev openExteriorTangle := ofOpenTangleData outside

def OpenTrace (et : List Color) : Prop :=
  ∃ r : J ⊕ B → Mettapedia.GraphTheory.FourColor.Color,
    OpenTangleClosedWitness.IsColor outside r ∧
      (List.finRange 6).map (fun i => r (.inr (seam i))) = et.map palette

private theorem palette_agrees (c : Color) : PhysicalKempeBoundary.palette c = palette c := by
  cases c <;> rfl

/-- Forgetting rotations preserves precisely the full exterior colouring
witnesses and their ordered six-port observation. -/
theorem openTrace_iff (et : List Color) :
    PhysicalKempeBoundary.Trace (orderedTaitSupport seam (openExteriorTangle outside)) et ↔
      OpenTrace outside seam et := by
  constructor
  · rintro ⟨w, ⟨c, hc, he⟩, rfl⟩
    refine ⟨c.color, ⟨c.invariant, ?_, hc.1⟩, ?_⟩
    · intro d e hv hn
      exact hc.2 d e (by simpa [openExteriorTangle, ofOpenTangleData] using hv) hn
    · change _ = (List.ofFn (PhysicalKempeBoundary.referenceWord w)).map palette
      rw [List.map_ofFn, ← List.ofFn_eq_map]
      apply congrArg List.ofFn
      funext i
      have hi := congrFun he (seam i)
      have hread : c.color (.inr (seam i)) = (w i).val := by
        simpa only [word, Equiv.symm_apply_apply] using hi
      rw [hread, Function.comp_apply, ← palette_agrees]
      exact (PhysicalKempeBoundary.palette.apply_symm_apply _).symm
  · rintro ⟨r, hr, he⟩
    let c : PortTangle.Coloring (openExteriorTangle outside) := ⟨r, hr.1⟩
    have hc : IsProper c := ⟨hr.2.2, fun d e hv hn =>
      hr.2.1 (by simpa [openExteriorTangle, ofOpenTangleData] using hv) hn⟩
    refine ⟨orderedProperBoundaryWord seam c hc,
      orderedProperBoundaryWord_mem_orderedTaitSupport seam _ c hc, ?_⟩
    apply List.map_injective_iff.mpr PhysicalKempeBoundary.palette.injective
    change (List.ofFn (PhysicalKempeBoundary.referenceWord _)).map
        PhysicalKempeBoundary.palette = et.map PhysicalKempeBoundary.palette
    rw [List.map_ofFn]
    have hpal : (et.map palette) = et.map PhysicalKempeBoundary.palette := by
      apply List.map_congr_left
      intro a _
      exact (palette_agrees a).symm
    rw [← hpal, ← he, ← List.ofFn_eq_map]
    apply congrArg List.ofFn
    funext i
    exact PhysicalKempeBoundary.palette.apply_symm_apply _

/-- Physical switching discharges the abstract exterior-closure hypothesis. -/
theorem open_exterior_closed
    (hcubic : IsCubic (openExteriorTangle outside))
    (hnoncrossing : ∀ (c : PortTangle.Coloring (openExteriorTangle outside)) (hc : IsProper c)
      (pair : TaitColorPair),
      IsNoncrossingMatching (orderedPhysicalMate seam (openExteriorTangle outside)
        hcubic c hc pair)) :
    KempeClosed (OpenTrace outside seam) := by
  have h := PhysicalKempeBoundary.ordered_closed seam (openExteriorTangle outside)
    hcubic hnoncrossing
  simpa only [KempeClosed, openTrace_iff] using h

omit [Fintype W] [DecidableEq W] [Fintype J] [DecidableEq J] [Fintype B] [DecidableEq B] in
/-- Actual joint colouring witnesses in the two ordinary open pieces. -/
theorem open_compatible_darts (hclosed : KempeClosed (OpenTrace outside seam))
    (et : List Color) (hlen : et.length = 6) (hzero : (0 : Color) ∉ et)
    (hsum : et.sum = 0) (hold : OpenTrace outside seam et) :
    ∃ k : graph.Coloring Color, ∃ r : J ⊕ B → Mettapedia.GraphTheory.FourColor.Color,
      OpenTangleClosedWitness.IsColor outside r ∧
        ∀ i, colouring k (.inr i) = r (.inr (seam i)) := by
  obtain ⟨k, r, hr, he⟩ := compatible_colouring hclosed et hlen hzero hsum hold
  refine ⟨k, r, hr, ?_⟩
  have hmaps := (boundary_colouring k).trans he.symm
  intro i
  exact List.map_inj_left.mp hmaps i (List.mem_finRange i)

/-- The exterior may be recoloured, but the final witnesses agree jointly at
all ports and colour the literal closed map. -/
theorem open_colorable_of_physical_noncrossing
    (hcubic : IsCubic (openExteriorTangle outside))
    (hnoncrossing : ∀ (c : PortTangle.Coloring (openExteriorTangle outside)) (hc : IsProper c)
      (pair : TaitColorPair), IsNoncrossingMatching
        (orderedPhysicalMate seam (openExteriorTangle outside) hcubic c hc pair))
    (r : J ⊕ B → Mettapedia.GraphTheory.FourColor.Color)
    (hr : OpenTangleClosedWitness.IsColor outside r) :
    RotationSystemTaitColorable (outside.composeRotationSystem piece seam.symm) := by
  let c : PortTangle.Coloring (openExteriorTangle outside) := ⟨r, hr.1⟩
  have hc : IsProper c := ⟨hr.2.2, fun d e hv hn => hr.2.1 hv hn⟩
  let w := orderedProperBoundaryWord seam c hc
  have hw := orderedProperBoundaryWord_mem_orderedTaitSupport seam (openExteriorTangle outside) c hc
  have ht : PhysicalKempeBoundary.Trace
      (orderedTaitSupport seam (openExteriorTangle outside)) (PhysicalKempeBoundary.encode w) :=
    ⟨w, hw, rfl⟩
  obtain ⟨hlen, hzero, hsum⟩ := PhysicalKempeBoundary.trace_valid seam _ hcubic ht
  obtain ⟨k, r', hr', hm⟩ := open_compatible_darts outside seam
    (open_exterior_closed outside seam hcubic hnoncrossing) _ hlen hzero hsum
    ((openTrace_iff outside seam _).mp ht)
  obtain ⟨result, hresult, _⟩ := OpenTangleClosedWitness.glueOpen outside piece seam.symm
    r' (colouring k) hr' (colouring_valid k) (fun b => by
      simpa only [Equiv.apply_symm_apply] using (hm (seam.symm b)).symm)
  exact ⟨result, hresult⟩

/-- A tree colouring supplies the one exterior witness used by joint repair. -/
theorem open_reconstruct_from_tree
    (hcubic : IsCubic (openExteriorTangle outside))
    (hnoncrossing : ∀ (c : PortTangle.Coloring (openExteriorTangle outside)) (hc : IsProper c)
      (pair : TaitColorPair), IsNoncrossingMatching
        (orderedPhysicalMate seam (openExteriorTangle outside) hcubic c hc pair))
    (hc : RotationSystemTaitColorable (outside.composeRotationSystem Tree.piece seam.symm)) :
    RotationSystemTaitColorable (outside.composeRotationSystem piece seam.symm) := by
  obtain ⟨c, hc⟩ := hc
  obtain ⟨r, _, hr, _, _, _⟩ := OpenTangleClosedWitness.restrictOpen outside Tree.piece seam.symm c hc
  exact open_colorable_of_physical_noncrossing outside seam hcubic hnoncrossing r hr

end
end FourColor.PentagonalLobePatch.Tangle
