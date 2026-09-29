import MettapediaFourColor.PentagonalLobeTangle
import MettapediaFourColor.PhysicalKempeBoundary

/-!
# Pentagonal lobe repair against an actual exterior

The port-tangle and two-sided-tangle languages have identical boundary
observations and retain the same full colouring witnesses. Physical
noncrossing supplies reference Kempe closure, while cubic incidence supplies
the zero-sum input. Thus any proper exterior colouring can be repaired to
glue to the literal sixteen-vertex patch.

This result still needs geometric recognition and a valid smaller map to
supply that exterior colouring in a strict reduction argument.
-/

namespace FourColor.PentagonalLobePatch.Tangle

open Mettapedia.GraphTheory.FourColor
open GoertzelV24OpenTangleComposition SerialTangleSmallCutTransfer
open GoertzelV24PortTangleGluing GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24PortTangleCutParity
open GoertzelV24PhysicalKempeNoncrossingClosure
open GoertzelV24HexagonPairingTargetAwareBoundary

noncomputable section
universe u
variable {W J L R : Type u}
  (outside : TwoSidedOpenTangleData W J L R) (seam : Fin 6 ≃ L ⊕ R)

abbrev exteriorTangle := ofOpenTangleData (asOpen outside)

variable [Fintype W] [DecidableEq W] [Fintype J] [DecidableEq J]
  [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

private theorem palette_agrees (c : Color) : PhysicalKempeBoundary.palette c = palette c := by
  cases c <;> rfl

/-- Forgetting rotations and the left/right boundary split preserves precisely
the full exterior witnesses and their ordered six-port observation. -/
theorem physicalTrace_iff (et : List Color) :
    PhysicalKempeBoundary.Trace (orderedTaitSupport seam (exteriorTangle outside)) et ↔
      ExteriorTrace outside seam et := by
  constructor
  · rintro ⟨w, ⟨c, hc, he⟩, rfl⟩
    refine ⟨c.color, ⟨c.invariant, ?_, hc.1⟩, ?_⟩
    · intro d e hv hn
      exact hc.2 d e (by simpa [exteriorTangle, ofOpenTangleData, asOpen_vertOf] using hv) hn
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
    let c : PortTangle.Coloring (exteriorTangle outside) := ⟨r, hr.1⟩
    have hc : IsProper c := ⟨hr.2.2, fun d e hv hn =>
      hr.2.1 (by simpa [exteriorTangle, ofOpenTangleData, asOpen_vertOf] using hv) hn⟩
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
theorem exterior_closed
    (hcubic : IsCubic (exteriorTangle outside))
    (hnoncrossing : ∀ (c : PortTangle.Coloring (exteriorTangle outside)) (hc : IsProper c)
      (pair : TaitColorPair),
      IsNoncrossingMatching (orderedPhysicalMate seam (exteriorTangle outside)
        hcubic c hc pair)) :
    KempeClosed (ExteriorTrace outside seam) := by
  have h := PhysicalKempeBoundary.ordered_closed seam (exteriorTangle outside)
    hcubic hnoncrossing
  simpa only [KempeClosed, physicalTrace_iff] using h

/-- One genuine exterior colouring, cubicity and physical noncrossing now
suffice for a colouring of the whole sewn map. The exterior may be recoloured. -/
theorem sewn_colorable_of_physical_noncrossing
    (hcubic : IsCubic (exteriorTangle outside))
    (hnoncrossing : ∀ (c : PortTangle.Coloring (exteriorTangle outside)) (hc : IsProper c)
      (pair : TaitColorPair),
      IsNoncrossingMatching (orderedPhysicalMate seam (exteriorTangle outside)
        hcubic c hc pair))
    (r : outside.Coloring) (hr : outside.IsTaitColoring r) :
    ∃ c : (OpenTangleClosedWitness.sewn piece outside seam).EdgeColoring
        Mettapedia.GraphTheory.FourColor.Color,
      (OpenTangleClosedWitness.sewn piece outside seam).IsTaitEdgeColoring c := by
  let c : PortTangle.Coloring (exteriorTangle outside) := ⟨r, hr.1⟩
  have hc : IsProper c := ⟨hr.2.2, fun d e hv hn =>
    hr.2.1 (by simpa [exteriorTangle, ofOpenTangleData, asOpen_vertOf] using hv) hn⟩
  let w := orderedProperBoundaryWord seam c hc
  have hw := orderedProperBoundaryWord_mem_orderedTaitSupport seam _ c hc
  have ht : PhysicalKempeBoundary.Trace
      (orderedTaitSupport seam (exteriorTangle outside)) (PhysicalKempeBoundary.encode w) :=
    ⟨w, hw, rfl⟩
  obtain ⟨hlen, hzero, hsum⟩ := PhysicalKempeBoundary.trace_valid seam _ hcubic ht
  exact sewn_colorable outside seam (exterior_closed outside seam hcubic hnoncrossing)
    _ hlen hzero hsum ((physicalTrace_iff outside seam _).mp ht)

end

end FourColor.PentagonalLobePatch.Tangle
