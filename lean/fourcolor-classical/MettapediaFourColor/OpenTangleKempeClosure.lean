import MettapediaFourColor.OpenTangleKempeRepair
import Mettapedia.GraphTheory.FourColor.Compositional.CyclicBoundaryMatching

/-!
# Physical repair semantics at every boundary width

The exact observation of a cubic open tangle is reference Kempe-closed when
its physical bichromatic pairings are noncrossing. The same original pairing
reconstructs every chromogram answer by switching whole physical components.
No boundary-size enumeration is used by the matching translation.
-/

namespace FourColor.OpenTangleKempeRepair

open Mettapedia.GraphTheory.FourColor
open GoertzelV24OpenTangleComposition
open GoertzelV24PortTangleGluing GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24PortTangleCutParity GoertzelV24PortTanglePhysicalKempeClosure
open GoertzelV24PortTangleCommonKempeWeb GoertzelV24HexagonPairingTargetAwareBoundary
open Compositional.BoundaryKempeSwitch Compositional.CyclicBoundaryMatching
open PhysicalKempeBoundary (palette perm perm_zero decode_swap)

noncomputable section
universe u
variable {V I B : Type u} {n : ℕ}
  (T : OpenTangleData V I B) (order : Fin n ≃ B)

/-- The observation retains exactly a proper physical colouring and its
ordered boundary word, expressed in the reference palette. -/
theorem trace_iff_coloring {et : List Color} :
    Trace T order et ↔
      ∃ c : Coloring (ofOpenTangleData T), IsProper c ∧
        List.ofFn (fun i => palette.symm (c.color (.inr (order i)))) = et := by
  constructor
  · rintro ⟨r, hr, he⟩
    refine ⟨⟨r, hr.1⟩, ⟨hr.2.2, fun d e hv hn => hr.2.1 hv hn⟩, ?_⟩
    have hh := congrArg (List.map palette.symm) he
    simpa [List.map_map, Function.comp_def, List.ofFn_eq_map] using hh
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c.color, ⟨c.invariant, (fun hv hn => hc.2 _ _ hv hn), hc.1⟩, ?_⟩
    simp [List.ofFn_eq_map, List.map_map, Function.comp_def]

theorem trace_of_support
    (w : Fin n → {color : Mettapedia.GraphTheory.FourColor.Color // color ≠ 0})
    (hw : w ∈ supportInCoordinates order (ofOpenTangleData T)) :
    Trace T order (List.ofFn (fun i => palette.symm (w i).val)) := by
  obtain ⟨c, hc, he⟩ := hw
  apply (trace_iff_coloring T order).mpr
  refine ⟨c, hc, ?_⟩
  apply congrArg List.ofFn
  funext i
  exact congrArg palette.symm (by simpa [PortTangle.word] using congrFun he (order i))

variable [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
  [Fintype B] [DecidableEq B]

/-- Physical closure gives reference closure at arbitrary finite width.
The hypothesis concerns the actual components of each genuine colouring. -/
theorem closed_of_physical_noncrossing
    (hcubic : IsCubic (ofOpenTangleData T))
    (hnoncrossing : ∀ (c : Coloring (ofOpenTangleData T)) (hc : IsProper c),
      IsNoncrossingMatching (physicalMateInCoordinates order
        (ofOpenTangleData T) hcubic c hc .bluePurple)) :
    KempeClosed (Trace T order) := by
  classical
  intro et het
  obtain ⟨c, hc, rfl⟩ := (trace_iff_coloring T order).mp het
  let w : Fin n → Color := fun i => palette.symm (c.color (.inr (order i)))
  have hz : ∀ i, w i ≠ 0 := by
    intro i he
    apply hc.1 (.inr (order i))
    simpa [w] using congrArg palette he
  let mate := physicalMateInCoordinates order (ofOpenTangleData T) hcubic c hc .bluePurple
  have hinv : ∀ i, mate (mate i) = i :=
    physicalMateInCoordinates_involutive order (ofOpenTangleData T) hcubic c hc .bluePurple
  have hactive (i : Fin n) :
      pairActiveDart c .bluePurple (.inr (order i)) ↔ w i ≠ .c1 := by
    have he : c.color (.inr (order i)) = palette (w i) :=
      (palette.apply_symm_apply _).symm
    change (c.color (.inr (order i)) = blue ∨
      c.color (.inr (order i)) = purple) ↔ _
    rw [he]
    have hi := hz i
    cases hw : w i <;> simp_all [PhysicalKempeBoundary.palette, red, blue, purple]
  have hf : ∀ i, mate i = i ↔ w i = .c1 := by
    intro i
    constructor
    · intro he
      by_contra hn
      apply physicalMate_ne_of_active (ofOpenTangleData T) hcubic c hc
        .bluePurple (order i) ((hactive i).mpr hn)
      simpa [mate, physicalMateInCoordinates] using congrArg order he
    · intro he
      apply order.injective
      simpa [mate, physicalMateInCoordinates] using
        physicalMate_eq_self_of_inactive (ofOpenTangleData T) hcubic c hc
          .bluePurple (order i) (by rw [hactive, he]; simp)
  refine ⟨?_, ?_⟩
  · intro g
    apply (trace_iff_coloring T order).mpr
    refine ⟨relabelColoring _ (perm g) c,
      relabelColoring_isProper _ (perm g) (perm_zero g) c hc, ?_⟩
    simp [relabelColoring, PhysicalKempeBoundary.perm, List.map_ofFn, Function.comp_def]
  · obtain ⟨hg, hall⟩ := KempeMatchingChromogram.reconstruct mate w hinv
      (hnoncrossing c hc) hz hf
    refine ⟨KempeMatchingChromogram.gram mate w, hg, ?_⟩
    intro et' het'
    obtain ⟨selected, hu, he⟩ := hall et' het'
    have hs := switchBoundaryWord_mem_supportInCoordinates order (ofOpenTangleData T)
      hcubic c hc .bluePurple selected hu
    have ht := trace_of_support T order _ hs
    convert ht using 1
    rw [← he]
    apply congrArg List.ofFn
    funext i
    by_cases hi : i ∈ selected <;>
      simp [switchBoundaryWord, properBoundaryWordInCoordinates, properBoundaryWord,
        PortTangle.word, hi, TaitColorPair.colors, decode_swap, w]

end
end FourColor.OpenTangleKempeRepair
