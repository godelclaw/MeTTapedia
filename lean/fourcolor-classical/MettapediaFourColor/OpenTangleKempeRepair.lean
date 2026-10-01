import MettapediaFourColor.PhysicalKempeBoundary
import MettapediaFourColor.KempeBoundarySplit
import Mettapedia.GraphTheory.FourColor.OpenTangleClosedWitness
import Mettapedia.GraphTheory.FourColor.OpenTangleIsomorphismColoring

/-!
# Repair at an arbitrary ordered open boundary

The observation retains a whole interior colouring and its complete boundary
word. Abstract repair selects compatible words; their genuine witnesses then
glue. Boundary width is a parameter. Physical Kempe closure is an explicit
obligation, rather than a consequence of the observation's definition.
-/

namespace FourColor.OpenTangleKempeRepair

open Mettapedia.GraphTheory.FourColor
open GoertzelV24OpenTangleComposition GoertzelV24TwoEdgeCutMinimality
open GoertzelV24PortTangleGluing GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24PortTangleCutParity GoertzelV24PortTanglePhysicalKempeClosure
open GoertzelV24PortTangleCommonKempeWeb
open PhysicalKempeBoundary (palette paletteAdd)

noncomputable section
universe u
variable {V I B : Type*} {W J C : Type u}
  {n : ℕ}

/-- Exact ordered observation, with the realizing colour assignment retained. -/
def Trace (T : OpenTangleData V I B) (order : Fin n ≃ B) (et : List Color) : Prop :=
  ∃ c : I ⊕ B → Mettapedia.GraphTheory.FourColor.Color,
    OpenTangleClosedWitness.IsColor T c ∧
      (List.finRange n).map (fun i => c (.inr (order i))) = et.map palette

/-- Exact representation transport retains the same whole boundary word. -/
theorem trace_transport {P : OpenTangleData V I B} {Q : OpenTangleData W J C}
    (e : OpenTangleIsomorphism.Iso P Q) (order : Fin n ≃ B) {et : List Color}
    (h : Trace P order et) : Trace Q (order.trans e.boundary) et := by
  obtain ⟨c, hc, he⟩ := h
  refine ⟨e.mapColor c, e.mapColor_valid hc, ?_⟩
  simpa only [Equiv.trans_apply, e.mapColor_boundary] using he

variable [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
  [Fintype B] [DecidableEq B] [Fintype W] [DecidableEq W]
  [Fintype J] [DecidableEq J] [Fintype C] [DecidableEq C]

variable (piece : OpenTangleData V I (Fin n)) (outside : OpenTangleData W J C)
  (seam : Fin n ≃ C)

/-- A closed observation need only read back to genuine exterior witnesses.
It need not describe every exterior colouring. The final two assignments
agree on all ports at once, and the selected exterior may be recoloured. -/
theorem glue_of_closed_observation
    (hrepair : KempeBoundarySplit.Repairs (Trace piece (Equiv.refl _)) n)
    (E : List Color → Prop) (hclosed : KempeClosed E)
    (hread : ∀ et, E et → Trace outside seam et)
    (et : List Color) (hlen : et.length = n) (hzero : (0 : Color) ∉ et)
    (hsum : et.sum = 0) (hold : E et) :
    RotationSystemTaitColorable (outside.composeRotationSystem piece seam.symm) := by
  obtain ⟨es, ⟨l, hl, hel⟩, hes⟩ := hrepair et hlen hzero hsum E hclosed hold
  obtain ⟨r, hr, her⟩ := hread es hes
  have hm (i : Fin n) : l (.inr i) = r (.inr (seam i)) :=
    List.map_inj_left.mp (hel.trans her.symm) i (List.mem_finRange i)
  obtain ⟨result, hresult, _⟩ := OpenTangleClosedWitness.glueOpen outside piece seam.symm
    r l hr hl (fun b => by simpa only [Equiv.apply_symm_apply] using (hm (seam.symm b)).symm)
  exact ⟨result, hresult⟩

/-- Specialize the observation to the complete physical exterior trace. -/
theorem glue_of_repair
    (hrepair : KempeBoundarySplit.Repairs (Trace piece (Equiv.refl _)) n)
    (hclosed : KempeClosed (Trace outside seam))
    (et : List Color) (hlen : et.length = n) (hzero : (0 : Color) ∉ et)
    (hsum : et.sum = 0) (hold : Trace outside seam et) :
    RotationSystemTaitColorable (outside.composeRotationSystem piece seam.symm) :=
  glue_of_closed_observation piece outside seam hrepair (Trace outside seam)
    hclosed (fun _ h => h) et hlen hzero hsum hold

omit [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B] in
/-- Actual cubic colourings supply proper zero-sum words at any width. -/
theorem trace_valid
    (hcubic : IsCubic (ofOpenTangleData outside))
    {et : List Color} (h : Trace outside seam et) :
    et.length = n ∧ (0 : Color) ∉ et ∧ et.sum = 0 := by
  obtain ⟨r, hr, he⟩ := h
  have hlen := congrArg List.length he
  simp only [List.length_map, List.length_finRange] at hlen
  refine ⟨hlen.symm, ?_, ?_⟩
  · intro hz
    have hm : (0 : Mettapedia.GraphTheory.FourColor.Color) ∈ et.map palette :=
      List.mem_map.mpr ⟨0, hz, rfl⟩
    rw [← he] at hm
    obtain ⟨i, _, hi⟩ := List.mem_map.mp hm
    exact hr.2.2 _ hi
  · let c : PortTangle.Coloring (ofOpenTangleData outside) := ⟨r, hr.1⟩
    have hc : IsProper c := ⟨hr.2.2, fun d e hv hn => hr.2.1 hv hn⟩
    have hs := taitSupport_subset_zeroSum (ofOpenTangleData outside) hcubic
      (properBoundaryWord_mem_taitSupport _ c hc)
    have hs' : (∑ i : Fin n, r (.inr (seam i))) = 0 := by
      exact (seam.sum_comp (fun b => r (.inr b))).trans hs
    apply palette.injective
    change paletteAdd et.sum = paletteAdd 0
    rw [map_list_sum]
    change (et.map palette).sum = 0
    rw [← he, ← List.ofFn_eq_map, List.sum_ofFn]
    exact hs'

/-- A genuine exterior colouring is enough once its physical closure and
the interior's repair law have been proved. -/
theorem colorable_of_exterior
    (hrepair : KempeBoundarySplit.Repairs (Trace piece (Equiv.refl _)) n)
    (hcubic : IsCubic (ofOpenTangleData outside))
    (hclosed : KempeClosed (Trace outside seam))
    (r : J ⊕ C → Mettapedia.GraphTheory.FourColor.Color)
    (hr : OpenTangleClosedWitness.IsColor outside r) :
    RotationSystemTaitColorable (outside.composeRotationSystem piece seam.symm) := by
  let et : List Color := (List.finRange n).map (fun i => palette.symm (r (.inr (seam i))))
  have ht : Trace outside seam et := ⟨r, hr, by simp [et, List.map_map]⟩
  obtain ⟨hlen, hzero, hsum⟩ := trace_valid outside seam hcubic ht
  exact glue_of_repair piece outside seam hrepair hclosed et hlen hzero hsum ht

end
end FourColor.OpenTangleKempeRepair
