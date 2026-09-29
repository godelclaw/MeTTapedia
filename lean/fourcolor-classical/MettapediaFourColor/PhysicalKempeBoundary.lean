import MettapediaFourColor.KempeMatchingReconstruction
import Mettapedia.GraphTheory.FourColor.GoertzelV24PhysicalKempeNoncrossingClosure

/-!
# Physical exterior supports are reference Kempe-closed

The colour identification and ordered boundary observation commute with global
relabelling and simultaneous switches of whole physical Kempe components.
The shared noncrossing component matching translates to a chromogram; every
chromogram answer reconstructs through that same matching.

This bridge transports existence and genuine colouring witnesses. It makes no
claim about the number of colourings or the length of a recolouring history.
-/

namespace FourColor.PhysicalKempeBoundary

open Mettapedia.GraphTheory.FourColor
open GoertzelV24HexagonPairingTargetAwareBoundary
open GoertzelV24PhysicalKempeNoncrossingClosure
open GoertzelV24PortTangleGluing GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24PortTangleCutParity GoertzelV24PortTanglePhysicalKempeClosure
open KempeMatchingChromogram (Ports)

/-- An exact identification of the reference and physical Klein palettes. -/
def palette : Color ≃ Mettapedia.GraphTheory.FourColor.Color where
  toFun
    | .c0 => 0
    | .c1 => red
    | .c2 => blue
    | .c3 => purple
  invFun c := if c = 0 then .c0 else if c = red then .c1
    else if c = blue then .c2 else .c3
  left_inv := by decide +kernel
  right_inv := by decide +kernel

@[simp] theorem palette_zero : palette 0 = 0 := rfl
@[simp] theorem palette_symm_zero : palette.symm 0 = 0 := rfl

def paletteAdd : Color ≃+ Mettapedia.GraphTheory.FourColor.Color where
  toEquiv := palette
  map_add' := by decide +kernel

def referenceWord (w : HexagonTaitWord) : Ports → Color :=
  fun i => palette.symm (w i).val

def encode (w : HexagonTaitWord) : List Color := List.ofFn (referenceWord w)

theorem referenceWord_ne_zero (w : HexagonTaitWord) (i : Ports) :
    referenceWord w i ≠ 0 := by
  intro h
  apply (w i).property
  have hp := congrArg palette h
  simpa [referenceWord] using hp

/-- The exact observed language; membership retains a complete physical word. -/
def Trace (support : Set HexagonTaitWord) (et : List Color) : Prop :=
  ∃ w ∈ support, encode w = et

def perm (g : EdgePerm) : Mettapedia.GraphTheory.FourColor.Color ≃
    Mettapedia.GraphTheory.FourColor.Color :=
  (palette.symm.trans g.toAddEquiv.toEquiv).trans palette

theorem perm_zero (g : EdgePerm) : perm g 0 = 0 := by
  simp [perm]

def permWord (g : EdgePerm) (w : HexagonTaitWord) : HexagonTaitWord :=
  relabelTaitWord (perm g) (perm_zero g) w

theorem encode_permWord (g : EdgePerm) (w : HexagonTaitWord) :
    encode (permWord g w) = (encode w).map g := by
  simp [encode, referenceWord, permWord, relabelTaitWord, perm]

private theorem decode_swap (c : Mettapedia.GraphTheory.FourColor.Color) :
    palette.symm (Mettapedia.GraphTheory.FourColor.Color.swap blue purple c) =
      EdgePerm.e132 (palette.symm c) := by
  obtain ⟨c, rfl⟩ := palette.surjective c
  cases c <;> decide +kernel

theorem encode_swap (w : HexagonTaitWord) (selected : Finset Ports) :
    encode (swapBoundaryWord w .bluePurple selected) =
      List.ofFn (fun i => if i ∈ selected then EdgePerm.e132 (referenceWord w i)
        else referenceWord w i) := by
  unfold encode
  apply congrArg List.ofFn
  funext i
  by_cases h : i ∈ selected <;>
    simp [referenceWord, swapBoundaryWord, h, TaitColorPair.colors, decode_swap]

private theorem active_iff (w : HexagonTaitWord) (i : Ports) :
    activePort w .bluePurple i ↔ referenceWord w i ≠ .c1 := by
  have hz := referenceWord_ne_zero w i
  have he : (w i).val = palette (referenceWord w i) := (palette.apply_symm_apply _).symm
  unfold activePort
  rw [he]
  cases hc : referenceWord w i <;>
    simp_all [TaitColorPair.colors, palette, red, blue, purple]

/-- Exact transport of physical component closure to the reference language.
All answers use the one matching supplied for the original physical word. -/
theorem closed (support : Set HexagonTaitWord)
    [DecidablePred (fun w => w ∈ support)]
    (hperm : ∀ g w, w ∈ support → permWord g w ∈ support)
    (hclosed : BoundaryKempeClosed support) : KempeClosed (Trace support) := by
  rintro et ⟨w, hw, rfl⟩
  refine ⟨?_, ?_⟩
  · intro g
    exact ⟨permWord g w, hperm g w hw, encode_permWord g w⟩
  · obtain ⟨mate, hm, hn, hs⟩ := hclosed w hw .bluePurple
    have hf : ∀ i, mate i = i ↔ referenceWord w i = .c1 := by
      intro i
      constructor
      · intro he
        by_contra hne
        exact (hm i).2.2.1 ((active_iff w i).mpr hne) he
      · intro he
        exact (hm i).2.2.2 (by rw [active_iff, he]; simp)
    obtain ⟨hg, hall⟩ := KempeMatchingChromogram.reconstruct mate (referenceWord w)
      (fun i => (hm i).2.1) hn (referenceWord_ne_zero w) hf
    refine ⟨KempeMatchingChromogram.gram mate (referenceWord w), hg, ?_⟩
    intro et' het'
    obtain ⟨selected, hu, he⟩ := hall et' het'
    exact ⟨swapBoundaryWord w .bluePurple selected, hs selected hu,
      (encode_swap w selected).trans he⟩

section PortTangle

universe u
variable {V I P : Type u} [Fintype V] [Fintype I] [Fintype P]
  [DecidableEq V] [DecidableEq I] [DecidableEq P]

omit [Fintype V] [Fintype I] [Fintype P] [DecidableEq V] [DecidableEq I] [DecidableEq P] in
theorem permWord_mem_orderedTaitSupport (order : Ports ≃ P) (T : PortTangle V I P)
    (g : EdgePerm) (w : HexagonTaitWord) (hw : w ∈ orderedTaitSupport order T) :
    permWord g w ∈ orderedTaitSupport order T := by
  obtain ⟨c, hc, he⟩ := hw
  refine ⟨relabelColoring T (perm g) c,
    relabelColoring_isProper T (perm g) (perm_zero g) c hc, ?_⟩
  funext p
  have hp := congrFun he p
  change perm g (c.color (.inr p)) = perm g (w (order.symm p)).val
  exact congrArg (perm g) hp

/-- A consumer on actual cubic tangles: physical noncrossing, together with
proved physical switching and palette invariance, discharges reference closure. -/
theorem ordered_closed (order : Ports ≃ P) (T : PortTangle V I P)
    (hcubic : IsCubic T)
    (hnoncrossing : ∀ (c : Coloring T) (hc : IsProper c) (pair : TaitColorPair),
      IsNoncrossingMatching (orderedPhysicalMate order T hcubic c hc pair)) :
    KempeClosed (Trace (orderedTaitSupport order T)) := by
  classical
  exact closed _ (permWord_mem_orderedTaitSupport order T)
    (boundaryKempeClosed_orderedTaitSupport_of_physical_noncrossing
      order T hcubic hnoncrossing)

/-- Every observed exterior word has exactly the proper zero-sum form consumed
by boundary repair. The sum is derived from the actual cubic incidence law. -/
theorem trace_valid (order : Ports ≃ P) (T : PortTangle V I P) (hcubic : IsCubic T)
    {et : List Color} (het : Trace (orderedTaitSupport order T) et) :
    et.length = 6 ∧ (0 : Color) ∉ et ∧ et.sum = 0 := by
  obtain ⟨w, hw, rfl⟩ := het
  refine ⟨by simp [encode], ?_, ?_⟩
  · intro hz
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hz
    exact referenceWord_ne_zero w i hi
  · have hsum := taitSupport_subset_zeroSum T hcubic hw
    have hwSum : (∑ i : Ports, (w i).val) = 0 := by
      have he := order.sum_comp (fun p => (w (order.symm p)).val)
      simpa only [Equiv.symm_apply_apply] using he.trans hsum
    apply palette.injective
    change paletteAdd ((encode w).sum) = paletteAdd 0
    rw [map_list_sum]
    change ((List.ofFn (referenceWord w)).map palette).sum = 0
    rw [List.map_ofFn, List.sum_ofFn]
    simpa only [Function.comp_apply, referenceWord, Equiv.apply_symm_apply] using hwSum

end PortTangle

section Embedded

open SimpleGraphDartRotation GoertzelV24OrbitFaceTwoSided
open GoertzelV24FaceDualConnectedness GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceCurvatureBulk GoertzelV24RotationCutDartDecomposition
open GoertzelV24VertexSidePrimalKempeTrail GoertzelV24VertexSideOpenTangle

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- An embedded consumer: the existing spherical separator theorem supplies
physical noncrossing on a six-port cyclic bond boundary. -/
theorem vertexSide_closed
    (graphData : Data G)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hdual : (interiorDualGraph (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (keep : V → Prop)
    (hcomplementConnected : (G.induce {v | ¬keep v}).Connected)
    (data : SixPortCyclicBondBoundaryData graphData.toRotationSystem keep)
    (outer : RetainedDart graphData.toRotationSystem keep) :
    KempeClosed (Trace (orderedTaitSupport data.order
      (vertexSidePortTangle graphData keep outer))) := by
  classical
  exact closed _ (permWord_mem_orderedTaitSupport data.order _)
    (boundaryKempeClosed_orderedVertexSideTaitSupport graphData htwoSided hdual
      hconnected hsphere hcubic hrotation keep hcomplementConnected data outer)

end Embedded

end FourColor.PhysicalKempeBoundary
