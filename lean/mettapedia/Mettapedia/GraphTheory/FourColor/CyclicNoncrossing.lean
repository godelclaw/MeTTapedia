import Mettapedia.GraphTheory.FourColor.Compositional.CyclicBoundaryMatching
import Mettapedia.GraphTheory.FourColor.KempeDerivation

/-!
# Physical noncrossing at any arity, and physically sound derivations on vertex sides

The five-port instance of "the physical bichromatic mate of a spherical shore
is noncrossing in its facial cyclic coordinates" used a brute-forced arc
witness.  Here the arc witness is arithmetic, so the theorem holds at every
cyclic length `n ≥ 2` (`physicalMateInCoordinates_isNoncrossing`).  Combined
with `KempeDerivation.exists_mem_target_of_derivable`, a derivable boundary
word of a vertex side's exact support yields a target word of that support
(`exists_mem_target_of_derivable_vertexSide`).
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional
namespace CyclicNoncrossing

open BoundaryKempeSwitch CyclicBoundaryMatching
open Equiv Equiv.Perm
open GoertzelV24CyclicBondBoundary
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexagonPairingTargetAwareBoundary
open GoertzelV24OpenTangleComposition
open GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24PhysicalKempeNoncrossing
open GoertzelV24PortTangleCommonKempeWeb
open GoertzelV24PortTangleCutParity
open GoertzelV24PortTangleGluing
open GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24PortTanglePhysicalKempeClosure
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24VertexSideOpenTangle
open GoertzelV24VertexSidePrimalKempeTrail
open SimpleGraph
open SimpleGraphDartRotation

/-! ## Arithmetic of the cyclic rotation -/

theorem val_iterate_finRotate (m : Nat) :
    ∀ (j : Nat) (x : Fin (m + 1)), ((finRotate (m + 1))^[j] x).val = (x.val + j) % (m + 1)
  | 0, x => by simp [Nat.mod_eq_of_lt x.isLt]
  | j + 1, x => by
    rw [Function.iterate_succ_apply', finRotate_apply, Fin.val_add, Fin.val_one',
      val_iterate_finRotate m j x, ← Nat.add_assoc, Nat.add_mod (x.val + j) 1]

/-- the two boundary arcs between a chord's endpoints, with their steps -/
def ArcWitness {n : Nat} (cut separator left right : Fin n) : Prop :=
  ∃ leftSteps rightSteps : Nat,
    (finRotate n)^[leftSteps] (finRotate n cut) = left ∧
    (finRotate n)^[rightSteps] right = cut ∧
    (∀ index, index < leftSteps →
      let port := (finRotate n)^[index] (finRotate n cut)
      port ≠ cut ∧ port ≠ separator) ∧
    (∀ index, index < rightSteps →
      let port := (finRotate n)^[index] right
      port ≠ cut ∧ port ≠ separator)

theorem arcWitness_of_lt {m : Nat} (cut left separator right : Fin (m + 1))
    (hcutLeft : cut < left) (hleftSeparator : left < separator)
    (hseparatorRight : separator < right) :
    ArcWitness cut separator left right := by
  have h1 : cut.val < left.val := hcutLeft
  have h2 : left.val < separator.val := hleftSeparator
  have h3 : separator.val < right.val := hseparatorRight
  have hr := right.isLt
  have e1 : 1 % (m + 1) = 1 := Nat.mod_eq_of_lt (by omega)
  have e2 : (cut.val + 1) % (m + 1) = cut.val + 1 := Nat.mod_eq_of_lt (by omega)
  have hleftVal : ∀ index, index ≤ left.val - cut.val - 1 →
      ((finRotate (m + 1))^[index] (finRotate (m + 1) cut)).val = cut.val + 1 + index := by
    intro index hindex
    rw [val_iterate_finRotate, finRotate_apply, Fin.val_add, Fin.val_one', e1, e2]
    exact Nat.mod_eq_of_lt (by omega)
  have hrightVal : ∀ index, ((finRotate (m + 1))^[index] right).val = (right.val + index) % (m + 1) :=
    fun index => val_iterate_finRotate m index right
  refine ⟨left.val - cut.val - 1, (m + 1) - right.val + cut.val, ?_, ?_, ?_, ?_⟩
  · apply Fin.ext
    rw [hleftVal _ le_rfl]; omega
  · apply Fin.ext
    rw [hrightVal, show right.val + ((m + 1) - right.val + cut.val) = (m + 1) + cut.val by omega,
      Nat.add_mod_left]
    exact Nat.mod_eq_of_lt cut.isLt
  · intro index hindex
    have hv := hleftVal index (by omega)
    exact ⟨fun h => by have := congrArg Fin.val h; rw [hv] at this; omega,
      fun h => by have := congrArg Fin.val h; rw [hv] at this; omega⟩
  · intro index hindex
    have hv := hrightVal index
    by_cases hsmall : index < (m + 1) - right.val
    · rw [Nat.mod_eq_of_lt (by omega)] at hv
      exact ⟨fun h => by have := congrArg Fin.val h; rw [hv] at this; omega,
        fun h => by have := congrArg Fin.val h; rw [hv] at this; omega⟩
    · rw [show right.val + index = (m + 1) + (index - ((m + 1) - right.val)) by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hv
      exact ⟨fun h => by have := congrArg Fin.val h; rw [hv] at this; omega,
        fun h => by have := congrArg Fin.val h; rw [hv] at this; omega⟩

theorem mate_min_eq_max {n : Nat} (mate : Fin n → Fin n)
    (hinvolutive : ∀ port, mate (mate port) = port) (port : Fin n) :
    mate (min port (mate port)) = max port (mate port) := by
  by_cases hle : port ≤ mate port
  · rw [min_eq_left hle, max_eq_right hle]
  · have hge : mate port ≤ port := le_of_not_ge hle
    rw [min_eq_right hge, max_eq_left hge, hinvolutive]

theorem exists_orientedArcWitness_of_chordsCross {m : Nat} (mate : Fin (m + 1) → Fin (m + 1))
    (hinvolutive : ∀ port, mate (mate port) = port) {first third : Fin (m + 1)}
    (hcross : ChordsCross first (mate first) third (mate third)) :
    ∃ cut separator left right : Fin (m + 1),
      mate cut = separator ∧ mate left = right ∧
      cut < left ∧ left < separator ∧ separator < right ∧
      ArcWitness cut separator left right := by
  unfold CyclicBoundaryMatching.ChordsCross at hcross
  rcases hcross with hcross | hcross
  · refine ⟨min first (mate first), max first (mate first),
      min third (mate third), max third (mate third),
      mate_min_eq_max mate hinvolutive first, mate_min_eq_max mate hinvolutive third, ?_⟩
    have hcutLeft : min first (mate first) < min third (mate third) := hcross.1
    have hleftSeparator : min third (mate third) < max first (mate first) := hcross.2.1
    have hseparatorRight : max first (mate first) < max third (mate third) := hcross.2.2
    exact ⟨hcutLeft, hleftSeparator, hseparatorRight,
      arcWitness_of_lt _ _ _ _ hcutLeft hleftSeparator hseparatorRight⟩
  · refine ⟨min third (mate third), max third (mate third),
      min first (mate first), max first (mate first),
      mate_min_eq_max mate hinvolutive third, mate_min_eq_max mate hinvolutive first, ?_⟩
    have hcutLeft : min third (mate third) < min first (mate first) := hcross.1
    have hleftSeparator : min first (mate first) < max third (mate third) := hcross.2.1
    have hseparatorRight : max third (mate third) < max first (mate first) := hcross.2.2
    exact ⟨hcutLeft, hleftSeparator, hseparatorRight,
      arcWitness_of_lt _ _ _ _ hcutLeft hleftSeparator hseparatorRight⟩

/-! ## Spherical shores -/

section GraphBacked

variable {V₁ : Type*} [Fintype V₁] [DecidableEq V₁]
  {G : SimpleGraph V₁} [DecidableRel G.Adj]

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- **On a spherical shore with a cyclic facial boundary of any length, the literal physical
bichromatic mate is noncrossing.** -/
theorem physicalMateInCoordinates_isNoncrossing
    (graphData : Data G)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (keep : V₁ → Prop)
    (hcomplementConnected : (G.induce {vertex | ¬keep vertex}).Connected)
    {n : Nat} (hn : 2 ≤ n)
    (order : Fin n ≃ BoundaryDart graphData.toRotationSystem keep)
    (hsuccessor : order.permCongr (finRotate n) =
      retainedRegionBoundarySuccessor graphData.toRotationSystem keep)
    (outer : RetainedDart graphData.toRotationSystem keep)
    (coloring : Coloring (vertexSidePortTangle graphData keep outer))
    (hproper : IsProper coloring) (pair : TaitColorPair) :
    IsNoncrossingMatching
      (physicalMateInCoordinates order
        (vertexSidePortTangle graphData keep outer)
        (isCubic_vertexSidePortTangle graphData keep outer hcubic)
        coloring hproper pair) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  let T := vertexSidePortTangle graphData keep outer
  let hcubicT := isCubic_vertexSidePortTangle graphData keep outer hcubic
  let mate := physicalMateInCoordinates order T hcubicT coloring hproper pair
  let data : CyclicBondBoundaryData graphData.toRotationSystem keep :=
    { length := m + 1
      two_le_length := hn
      order := order
      successor_eq := hsuccessor }
  intro first third hcross
  have hinvolutive : ∀ port, mate (mate port) = port := fun port =>
    physicalMateInCoordinates_involutive order T hcubicT coloring hproper pair port
  rcases exists_orientedArcWitness_of_chordsCross mate hinvolutive hcross with
    ⟨cut, separator, left, right, hcutMate, hleftMate,
      hcutLeft, hleftSeparator, hseparatorRight, harcs⟩
  rcases harcs with ⟨leftSteps, rightSteps, hleftPort, hrightPort, hleftAvoid, hrightAvoid⟩
  have hphysicalCut : physicalMate T hcubicT coloring hproper pair (order cut) = order separator :=
    physicalMate_order_eq_of_coordinate_eq order T hcubicT coloring hproper pair hcutMate
  have hphysicalLeft : physicalMate T hcubicT coloring hproper pair (order left) = order right :=
    physicalMate_order_eq_of_coordinate_eq order T hcubicT coloring hproper pair hleftMate
  have hcutNeSeparator : cut ≠ separator := ne_of_lt (hcutLeft.trans hleftSeparator)
  have hleftNeRight : left ≠ right := ne_of_lt (hleftSeparator.trans hseparatorRight)
  have hcutActive : pairActiveDart coloring pair (Sum.inr (order cut)) := by
    by_contra hinactive
    have hself := physicalMate_eq_self_of_inactive T hcubicT coloring hproper pair (order cut)
      hinactive
    exact hcutNeSeparator (order.injective (hself.symm.trans hphysicalCut))
  have hleftActive : pairActiveDart coloring pair (Sum.inr (order left)) := by
    by_contra hinactive
    have hself := physicalMate_eq_self_of_inactive T hcubicT coloring hproper pair (order left)
      hinactive
    exact hleftNeRight (order.injective (hself.symm.trans hphysicalLeft))
  have hcutSpec := (physicalMate_eq_iff_of_active T hcubicT coloring hproper pair
    (order cut) (order separator) hcutActive).1 hphysicalCut
  have hleftSpec := (physicalMate_eq_iff_of_active T hcubicT coloring hproper pair
    (order left) (order right) hleftActive).1 hphysicalLeft
  have hdistinctComponents : ¬KempeConnected T coloring pair
      (Sum.inr (order cut)) (Sum.inr (order left)) := by
    intro hconnectedComponents
    have hcutToLeft : physicalMate T hcubicT coloring hproper pair (order cut) = order left :=
      (physicalMate_eq_iff_of_active T hcubicT coloring hproper pair
        (order cut) (order left) hcutActive).2
        ⟨order.injective.ne (ne_of_gt hcutLeft), hleftActive, hconnectedComponents⟩
    exact (ne_of_gt hleftSeparator) (order.injective (hphysicalCut.symm.trans hcutToLeft))
  exact no_distinct_kempe_components_between_boundary_arcs
    graphData htwoSided hdual hconnected hsphere hcubic hrotation
    keep hcomplementConnected data outer coloring pair
    cut separator left right hcutNeSeparator hleftNeRight
    leftSteps rightSteps hleftPort hrightPort hleftAvoid hrightAvoid
    ⟨ne_of_gt hcutLeft, ne_of_lt hleftSeparator⟩
    ⟨ne_of_gt (hcutLeft.trans (hleftSeparator.trans hseparatorRight)), ne_of_gt hseparatorRight⟩
    hcutActive hcutSpec.2.1 hleftActive hleftSpec.2.1
    hcutSpec.2.2 hleftSpec.2.2 hdistinctComponents

open KempeDerivation in
/-- **physically sound derivations on a spherical vertex side**: a derivable word of the
side's exact support, in facial cyclic coordinates, yields a target word of that support -/
theorem exists_mem_target_of_derivable_vertexSide
    (graphData : Data G)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (keep : V₁ → Prop)
    (hcomplementConnected : (G.induce {vertex | ¬keep vertex}).Connected)
    {n : Nat} (hn : 2 ≤ n)
    (order : Fin n ≃ BoundaryDart graphData.toRotationSystem keep)
    (hsuccessor : order.permCongr (finRotate n) =
      retainedRegionBoundarySuccessor graphData.toRotationSystem keep)
    (outer : RetainedDart graphData.toRotationSystem keep)
    {target : Set (Word n)} {w : Word n} (hd : Derivable target w)
    (hw : w ∈ supportInCoordinates order (vertexSidePortTangle graphData keep outer)) :
    ∃ w' ∈ target, w' ∈ supportInCoordinates order (vertexSidePortTangle graphData keep outer) :=
  exists_mem_target_of_derivable order (vertexSidePortTangle graphData keep outer)
    (isCubic_vertexSidePortTangle graphData keep outer hcubic)
    (fun coloring hproper pair => physicalMateInCoordinates_isNoncrossing graphData htwoSided
      hdual hconnected hsphere hcubic hrotation keep hcomplementConnected hn order hsuccessor
      outer coloring hproper pair)
    hd hw

end GraphBacked

end CyclicNoncrossing
end Mettapedia.GraphTheory.FourColor.Compositional
