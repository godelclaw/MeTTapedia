import Mathlib.Tactic.FinCases
import Mettapedia.GraphTheory.FourColor.Compositional.BoundaryKempeSwitch
import Mettapedia.GraphTheory.FourColor.GoertzelV24PhysicalKempeNoncrossing

/-!
# Physical matchings on a cyclic boundary

This file separates the arity-generic notion of crossing boundary chords from
the older six-port consumer.  It then proves the five-port instance needed by
the exact five-cut lane: the physical bichromatic mate of a spherical shore is
noncrossing in its facial cyclic coordinates.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace CyclicBoundaryMatching

open BoundaryKempeSwitch
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

/-- Two chords cross when their endpoints interleave in the displayed
linearization of a finite cyclic order.  The definition is independent of
the orientation chosen for either chord. -/
def ChordsCross {n : Nat}
    (first second third fourth : Fin n) : Prop :=
  let a := min first.1 second.1
  let b := max first.1 second.1
  let c := min third.1 fourth.1
  let d := max third.1 fourth.1
  (a < c ∧ c < b ∧ b < d) ∨ (c < a ∧ a < d ∧ d < b)

/-- No two chords of a mate interleave in the cyclic boundary order. -/
def IsNoncrossingMatching {n : Nat} (mate : Fin n → Fin n) : Prop :=
  ∀ first third, ¬ ChordsCross first (mate first) third (mate third)

universe u v

variable {V I P : Type u} {Q : Type v}
  [Fintype V] [Fintype I] [Fintype P] [Fintype Q]
  [DecidableEq V] [DecidableEq I] [DecidableEq P] [DecidableEq Q]

omit [Fintype Q] [DecidableEq Q] in
/-- The physical mate remains involutive in arbitrary boundary coordinates. -/
theorem physicalMateInCoordinates_involutive
    (order : Q ≃ P) (T : PortTangle V I P) (hcubic : IsCubic T)
    (coloring : Coloring T) (hproper : IsProper coloring)
    (pair : TaitColorPair) (coordinate : Q) :
    physicalMateInCoordinates order T hcubic coloring hproper pair
        (physicalMateInCoordinates order T hcubic coloring hproper pair
          coordinate) = coordinate := by
  apply order.injective
  simp [physicalMateInCoordinates,
    physicalMate_involutive T hcubic coloring hproper pair]

omit [Fintype Q] [DecidableEq Q] in
/-- Equality of mates in coordinates is equality of the corresponding
physical boundary ports. -/
theorem physicalMate_order_eq_of_coordinate_eq
    (order : Q ≃ P) (T : PortTangle V I P) (hcubic : IsCubic T)
    (coloring : Coloring T) (hproper : IsProper coloring)
    (pair : TaitColorPair) {first second : Q}
    (hmatch : physicalMateInCoordinates order T hcubic coloring hproper pair
      first = second) :
    physicalMate T hcubic coloring hproper pair (order first) = order second := by
  have htransport := congrArg order hmatch
  simpa [physicalMateInCoordinates] using htransport

/-! ## Five cyclic ports -/

private def leftArcBad (cut separator : Fin 5) (steps : Fin 5) :
    Finset (Fin 5) :=
  Finset.univ.filter fun index =>
    index < steps ∧
      let port := (finRotate 5)^[index.val] (finRotate 5 cut)
      port = cut ∨ port = separator

private def rightArcBad (cut separator right : Fin 5) (steps : Fin 5) :
    Finset (Fin 5) :=
  Finset.univ.filter fun index =>
    index < steps ∧
      let port := (finRotate 5)^[index.val] right
      port = cut ∨ port = separator

private def FiniteArcWitness
    (cut separator left right : Fin 5) : Prop :=
  ∃ leftSteps rightSteps : Fin 5,
    (finRotate 5)^[leftSteps.val] (finRotate 5 cut) = left ∧
    (finRotate 5)^[rightSteps.val] right = cut ∧
    leftArcBad cut separator leftSteps = ∅ ∧
    rightArcBad cut separator right rightSteps = ∅

private theorem finiteArcWitness_of_lt
    (cut left separator right : Fin 5)
    (hcutLeft : cut < left) (hleftSeparator : left < separator)
    (hseparatorRight : separator < right) :
    FiniteArcWitness cut separator left right := by
  fin_cases cut
  all_goals fin_cases left
  all_goals fin_cases separator
  all_goals fin_cases right
  all_goals simp_all only [Fin.mk_lt_mk]
  all_goals try omega
  all_goals unfold FiniteArcWitness
  all_goals decide

private def ArcWitness (cut separator left right : Fin 5) : Prop :=
  ∃ leftSteps rightSteps : Nat,
    (finRotate 5)^[leftSteps] (finRotate 5 cut) = left ∧
    (finRotate 5)^[rightSteps] right = cut ∧
    (∀ index, index < leftSteps →
      let port := (finRotate 5)^[index] (finRotate 5 cut)
      port ≠ cut ∧ port ≠ separator) ∧
    (∀ index, index < rightSteps →
      let port := (finRotate 5)^[index] right
      port ≠ cut ∧ port ≠ separator)

private theorem arcWitness_of_finite
    {cut separator left right : Fin 5}
    (h : FiniteArcWitness cut separator left right) :
    ArcWitness cut separator left right := by
  rcases h with ⟨leftSteps, rightSteps, hleft, hright, hleftAvoid,
    hrightAvoid⟩
  refine ⟨leftSteps.val, rightSteps.val, hleft, hright, ?_, ?_⟩
  · intro index hindex
    have hi : index < 5 := lt_trans hindex leftSteps.isLt
    have hnot : (⟨index, hi⟩ : Fin 5) ∉
        leftArcBad cut separator leftSteps := by
      rw [hleftAvoid]
      simp
    simp [leftArcBad] at hnot
    simpa [finRotate_apply] using hnot hindex
  · intro index hindex
    have hi : index < 5 := lt_trans hindex rightSteps.isLt
    have hnot : (⟨index, hi⟩ : Fin 5) ∉
        rightArcBad cut separator right rightSteps := by
      rw [hrightAvoid]
      simp
    simp [rightArcBad] at hnot
    exact hnot hindex

private theorem arcWitness_of_lt
    (cut left separator right : Fin 5)
    (hcutLeft : cut < left) (hleftSeparator : left < separator)
    (hseparatorRight : separator < right) :
    ArcWitness cut separator left right :=
  arcWitness_of_finite
    (finiteArcWitness_of_lt cut left separator right
      hcutLeft hleftSeparator hseparatorRight)

private theorem mate_min_eq_max
    (mate : Fin 5 → Fin 5) (hinvolutive : ∀ port, mate (mate port) = port)
    (port : Fin 5) :
    mate (min port (mate port)) = max port (mate port) := by
  by_cases hle : port ≤ mate port
  · rw [min_eq_left hle, max_eq_right hle]
  · have hge : mate port ≤ port := le_of_not_ge hle
    rw [min_eq_right hge, max_eq_left hge, hinvolutive]

private theorem exists_orientedArcWitness_of_chordsCross
    (mate : Fin 5 → Fin 5) (hinvolutive : ∀ port, mate (mate port) = port)
    {first third : Fin 5}
    (hcross : ChordsCross first (mate first) third (mate third)) :
    ∃ cut separator left right : Fin 5,
      mate cut = separator ∧ mate left = right ∧
      cut < left ∧ left < separator ∧ separator < right ∧
      ArcWitness cut separator left right := by
  unfold ChordsCross at hcross
  rcases hcross with hcross | hcross
  · refine ⟨min first (mate first), max first (mate first),
      min third (mate third), max third (mate third),
      mate_min_eq_max mate hinvolutive first,
      mate_min_eq_max mate hinvolutive third, ?_⟩
    have hcutLeft :
        min first (mate first) < min third (mate third) := hcross.1
    have hleftSeparator :
        min third (mate third) < max first (mate first) := hcross.2.1
    have hseparatorRight :
        max first (mate first) < max third (mate third) := hcross.2.2
    exact ⟨hcutLeft, hleftSeparator, hseparatorRight,
      arcWitness_of_lt _ _ _ _ hcutLeft hleftSeparator hseparatorRight⟩
  · refine ⟨min third (mate third), max third (mate third),
      min first (mate first), max first (mate first),
      mate_min_eq_max mate hinvolutive third,
      mate_min_eq_max mate hinvolutive first, ?_⟩
    have hcutLeft :
        min third (mate third) < min first (mate first) := hcross.1
    have hleftSeparator :
        min first (mate first) < max third (mate third) := hcross.2.1
    have hseparatorRight :
        max third (mate third) < max first (mate first) := hcross.2.2
    exact ⟨hcutLeft, hleftSeparator, hseparatorRight,
      arcWitness_of_lt _ _ _ _ hcutLeft hleftSeparator hseparatorRight⟩

section GraphBacked

variable {V₁ : Type*} [Fintype V₁] [DecidableEq V₁]
  {G : SimpleGraph V₁} [DecidableRel G.Adj]

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- A vertex-shore port tangle inherits cubicity from the ambient rotation
system. -/
theorem isCubic_vertexSidePortTangle
    (graphData : Data G) (keep : V₁ → Prop)
    (outer : RetainedDart graphData.toRotationSystem keep)
    (hcubic : graphData.toRotationSystem.IsCubic) :
    IsCubic (vertexSidePortTangle graphData keep outer) := by
  exact isCubic_ofOpenTangleData
    (ofVertexSide graphData.toRotationSystem keep outer)
    (openIsCubic_ofVertexSide graphData.toRotationSystem keep outer hcubic)

/-- On a spherical shore with a five-port cyclic facial boundary, the
literal physical bichromatic mate is noncrossing. -/
theorem physicalMateInCoordinates_isNoncrossing_five
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
    (order : Fin 5 ≃ BoundaryDart graphData.toRotationSystem keep)
    (hsuccessor : order.permCongr (finRotate 5) =
      retainedRegionBoundarySuccessor graphData.toRotationSystem keep)
    (outer : RetainedDart graphData.toRotationSystem keep)
    (coloring : Coloring (vertexSidePortTangle graphData keep outer))
    (hproper : IsProper coloring) (pair : TaitColorPair) :
    IsNoncrossingMatching
      (physicalMateInCoordinates order
        (vertexSidePortTangle graphData keep outer)
        (isCubic_vertexSidePortTangle graphData keep outer hcubic)
        coloring hproper pair) := by
  let T := vertexSidePortTangle graphData keep outer
  let hcubicT := isCubic_vertexSidePortTangle graphData keep outer hcubic
  let mate := physicalMateInCoordinates order T hcubicT coloring hproper pair
  let data : CyclicBondBoundaryData graphData.toRotationSystem keep :=
    { length := 5
      two_le_length := by omega
      order := order
      successor_eq := hsuccessor }
  intro first third hcross
  have hinvolutive : ∀ port, mate (mate port) = port := by
    intro port
    exact physicalMateInCoordinates_involutive
      order T hcubicT coloring hproper pair port
  rcases exists_orientedArcWitness_of_chordsCross mate hinvolutive hcross with
    ⟨cut, separator, left, right, hcutMate, hleftMate,
      hcutLeft, hleftSeparator, hseparatorRight, harcs⟩
  rcases harcs with
    ⟨leftSteps, rightSteps, hleftPort, hrightPort,
      hleftAvoid, hrightAvoid⟩
  have hphysicalCut :
      physicalMate T hcubicT coloring hproper pair (order cut) =
        order separator :=
    physicalMate_order_eq_of_coordinate_eq
      order T hcubicT coloring hproper pair hcutMate
  have hphysicalLeft :
      physicalMate T hcubicT coloring hproper pair (order left) =
        order right :=
    physicalMate_order_eq_of_coordinate_eq
      order T hcubicT coloring hproper pair hleftMate
  have hcutNeSeparator : cut ≠ separator :=
    ne_of_lt (hcutLeft.trans hleftSeparator)
  have hleftNeRight : left ≠ right :=
    ne_of_lt (hleftSeparator.trans hseparatorRight)
  have hcutActive : pairActiveDart coloring pair (Sum.inr (order cut)) := by
    by_contra hinactive
    have hself := physicalMate_eq_self_of_inactive
      T hcubicT coloring hproper pair (order cut) hinactive
    have horderEq : order cut = order separator :=
      hself.symm.trans hphysicalCut
    exact hcutNeSeparator (order.injective horderEq)
  have hleftActive : pairActiveDart coloring pair (Sum.inr (order left)) := by
    by_contra hinactive
    have hself := physicalMate_eq_self_of_inactive
      T hcubicT coloring hproper pair (order left) hinactive
    have horderEq : order left = order right :=
      hself.symm.trans hphysicalLeft
    exact hleftNeRight (order.injective horderEq)
  have hcutSpec :=
    (physicalMate_eq_iff_of_active T hcubicT coloring hproper pair
      (order cut) (order separator) hcutActive).1 hphysicalCut
  have hleftSpec :=
    (physicalMate_eq_iff_of_active T hcubicT coloring hproper pair
      (order left) (order right) hleftActive).1 hphysicalLeft
  have hdistinctComponents : ¬KempeConnected T coloring pair
      (Sum.inr (order cut)) (Sum.inr (order left)) := by
    intro hconnectedComponents
    have hcutToLeft :
        physicalMate T hcubicT coloring hproper pair (order cut) =
          order left :=
      (physicalMate_eq_iff_of_active T hcubicT coloring hproper pair
        (order cut) (order left) hcutActive).2
        ⟨order.injective.ne (ne_of_gt hcutLeft),
          hleftActive, hconnectedComponents⟩
    have hseparatorEqLeft : order separator = order left :=
      hphysicalCut.symm.trans hcutToLeft
    exact (ne_of_gt hleftSeparator)
      (order.injective hseparatorEqLeft)
  exact no_distinct_kempe_components_between_boundary_arcs
    graphData htwoSided hdual hconnected hsphere hcubic hrotation
    keep hcomplementConnected data outer coloring pair
    cut separator left right hcutNeSeparator hleftNeRight
    leftSteps rightSteps hleftPort hrightPort hleftAvoid hrightAvoid
    ⟨ne_of_gt hcutLeft, ne_of_lt hleftSeparator⟩
    ⟨ne_of_gt (hcutLeft.trans (hleftSeparator.trans hseparatorRight)),
      ne_of_gt hseparatorRight⟩
    hcutActive hcutSpec.2.1 hleftActive hleftSpec.2.1
    hcutSpec.2.2 hleftSpec.2.2 hdistinctComponents

end GraphBacked

end CyclicBoundaryMatching

end Mettapedia.GraphTheory.FourColor.Compositional
