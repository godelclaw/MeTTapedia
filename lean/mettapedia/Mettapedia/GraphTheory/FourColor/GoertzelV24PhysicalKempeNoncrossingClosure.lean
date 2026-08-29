import Mettapedia.GraphTheory.FourColor.GoertzelV24PhysicalKempeNoncrossing
import Mettapedia.GraphTheory.FourColor.GoertzelV24PortTanglePhysicalKempeClosure
import Mathlib.Tactic.FinCases

/-!
# Six-port closure of physical Kempe noncrossing

The graph-backed separator theorem proves that two distinct physical
bichromatic components cannot have alternating endpoints on one cyclic bond
boundary.  This file turns that cyclic-arc statement into the literal
six-port `IsNoncrossingMatching` predicate used by the finite boundary audit.

The matching is not supplied independently.  It is the physical mate obtained
from the common bichromatic dart web of one proper colouring.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24PhysicalKempeNoncrossingClosure

open Equiv Equiv.Perm
open SimpleGraph
open SimpleGraphDartRotation
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

noncomputable section

/-! ## Finite cyclic-arc witnesses -/

private def leftArcBad (cut separator : Fin 6) (steps : Fin 6) :
    Finset (Fin 6) :=
  Finset.univ.filter fun index =>
    index < steps ∧
      let port := (finRotate 6)^[index.val] (finRotate 6 cut)
      port = cut ∨ port = separator

private def rightArcBad (cut separator right : Fin 6) (steps : Fin 6) :
    Finset (Fin 6) :=
  Finset.univ.filter fun index =>
    index < steps ∧
      let port := (finRotate 6)^[index.val] right
      port = cut ∨ port = separator

private def FiniteArcWitness
    (cut separator left right : Fin 6) : Prop :=
  ∃ leftSteps rightSteps : Fin 6,
    (finRotate 6)^[leftSteps.val] (finRotate 6 cut) = left ∧
    (finRotate 6)^[rightSteps.val] right = cut ∧
    leftArcBad cut separator leftSteps = ∅ ∧
    rightArcBad cut separator right rightSteps = ∅

private theorem finiteArcWitness_of_lt
    (cut left separator right : Fin 6)
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

private def ArcWitness (cut separator left right : Fin 6) : Prop :=
  ∃ leftSteps rightSteps : Nat,
    (finRotate 6)^[leftSteps] (finRotate 6 cut) = left ∧
    (finRotate 6)^[rightSteps] right = cut ∧
    (∀ index, index < leftSteps →
      let port := (finRotate 6)^[index] (finRotate 6 cut)
      port ≠ cut ∧ port ≠ separator) ∧
    (∀ index, index < rightSteps →
      let port := (finRotate 6)^[index] right
      port ≠ cut ∧ port ≠ separator)

private theorem arcWitness_of_finite
    {cut separator left right : Fin 6}
    (h : FiniteArcWitness cut separator left right) :
    ArcWitness cut separator left right := by
  rcases h with ⟨leftSteps, rightSteps, hleft, hright, hleftAvoid,
    hrightAvoid⟩
  refine ⟨leftSteps.val, rightSteps.val, hleft, hright, ?_, ?_⟩
  · intro index hindex
    have hi : index < 6 := lt_trans hindex leftSteps.isLt
    have hnot : (⟨index, hi⟩ : Fin 6) ∉
        leftArcBad cut separator leftSteps := by
      rw [hleftAvoid]
      simp
    simp [leftArcBad] at hnot
    simpa [finRotate_apply] using hnot hindex
  · intro index hindex
    have hi : index < 6 := lt_trans hindex rightSteps.isLt
    have hnot : (⟨index, hi⟩ : Fin 6) ∉
        rightArcBad cut separator right rightSteps := by
      rw [hrightAvoid]
      simp
    simp [rightArcBad] at hnot
    exact hnot hindex

private theorem arcWitness_of_lt
    (cut left separator right : Fin 6)
    (hcutLeft : cut < left) (hleftSeparator : left < separator)
    (hseparatorRight : separator < right) :
    ArcWitness cut separator left right :=
  arcWitness_of_finite
    (finiteArcWitness_of_lt cut left separator right
      hcutLeft hleftSeparator hseparatorRight)

/-! ## Six cyclic ports and the physical matching in those coordinates -/

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- A cyclic bond boundary whose cardinality is literally six. -/
structure SixPortCyclicBondBoundaryData
    (RS : RotationSystem V E) (keep : V → Prop) where
  order : Fin 6 ≃ BoundaryDart RS keep
  successor_eq :
    order.permCongr (finRotate 6) =
      retainedRegionBoundarySuccessor RS keep

namespace SixPortCyclicBondBoundaryData

variable {RS : RotationSystem V E} {keep : V → Prop}

/-- Forget that the cyclic boundary length was definitionally six. -/
def toCyclicBondBoundaryData
    (data : SixPortCyclicBondBoundaryData RS keep) :
    CyclicBondBoundaryData RS keep where
  length := 6
  two_le_length := by omega
  order := data.order
  successor_eq := data.successor_eq

end SixPortCyclicBondBoundaryData

universe u

variable {V₀ I₀ P₀ : Type u}
  [Fintype V₀] [Fintype I₀] [Fintype P₀]
  [DecidableEq V₀] [DecidableEq I₀] [DecidableEq P₀]

/-- Read the physical common-web mate in fixed six-port cyclic coordinates. -/
noncomputable def orderedPhysicalMate
    (order : Fin 6 ≃ P₀) (T : PortTangle V₀ I₀ P₀)
    (hcubic : IsCubic T) (coloring : Coloring T)
    (hproper : IsProper coloring) (pair : TaitColorPair) : Fin 6 → Fin 6 :=
  fun port => order.symm
    (physicalMate T hcubic coloring hproper pair (order port))

theorem orderedPhysicalMate_involutive
    (order : Fin 6 ≃ P₀) (T : PortTangle V₀ I₀ P₀)
    (hcubic : IsCubic T) (coloring : Coloring T)
    (hproper : IsProper coloring) (pair : TaitColorPair)
    (port : Fin 6) :
    orderedPhysicalMate order T hcubic coloring hproper pair
        (orderedPhysicalMate order T hcubic coloring hproper pair port) = port := by
  apply order.injective
  simp [orderedPhysicalMate,
    physicalMate_involutive T hcubic coloring hproper pair]

theorem physicalMate_order_eq_of_orderedPhysicalMate_eq
    (order : Fin 6 ≃ P₀) (T : PortTangle V₀ I₀ P₀)
    (hcubic : IsCubic T) (coloring : Coloring T)
    (hproper : IsProper coloring) (pair : TaitColorPair)
    {first second : Fin 6}
    (hmatch : orderedPhysicalMate order T hcubic coloring hproper pair first =
      second) :
    physicalMate T hcubic coloring hproper pair (order first) = order second := by
  have htransport := congrArg order hmatch
  simpa [orderedPhysicalMate] using htransport

/-- Read the exact physical support in fixed six-port coordinates. -/
def orderedTaitSupport (order : Fin 6 ≃ P₀) (T : PortTangle V₀ I₀ P₀) :
    Set HexagonTaitWord :=
  {boundary | (fun port =>
    ⟨(boundary (order.symm port)).1,
      (boundary (order.symm port)).2⟩) ∈ taitSupport T}

/-- The boundary word of one proper colouring, in cyclic six-port
coordinates. -/
def orderedProperBoundaryWord
    (order : Fin 6 ≃ P₀) {T : PortTangle V₀ I₀ P₀}
    (coloring : Coloring T) (hproper : IsProper coloring) : HexagonTaitWord :=
  fun port => properBoundaryWord coloring hproper (order port)

theorem orderedProperBoundaryWord_mem_orderedTaitSupport
    (order : Fin 6 ≃ P₀) (T : PortTangle V₀ I₀ P₀)
    (coloring : Coloring T) (hproper : IsProper coloring) :
    orderedProperBoundaryWord order coloring hproper ∈ orderedTaitSupport order T := by
  have hmem := properBoundaryWord_mem_taitSupport T coloring hproper
  change (fun port =>
    ⟨(orderedProperBoundaryWord order coloring hproper
      (order.symm port)).1,
      (orderedProperBoundaryWord order coloring hproper
        (order.symm port)).2⟩) ∈ taitSupport T
  convert hmem using 1
  funext port
  apply Subtype.ext
  simp [orderedProperBoundaryWord]

/-- The physical common-web mate remains an active matching after passing to
cyclic six-port coordinates. -/
theorem orderedPhysicalMate_isActiveMatching
    (order : Fin 6 ≃ P₀) (T : PortTangle V₀ I₀ P₀)
    (hcubic : IsCubic T) (coloring : Coloring T)
    (hproper : IsProper coloring) (pair : TaitColorPair) :
    IsActiveMatching (orderedProperBoundaryWord order coloring hproper) pair
      (orderedPhysicalMate order T hcubic coloring hproper pair) := by
  intro port
  refine ⟨?_, orderedPhysicalMate_involutive
    order T hcubic coloring hproper pair port, ?_, ?_⟩
  · change pairActiveDart coloring pair (Sum.inr (order port)) ↔
      pairActiveDart coloring pair
        (Sum.inr (order
          (orderedPhysicalMate order T hcubic coloring hproper pair port)))
    simpa [orderedPhysicalMate] using
      (physicalMate_active_iff T hcubic coloring hproper pair (order port)).symm
  · intro hactive heq
    have htransport := congrArg order heq
    apply physicalMate_ne_of_active T hcubic coloring hproper pair
      (order port) hactive
    simpa [orderedPhysicalMate] using htransport
  · intro hinactive
    apply order.injective
    simpa [orderedPhysicalMate] using
      physicalMate_eq_self_of_inactive T hcubic coloring hproper pair
        (order port) hinactive

/-- Transport a selected set of cyclic coordinates back to physical ports. -/
def physicalSelectedPorts
    (order : Fin 6 ≃ P₀) (selected : Finset (Fin 6)) : Finset P₀ :=
  selected.map order.toEmbedding

@[simp]
theorem mem_physicalSelectedPorts_iff
    (order : Fin 6 ≃ P₀) (selected : Finset (Fin 6)) (port : P₀) :
    port ∈ physicalSelectedPorts order selected ↔ order.symm port ∈ selected := by
  simp [physicalSelectedPorts]

/-- Every selected union of physical matched components can be switched in
the original tangle, and its cyclic-coordinate boundary word stays in the
same exact ordered support. -/
theorem swap_orderedProperBoundaryWord_mem_orderedTaitSupport
    (order : Fin 6 ≃ P₀) (T : PortTangle V₀ I₀ P₀)
    (hcubic : IsCubic T) (coloring : Coloring T)
    (hproper : IsProper coloring) (pair : TaitColorPair)
    (selected : Finset (Fin 6))
    (hunion : IsComponentUnion
      (orderedPhysicalMate order T hcubic coloring hproper pair) selected) :
    swapBoundaryWord (orderedProperBoundaryWord order coloring hproper)
      pair selected ∈ orderedTaitSupport order T := by
  let selectedPorts := physicalSelectedPorts order selected
  have hunionPhysical : ∀ port : P₀,
      port ∈ selectedPorts ↔
        physicalMate T hcubic coloring hproper pair port ∈ selectedPorts := by
    intro port
    simpa [selectedPorts, orderedPhysicalMate] using
      hunion (order.symm port)
  let selectedDarts := selectedPhysicalComponents T coloring pair selectedPorts
  let region := selectedPhysicalComponents_kempeRegion
    T coloring pair selectedPorts
  let switched := switchRegion T coloring pair selectedDarts region
  let switchedProper := switchRegion_isProper
    T coloring hproper pair selectedDarts region
  have hmem : orderedProperBoundaryWord order switched switchedProper ∈
      orderedTaitSupport order T :=
    orderedProperBoundaryWord_mem_orderedTaitSupport
      order T switched switchedProper
  have hword : orderedProperBoundaryWord order switched switchedProper =
      swapBoundaryWord (orderedProperBoundaryWord order coloring hproper)
        pair selected := by
    funext port
    have hselectedDart : selectedDarts (Sum.inr (order port)) ↔
        port ∈ selected ∧
          pairActiveDart coloring pair (Sum.inr (order port)) := by
      have hphysical := selectedPhysicalComponents_boundary_iff
        T hcubic coloring hproper pair selectedPorts hunionPhysical (order port)
      simpa [selectedPorts] using hphysical
    by_cases hport : port ∈ selected
    · by_cases hactive : pairActiveDart coloring pair (Sum.inr (order port))
      · apply Subtype.ext
        simp only [orderedProperBoundaryWord, properBoundaryWord, word,
          swapBoundaryWord, if_pos hport]
        exact switchRegion_color_of_mem T coloring pair selectedDarts region
          (hselectedDart.2 ⟨hport, hactive⟩)
      · have hnotSelected : ¬selectedDarts (Sum.inr (order port)) := by
          intro h
          exact hactive (hselectedDart.1 h).2
        have hswap : Color.swap pair.colors.1 pair.colors.2
            (properBoundaryWord coloring hproper (order port)).1 =
            (properBoundaryWord coloring hproper (order port)).1 :=
          pairSwap_eq_self_of_not_active pair _ hactive
        apply Subtype.ext
        simp only [orderedProperBoundaryWord, properBoundaryWord, word,
          swapBoundaryWord, if_pos hport]
        calc
          _ = coloring.color (Sum.inr (order port)) :=
            switchRegion_color_of_not_mem T coloring pair selectedDarts region
              hnotSelected
          _ = _ := hswap.symm
    · have hnotSelected : ¬selectedDarts (Sum.inr (order port)) := by
        intro h
        exact hport (hselectedDart.1 h).1
      apply Subtype.ext
      simp only [orderedProperBoundaryWord, properBoundaryWord, word,
        swapBoundaryWord, if_neg hport]
      exact switchRegion_color_of_not_mem T coloring pair selectedDarts region
        hnotSelected
  rw [hword] at hmem
  exact hmem

noncomputable instance orderedTaitSupportDecidablePred
    (order : Fin 6 ≃ P₀) (T : PortTangle V₀ I₀ P₀) :
    DecidablePred (fun word : HexagonTaitWord =>
      word ∈ orderedTaitSupport order T) :=
  Classical.decPred _

/-- Noncrossing of every physical mate makes the exact ordered physical
support boundary-Kempe closed. -/
theorem boundaryKempeClosed_orderedTaitSupport_of_physical_noncrossing
    (order : Fin 6 ≃ P₀) (T : PortTangle V₀ I₀ P₀)
    (hcubic : IsCubic T)
    (hnoncrossing : ∀ (coloring : Coloring T) (hproper : IsProper coloring)
      (pair : TaitColorPair),
      IsNoncrossingMatching
        (orderedPhysicalMate order T hcubic coloring hproper pair)) :
    @BoundaryKempeClosed (orderedTaitSupport order T)
      (orderedTaitSupportDecidablePred order T) := by
  intro boundary hboundary pair
  rcases hboundary with ⟨coloring, hproper, hword⟩
  have hboundaryEq :
      orderedProperBoundaryWord order coloring hproper = boundary := by
    funext port
    apply Subtype.ext
    have hport := congrFun hword (order port)
    change coloring.color (Sum.inr (order port)) = (boundary port).1
    simpa [word] using hport
  rw [← hboundaryEq]
  refine ⟨orderedPhysicalMate order T hcubic coloring hproper pair,
    orderedPhysicalMate_isActiveMatching
      order T hcubic coloring hproper pair,
    hnoncrossing coloring hproper pair, ?_⟩
  intro selected hunion
  exact swap_orderedProperBoundaryWord_mem_orderedTaitSupport
    order T hcubic coloring hproper pair selected hunion

private theorem mate_min_eq_max
    (mate : Fin 6 → Fin 6) (hinvolutive : ∀ port, mate (mate port) = port)
    (port : Fin 6) :
    mate (min port (mate port)) = max port (mate port) := by
  by_cases hle : port ≤ mate port
  · rw [min_eq_left hle, max_eq_right hle]
  · have hge : mate port ≤ port := le_of_not_ge hle
    rw [min_eq_right hge, max_eq_left hge, hinvolutive]

private theorem exists_orientedArcWitness_of_chordsCross
    (mate : Fin 6 → Fin 6) (hinvolutive : ∀ port, mate (mate port) = port)
    {first third : Fin 6}
    (hcross : ChordsCross first (mate first) third (mate third)) :
    ∃ cut separator left right : Fin 6,
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
        min first (mate first) < min third (mate third) := by
      change min first.val (mate first).val < min third.val (mate third).val
      exact hcross.1
    have hleftSeparator :
        min third (mate third) < max first (mate first) := by
      change min third.val (mate third).val < max first.val (mate first).val
      exact hcross.2.1
    have hseparatorRight :
        max first (mate first) < max third (mate third) := by
      change max first.val (mate first).val < max third.val (mate third).val
      exact hcross.2.2
    exact ⟨hcutLeft, hleftSeparator, hseparatorRight,
      arcWitness_of_lt _ _ _ _ hcutLeft hleftSeparator hseparatorRight⟩
  · refine ⟨min third (mate third), max third (mate third),
      min first (mate first), max first (mate first),
      mate_min_eq_max mate hinvolutive third,
      mate_min_eq_max mate hinvolutive first, ?_⟩
    have hcutLeft :
        min third (mate third) < min first (mate first) := by
      change min third.val (mate third).val < min first.val (mate first).val
      exact hcross.1
    have hleftSeparator :
        min first (mate first) < max third (mate third) := by
      change min first.val (mate first).val < max third.val (mate third).val
      exact hcross.2.1
    have hseparatorRight :
        max third (mate third) < max first (mate first) := by
      change max third.val (mate third).val < max first.val (mate first).val
      exact hcross.2.2
    exact ⟨hcutLeft, hleftSeparator, hseparatorRight,
      arcWitness_of_lt _ _ _ _ hcutLeft hleftSeparator hseparatorRight⟩

/-! ## The graph-backed six-port noncrossing theorem -/

section GraphBacked

variable {V₁ : Type*} [Fintype V₁] [DecidableEq V₁]
  {G : SimpleGraph V₁} [DecidableRel G.Adj]

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The literal port tangle cut out by a vertex shore remains cubic. -/
theorem isCubic_vertexSidePortTangle
    (graphData : Data G) (keep : V₁ → Prop)
    (outer : RetainedDart graphData.toRotationSystem keep)
    (hcubic : graphData.toRotationSystem.IsCubic) :
    IsCubic (vertexSidePortTangle graphData keep outer) := by
  exact isCubic_ofOpenTangleData
    (ofVertexSide graphData.toRotationSystem keep outer)
    (openIsCubic_ofVertexSide graphData.toRotationSystem keep outer hcubic)

/-- **Physical six-port noncrossing.**

On a connected shore of a connected spherical cubic map, cyclic facial first
return makes the physical common-web mate a noncrossing six-port matching.
All matching edges come from the one literal bichromatic component relation;
none is supplied as an independent boundary certificate. -/
theorem orderedPhysicalMate_isNoncrossing
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
    (data : SixPortCyclicBondBoundaryData
      graphData.toRotationSystem keep)
    (outer : RetainedDart graphData.toRotationSystem keep)
    (coloring : Coloring (vertexSidePortTangle graphData keep outer))
    (hproper : IsProper coloring) (pair : TaitColorPair) :
    IsNoncrossingMatching
      (orderedPhysicalMate data.order
        (vertexSidePortTangle graphData keep outer)
        (isCubic_vertexSidePortTangle graphData keep outer hcubic)
        coloring hproper pair) := by
  let T := vertexSidePortTangle graphData keep outer
  let hcubicT := isCubic_vertexSidePortTangle graphData keep outer hcubic
  let mate := orderedPhysicalMate data.order T hcubicT coloring hproper pair
  intro first third hcross
  have hinvolutive : ∀ port, mate (mate port) = port := by
    intro port
    exact orderedPhysicalMate_involutive
      data.order T hcubicT coloring hproper pair port
  rcases exists_orientedArcWitness_of_chordsCross mate hinvolutive hcross with
    ⟨cut, separator, left, right, hcutMate, hleftMate,
      hcutLeft, hleftSeparator, hseparatorRight, harcs⟩
  rcases harcs with
    ⟨leftSteps, rightSteps, hleftPort, hrightPort,
      hleftAvoid, hrightAvoid⟩
  have hphysicalCut :
      physicalMate T hcubicT coloring hproper pair (data.order cut) =
        data.order separator :=
    physicalMate_order_eq_of_orderedPhysicalMate_eq
      data.order T hcubicT coloring hproper pair hcutMate
  have hphysicalLeft :
      physicalMate T hcubicT coloring hproper pair (data.order left) =
        data.order right :=
    physicalMate_order_eq_of_orderedPhysicalMate_eq
      data.order T hcubicT coloring hproper pair hleftMate
  have hcutNeSeparator : cut ≠ separator :=
    ne_of_lt (hcutLeft.trans hleftSeparator)
  have hleftNeRight : left ≠ right :=
    ne_of_lt (hleftSeparator.trans hseparatorRight)
  have hcutActive : pairActiveDart coloring pair (Sum.inr (data.order cut)) := by
    by_contra hinactive
    have hself := physicalMate_eq_self_of_inactive
      T hcubicT coloring hproper pair (data.order cut) hinactive
    have horderEq : data.order cut = data.order separator :=
      hself.symm.trans hphysicalCut
    exact hcutNeSeparator (data.order.injective horderEq)
  have hleftActive : pairActiveDart coloring pair (Sum.inr (data.order left)) := by
    by_contra hinactive
    have hself := physicalMate_eq_self_of_inactive
      T hcubicT coloring hproper pair (data.order left) hinactive
    have horderEq : data.order left = data.order right :=
      hself.symm.trans hphysicalLeft
    exact hleftNeRight (data.order.injective horderEq)
  have hcutSpec :=
    (physicalMate_eq_iff_of_active T hcubicT coloring hproper pair
      (data.order cut) (data.order separator) hcutActive).1 hphysicalCut
  have hleftSpec :=
    (physicalMate_eq_iff_of_active T hcubicT coloring hproper pair
      (data.order left) (data.order right) hleftActive).1 hphysicalLeft
  have hdistinctComponents : ¬KempeConnected T coloring pair
      (Sum.inr (data.order cut)) (Sum.inr (data.order left)) := by
    intro hconnectedComponents
    have hcutToLeft :
        physicalMate T hcubicT coloring hproper pair (data.order cut) =
          data.order left :=
      (physicalMate_eq_iff_of_active T hcubicT coloring hproper pair
        (data.order cut) (data.order left) hcutActive).2
        ⟨data.order.injective.ne (ne_of_gt hcutLeft),
          hleftActive, hconnectedComponents⟩
    have hseparatorEqLeft : data.order separator = data.order left :=
      hphysicalCut.symm.trans hcutToLeft
    exact (ne_of_gt hleftSeparator)
      (data.order.injective hseparatorEqLeft)
  exact no_distinct_kempe_components_between_boundary_arcs
    graphData htwoSided hdual hconnected hsphere hcubic hrotation
    keep hcomplementConnected data.toCyclicBondBoundaryData outer coloring pair
    cut separator left right hcutNeSeparator hleftNeRight
    leftSteps rightSteps hleftPort hrightPort hleftAvoid hrightAvoid
    ⟨ne_of_gt hcutLeft, ne_of_lt hleftSeparator⟩
    ⟨ne_of_gt (hcutLeft.trans (hleftSeparator.trans hseparatorRight)),
      ne_of_gt hseparatorRight⟩
    hcutActive hcutSpec.2.1 hleftActive hleftSpec.2.1
    hcutSpec.2.2 hleftSpec.2.2 hdistinctComponents

/-- **Exact physical boundary closure for a six-port spherical shore.**

The ordered support contains precisely the boundary words realized by the
literal shore tangle.  For every such word and every colour pair, the matching
and every permitted switch are supplied by the actual bichromatic components
of the realizing colouring; cyclic first return supplies noncrossing. -/
theorem boundaryKempeClosed_orderedVertexSideTaitSupport
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
    (data : SixPortCyclicBondBoundaryData
      graphData.toRotationSystem keep)
    (outer : RetainedDart graphData.toRotationSystem keep) :
    @BoundaryKempeClosed
      (orderedTaitSupport data.order
        (vertexSidePortTangle graphData keep outer))
      (orderedTaitSupportDecidablePred data.order
        (vertexSidePortTangle graphData keep outer)) := by
  apply boundaryKempeClosed_orderedTaitSupport_of_physical_noncrossing
    data.order (vertexSidePortTangle graphData keep outer)
    (isCubic_vertexSidePortTangle graphData keep outer hcubic)
  intro coloring hproper pair
  exact orderedPhysicalMate_isNoncrossing
    graphData htwoSided hdual hconnected hsphere hcubic hrotation
    keep hcomplementConnected data outer coloring hproper pair

end GraphBacked

end

end GoertzelV24PhysicalKempeNoncrossingClosure

end Mettapedia.GraphTheory.FourColor
