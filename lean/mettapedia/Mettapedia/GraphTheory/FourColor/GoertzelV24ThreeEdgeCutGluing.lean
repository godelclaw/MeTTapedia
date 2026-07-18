import Mettapedia.GraphTheory.FourColor.GoertzelV24ThreeEdgeCutCap

namespace Mettapedia.GraphTheory.FourColor

namespace RotationSystem

open GoertzelV24ThreeEdgeCutColor
open GoertzelV24RotationCutDartDecomposition

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- An exact ordered three-edge cut, independent of the choice of outer dart.
It determines two complementary three-star caps. -/
structure ThreeEdgeCutPairData (RS : RotationSystem V E) where
  side : Finset V
  crossing : Fin 3 → E
  crossing_injective : Function.Injective crossing
  boundary_eq : RS.vertexSideEdgeBoundary side = orderedCut crossing

namespace ThreeEdgeCutPairData

variable {RS : RotationSystem V E} (data : ThreeEdgeCutPairData RS)

theorem crossing_mem_boundary (step : Fin 3) :
    data.crossing step ∈ RS.vertexSideEdgeBoundary data.side := by
  rw [data.boundary_eq]
  exact Finset.mem_image.mpr ⟨step, Finset.mem_univ step, rfl⟩

/-- The complementary side has the same exact ordered boundary. -/
theorem complement_boundary_eq :
    RS.vertexSideEdgeBoundary data.sideᶜ = orderedCut data.crossing := by
  rw [RS.vertexSideEdgeBoundary_compl data.side, data.boundary_eq]

theorem crossing_mem_complement_boundary (step : Fin 3) :
    data.crossing step ∈ RS.vertexSideEdgeBoundary data.sideᶜ := by
  rw [data.complement_boundary_eq]
  exact Finset.mem_image.mpr ⟨step, Finset.mem_univ step, rfl⟩

/-- Root each half at the outward dart of the first ordered cut edge. -/
def sideRoot : RS.D :=
  (RS.boundaryDartOfCrossingEdge data.side (data.crossing 0)
    (data.crossing_mem_boundary 0)).1.1

def complementRoot : RS.D :=
  (RS.boundaryDartOfCrossingEdge data.sideᶜ (data.crossing 0)
    (data.crossing_mem_complement_boundary 0)).1.1

def sideRootedRotationSystem : RotationSystem V E :=
  RS.withOuter data.sideRoot

def complementRootedRotationSystem : RotationSystem V E :=
  RS.withOuter data.complementRoot

/-- The chosen side as rooted three-star cap data. -/
def sideData : ThreeEdgeCutSideData data.sideRootedRotationSystem where
  side := data.side
  crossing := data.crossing
  crossing_injective := data.crossing_injective
  boundary_eq := by
    simpa [sideRootedRotationSystem] using data.boundary_eq
  outer_mem := by
    change RS.vertOf data.sideRoot ∈ data.side
    exact (RS.boundaryDartOfCrossingEdge data.side (data.crossing 0)
      (data.crossing_mem_boundary 0)).1.2

/-- The complementary side as independently rooted three-star cap data. -/
def complementData :
    ThreeEdgeCutSideData data.complementRootedRotationSystem where
  side := data.sideᶜ
  crossing := data.crossing
  crossing_injective := data.crossing_injective
  boundary_eq := by
    simpa [complementRootedRotationSystem] using data.complement_boundary_eq
  outer_mem := by
    change RS.vertOf data.complementRoot ∈ data.sideᶜ
    exact (RS.boundaryDartOfCrossingEdge data.sideᶜ (data.crossing 0)
      (data.crossing_mem_complement_boundary 0)).1.2

/-- Two vertices on the opposite side make the chosen cap strictly smaller. -/
theorem card_sideCapVertex_lt
    (first second : V) (hfirst : first ∉ data.side)
    (hsecond : second ∉ data.side) (hne : second ≠ first) :
    Fintype.card data.sideData.CapVertex < Fintype.card V := by
  exact data.sideData.card_capVertex_lt_of_two_deleted
    first second hfirst hsecond hne

/-- Two vertices on the chosen side make the complementary cap strictly
smaller. -/
theorem card_complementCapVertex_lt
    (first second : V) (hfirst : first ∈ data.side)
    (hsecond : second ∈ data.side) (hne : second ≠ first) :
    Fintype.card data.complementData.CapVertex < Fintype.card V := by
  apply data.complementData.card_capVertex_lt_of_two_deleted first second
  · change first ∉ data.sideᶜ
    simpa using hfirst
  · change second ∉ data.sideᶜ
    simpa using hsecond
  · exact hne

/-- Both complementary cap constructions preserve cubicity. -/
theorem sideCap_isCubic (hCubic : RS.IsCubic) :
    data.sideData.capRotationSystem.IsCubic := by
  apply data.sideData.capRotationSystem_isCubic
  simpa [sideRootedRotationSystem] using hCubic

theorem complementCap_isCubic (hCubic : RS.IsCubic) :
    data.complementData.capRotationSystem.IsCubic := by
  apply data.complementData.capRotationSystem_isCubic
  simpa [complementRootedRotationSystem] using hCubic

/-- Restrict an ambient Tait coloring to either capped half. -/
def sideCapColoring
    (hCubic : RS.IsCubic) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C) :
    data.sideData.capRotationSystem.EdgeColoring Color :=
  data.sideData.capColoring
    (by simpa [sideRootedRotationSystem] using hCubic) C hC

def complementCapColoring
    (hCubic : RS.IsCubic) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C) :
    data.complementData.capRotationSystem.EdgeColoring Color :=
  data.complementData.capColoring
    (by simpa [complementRootedRotationSystem] using hCubic) C hC

theorem sideCapColoring_isTait
    (hCubic : RS.IsCubic) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C) :
    data.sideData.capRotationSystem.IsTaitEdgeColoring
      (data.sideCapColoring hCubic C hC) := by
  exact data.sideData.capColoring_isTait
    (by simpa [sideRootedRotationSystem] using hCubic) C hC

theorem complementCapColoring_isTait
    (hCubic : RS.IsCubic) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C) :
    data.complementData.capRotationSystem.IsTaitEdgeColoring
      (data.complementCapColoring hCubic C hC) := by
  exact data.complementData.capColoring_isTait
    (by simpa [complementRootedRotationSystem] using hCubic) C hC

theorem sideCapColoring_capEdge
    (hCubic : RS.IsCubic) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C) (step : Fin 3) :
    data.sideCapColoring hCubic C hC (data.sideData.capEdge step) =
      C (data.crossing step) := by
  exact data.sideData.capColoring_capEdge
    (by simpa [sideRootedRotationSystem] using hCubic) C hC step

theorem complementCapColoring_capEdge
    (hCubic : RS.IsCubic) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C) (step : Fin 3) :
    data.complementCapColoring hCubic C hC
        (data.complementData.capEdge step) = C (data.crossing step) := by
  exact data.complementData.capColoring_capEdge
    (by simpa [complementRootedRotationSystem] using hCubic) C hC step

/-- The cap edge containing an old dart based on the chosen side. -/
def sideCapEdgeOfDart (dart : RS.D)
    (hside : RS.vertOf dart ∈ data.side) :
    data.sideData.capRewiredDartSystem.Edge :=
  data.sideData.capEdgeOfRetainedDart ⟨dart, hside⟩

/-- The cap edge containing an old dart based on the complementary side. -/
def complementCapEdgeOfDart (dart : RS.D)
    (hcomplement : RS.vertOf dart ∈ data.sideᶜ) :
    data.complementData.capRewiredDartSystem.Edge :=
  data.complementData.capEdgeOfRetainedDart ⟨dart, hcomplement⟩

/-- Read each old dart color from the capped half containing its base
vertex. -/
def gluedDartColor
    (sideColoring : data.sideData.capRotationSystem.EdgeColoring Color)
    (complementColoring :
      data.complementData.capRotationSystem.EdgeColoring Color)
    (dart : RS.D) : Color :=
  if hside : RS.vertOf dart ∈ data.side then
    sideColoring (data.sideCapEdgeOfDart dart hside)
  else
    complementColoring
      (data.complementCapEdgeOfDart dart (by simpa using hside))

/-- The two boundary enumerations assign the same ordered position to the
opposite darts of one old crossing edge. -/
theorem boundarySteps_eq
    (dart : RS.D) (hside : RS.vertOf dart ∈ data.side)
    (hsideAlpha : RS.vertOf (RS.alpha dart) ∉ data.side) :
    data.complementData.crossingBoundaryDartEquiv.symm
        ⟨⟨RS.alpha dart, by
          change RS.vertOf (RS.alpha dart) ∈ data.sideᶜ
          simpa using hsideAlpha⟩, by
          change RS.vertOf (RS.alpha (RS.alpha dart)) ∉ data.sideᶜ
          simpa [RS.alpha_involutive] using hside⟩ =
      data.sideData.crossingBoundaryDartEquiv.symm
        ⟨⟨dart, hside⟩, hsideAlpha⟩ := by
  let sideBoundary : BoundaryDart data.sideRootedRotationSystem
      data.sideData.keep := ⟨⟨dart, hside⟩, hsideAlpha⟩
  let complementBoundary :
      BoundaryDart data.complementRootedRotationSystem
        data.complementData.keep :=
    ⟨⟨RS.alpha dart, by
      change RS.vertOf (RS.alpha dart) ∈ data.sideᶜ
      simpa using hsideAlpha⟩, by
      change RS.vertOf (RS.alpha (RS.alpha dart)) ∉ data.sideᶜ
      simpa [RS.alpha_involutive] using hside⟩
  change data.complementData.crossingBoundaryDartEquiv.symm
      complementBoundary =
    data.sideData.crossingBoundaryDartEquiv.symm sideBoundary
  apply data.crossing_injective
  have hcomplementEdge :
      RS.edgeOf complementBoundary.1.1 =
        data.crossing
          (data.complementData.crossingBoundaryDartEquiv.symm
            complementBoundary) := by
    change data.complementRootedRotationSystem.edgeOf
        complementBoundary.1.1 =
      data.complementData.crossing
        (data.complementData.crossingBoundaryDartEquiv.symm
          complementBoundary)
    calc
      _ = data.complementRootedRotationSystem.edgeOf
          (data.complementData.crossingBoundaryDartEquiv
            (data.complementData.crossingBoundaryDartEquiv.symm
              complementBoundary)).1.1 := by
        congr 1
        exact congrArg
          (fun boundary : BoundaryDart data.complementRootedRotationSystem
              data.complementData.keep => boundary.1.1)
          (data.complementData.crossingBoundaryDartEquiv.apply_symm_apply
            complementBoundary).symm
      _ = _ := data.complementData.crossingBoundaryDartEquiv_edgeOf
        (data.complementData.crossingBoundaryDartEquiv.symm complementBoundary)
  have hsideEdge :
      RS.edgeOf sideBoundary.1.1 =
        data.crossing
          (data.sideData.crossingBoundaryDartEquiv.symm sideBoundary) := by
    change data.sideRootedRotationSystem.edgeOf sideBoundary.1.1 =
      data.sideData.crossing
        (data.sideData.crossingBoundaryDartEquiv.symm sideBoundary)
    calc
      _ = data.sideRootedRotationSystem.edgeOf
          (data.sideData.crossingBoundaryDartEquiv
            (data.sideData.crossingBoundaryDartEquiv.symm sideBoundary)).1.1 := by
        congr 1
        exact congrArg
          (fun boundary : BoundaryDart data.sideRootedRotationSystem
              data.sideData.keep => boundary.1.1)
          (data.sideData.crossingBoundaryDartEquiv.apply_symm_apply
            sideBoundary).symm
      _ = _ := data.sideData.crossingBoundaryDartEquiv_edgeOf
        (data.sideData.crossingBoundaryDartEquiv.symm sideBoundary)
  rw [← hcomplementEdge, ← hsideEdge]
  change RS.edgeOf (RS.alpha dart) = RS.edgeOf dart
  exact RS.edge_alpha dart

/-- Positionwise agreement of the three cap edges makes the piecewise dart
color invariant under the old edge involution. -/
theorem gluedDartColor_alpha
    (sideColoring : data.sideData.capRotationSystem.EdgeColoring Color)
    (complementColoring :
      data.complementData.capRotationSystem.EdgeColoring Color)
    (hseam : ∀ step : Fin 3,
      sideColoring (data.sideData.capEdge step) =
        complementColoring (data.complementData.capEdge step))
    (dart : RS.D) :
    data.gluedDartColor sideColoring complementColoring (RS.alpha dart) =
      data.gluedDartColor sideColoring complementColoring dart := by
  by_cases hside : RS.vertOf dart ∈ data.side
  · by_cases hsideAlpha : RS.vertOf (RS.alpha dart) ∈ data.side
    · rw [gluedDartColor, dif_pos hsideAlpha, gluedDartColor, dif_pos hside]
      exact congrArg sideColoring
        (data.sideData.capEdgeOfRetainedDart_alpha_of_internal
          dart hside hsideAlpha)
    · rw [gluedDartColor, dif_neg hsideAlpha, gluedDartColor, dif_pos hside]
      let sideBoundary : BoundaryDart data.sideRootedRotationSystem
          data.sideData.keep := ⟨⟨dart, hside⟩, hsideAlpha⟩
      let complementBoundary :
          BoundaryDart data.complementRootedRotationSystem
            data.complementData.keep :=
        ⟨⟨RS.alpha dart, by
          change RS.vertOf (RS.alpha dart) ∈ data.sideᶜ
          simpa using hsideAlpha⟩, by
          change RS.vertOf (RS.alpha (RS.alpha dart)) ∉ data.sideᶜ
          simpa [RS.alpha_involutive] using hside⟩
      change complementColoring
          (data.complementData.capEdgeOfRetainedDart complementBoundary.1) =
        sideColoring
          (data.sideData.capEdgeOfRetainedDart sideBoundary.1)
      rw [data.complementData.capEdgeOfRetainedDart_eq_capEdge_of_boundary,
        data.sideData.capEdgeOfRetainedDart_eq_capEdge_of_boundary]
      have hsteps :
          data.complementData.crossingBoundaryDartEquiv.symm
              complementBoundary =
            data.sideData.crossingBoundaryDartEquiv.symm sideBoundary :=
        data.boundarySteps_eq dart hside hsideAlpha
      rw [hsteps]
      exact (hseam _).symm
  · by_cases hsideAlpha : RS.vertOf (RS.alpha dart) ∈ data.side
    · rw [gluedDartColor, dif_pos hsideAlpha, gluedDartColor, dif_neg hside]
      have hreverse := data.boundarySteps_eq (RS.alpha dart) hsideAlpha
        (by simpa [RS.alpha_involutive] using hside)
      let complementBoundary :
          BoundaryDart data.complementRootedRotationSystem
            data.complementData.keep :=
        ⟨⟨dart, by
          change RS.vertOf dart ∈ data.sideᶜ
          simpa using hside⟩, by
          change RS.vertOf (RS.alpha dart) ∉ data.sideᶜ
          simpa using hsideAlpha⟩
      let sideBoundary : BoundaryDart data.sideRootedRotationSystem
          data.sideData.keep :=
        ⟨⟨RS.alpha dart, hsideAlpha⟩, by
          change RS.vertOf (RS.alpha (RS.alpha dart)) ∉ data.side
          simpa [RS.alpha_involutive] using hside⟩
      change sideColoring
          (data.sideData.capEdgeOfRetainedDart sideBoundary.1) =
        complementColoring
          (data.complementData.capEdgeOfRetainedDart complementBoundary.1)
      rw [data.sideData.capEdgeOfRetainedDart_eq_capEdge_of_boundary,
        data.complementData.capEdgeOfRetainedDart_eq_capEdge_of_boundary]
      have hsteps :
          data.complementData.crossingBoundaryDartEquiv.symm
              complementBoundary =
            data.sideData.crossingBoundaryDartEquiv.symm sideBoundary := by
        simpa [sideBoundary, complementBoundary, RS.alpha_involutive] using
          hreverse
      rw [hsteps]
      exact hseam _
    · rw [gluedDartColor, dif_neg hsideAlpha, gluedDartColor, dif_neg hside]
      exact congrArg complementColoring
        (data.complementData.capEdgeOfRetainedDart_alpha_of_internal
          dart (by
            change RS.vertOf dart ∈ data.sideᶜ
            simpa using hside) (by
            change RS.vertOf (RS.alpha dart) ∈ data.sideᶜ
            simpa using hsideAlpha))

/-- At one old vertex, properness comes from the unique capped half containing
that vertex. -/
theorem gluedDartColor_proper
    (sideColoring : data.sideData.capRotationSystem.EdgeColoring Color)
    (complementColoring :
      data.complementData.capRotationSystem.EdgeColoring Color)
    {left right : RS.D}
    (hvertex : RS.vertOf left = RS.vertOf right) (hne : left ≠ right) :
    data.gluedDartColor sideColoring complementColoring left ≠
      data.gluedDartColor sideColoring complementColoring right := by
  by_cases hside : RS.vertOf left ∈ data.side
  · have hsideRight : RS.vertOf right ∈ data.side := by
      rw [← hvertex]
      exact hside
    rw [gluedDartColor, dif_pos hside, gluedDartColor, dif_pos hsideRight]
    apply sideColoring.valid
    exact data.sideData.capEdgeAdj_of_retainedDarts
      ⟨left, hside⟩ ⟨right, hsideRight⟩ hvertex hne
  · have hsideRight : RS.vertOf right ∉ data.side := by
      rw [← hvertex]
      exact hside
    rw [gluedDartColor, dif_neg hside, gluedDartColor, dif_neg hsideRight]
    apply complementColoring.valid
    exact data.complementData.capEdgeAdj_of_retainedDarts
      ⟨left, by
        change RS.vertOf left ∈ data.sideᶜ
        simpa using hside⟩
      ⟨right, by
        change RS.vertOf right ∈ data.sideᶜ
        simpa using hsideRight⟩ hvertex hne

/-- Glue cap colorings whose three ordered seam colors agree. -/
def gluedColoring
    (sideColoring : data.sideData.capRotationSystem.EdgeColoring Color)
    (complementColoring :
      data.complementData.capRotationSystem.EdgeColoring Color)
    (hseam : ∀ step : Fin 3,
      sideColoring (data.sideData.capEdge step) =
        complementColoring (data.complementData.capEdge step)) :
    RS.EdgeColoring Color :=
  RS.dartDescendedColoring
    (data.gluedDartColor sideColoring complementColoring)
    (data.gluedDartColor_alpha sideColoring complementColoring hseam)
    (data.gluedDartColor_proper sideColoring complementColoring)

theorem gluedColoring_isTait
    (sideColoring : data.sideData.capRotationSystem.EdgeColoring Color)
    (complementColoring :
      data.complementData.capRotationSystem.EdgeColoring Color)
    (hsideTait : data.sideData.capRotationSystem.IsTaitEdgeColoring
      sideColoring)
    (hcomplementTait :
      data.complementData.capRotationSystem.IsTaitEdgeColoring
        complementColoring)
    (hseam : ∀ step : Fin 3,
      sideColoring (data.sideData.capEdge step) =
        complementColoring (data.complementData.capEdge step)) :
    RS.IsTaitEdgeColoring
      (data.gluedColoring sideColoring complementColoring hseam) := by
  apply RS.dartDescendedColoring_isTait
    (data.gluedDartColor sideColoring complementColoring)
    (data.gluedDartColor_alpha sideColoring complementColoring hseam)
    (data.gluedDartColor_proper sideColoring complementColoring)
  intro dart
  by_cases hside : RS.vertOf dart ∈ data.side
  · rw [gluedDartColor, dif_pos hside]
    exact hsideTait _
  · rw [gluedDartColor, dif_neg hside]
    exact hcomplementTait _

/-- Relabel the complementary cap by the unique ordered permutation carrying
its boundary Tait triple to the chosen side's boundary triple. -/
def alignedComplementColoring
    (sideColoring : data.sideData.capRotationSystem.EdgeColoring Color)
    (complementColoring :
      data.complementData.capRotationSystem.EdgeColoring Color)
    (hsideTait : data.sideData.capRotationSystem.IsTaitEdgeColoring
      sideColoring)
    (hcomplementTait :
      data.complementData.capRotationSystem.IsTaitEdgeColoring
        complementColoring) :
    data.complementData.capRotationSystem.EdgeColoring Color :=
  data.complementData.capRotationSystem.relabelColoring complementColoring
    (alignTaitTripleColorEquiv
      (data.complementData.capEdge_isTaitColorTriple
        complementColoring hcomplementTait)
      (data.sideData.capEdge_isTaitColorTriple sideColoring hsideTait))

/-- The aligned complementary coloring agrees at every ordered cap edge. -/
theorem alignedComplementColoring_capEdge
    (sideColoring : data.sideData.capRotationSystem.EdgeColoring Color)
    (complementColoring :
      data.complementData.capRotationSystem.EdgeColoring Color)
    (hsideTait : data.sideData.capRotationSystem.IsTaitEdgeColoring
      sideColoring)
    (hcomplementTait :
      data.complementData.capRotationSystem.IsTaitEdgeColoring
        complementColoring)
    (step : Fin 3) :
    data.alignedComplementColoring sideColoring complementColoring
        hsideTait hcomplementTait (data.complementData.capEdge step) =
      sideColoring (data.sideData.capEdge step) := by
  fin_cases step <;>
    simp [alignedComplementColoring]

theorem alignedComplementColoring_isTait
    (sideColoring : data.sideData.capRotationSystem.EdgeColoring Color)
    (complementColoring :
      data.complementData.capRotationSystem.EdgeColoring Color)
    (hsideTait : data.sideData.capRotationSystem.IsTaitEdgeColoring
      sideColoring)
    (hcomplementTait :
      data.complementData.capRotationSystem.IsTaitEdgeColoring
        complementColoring) :
    data.complementData.capRotationSystem.IsTaitEdgeColoring
      (data.alignedComplementColoring sideColoring complementColoring
        hsideTait hcomplementTait) := by
  apply data.complementData.capRotationSystem.relabelColoring_isTait
  · exact alignTaitTripleColorEquiv_zero _ _
  · exact hcomplementTait

/-- Canonically glue two arbitrary Tait-colored caps after ordered boundary
alignment. -/
def gluedColoringFromCaps
    (sideColoring : data.sideData.capRotationSystem.EdgeColoring Color)
    (complementColoring :
      data.complementData.capRotationSystem.EdgeColoring Color)
    (hsideTait : data.sideData.capRotationSystem.IsTaitEdgeColoring
      sideColoring)
    (hcomplementTait :
      data.complementData.capRotationSystem.IsTaitEdgeColoring
        complementColoring) : RS.EdgeColoring Color :=
  data.gluedColoring sideColoring
    (data.alignedComplementColoring sideColoring complementColoring
      hsideTait hcomplementTait)
    (fun step =>
      (data.alignedComplementColoring_capEdge sideColoring complementColoring
        hsideTait hcomplementTait step).symm)

theorem gluedColoringFromCaps_isTait
    (sideColoring : data.sideData.capRotationSystem.EdgeColoring Color)
    (complementColoring :
      data.complementData.capRotationSystem.EdgeColoring Color)
    (hsideTait : data.sideData.capRotationSystem.IsTaitEdgeColoring
      sideColoring)
    (hcomplementTait :
      data.complementData.capRotationSystem.IsTaitEdgeColoring
        complementColoring) :
    RS.IsTaitEdgeColoring
      (data.gluedColoringFromCaps sideColoring complementColoring
        hsideTait hcomplementTait) := by
  apply data.gluedColoring_isTait
  · exact hsideTait
  · exact data.alignedComplementColoring_isTait sideColoring
      complementColoring hsideTait hcomplementTait

/-- Tait colorability of the two capped halves implies Tait colorability of
the ambient rotation system. -/
theorem taitColorable_of_caps
    (hside : ∃ sideColoring,
      data.sideData.capRotationSystem.IsTaitEdgeColoring sideColoring)
    (hcomplement : ∃ complementColoring,
      data.complementData.capRotationSystem.IsTaitEdgeColoring
        complementColoring) :
    ∃ C : RS.EdgeColoring Color, RS.IsTaitEdgeColoring C := by
  rcases hside with ⟨sideColoring, hsideTait⟩
  rcases hcomplement with ⟨complementColoring, hcomplementTait⟩
  exact ⟨data.gluedColoringFromCaps sideColoring complementColoring
      hsideTait hcomplementTait,
    data.gluedColoringFromCaps_isTait sideColoring complementColoring
      hsideTait hcomplementTait⟩

/-- An ambient Tait coloring restricts to both capped halves. -/
theorem caps_taitColorable_of_ambient
    (hCubic : RS.IsCubic) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C) :
    (∃ sideColoring,
        data.sideData.capRotationSystem.IsTaitEdgeColoring sideColoring) ∧
      (∃ complementColoring,
        data.complementData.capRotationSystem.IsTaitEdgeColoring
          complementColoring) := by
  exact ⟨⟨data.sideCapColoring hCubic C hC,
      data.sideCapColoring_isTait hCubic C hC⟩,
    ⟨data.complementCapColoring hCubic C hC,
      data.complementCapColoring_isTait hCubic C hC⟩⟩

/-- Exact colorability equation for an ordered three-edge cut. -/
theorem taitColorable_iff_caps (hCubic : RS.IsCubic) :
    (∃ C : RS.EdgeColoring Color, RS.IsTaitEdgeColoring C) ↔
      (∃ sideColoring,
          data.sideData.capRotationSystem.IsTaitEdgeColoring sideColoring) ∧
        (∃ complementColoring,
          data.complementData.capRotationSystem.IsTaitEdgeColoring
            complementColoring) := by
  constructor
  · rintro ⟨C, hC⟩
    exact data.caps_taitColorable_of_ambient hCubic C hC
  · rintro ⟨hside, hcomplement⟩
    exact data.taitColorable_of_caps hside hcomplement

end ThreeEdgeCutPairData

end

end RotationSystem

end Mettapedia.GraphTheory.FourColor
