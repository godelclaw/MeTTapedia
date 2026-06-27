import Mettapedia.GraphTheory.FourColor.Theorem49ColoringGeneratorFamilyRoute

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- An explicit projected coloring family detects every nonzero selected-boundary-zero chain once
a finite set of controlling coordinates has two ingredients:

1. vanishing on those coordinates forces vanishing of the whole chain; and
2. every nonzero value on each controlling coordinate is separated by some projected generator
   equal to a single-coordinate chain there.

This is the direct Lean interface for the current finite-lab certificates on the wheel/shared
benchmarks, and for future explicit finite `F₂` detector outputs of the same shape. -/
theorem BoundaryZeroProjectedColoringGeneratorDetector.of_singleCoordinateWitnesses
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    (controlEdges : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hwitness :
      ∀ e ∈ controlEdges, ∀ d : Color, d ≠ 0 →
        ∃ c : Color,
          Pi.single e c ∈ projectedColoringGeneratorSubspace emb colorings ∧
            colorDot c d ≠ 0) :
    BoundaryZeroProjectedColoringGeneratorDetector emb colorings := by
  intro z hzBoundary hzNonzero
  classical
  have hcoord : ∃ e ∈ controlEdges, z e ≠ 0 := by
    by_contra hnone
    apply hzNonzero
    apply hcontrol hzBoundary
    intro e he
    by_contra hze
    exact hnone ⟨e, he, hze⟩
  rcases hcoord with ⟨e, he, hze⟩
  rcases hwitness e he (z e) hze with ⟨c, hcmem, hcdot⟩
  refine ⟨Pi.single e c, hcmem, ?_⟩
  rw [chainDotBilinForm_single_left]
  exact hcdot

/-- Red/blue basis form of the explicit projected coloring-family detector.  It is enough to
know that the projected generator subspace contains the red and blue single-coordinate probes on
each controlling edge. -/
theorem BoundaryZeroProjectedColoringGeneratorDetector.of_redBlueSingleCoordinateMemberships
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    (controlEdges : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hred :
      ∀ e ∈ controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblue :
      ∀ e ∈ controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings) :
    BoundaryZeroProjectedColoringGeneratorDetector emb colorings :=
  BoundaryZeroProjectedColoringGeneratorDetector.of_singleCoordinateWitnesses
    controlEdges hcontrol
    (by
      intro e he d hd
      by_cases hredDot : colorDot red d ≠ 0
      · exact ⟨red, hred e he, hredDot⟩
      · have hredZero : colorDot red d = 0 := by
          by_contra h
          exact hredDot h
        have hblueDot : colorDot blue d ≠ 0 := by
          intro hblueZero
          have hdRed : colorDot d red = 0 := by
            simpa [colorDot_comm] using hredZero
          have hdBlue : colorDot d blue = 0 := by
            simpa [colorDot_comm] using hblueZero
          exact hd (color_eq_zero_of_colorDot_red_blue hdRed hdBlue)
        exact ⟨blue, hblue e he, hblueDot⟩)

/-- Concrete finite-generator certificate form of the explicit projected coloring-family
detector.  The checker supplies, for every controlling edge, red and blue projected face
generators whose boundary-erased chains are exactly the corresponding single-coordinate probes. -/
theorem BoundaryZeroProjectedColoringGeneratorDetector.of_projectedFaceGeneratorEqualities
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    (controlEdges : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hred :
      ∀ e ∈ controlEdges,
        ∃ C ∈ colorings, ∃ f : emb.Face, ∃ a b : Color,
          ValidColorPair a b ∧
            boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                (polarizedFaceGenerator C a b (emb.faceBoundary f)) =
              Pi.single e red)
    (hblue :
      ∀ e ∈ controlEdges,
        ∃ C ∈ colorings, ∃ f : emb.Face, ∃ a b : Color,
          ValidColorPair a b ∧
            boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                (polarizedFaceGenerator C a b (emb.faceBoundary f)) =
              Pi.single e blue) :
    BoundaryZeroProjectedColoringGeneratorDetector emb colorings := by
  have hmembers :=
    redBlueSingleCoordinateMemberships_of_projectedFaceGeneratorEqualities
      (emb := emb) (colorings := colorings) controlEdges hred hblue
  exact
    BoundaryZeroProjectedColoringGeneratorDetector.of_redBlueSingleCoordinateMemberships
      controlEdges hcontrol hmembers.1 hmembers.2

/-- Unique projected-bicolored-edge certificate form of the explicit projected coloring-family
detector.  This is the direct shape exported by finite searches that identify one
non-boundary face edge whose color lies in a valid pair, with every other non-boundary edge on
that face outside the same color pair. -/
theorem BoundaryZeroProjectedColoringGeneratorDetector.of_uniqueProjectedBicoloredCertificates
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    (controlEdges : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hred :
      ∀ e ∈ controlEdges,
        ∃ C ∈ colorings, ∃ f : emb.Face, ∃ a b : Color,
          ValidColorPair a b ∧
            a + b = red ∧
              e ∈ emb.faceBoundary f ∧
                e ∉ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∧
                  (C e = a ∨ C e = b) ∧
                    ∀ e' : G.edgeSet,
                      e' ≠ e →
                      e' ∉ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces →
                      e' ∈ emb.faceBoundary f →
                        ¬ (C e' = a ∨ C e' = b))
    (hblue :
      ∀ e ∈ controlEdges,
        ∃ C ∈ colorings, ∃ f : emb.Face, ∃ a b : Color,
          ValidColorPair a b ∧
            a + b = blue ∧
              e ∈ emb.faceBoundary f ∧
                e ∉ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∧
                  (C e = a ∨ C e = b) ∧
                    ∀ e' : G.edgeSet,
                      e' ≠ e →
                      e' ∉ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces →
                      e' ∈ emb.faceBoundary f →
                        ¬ (C e' = a ∨ C e' = b)) :
    BoundaryZeroProjectedColoringGeneratorDetector emb colorings := by
  apply BoundaryZeroProjectedColoringGeneratorDetector.of_projectedFaceGeneratorEqualities
    controlEdges hcontrol
  · intro e he
    rcases hred e he with
      ⟨C, hC, f, a, b, hab, hsum, hface, hnotBoundary, hcolor, hunique⟩
    exact
      exists_projectedFaceGenerator_eq_single_of_unique_projected_bicolored
        (emb := emb) (colorings := colorings) (c := red)
        hC f hab hsum hface hnotBoundary hcolor hunique
  · intro e he
    rcases hblue e he with
      ⟨C, hC, f, a, b, hab, hsum, hface, hnotBoundary, hcolor, hunique⟩
    exact
      exists_projectedFaceGenerator_eq_single_of_unique_projected_bicolored
        (emb := emb) (colorings := colorings) (c := blue)
        hC f hab hsum hface hnotBoundary hcolor hunique

/-- Route form of the same explicit coordinate certificate: once an explicit coloring family
inside the chosen edge-Kempe closure has enough single-coordinate witnesses on a controlling edge
set, the full theorem-4.9 synthesis package follows for the base coloring. -/
theorem theorem49BoundaryRootSynthesis_of_singleCoordinateWitnesses
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (controlEdges : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hwitness :
      ∀ e ∈ controlEdges, ∀ d : Color, d ≠ 0 →
        ∃ c : Color,
          Pi.single e c ∈ projectedColoringGeneratorSubspace emb colorings ∧
            colorDot c d ≠ 0) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_boundaryZeroProjectedColoringGeneratorDetector
    emb C₀ colorings hsubset
    (BoundaryZeroProjectedColoringGeneratorDetector.of_singleCoordinateWitnesses
      controlEdges hcontrol hwitness)

/-- Route form for red/blue single-coordinate projected-generator memberships. -/
theorem theorem49BoundaryRootSynthesis_of_redBlueSingleCoordinateMemberships
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (controlEdges : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hred :
      ∀ e ∈ controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblue :
      ∀ e ∈ controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_boundaryZeroProjectedColoringGeneratorDetector
    emb C₀ colorings hsubset
    (BoundaryZeroProjectedColoringGeneratorDetector.of_redBlueSingleCoordinateMemberships
      controlEdges hcontrol hred hblue)

/-- Route form for concrete projected face-generator equality certificates emitted by finite
configuration checks. -/
theorem theorem49BoundaryRootSynthesis_of_projectedFaceGeneratorEqualities
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (controlEdges : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hred :
      ∀ e ∈ controlEdges,
        ∃ C ∈ colorings, ∃ f : emb.Face, ∃ a b : Color,
          ValidColorPair a b ∧
            boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                (polarizedFaceGenerator C a b (emb.faceBoundary f)) =
              Pi.single e red)
    (hblue :
      ∀ e ∈ controlEdges,
        ∃ C ∈ colorings, ∃ f : emb.Face, ∃ a b : Color,
          ValidColorPair a b ∧
            boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                (polarizedFaceGenerator C a b (emb.faceBoundary f)) =
              Pi.single e blue) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_boundaryZeroProjectedColoringGeneratorDetector
    emb C₀ colorings hsubset
    (BoundaryZeroProjectedColoringGeneratorDetector.of_projectedFaceGeneratorEqualities
      controlEdges hcontrol hred hblue)

/-- Route form for unique projected-bicolored-edge finite certificates. -/
theorem theorem49BoundaryRootSynthesis_of_uniqueProjectedBicoloredCertificates
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (controlEdges : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hred :
      ∀ e ∈ controlEdges,
        ∃ C ∈ colorings, ∃ f : emb.Face, ∃ a b : Color,
          ValidColorPair a b ∧
            a + b = red ∧
              e ∈ emb.faceBoundary f ∧
                e ∉ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∧
                  (C e = a ∨ C e = b) ∧
                    ∀ e' : G.edgeSet,
                      e' ≠ e →
                      e' ∉ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces →
                      e' ∈ emb.faceBoundary f →
                        ¬ (C e' = a ∨ C e' = b))
    (hblue :
      ∀ e ∈ controlEdges,
        ∃ C ∈ colorings, ∃ f : emb.Face, ∃ a b : Color,
          ValidColorPair a b ∧
            a + b = blue ∧
              e ∈ emb.faceBoundary f ∧
                e ∉ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∧
                  (C e = a ∨ C e = b) ∧
                    ∀ e' : G.edgeSet,
                      e' ≠ e →
                      e' ∉ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces →
                      e' ∈ emb.faceBoundary f →
                        ¬ (C e' = a ∨ C e' = b)) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_boundaryZeroProjectedColoringGeneratorDetector
    emb C₀ colorings hsubset
    (BoundaryZeroProjectedColoringGeneratorDetector.of_uniqueProjectedBicoloredCertificates
      controlEdges hcontrol hred hblue)

end Mettapedia.GraphTheory.FourColor
