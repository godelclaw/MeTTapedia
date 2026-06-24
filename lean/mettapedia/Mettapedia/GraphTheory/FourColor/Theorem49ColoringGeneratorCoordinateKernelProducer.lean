import Mettapedia.GraphTheory.FourColor.Shells

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- Coordinatewise separation certificate produced by explicit single-coordinate witnesses.  If
the chosen controlling coordinates determine every selected-boundary-zero chain, and the family
contains a single-coordinate separator for every nonzero value on each controlling coordinate,
then all-zero family pairings force the whole selected-boundary-zero chain to be zero.

This is the equation-level surface a finite configuration generator can aim to emit before the
kernel and synthesis wrappers are recovered. -/
theorem familyPairing_separates_of_singleCoordinateWitnesses
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (controlEdges : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hwitness :
      ∀ e ∈ controlEdges, ∀ d : Color, d ≠ 0 →
        ∃ i : κ,
          ∃ c : Color,
            ((family i : projectedColoringGeneratorSubspace emb colorings) : G.edgeSet → Color) =
                Pi.single e c ∧
              colorDot c d ≠ 0) :
    ∀ z : planarBoundaryZeroSubmodule emb,
      (∀ i,
        chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color)
          (z : G.edgeSet → Color) = 0) →
        z = 0 := by
  intro z hzero
  apply Subtype.ext
  apply hcontrol z.property
  intro e he
  by_contra hze
  rcases hwitness e he ((z : G.edgeSet → Color) e) hze with ⟨i, c, hfamily, hcdot⟩
  have hpairZero := hzero i
  rw [hfamily, chainDotBilinForm_single_left] at hpairZero
  exact hcdot hpairZero

/-- Edge-local red/blue coordinate detector.  If a selected chain is nonzero on one edge and the
generated family contains the red and blue single-coordinate chains on that edge, then one member
of the family pairs nontrivially with the chain.  This is the algebraic witness shape consumed by
the finite separator/cocycle generator: an edge-sized obstruction becomes a concrete pairing
counterexample. -/
theorem exists_familyPairing_ne_zero_of_redBlueSingleCoordinateWitness
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (e : G.edgeSet) {z : G.edgeSet → Color}
    (hz : z e ≠ 0)
    (hwitnessRed :
      ∃ i : κ,
        ((family i : projectedColoringGeneratorSubspace emb colorings) : G.edgeSet → Color) =
          Pi.single e red)
    (hwitnessBlue :
      ∃ i : κ,
        ((family i : projectedColoringGeneratorSubspace emb colorings) : G.edgeSet → Color) =
          Pi.single e blue) :
    ∃ i : κ,
      chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color) z ≠ 0 := by
  by_cases hred : colorDot red (z e) ≠ 0
  · rcases hwitnessRed with ⟨i, hfamily⟩
    refine ⟨i, ?_⟩
    rw [hfamily, chainDotBilinForm_single_left]
    exact hred
  · have hredZero : colorDot red (z e) = 0 := by
      by_contra h
      exact hred h
    have hblue : colorDot blue (z e) ≠ 0 := by
      intro hblueZero
      have hzRed : colorDot (z e) red = 0 := by
        simpa [colorDot_comm] using hredZero
      have hzBlue : colorDot (z e) blue = 0 := by
        simpa [colorDot_comm] using hblueZero
      exact hz (color_eq_zero_of_colorDot_red_blue hzRed hzBlue)
    rcases hwitnessBlue with ⟨i, hfamily⟩
    refine ⟨i, ?_⟩
    rw [hfamily, chainDotBilinForm_single_left]
    exact hblue

/-- Predicate-indexed edge-witness form of the red/blue detector.  A finite checker may emit an
edge satisfying some local predicate `P`; if the selected chain is nonzero on that edge and the
generator family contains the red and blue single-coordinate chains there, then the family has a
nonzero pairing with the chain. -/
theorem exists_familyPairing_ne_zero_of_edgePredicateWitness
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (P : G.edgeSet → Prop) {z : G.edgeSet → Color}
    (hedge : ∃ e : G.edgeSet, P e ∧ z e ≠ 0)
    (hwitnessRed :
      ∀ e : G.edgeSet, P e →
        ∃ i : κ,
          ((family i : projectedColoringGeneratorSubspace emb colorings) : G.edgeSet → Color) =
            Pi.single e red)
    (hwitnessBlue :
      ∀ e : G.edgeSet, P e →
        ∃ i : κ,
          ((family i : projectedColoringGeneratorSubspace emb colorings) : G.edgeSet → Color) =
            Pi.single e blue) :
    ∃ i : κ,
      chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color) z ≠ 0 := by
  rcases hedge with ⟨e, hP, hz⟩
  exact exists_familyPairing_ne_zero_of_redBlueSingleCoordinateWitness
    family e hz (hwitnessRed e hP) (hwitnessBlue e hP)

/-- Predicate-indexed coordinate separation.  Instead of first materializing a finite control
set, a checker may expose a predicate `P` for its emitted edge witnesses.  If vanishing on all
`P` edges forces a selected-boundary-zero chain to vanish, and if the generator family supplies
red/blue single-coordinate chains on every `P` edge, then family pairings separate the whole
selected-boundary-zero subspace. -/
theorem familyPairing_separates_of_edgePredicateWitnesses
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (P : G.edgeSet → Prop)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e : G.edgeSet, P e → z e = 0) →
          z = 0)
    (hwitnessRed :
      ∀ e : G.edgeSet, P e →
        ∃ i : κ,
          ((family i : projectedColoringGeneratorSubspace emb colorings) : G.edgeSet → Color) =
            Pi.single e red)
    (hwitnessBlue :
      ∀ e : G.edgeSet, P e →
        ∃ i : κ,
          ((family i : projectedColoringGeneratorSubspace emb colorings) : G.edgeSet → Color) =
            Pi.single e blue) :
    ∀ z : planarBoundaryZeroSubmodule emb,
      (∀ i,
        chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color)
          (z : G.edgeSet → Color) = 0) →
        z = 0 := by
  intro z hzero
  apply Subtype.ext
  apply hcontrol z.property
  intro e hP
  by_contra hze
  rcases exists_familyPairing_ne_zero_of_redBlueSingleCoordinateWitness
      family e hze (hwitnessRed e hP) (hwitnessBlue e hP) with
    ⟨i, hpairNonzero⟩
  exact hpairNonzero (hzero i)

/-- Red/blue basis form of the coordinatewise separation certificate.  For each controlling edge
it is enough for the generated family to contain the red and blue single-coordinate chains there:
one of the two has nonzero dot product with any nonzero color on that edge. -/
theorem familyPairing_separates_of_redBlueSingleCoordinateWitnesses
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (controlEdges : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hwitnessRed :
      ∀ e ∈ controlEdges,
        ∃ i : κ,
          ((family i : projectedColoringGeneratorSubspace emb colorings) : G.edgeSet → Color) =
            Pi.single e red)
    (hwitnessBlue :
      ∀ e ∈ controlEdges,
        ∃ i : κ,
          ((family i : projectedColoringGeneratorSubspace emb colorings) : G.edgeSet → Color) =
            Pi.single e blue) :
    ∀ z : planarBoundaryZeroSubmodule emb,
      (∀ i,
        chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color)
          (z : G.edgeSet → Color) = 0) →
        z = 0 :=
by
  intro z hzero
  apply Subtype.ext
  apply hcontrol z.property
  intro e he
  by_contra hze
  rcases exists_familyPairing_ne_zero_of_redBlueSingleCoordinateWitness
      family e hze (hwitnessRed e he) (hwitnessBlue e he) with
    ⟨i, hpairNonzero⟩
  exact hpairNonzero (hzero i)

/-- Direct producer-side kernel certificate: an explicit projected-generator family has trivial
selected-boundary-zero pairing kernel once a finite set of controlling coordinates has two
ingredients:

1. vanishing on those coordinates forces vanishing of the whole chain; and
2. every nonzero value on each controlling coordinate is separated by some member of the chosen
   family that is exactly a single-coordinate chain there.

Unlike the older detector-facing theorem, this lands directly on
`LinearMap.ker (planarBoundaryZeroFamilyPairingMap family) = ⊥`, which is the certificate shape a
future verified finite `F₂` checker is expected to output. -/
theorem ker_planarBoundaryZeroFamilyPairingMap_eq_bot_of_singleCoordinateWitnesses
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (controlEdges : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hwitness :
      ∀ e ∈ controlEdges, ∀ d : Color, d ≠ 0 →
        ∃ i : κ,
          ∃ c : Color,
            ((family i : projectedColoringGeneratorSubspace emb colorings) : G.edgeSet → Color) =
                Pi.single e c ∧
              colorDot c d ≠ 0) :
    LinearMap.ker (planarBoundaryZeroFamilyPairingMap family) = ⊥ :=
  (ker_planarBoundaryZeroFamilyPairingMap_eq_bot_iff_forall_pairing_eq_zero_imp_eq_zero
    family).2
    (familyPairing_separates_of_singleCoordinateWitnesses
      family controlEdges hcontrol hwitness)

/-- Direct producer-side kernel certificate from a checker-emitted edge predicate.  The predicate
must control the selected-boundary-zero chains, and the generator family must provide red/blue
single-coordinate witnesses on every emitted edge. -/
theorem ker_planarBoundaryZeroFamilyPairingMap_eq_bot_of_edgePredicateWitnesses
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (P : G.edgeSet → Prop)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e : G.edgeSet, P e → z e = 0) →
          z = 0)
    (hwitnessRed :
      ∀ e : G.edgeSet, P e →
        ∃ i : κ,
          ((family i : projectedColoringGeneratorSubspace emb colorings) : G.edgeSet → Color) =
            Pi.single e red)
    (hwitnessBlue :
      ∀ e : G.edgeSet, P e →
        ∃ i : κ,
          ((family i : projectedColoringGeneratorSubspace emb colorings) : G.edgeSet → Color) =
            Pi.single e blue) :
    LinearMap.ker (planarBoundaryZeroFamilyPairingMap family) = ⊥ :=
  (ker_planarBoundaryZeroFamilyPairingMap_eq_bot_iff_forall_pairing_eq_zero_imp_eq_zero
    family).2
    (familyPairing_separates_of_edgePredicateWitnesses
      family P hcontrol hwitnessRed hwitnessBlue)

/-- Route form through the coordinatewise separation interface: explicit single-coordinate
witnesses for a controlling edge set already give the full theorem-4.9 synthesis package. -/
theorem theorem49BoundaryRootSynthesis_of_singleCoordinateFamilyPairingSeparation
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (controlEdges : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hwitness :
      ∀ e ∈ controlEdges, ∀ d : Color, d ≠ 0 →
        ∃ i : κ,
          ∃ c : Color,
            ((family i : projectedColoringGeneratorSubspace emb colorings) : G.edgeSet → Color) =
                Pi.single e c ∧
              colorDot c d ≠ 0) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_familyPairingSeparates emb C₀ colorings hsubset family
    (familyPairing_separates_of_singleCoordinateWitnesses
      family controlEdges hcontrol hwitness)

/-- Synthesis route for red/blue coordinate generators.  A finite generator only has to prove that
the red and blue single-coordinate chains on every controlling edge belong to the selected
projected coloring family. -/
theorem theorem49BoundaryRootSynthesis_of_redBlueSingleCoordinateFamilyPairingSeparation
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (controlEdges : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hwitnessRed :
      ∀ e ∈ controlEdges,
        ∃ i : κ,
          ((family i : projectedColoringGeneratorSubspace emb colorings) : G.edgeSet → Color) =
            Pi.single e red)
    (hwitnessBlue :
      ∀ e ∈ controlEdges,
        ∃ i : κ,
          ((family i : projectedColoringGeneratorSubspace emb colorings) : G.edgeSet → Color) =
            Pi.single e blue) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_familyPairingSeparates emb C₀ colorings hsubset family
    (familyPairing_separates_of_redBlueSingleCoordinateWitnesses
      family controlEdges hcontrol hwitnessRed hwitnessBlue)

/-- Synthesis route from a predicate-indexed finite generator.  This is the checker-facing form:
identify the emitted edge predicate, prove that the predicate controls selected-boundary-zero
chains, and provide red/blue single-coordinate generator witnesses on those emitted edges. -/
theorem theorem49BoundaryRootSynthesis_of_edgePredicateFamilyPairingSeparation
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (P : G.edgeSet → Prop)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e : G.edgeSet, P e → z e = 0) →
          z = 0)
    (hwitnessRed :
      ∀ e : G.edgeSet, P e →
        ∃ i : κ,
          ((family i : projectedColoringGeneratorSubspace emb colorings) : G.edgeSet → Color) =
            Pi.single e red)
    (hwitnessBlue :
      ∀ e : G.edgeSet, P e →
        ∃ i : κ,
          ((family i : projectedColoringGeneratorSubspace emb colorings) : G.edgeSet → Color) =
            Pi.single e blue) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_familyPairingSeparates emb C₀ colorings hsubset family
    (familyPairing_separates_of_edgePredicateWitnesses
      family P hcontrol hwitnessRed hwitnessBlue)

/-- Route form of the same producer-side certificate: explicit coordinate witnesses for a chosen
family already give the full theorem-4.9 synthesis package for the base coloring. -/
theorem theorem49BoundaryRootSynthesis_of_singleCoordinateFamilyWitnesses
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (controlEdges : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hwitness :
      ∀ e ∈ controlEdges, ∀ d : Color, d ≠ 0 →
        ∃ i : κ,
          ∃ c : Color,
            ((family i : projectedColoringGeneratorSubspace emb colorings) : G.edgeSet → Color) =
                Pi.single e c ∧
              colorDot c d ≠ 0) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_familyPairingKerEqBot emb C₀ colorings hsubset family
    (ker_planarBoundaryZeroFamilyPairingMap_eq_bot_of_singleCoordinateWitnesses
      family controlEdges hcontrol hwitness)

/-- Bundle the same explicit coordinate certificate directly as a closed-walk family-kernel shell.
This is the first non-legacy shell-facing producer surface for the finite `F₂` lane. -/
def ClosedWalkNeighborhoodPairingKernelShell.of_singleCoordinateWitnesses
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    (shell : ClosedWalkExactShell emb)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure shell.tait.coloring)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (controlEdges : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hwitness :
      ∀ e ∈ controlEdges, ∀ d : Color, d ≠ 0 →
        ∃ i : κ,
          ∃ c : Color,
            ((family i : projectedColoringGeneratorSubspace emb colorings) : G.edgeSet → Color) =
                Pi.single e c ∧
              colorDot c d ≠ 0) :
    ClosedWalkNeighborhoodPairingKernelShell emb where
  exactShell := shell
  colorings := colorings
  subset_closure := hsubset
  κ := κ
  family := family
  pairingKernel_eq_bot :=
    ker_planarBoundaryZeroFamilyPairingMap_eq_bot_of_singleCoordinateWitnesses
      family controlEdges hcontrol hwitness

/-- Successor-cycle version of the same shell-facing producer. -/
def SuccessorCycleNeighborhoodPairingKernelShell.of_singleCoordinateWitnesses
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    (shell : SuccessorCycleExactShell emb)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure shell.tait.coloring)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (controlEdges : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hwitness :
      ∀ e ∈ controlEdges, ∀ d : Color, d ≠ 0 →
        ∃ i : κ,
          ∃ c : Color,
            ((family i : projectedColoringGeneratorSubspace emb colorings) : G.edgeSet → Color) =
                Pi.single e c ∧
              colorDot c d ≠ 0) :
    SuccessorCycleNeighborhoodPairingKernelShell emb where
  exactShell := shell
  colorings := colorings
  subset_closure := hsubset
  κ := κ
  family := family
  pairingKernel_eq_bot :=
    ker_planarBoundaryZeroFamilyPairingMap_eq_bot_of_singleCoordinateWitnesses
      family controlEdges hcontrol hwitness

end Mettapedia.GraphTheory.FourColor
