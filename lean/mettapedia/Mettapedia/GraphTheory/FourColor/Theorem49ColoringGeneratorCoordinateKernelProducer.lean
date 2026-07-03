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

/-- All-zero predicate-indexed red/blue pairings force vanishing on every emitted predicate edge.
This is the contrapositive diagnostic form of `exists_familyPairing_ne_zero_of_edgePredicateWitness`:
if a checker has red/blue single-coordinate probes for each `P` edge and every family pairing with
`z` is zero, then no `P` edge can carry a nonzero coordinate of `z`. -/
theorem edgePredicate_vanishes_of_forall_familyPairing_eq_zero
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (P : G.edgeSet → Prop) {z : G.edgeSet → Color}
    (hpairZero :
      ∀ i : κ,
        chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color) z = 0)
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
    ∀ e : G.edgeSet, P e → z e = 0 := by
  intro e hP
  by_contra hze
  rcases exists_familyPairing_ne_zero_of_edgePredicateWitness family P
      ⟨e, hP, hze⟩ hwitnessRed hwitnessBlue with
    ⟨i, hpair⟩
  exact hpair (hpairZero i)

/-- All-zero predicate-indexed family pairings for a nonzero selected-boundary-zero chain produce
the explicit predicate obstruction used by the finite detector.  This is the reusable diagnostic
state: the current red/blue single-coordinate family failed to detect `z`, so `z` is a nonzero
boundary-zero chain invisible to every emitted predicate edge. -/
theorem exists_boundaryZeroChainObstruction_of_forall_familyPairing_eq_zero
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (P : G.edgeSet → Prop) {z : G.edgeSet → Color}
    (hzBoundary : z ∈ planarBoundaryZeroSubmodule emb)
    (hzNonzero : z ≠ 0)
    (hpairZero :
      ∀ i : κ,
        chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color) z = 0)
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
    ∃ z : G.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule emb ∧
        z ≠ 0 ∧
          ∀ e : G.edgeSet, P e → z e = 0 :=
  ⟨z, hzBoundary, hzNonzero,
    edgePredicate_vanishes_of_forall_familyPairing_eq_zero family P
      hpairZero hwitnessRed hwitnessBlue⟩

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

/-- Witness form of predicate control.  Saying that vanishing on all `P` edges forces a selected-
boundary-zero chain to vanish is equivalent to saying that every nonzero selected-boundary-zero
chain has a nonzero coordinate on some `P` edge.  This is the finite-generator form of the
control obligation. -/
theorem edgePredicateControls_iff_forall_nonzero_exists_edgePredicateWitness
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    (P : G.edgeSet → Prop) :
    (∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      (∀ e : G.edgeSet, P e → z e = 0) →
        z = 0) ↔
    (∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      z ≠ 0 →
        ∃ e : G.edgeSet, P e ∧ z e ≠ 0) := by
  constructor
  · intro hcontrol z hzBoundary hzNonzero
    by_contra hno
    apply hzNonzero
    apply hcontrol hzBoundary
    intro e hP
    by_contra hze
    exact hno ⟨e, hP, hze⟩
  · intro hwitness z hzBoundary hvanish
    by_contra hzNonzero
    rcases hwitness hzBoundary hzNonzero with ⟨e, hP, hze⟩
    exact hze (hvanish e hP)

/-- Exact obstruction boundary for predicate-indexed control.  Vanishing on all `P` edges controls
the selected-boundary-zero subspace iff no nonzero selected-boundary-zero chain vanishes on every
`P` edge.  This is the reusable algebraic success/failure boundary behind finite generator runs. -/
theorem edgePredicateControls_iff_no_boundaryZeroChainObstruction
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    (P : G.edgeSet → Prop) :
    (∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      (∀ e : G.edgeSet, P e → z e = 0) →
        z = 0) ↔
    ¬ ∃ z : G.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule emb ∧
        z ≠ 0 ∧
          ∀ e : G.edgeSet, P e → z e = 0 := by
  constructor
  · intro hcontrol hobs
    rcases hobs with ⟨z, hzBoundary, hzNonzero, hvanish⟩
    exact hzNonzero (hcontrol hzBoundary hvanish)
  · intro hno z hzBoundary hvanish
    by_contra hzNonzero
    exact hno ⟨z, hzBoundary, hzNonzero, hvanish⟩

/-- A predicate obstruction is a concrete nonzero kernel witness for a family that only tests the
red/blue single-coordinate chains on predicate edges.  This is the generator-facing failure mode:
when a finite run emits a nonzero boundary-zero chain invisible on all emitted edges, every
predicate-only red/blue probe family has a nontrivial pairing kernel and therefore cannot justify
the synthesis route by coordinate separation alone. -/
theorem exists_nonzero_mem_ker_planarBoundaryZeroFamilyPairingMap_of_boundaryZeroChainObstruction
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (P : G.edgeSet → Prop)
    (hfamily :
      ∀ i : κ,
        ∃ e : G.edgeSet, P e ∧
          (((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) = Pi.single e red ∨
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) = Pi.single e blue))
    (z : G.edgeSet → Color)
    (hzBoundary : z ∈ planarBoundaryZeroSubmodule emb)
    (hzNonzero : z ≠ 0)
    (hvanish : ∀ e : G.edgeSet, P e → z e = 0) :
    ∃ w : planarBoundaryZeroSubmodule emb,
      w ∈ LinearMap.ker (planarBoundaryZeroFamilyPairingMap family) ∧
        w ≠ 0 := by
  have hpairZero :
      ∀ i : κ,
        chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color) z = 0 := by
    intro i
    rcases hfamily i with ⟨e, hP, hred | hblue⟩
    · rw [hred, chainDotBilinForm_single_left]
      rw [hvanish e hP]
      simp [colorDot]
    · rw [hblue, chainDotBilinForm_single_left]
      rw [hvanish e hP]
      simp [colorDot]
  exact
    exists_nonzero_mem_ker_planarBoundaryZeroFamilyPairingMap_of_forall_familyPairing_eq_zero
      family hzBoundary hzNonzero hpairZero

/-- A predicate obstruction rules out a trivial family-pairing kernel for any family that only
tests red/blue single-coordinate chains on predicate edges.  This is the exact contradiction form
a finite generator can use: a returned obstruction means the current predicate-only probe family
cannot be a complete detector. -/
theorem not_ker_planarBoundaryZeroFamilyPairingMap_eq_bot_of_boundaryZeroChainObstruction
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (P : G.edgeSet → Prop)
    (hfamily :
      ∀ i : κ,
        ∃ e : G.edgeSet, P e ∧
          (((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) = Pi.single e red ∨
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) = Pi.single e blue))
    (hobs :
      ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            ∀ e : G.edgeSet, P e → z e = 0) :
    LinearMap.ker (planarBoundaryZeroFamilyPairingMap family) ≠ ⊥ := by
  intro hker
  rcases hobs with ⟨z, hzBoundary, hzNonzero, hvanish⟩
  rcases exists_nonzero_mem_ker_planarBoundaryZeroFamilyPairingMap_of_boundaryZeroChainObstruction
      family P hfamily z hzBoundary hzNonzero hvanish with
    ⟨w, hwker, hwNonzero⟩
  have hwbot : w ∈ (⊥ : Submodule F2 (planarBoundaryZeroSubmodule emb)) := by
    simpa [hker] using hwker
  exact hwNonzero (by simpa using hwbot)

/-- Detector-enrichment boundary for predicate-indexed finite generators.  If `P` has a
boundary-zero obstruction but a red/blue single-coordinate family nevertheless has trivial
family-pairing kernel, then the family must probe at least one edge outside `P`.

This is the positive form of the obstruction: a failed emitted-edge predicate tells the next
generator pass exactly what kind of new information is required. -/
theorem exists_family_singleCoordinate_outside_predicate_of_boundaryZeroChainObstruction_of_ker_eq_bot
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (P : G.edgeSet → Prop)
    (hsingle :
      ∀ i : κ,
        ∃ e : G.edgeSet,
          (((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) = Pi.single e red ∨
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) = Pi.single e blue))
    (hobs :
      ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            ∀ e : G.edgeSet, P e → z e = 0)
    (hker : LinearMap.ker (planarBoundaryZeroFamilyPairingMap family) = ⊥) :
    ∃ i : κ, ∃ e : G.edgeSet,
      ¬ P e ∧
        (((family i : projectedColoringGeneratorSubspace emb colorings) :
              G.edgeSet → Color) = Pi.single e red ∨
          ((family i : projectedColoringGeneratorSubspace emb colorings) :
              G.edgeSet → Color) = Pi.single e blue) := by
  by_contra hnoOutside
  have hfamilyInside :
      ∀ i : κ,
        ∃ e : G.edgeSet, P e ∧
          (((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) = Pi.single e red ∨
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) = Pi.single e blue) := by
    intro i
    rcases hsingle i with ⟨e, hprobe⟩
    by_cases hP : P e
    · exact ⟨e, hP, hprobe⟩
    · exfalso
      exact hnoOutside ⟨i, e, hP, hprobe⟩
  exact
    not_ker_planarBoundaryZeroFamilyPairingMap_eq_bot_of_boundaryZeroChainObstruction
      family P hfamilyInside hobs hker

/-- A trivial-kernel single-coordinate detector must contain an outside-`P` probe that actually
sees the returned obstruction.  This is the constructive enrichment form: from the obstruction
chain `z`, the next generator pass gets a concrete family member, edge, and nonzero pairing that
cannot lie inside the failed predicate. -/
theorem exists_family_singleCoordinate_outside_predicate_pairing_ne_zero_of_boundaryZeroChainObstruction_of_ker_eq_bot
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (P : G.edgeSet → Prop)
    (hsingle :
      ∀ i : κ,
        ∃ e : G.edgeSet,
          (((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) = Pi.single e red ∨
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) = Pi.single e blue))
    (z : G.edgeSet → Color)
    (hzBoundary : z ∈ planarBoundaryZeroSubmodule emb)
    (hzNonzero : z ≠ 0)
    (hvanish : ∀ e : G.edgeSet, P e → z e = 0)
    (hker : LinearMap.ker (planarBoundaryZeroFamilyPairingMap family) = ⊥) :
    ∃ i : κ, ∃ e : G.edgeSet,
      ¬ P e ∧
        (((family i : projectedColoringGeneratorSubspace emb colorings) :
              G.edgeSet → Color) = Pi.single e red ∨
          ((family i : projectedColoringGeneratorSubspace emb colorings) :
              G.edgeSet → Color) = Pi.single e blue) ∧
        chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color) z ≠ 0 ∧
        z e ≠ 0 := by
  let z' : planarBoundaryZeroSubmodule emb := ⟨z, hzBoundary⟩
  have hzmapNonzero : planarBoundaryZeroFamilyPairingMap family z' ≠ 0 := by
    intro hzmap
    have hzkerMem : z' ∈ LinearMap.ker (planarBoundaryZeroFamilyPairingMap family) := by
      simpa using hzmap
    have hzbot : z' ∈ (⊥ : Submodule F2 (planarBoundaryZeroSubmodule emb)) := by
      simpa [hker] using hzkerMem
    have hzzero' : z' = 0 := by simpa using hzbot
    have hzzero : z = 0 := by
      change ((z' : planarBoundaryZeroSubmodule emb) : G.edgeSet → Color) = 0
      simpa using congrArg Subtype.val hzzero'
    exact hzNonzero hzzero
  classical
  have hexists : ∃ i, planarBoundaryZeroFamilyPairingMap family z' i ≠ 0 := by
    by_contra hnone
    apply hzmapNonzero
    ext i
    by_contra hi
    exact hnone ⟨i, hi⟩
  rcases hexists with ⟨i, hi⟩
  rcases hsingle i with ⟨e, hprobe⟩
  have hpair : chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color) z ≠ 0 := by
    simpa [planarBoundaryZeroFamilyPairingMap, z'] using hi
  have hnotP : ¬ P e := by
    intro hP
    rcases hprobe with hred | hblue
    · apply hpair
      rw [hred, chainDotBilinForm_single_left]
      rw [hvanish e hP]
      simp [colorDot]
    · apply hpair
      rw [hblue, chainDotBilinForm_single_left]
      rw [hvanish e hP]
      simp [colorDot]
  have hze : z e ≠ 0 := by
    intro hzero
    rcases hprobe with hred | hblue
    · apply hpair
      rw [hred, chainDotBilinForm_single_left]
      rw [hzero]
      simp [colorDot]
    · apply hpair
      rw [hblue, chainDotBilinForm_single_left]
      rw [hzero]
      simp [colorDot]
  exact ⟨i, e, hnotP, hprobe, hpair, hze⟩

/-- Finite-coordinate version of predicate control.  A concrete finite edge set controls the
selected-boundary-zero chains iff every nonzero selected-boundary-zero chain is nonzero on at
least one edge of that set.  This is the rank/kernel certificate shape expected from a finite
checker. -/
theorem finsetControls_iff_forall_nonzero_exists_mem_nonzero
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    (controlEdges : Finset G.edgeSet) :
    (∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      (∀ e ∈ controlEdges, z e = 0) →
        z = 0) ↔
    (∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      z ≠ 0 →
        ∃ e : G.edgeSet, e ∈ controlEdges ∧ z e ≠ 0) := by
  constructor
  · intro hcontrol z hzBoundary hzNonzero
    by_contra hno
    apply hzNonzero
    apply hcontrol hzBoundary
    intro e he
    by_contra hze
    exact hno ⟨e, he, hze⟩
  · intro hwitness z hzBoundary hvanish
    by_contra hzNonzero
    rcases hwitness hzBoundary hzNonzero with ⟨e, he, hze⟩
    exact hze (hvanish e he)

/-- Failure certificate for a finite control check.  If vanishing on the finite control set does
not force a selected-boundary-zero chain to vanish, then there is an explicit nonzero selected-
boundary-zero chain invisible on all controlling coordinates.  This is the obstruction a finite
checker should return when the control/rank test fails. -/
theorem not_finsetControls_iff_exists_nonzero_vanishes_on_finset
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    (controlEdges : Finset G.edgeSet) :
    (¬ ∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      (∀ e ∈ controlEdges, z e = 0) →
        z = 0) ↔
    ∃ z : G.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule emb ∧
        z ≠ 0 ∧
          ∀ e ∈ controlEdges, z e = 0 := by
  constructor
  · intro hnot
    by_contra hno
    apply hnot
    intro z hzBoundary hvanish
    by_contra hzNonzero
    exact hno ⟨z, hzBoundary, hzNonzero, hvanish⟩
  · rintro ⟨z, hzBoundary, hzNonzero, hvanish⟩ hcontrol
    exact hzNonzero (hcontrol hzBoundary hvanish)

/-- A successful finite control extension must see any obstruction to the base control set on
some genuinely new edge.  This is the finite-checker analogue of the outside-probe theorem:
given a nonzero selected-boundary-zero chain invisible on `baseEdges`, any larger successful
control set must contain an edge outside `baseEdges` where the chain is nonzero. -/
theorem exists_newControlEdge_nonzero_of_vanishes_on_base_of_finsetControls
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    (baseEdges controlEdges : Finset G.edgeSet)
    (z : G.edgeSet → Color)
    (hzBoundary : z ∈ planarBoundaryZeroSubmodule emb)
    (hzNonzero : z ≠ 0)
    (hvanishBase : ∀ e ∈ baseEdges, z e = 0)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0) :
    ∃ e : G.edgeSet, e ∈ controlEdges ∧ e ∉ baseEdges ∧ z e ≠ 0 := by
  by_contra hnoNew
  apply hzNonzero
  apply hcontrol hzBoundary
  intro e heControl
  by_cases heBase : e ∈ baseEdges
  · exact hvanishBase e heBase
  · by_contra hze
    exact hnoNew ⟨e, heControl, heBase, hze⟩

/-- Extension witness for a failed finite control check.  If `baseEdges` does not control the
selected-boundary-zero chains but `controlEdges` does, then a failed-control chain identifies a
new controlling edge in `controlEdges \ baseEdges` where it is nonzero. -/
theorem exists_obstruction_and_newControlEdge_nonzero_of_not_finsetControls_of_finsetControls
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    (baseEdges controlEdges : Finset G.edgeSet)
    (hnotBase :
      ¬ ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ baseEdges, z e = 0) →
          z = 0)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0) :
    ∃ z : G.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule emb ∧
        z ≠ 0 ∧
          (∀ e ∈ baseEdges, z e = 0) ∧
            ∃ e : G.edgeSet, e ∈ controlEdges ∧ e ∉ baseEdges ∧ z e ≠ 0 := by
  rcases (not_finsetControls_iff_exists_nonzero_vanishes_on_finset
      (G := G) (emb := emb) baseEdges).1 hnotBase with
    ⟨z, hzBoundary, hzNonzero, hvanishBase⟩
  exact ⟨z, hzBoundary, hzNonzero, hvanishBase,
    exists_newControlEdge_nonzero_of_vanishes_on_base_of_finsetControls
      baseEdges controlEdges z hzBoundary hzNonzero hvanishBase hcontrol⟩

/-- Predicate-indexed coordinate separation from the witness form of control.  This is the
checker-facing route: for every nonzero selected-boundary-zero chain, emit a `P` edge where it is
nonzero; red/blue single-coordinate witnesses on `P` edges then separate all family pairings. -/
theorem familyPairing_separates_of_edgePredicateNonzeroWitnesses
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (P : G.edgeSet → Prop)
    (hnonzero :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet, P e ∧ z e ≠ 0)
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
  by_contra hzNonzeroSubtype
  have hzNonzero : (z : G.edgeSet → Color) ≠ 0 := by
    intro hz
    exact hzNonzeroSubtype (Subtype.ext hz)
  rcases hnonzero z.property hzNonzero with ⟨e, hP, hze⟩
  rcases exists_familyPairing_ne_zero_of_redBlueSingleCoordinateWitness
      family e hze (hwitnessRed e hP) (hwitnessBlue e hP) with
    ⟨i, hpairNonzero⟩
  exact hpairNonzero (hzero i)

/-- Direct producer-side kernel certificate from witness-form predicate control. -/
theorem ker_planarBoundaryZeroFamilyPairingMap_eq_bot_of_edgePredicateNonzeroWitnesses
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (P : G.edgeSet → Prop)
    (hnonzero :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet, P e ∧ z e ≠ 0)
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
    (familyPairing_separates_of_edgePredicateNonzeroWitnesses
      family P hnonzero hwitnessRed hwitnessBlue)

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

/-- Synthesis route from witness-form predicate control.  This is the most direct finite-generator
target: every nonzero selected-boundary-zero chain must expose a nonzero coordinate on an emitted
edge. -/
theorem theorem49BoundaryRootSynthesis_of_edgePredicateNonzeroWitnesses
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (P : G.edgeSet → Prop)
    (hnonzero :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet, P e ∧ z e ≠ 0)
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
    (familyPairing_separates_of_edgePredicateNonzeroWitnesses
      family P hnonzero hwitnessRed hwitnessBlue)

/-- Finite-control witness form of the same route.  This is the certificate shape returned by
the `F₂` rank check: every nonzero selected-boundary-zero chain is nonzero on at least one
listed control edge, and the family contains red/blue probes on each listed edge. -/
theorem theorem49BoundaryRootSynthesis_of_controlEdgeNonzeroWitnesses
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (controlEdges : Finset G.edgeSet)
    (hnonzero :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet, e ∈ controlEdges ∧ z e ≠ 0)
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
  theorem49BoundaryRootSynthesis_of_edgePredicateNonzeroWitnesses
    emb C₀ colorings hsubset family (fun e => e ∈ controlEdges)
    hnonzero hwitnessRed hwitnessBlue

/--
Boundary-trimmed nonzero-coverage form of finite control.  If a finite control set determines
every selected-boundary-zero chain, then every nonzero chain has a nonzero coordinate on a
controlling edge outside the selected-boundary support; selected-boundary coordinates are already
zero by definition of the boundary-zero submodule.
-/
theorem exists_nonboundary_controlEdge_nonzero_of_controlEdges
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (controlEdges : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0) :
    ∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      z ≠ 0 →
        ∃ e : G.edgeSet,
          (e ∈ controlEdges ∧
            e ∉ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
            z e ≠ 0 := by
  intro z hzBoundary hzNonzero
  rcases (finsetControls_iff_forall_nonzero_exists_mem_nonzero
      (G := G) (emb := emb) controlEdges).1 hcontrol hzBoundary hzNonzero with
    ⟨e, heControl, hze⟩
  have heNotBoundary :
      e ∉ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces := by
    intro heBoundary
    exact hze (boundaryZero_of_mem_planarBoundaryZeroSubmodule hzBoundary e heBoundary)
  exact ⟨e, ⟨heControl, heNotBoundary⟩, hze⟩

/--
Boundary-trimmed finite-control kernel route.  A finite control set may contain
selected-boundary coordinates, but the pairing-kernel certificate only needs red/blue probes on
the non-boundary controlling edges.
-/
theorem ker_planarBoundaryZeroFamilyPairingMap_eq_bot_of_controlEdges_nonBoundaryWitnesses
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
      ∀ e : G.edgeSet,
        e ∈ controlEdges →
          e ∉ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces →
            ∃ i : κ,
              ((family i : projectedColoringGeneratorSubspace emb colorings) :
                  G.edgeSet → Color) =
                Pi.single e red)
    (hwitnessBlue :
      ∀ e : G.edgeSet,
        e ∈ controlEdges →
          e ∉ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces →
            ∃ i : κ,
              ((family i : projectedColoringGeneratorSubspace emb colorings) :
                  G.edgeSet → Color) =
                Pi.single e blue) :
    LinearMap.ker (planarBoundaryZeroFamilyPairingMap family) = ⊥ :=
  ker_planarBoundaryZeroFamilyPairingMap_eq_bot_of_edgePredicateNonzeroWitnesses
    family
    (fun e => e ∈ controlEdges ∧
      e ∉ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (exists_nonboundary_controlEdge_nonzero_of_controlEdges emb controlEdges hcontrol)
    (by
      intro e he
      exact hwitnessRed e he.1 he.2)
    (by
      intro e he
      exact hwitnessBlue e he.1 he.2)

/--
Boundary-trimmed finite-control synthesis route.  A finite edge set may contain selected-boundary
coordinates, but selected-boundary-zero chains vanish on those coordinates automatically.  Thus
the projected-generator witnesses are needed only for controlling edges outside the selected
boundary support.
-/
theorem theorem49BoundaryRootSynthesis_of_controlEdges_nonBoundaryWitnesses
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
      ∀ e : G.edgeSet,
        e ∈ controlEdges →
          e ∉ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces →
            ∃ i : κ,
              ((family i : projectedColoringGeneratorSubspace emb colorings) :
                  G.edgeSet → Color) =
                Pi.single e red)
    (hwitnessBlue :
      ∀ e : G.edgeSet,
        e ∈ controlEdges →
          e ∉ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces →
            ∃ i : κ,
              ((family i : projectedColoringGeneratorSubspace emb colorings) :
                  G.edgeSet → Color) =
                Pi.single e blue) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_familyPairingKerEqBot
    emb C₀ colorings hsubset family
    (ker_planarBoundaryZeroFamilyPairingMap_eq_bot_of_controlEdges_nonBoundaryWitnesses
      family controlEdges hcontrol hwitnessRed hwitnessBlue)

/--
Canonical finite red/blue single-coordinate family generated by membership certificates.  Its
index type is exactly a controlling edge together with the red/blue choice, so the witness
obligations used by the F₂ producer lane are recovered by evaluating the family at that index.
-/
def redBlueSingleCoordinateFamily
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    (controlEdges : Finset G.edgeSet)
    (hred :
      ∀ e ∈ controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblue :
      ∀ e ∈ controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings) :
    ({e : G.edgeSet // e ∈ controlEdges} × Bool) →
      projectedColoringGeneratorSubspace emb colorings :=
  fun i =>
    if i.2 then
      ⟨Pi.single i.1.1 red, hred i.1.1 i.1.2⟩
    else
      ⟨Pi.single i.1.1 blue, hblue i.1.1 i.1.2⟩

/-- The canonical finite red/blue family contains the red probe on every controlling edge. -/
theorem redBlueSingleCoordinateFamily_witnessRed
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    (controlEdges : Finset G.edgeSet)
    (hred :
      ∀ e ∈ controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblue :
      ∀ e ∈ controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings) :
    ∀ e ∈ controlEdges,
      ∃ i : ({e : G.edgeSet // e ∈ controlEdges} × Bool),
        ((redBlueSingleCoordinateFamily controlEdges hred hblue i :
            projectedColoringGeneratorSubspace emb colorings) : G.edgeSet → Color) =
          Pi.single e red := by
  intro e he
  exact ⟨(⟨e, he⟩, true), by simp [redBlueSingleCoordinateFamily]⟩

/-- The canonical finite red/blue family contains the blue probe on every controlling edge. -/
theorem redBlueSingleCoordinateFamily_witnessBlue
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    (controlEdges : Finset G.edgeSet)
    (hred :
      ∀ e ∈ controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblue :
      ∀ e ∈ controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings) :
    ∀ e ∈ controlEdges,
      ∃ i : ({e : G.edgeSet // e ∈ controlEdges} × Bool),
        ((redBlueSingleCoordinateFamily controlEdges hred hblue i :
            projectedColoringGeneratorSubspace emb colorings) : G.edgeSet → Color) =
          Pi.single e blue := by
  intro e he
  exact ⟨(⟨e, he⟩, false), by simp [redBlueSingleCoordinateFamily]⟩

/--
Witness package for the canonical finite red/blue family.  This discharges the common
producer-side obligation of red/blue witnesses from the simpler finite certificate that the
required single-coordinate probes lie in the projected generator subspace.
-/
theorem redBlueSingleCoordinateFamily_witnesses_of_memberships
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    (controlEdges : Finset G.edgeSet)
    (hred :
      ∀ e ∈ controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblue :
      ∀ e ∈ controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings) :
    (∀ e ∈ controlEdges,
      ∃ i : ({e : G.edgeSet // e ∈ controlEdges} × Bool),
        ((redBlueSingleCoordinateFamily controlEdges hred hblue i :
            projectedColoringGeneratorSubspace emb colorings) : G.edgeSet → Color) =
          Pi.single e red) ∧
      (∀ e ∈ controlEdges,
        ∃ i : ({e : G.edgeSet // e ∈ controlEdges} × Bool),
          ((redBlueSingleCoordinateFamily controlEdges hred hblue i :
              projectedColoringGeneratorSubspace emb colorings) : G.edgeSet → Color) =
            Pi.single e blue) :=
  ⟨redBlueSingleCoordinateFamily_witnessRed controlEdges hred hblue,
    redBlueSingleCoordinateFamily_witnessBlue controlEdges hred hblue⟩

/-- Every member of the canonical red/blue family is exactly a red or blue single-coordinate
probe on one of the declared controlling edges.  This is the support-side of the exact
success/failure boundary for finite red/blue control certificates. -/
theorem redBlueSingleCoordinateFamily_singleCoordinate_mem
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    (controlEdges : Finset G.edgeSet)
    (hred :
      ∀ e ∈ controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblue :
      ∀ e ∈ controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings) :
    ∀ i : ({e : G.edgeSet // e ∈ controlEdges} × Bool),
      ∃ e : G.edgeSet, e ∈ controlEdges ∧
        (((redBlueSingleCoordinateFamily controlEdges hred hblue i :
              projectedColoringGeneratorSubspace emb colorings) : G.edgeSet → Color) =
            Pi.single e red ∨
          ((redBlueSingleCoordinateFamily controlEdges hred hblue i :
              projectedColoringGeneratorSubspace emb colorings) : G.edgeSet → Color) =
            Pi.single e blue) := by
  rintro ⟨⟨e, he⟩, choice⟩
  refine ⟨e, he, ?_⟩
  cases choice <;> simp [redBlueSingleCoordinateFamily]

/-- If a chain vanishes on the declared control set, then it pairs to zero against every member
of the canonical red/blue single-coordinate family on that set. -/
theorem forall_redBlueSingleCoordinateFamily_pairing_eq_zero_of_vanishes_on_controlEdges
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    (controlEdges : Finset G.edgeSet)
    (hred :
      ∀ e ∈ controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblue :
      ∀ e ∈ controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    {z : G.edgeSet → Color}
    (hvanish : ∀ e ∈ controlEdges, z e = 0) :
    ∀ i : ({e : G.edgeSet // e ∈ controlEdges} × Bool),
      chainDotBilinForm G.edgeSet
          (redBlueSingleCoordinateFamily controlEdges hred hblue i : G.edgeSet → Color) z =
        0 := by
  rintro ⟨⟨e, he⟩, choice⟩
  cases choice
  · change chainDotBilinForm G.edgeSet (Pi.single e blue) z = 0
    rw [chainDotBilinForm_single_left, hvanish e he]
    simp
  · change chainDotBilinForm G.edgeSet (Pi.single e red) z = 0
    rw [chainDotBilinForm_single_left, hvanish e he]
    simp

/-- Exact finite-control boundary for the canonical red/blue family.  Its family-pairing kernel
is trivial exactly when vanishing on the chosen finite control set forces every selected-
boundary-zero chain to vanish.  This is the rank-check target exported by the validation lab in
pure Lean algebraic form. -/
theorem ker_planarBoundaryZeroFamilyPairingMap_redBlueSingleCoordinateFamily_eq_bot_iff_controlEdges
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    (controlEdges : Finset G.edgeSet)
    (hred :
      ∀ e ∈ controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblue :
      ∀ e ∈ controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings) :
    LinearMap.ker
        (planarBoundaryZeroFamilyPairingMap
          (redBlueSingleCoordinateFamily controlEdges hred hblue)) = ⊥ ↔
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0 := by
  constructor
  · intro hker z hzBoundary hvanish
    let z' : planarBoundaryZeroSubmodule emb := ⟨z, hzBoundary⟩
    have hpairZero :
        ∀ i : ({e : G.edgeSet // e ∈ controlEdges} × Bool),
          chainDotBilinForm G.edgeSet
              (redBlueSingleCoordinateFamily controlEdges hred hblue i :
                G.edgeSet → Color) z = 0 :=
      forall_redBlueSingleCoordinateFamily_pairing_eq_zero_of_vanishes_on_controlEdges
        controlEdges hred hblue hvanish
    have hz' :
        z' = 0 :=
      eq_zero_of_forall_family_pairing_eq_zero_of_ker_planarBoundaryZeroFamilyPairingMap_eq_bot
        (family := redBlueSingleCoordinateFamily controlEdges hred hblue) hker
        (by
          intro i
          simpa [z'] using hpairZero i)
    change ((z' : planarBoundaryZeroSubmodule emb) : G.edgeSet → Color) = 0
    simpa [z'] using congrArg Subtype.val hz'
  · intro hcontrol
    exact
      ker_planarBoundaryZeroFamilyPairingMap_eq_bot_of_edgePredicateNonzeroWitnesses
        (redBlueSingleCoordinateFamily controlEdges hred hblue)
        (fun e => e ∈ controlEdges)
        ((finsetControls_iff_forall_nonzero_exists_mem_nonzero
          (G := G) (emb := emb) controlEdges).1 hcontrol)
        (redBlueSingleCoordinateFamily_witnessRed controlEdges hred hblue)
        (redBlueSingleCoordinateFamily_witnessBlue controlEdges hred hblue)

/-- Failure-side form of the exact finite-control boundary for the canonical red/blue family.
The family has a nontrivial selected-boundary-zero pairing kernel exactly when the finite control
set misses a nonzero selected-boundary-zero chain.  This is the Lean form of the validation lab's
`obstruction_witness` branch. -/
theorem not_ker_planarBoundaryZeroFamilyPairingMap_redBlueSingleCoordinateFamily_eq_bot_iff_exists_nonzero_vanishes_on_controlEdges
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    (controlEdges : Finset G.edgeSet)
    (hred :
      ∀ e ∈ controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblue :
      ∀ e ∈ controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings) :
    LinearMap.ker
        (planarBoundaryZeroFamilyPairingMap
          (redBlueSingleCoordinateFamily controlEdges hred hblue)) ≠ ⊥ ↔
      ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            ∀ e ∈ controlEdges, z e = 0 := by
  have hkerIff :=
    ker_planarBoundaryZeroFamilyPairingMap_redBlueSingleCoordinateFamily_eq_bot_iff_controlEdges
      controlEdges hred hblue
  constructor
  · intro hker
    have hnotControl :
        ¬ ∀ ⦃z : G.edgeSet → Color⦄,
          z ∈ planarBoundaryZeroSubmodule emb →
          (∀ e ∈ controlEdges, z e = 0) →
            z = 0 := by
      intro hcontrol
      exact hker (hkerIff.2 hcontrol)
    exact
      (not_finsetControls_iff_exists_nonzero_vanishes_on_finset
        (G := G) (emb := emb) controlEdges).1 hnotControl
  · intro hobs hker
    have hcontrol := hkerIff.1 hker
    exact
      ((not_finsetControls_iff_exists_nonzero_vanishes_on_finset
        (G := G) (emb := emb) controlEdges).2 hobs) hcontrol

/-- Success-side complement of the exact finite-control boundary for the canonical red/blue
family.  A successful red/blue rank certificate is exactly the absence of a nonzero
selected-boundary-zero chain invisible on the declared control set. -/
theorem ker_planarBoundaryZeroFamilyPairingMap_redBlueSingleCoordinateFamily_eq_bot_iff_no_nonzero_vanishes_on_controlEdges
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    (controlEdges : Finset G.edgeSet)
    (hred :
      ∀ e ∈ controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblue :
      ∀ e ∈ controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings) :
    LinearMap.ker
        (planarBoundaryZeroFamilyPairingMap
          (redBlueSingleCoordinateFamily controlEdges hred hblue)) = ⊥ ↔
      ¬ ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            ∀ e ∈ controlEdges, z e = 0 := by
  constructor
  · intro hker hobs
    exact
      ((not_ker_planarBoundaryZeroFamilyPairingMap_redBlueSingleCoordinateFamily_eq_bot_iff_exists_nonzero_vanishes_on_controlEdges
        controlEdges hred hblue).2 hobs) hker
  · intro hno
    by_contra hker
    exact hno
      ((not_ker_planarBoundaryZeroFamilyPairingMap_redBlueSingleCoordinateFamily_eq_bot_iff_exists_nonzero_vanishes_on_controlEdges
        controlEdges hred hblue).1 hker)

/--
Edge-local detector for the canonical finite red/blue family.  Once the red and blue
single-coordinate probes on the finite control set are known to lie in the projected generator
subspace, any boundary-zero chain that is nonzero on a listed edge has a nonzero pairing with
one member of the canonical family.
-/
theorem exists_familyPairing_ne_zero_of_redBlueSingleCoordinateMembership
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    (controlEdges : Finset G.edgeSet)
    (hred :
      ∀ e ∈ controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblue :
      ∀ e ∈ controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    {e : G.edgeSet} (he : e ∈ controlEdges)
    {z : G.edgeSet → Color} (hz : z e ≠ 0) :
    ∃ i : ({e : G.edgeSet // e ∈ controlEdges} × Bool),
      chainDotBilinForm G.edgeSet
          (redBlueSingleCoordinateFamily controlEdges hred hblue i : G.edgeSet → Color) z ≠
        0 :=
  exists_familyPairing_ne_zero_of_redBlueSingleCoordinateWitness
    (redBlueSingleCoordinateFamily controlEdges hred hblue) e hz
    ((redBlueSingleCoordinateFamily_witnessRed controlEdges hred hblue) e he)
    ((redBlueSingleCoordinateFamily_witnessBlue controlEdges hred hblue) e he)

/--
Theorem 4.9 synthesis directly from finite red/blue single-coordinate membership certificates.
This removes the arbitrary-family handoff from the control-edge nonzero route: the canonical
red/blue family is built from the membership proofs.
-/
theorem theorem49BoundaryRootSynthesis_of_controlEdgeNonzeroMemberships
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (controlEdges : Finset G.edgeSet)
    (hnonzero :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet, e ∈ controlEdges ∧ z e ≠ 0)
    (hred :
      ∀ e ∈ controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblue :
      ∀ e ∈ controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_controlEdgeNonzeroWitnesses
    emb C₀ colorings hsubset
    (redBlueSingleCoordinateFamily controlEdges hred hblue) controlEdges hnonzero
    (redBlueSingleCoordinateFamily_witnessRed controlEdges hred hblue)
    (redBlueSingleCoordinateFamily_witnessBlue controlEdges hred hblue)

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

/-- Bundle witness-form predicate control directly as a closed-walk family-kernel shell.  This
matches the finite checker output before converting it to a vanishing-implies-zero control
statement. -/
def ClosedWalkNeighborhoodPairingKernelShell.of_edgePredicateNonzeroWitnesses
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    (shell : ClosedWalkExactShell emb)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure shell.tait.coloring)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (P : G.edgeSet → Prop)
    (hnonzero :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet, P e ∧ z e ≠ 0)
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
    ClosedWalkNeighborhoodPairingKernelShell emb where
  exactShell := shell
  colorings := colorings
  subset_closure := hsubset
  κ := κ
  family := family
  pairingKernel_eq_bot :=
    ker_planarBoundaryZeroFamilyPairingMap_eq_bot_of_edgePredicateNonzeroWitnesses
      family P hnonzero hwitnessRed hwitnessBlue

/-- Closed-walk shell producer from a concrete finite control set in the nonzero-witness form
emitted by the validation lab. -/
def ClosedWalkNeighborhoodPairingKernelShell.of_controlEdgeNonzeroWitnesses
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    (shell : ClosedWalkExactShell emb)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure shell.tait.coloring)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (controlEdges : Finset G.edgeSet)
    (hnonzero :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet, e ∈ controlEdges ∧ z e ≠ 0)
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
    ClosedWalkNeighborhoodPairingKernelShell emb :=
  ClosedWalkNeighborhoodPairingKernelShell.of_edgePredicateNonzeroWitnesses
    shell colorings hsubset family (fun e => e ∈ controlEdges)
    hnonzero hwitnessRed hwitnessBlue

/--
Closed-walk shell producer directly from finite red/blue single-coordinate membership
certificates.  The shell's family is the canonical finite red/blue family indexed by controlling
edges, so no external family witness packet is needed.
-/
def ClosedWalkNeighborhoodPairingKernelShell.of_controlEdgeNonzeroMemberships
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    (shell : ClosedWalkExactShell emb)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure shell.tait.coloring)
    (controlEdges : Finset G.edgeSet)
    (hnonzero :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet, e ∈ controlEdges ∧ z e ≠ 0)
    (hred :
      ∀ e ∈ controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblue :
      ∀ e ∈ controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings) :
    ClosedWalkNeighborhoodPairingKernelShell emb :=
  ClosedWalkNeighborhoodPairingKernelShell.of_controlEdgeNonzeroWitnesses
    shell colorings hsubset
    (redBlueSingleCoordinateFamily controlEdges hred hblue) controlEdges hnonzero
    (redBlueSingleCoordinateFamily_witnessRed controlEdges hred hblue)
    (redBlueSingleCoordinateFamily_witnessBlue controlEdges hred hblue)

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

/-- Successor-cycle shell producer from witness-form predicate control. -/
def SuccessorCycleNeighborhoodPairingKernelShell.of_edgePredicateNonzeroWitnesses
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    (shell : SuccessorCycleExactShell emb)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure shell.tait.coloring)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (P : G.edgeSet → Prop)
    (hnonzero :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet, P e ∧ z e ≠ 0)
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
    SuccessorCycleNeighborhoodPairingKernelShell emb where
  exactShell := shell
  colorings := colorings
  subset_closure := hsubset
  κ := κ
  family := family
  pairingKernel_eq_bot :=
    ker_planarBoundaryZeroFamilyPairingMap_eq_bot_of_edgePredicateNonzeroWitnesses
      family P hnonzero hwitnessRed hwitnessBlue

/-- Successor-cycle shell producer from a concrete finite control set in nonzero-witness form. -/
def SuccessorCycleNeighborhoodPairingKernelShell.of_controlEdgeNonzeroWitnesses
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    (shell : SuccessorCycleExactShell emb)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure shell.tait.coloring)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (controlEdges : Finset G.edgeSet)
    (hnonzero :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet, e ∈ controlEdges ∧ z e ≠ 0)
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
    SuccessorCycleNeighborhoodPairingKernelShell emb :=
  SuccessorCycleNeighborhoodPairingKernelShell.of_edgePredicateNonzeroWitnesses
    shell colorings hsubset family (fun e => e ∈ controlEdges)
    hnonzero hwitnessRed hwitnessBlue

/--
Successor-cycle shell producer directly from finite red/blue single-coordinate membership
certificates, using the canonical finite red/blue family.
-/
def SuccessorCycleNeighborhoodPairingKernelShell.of_controlEdgeNonzeroMemberships
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    (shell : SuccessorCycleExactShell emb)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure shell.tait.coloring)
    (controlEdges : Finset G.edgeSet)
    (hnonzero :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet, e ∈ controlEdges ∧ z e ≠ 0)
    (hred :
      ∀ e ∈ controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblue :
      ∀ e ∈ controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings) :
    SuccessorCycleNeighborhoodPairingKernelShell emb :=
  SuccessorCycleNeighborhoodPairingKernelShell.of_controlEdgeNonzeroWitnesses
    shell colorings hsubset
    (redBlueSingleCoordinateFamily controlEdges hred hblue) controlEdges hnonzero
    (redBlueSingleCoordinateFamily_witnessRed controlEdges hred hblue)
    (redBlueSingleCoordinateFamily_witnessBlue controlEdges hred hblue)

end Mettapedia.GraphTheory.FourColor
