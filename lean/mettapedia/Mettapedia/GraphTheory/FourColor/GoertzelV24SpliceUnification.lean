import Mettapedia.GraphTheory.FourColor.GoertzelV24ReductiveSpine
import Mettapedia.GraphTheory.FourColor.GoertzelV24RetainedVertexTaitSplice
import Mettapedia.GraphTheory.FourColor.GoertzelV24RetainedSpliceEuler
import Mettapedia.GraphTheory.FourColor.GoertzelV24CorridorSpliceObservables

/-!
# Splice interfaces for the compositional route

The source uses equal finite corridor profiles in two different directions.
For Addendum XXVII's closed-web shrinking step, the input already contains a
Tait coloring and equal profiles transport that witness *forward* to the
shortened object.  For the Seed/zero-count engine, a separate semantic
completion theorem may be needed to transport absence of an accepted output
*backward*.  These directions must not be conflated.

The corridor profile records boundary colors, tracked connectivity, and
capped face progress.  This file does not replace that state by an unproved
semantic surrogate.  It packages the concrete retained-vertex splice and
separates the logically different obligations:

* profile identity gives the forward coloring and its visible splice
  observables for the closed-web route;
* deleting a genuinely absent vertex gives strict size decrease;
* reverse semantic completion, used only where the zero-count route calls
  for it, is stated explicitly.

Keeping the last item separate prevents a one-way closed-web witness
transport from being silently promoted to a counterexample-preservation
claim about an unrelated target predicate.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SpliceUnification

open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24OrderedCutRotationSplice
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24OrderedCutOldFaceReturn
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RetainedVertexTaitSplice
open GoertzelV24RetainedSpliceEdgeDecomposition
open GoertzelV24RetainedSpliceEuler
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationSpliceConstructor
open GoertzelV24CurvatureScope
open GoertzelV24CorridorProfile
open GoertzelV24CorridorSpliceObservables
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24WindingClassification

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- An auxiliary colorability target for the separate reverse-completion
adapter.  It is not the closed-web-at-good-word witness used by the source's
forward Shrinking Lemma. -/
abbrev TaitColorable (RS : RotationSystem V E) : Prop :=
  ∃ C : RS.EdgeColoring Color, RS.IsTaitEdgeColoring C

/-! ## Concrete splice data -/

structure OrderedCutSpliceData
    (RS : RotationSystem V E)
    (n terminalCount faceFragmentCount : Nat) where
  keep : V → Prop
  left : GraphCorridorCutData RS n terminalCount faceFragmentCount
  right : GraphCorridorCutData RS n terminalCount faceFragmentCount
  leftCrosses : ∀ step, ∃ dart : RS.D,
    RS.edgeOf dart = left.crossingEdge step ∧
    keep (RS.vertOf dart) ∧
    ¬ keep (RS.vertOf (RS.alpha dart))
  rightCrosses : ∀ step, ∃ dart : RS.D,
    RS.edgeOf dart = right.crossingEdge step ∧
    keep (RS.vertOf dart) ∧
    ¬ keep (RS.vertOf (RS.alpha dart))
  leftInjective : Function.Injective left.crossingEdge
  rightInjective : Function.Injective right.crossingEdge
  cover : ∀ dart : BoundaryDart RS keep,
    RS.edgeOf dart.1.1 ∈ orderedCut left.crossingEdge ∨
      RS.edgeOf dart.1.1 ∈ orderedCut right.crossingEdge
  disjoint : Disjoint (orderedCut left.crossingEdge)
    (orderedCut right.crossingEdge)
  outer_kept : keep (RS.vertOf RS.outer)
  seamEndpoints : ∀ step,
    RS.vertOf
        (orderedBoundaryDart RS keep left.crossingEdge
          leftCrosses step).1.1.1 ≠
      RS.vertOf
        (orderedBoundaryDart RS keep right.crossingEdge
          rightCrosses step).1.1.1
  removed : V
  removed_not_kept : ¬ keep removed

/-! ## Port correspondences and profile relabelling

The finite profile has numbered ports, while the source's two transversals
come with their own geometric correspondence.  A finite-type enumeration is
not itself a transversal order.  The definitions in this section make the
correspondence explicit, so a future chord/annulus construction must supply
the actual matching rather than silently using an arbitrary enumeration.
-/

/-- Simultaneous relabelling of the three finite coordinate families in a
corridor profile.  The crossing component is the one used by the seam;
terminal and fragment relabellings keep the complete profile honest. -/
structure CorridorProfileIndexing
    (crossingEdgeCount terminalCount faceFragmentCount : Nat) where
  crossing : Equiv.Perm (Fin crossingEdgeCount)
  terminal : Equiv.Perm (Fin terminalCount)
  fragment : Equiv.Perm (Fin faceFragmentCount)

namespace CorridorProfileIndexing

variable {n terminalCount faceFragmentCount : Nat}

/-- The unchanged coordinate system. -/
def id : CorridorProfileIndexing n terminalCount faceFragmentCount where
  crossing := Equiv.refl _
  terminal := Equiv.refl _
  fragment := Equiv.refl _

/-- Relabel a crossing-or-terminal port. -/
def port (indexing : CorridorProfileIndexing n terminalCount faceFragmentCount) :
    CorridorPort n terminalCount → CorridorPort n terminalCount
  | .inl crossing => .inl (indexing.crossing crossing)
  | .inr terminal => .inr (indexing.terminal terminal)

@[simp] theorem port_inl
    (indexing : CorridorProfileIndexing n terminalCount faceFragmentCount)
    (crossing : Fin n) :
    indexing.port (.inl crossing) = .inl (indexing.crossing crossing) :=
  rfl

@[simp] theorem port_inr
    (indexing : CorridorProfileIndexing n terminalCount faceFragmentCount)
    (terminal : Fin terminalCount) :
    indexing.port (.inr terminal) = .inr (indexing.terminal terminal) :=
  rfl

end CorridorProfileIndexing

/-- Relabel raw cut data without changing its underlying region. -/
def reindexGraphCorridorCutData
    {RS : RotationSystem V E}
    {n terminalCount faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS n terminalCount faceFragmentCount)
    (indexing : CorridorProfileIndexing n terminalCount faceFragmentCount) :
    GraphCorridorCutData RS n terminalCount faceFragmentCount where
  regionEdges := data.regionEdges
  crossingEdge := fun index => data.crossingEdge (indexing.crossing index)
  terminalEdge := fun index => data.terminalEdge (indexing.terminal index)
  fragmentFace := fun index => data.fragmentFace (indexing.fragment index)
  fragmentEdges := fun index => data.fragmentEdges (indexing.fragment index)

omit [Fintype E] in
/-- Reordering an injective crossing list does not change its underlying cut
set.  It says nothing about geometric order; that information remains in the
caller-supplied correspondence. -/
theorem orderedCut_reindex
    {n : Nat} (crossingEdge : Fin n → E)
    (permutation : Equiv.Perm (Fin n)) :
    orderedCut (fun index => crossingEdge (permutation index)) =
      orderedCut crossingEdge := by
  ext edge
  simp only [orderedCut, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨index, hvalue⟩
    exact ⟨permutation index, hvalue⟩
  · rintro ⟨index, hvalue⟩
    refine ⟨permutation.symm index, ?_⟩
    simpa using hvalue

/-- The two raw cut sides before a particular seam matching is chosen.  This
is deliberately separate from `OrderedCutSpliceData`: source geometry must
first choose a port correspondence, then prove the resulting seam is valid. -/
structure OrderedCutSidesData
    (RS : RotationSystem V E)
    (n terminalCount faceFragmentCount : Nat) where
  keep : V → Prop
  left : GraphCorridorCutData RS n terminalCount faceFragmentCount
  right : GraphCorridorCutData RS n terminalCount faceFragmentCount
  leftCrosses : ∀ step, ∃ dart : RS.D,
    RS.edgeOf dart = left.crossingEdge step ∧
    keep (RS.vertOf dart) ∧
    ¬ keep (RS.vertOf (RS.alpha dart))
  rightCrosses : ∀ step, ∃ dart : RS.D,
    RS.edgeOf dart = right.crossingEdge step ∧
    keep (RS.vertOf dart) ∧
    ¬ keep (RS.vertOf (RS.alpha dart))
  leftInjective : Function.Injective left.crossingEdge
  rightInjective : Function.Injective right.crossingEdge
  cover : ∀ dart : BoundaryDart RS keep,
    RS.edgeOf dart.1.1 ∈ orderedCut left.crossingEdge ∨
      RS.edgeOf dart.1.1 ∈ orderedCut right.crossingEdge
  disjoint : Disjoint (orderedCut left.crossingEdge)
    (orderedCut right.crossingEdge)
  outer_kept : keep (RS.vertOf RS.outer)
  removed : V
  removed_not_kept : ¬ keep removed

namespace OrderedCutSidesData

variable {RS : RotationSystem V E}
  {n terminalCount faceFragmentCount : Nat}

/-- Install one explicitly certified seam correspondence on otherwise raw
cut sides.  The correspondence is intentionally an argument, not an
enumeration convention. -/
def splice
    (data : OrderedCutSidesData RS n terminalCount faceFragmentCount)
    (seamEndpoints : ∀ step,
      RS.vertOf
          (orderedBoundaryDart RS data.keep data.left.crossingEdge
            data.leftCrosses step).1.1.1 ≠
        RS.vertOf
          (orderedBoundaryDart RS data.keep data.right.crossingEdge
            data.rightCrosses step).1.1.1) :
    OrderedCutSpliceData RS n terminalCount faceFragmentCount where
  keep := data.keep
  left := data.left
  right := data.right
  leftCrosses := data.leftCrosses
  rightCrosses := data.rightCrosses
  leftInjective := data.leftInjective
  rightInjective := data.rightInjective
  cover := data.cover
  disjoint := data.disjoint
  outer_kept := data.outer_kept
  seamEndpoints := seamEndpoints
  removed := data.removed
  removed_not_kept := data.removed_not_kept

/-- Forget the particular seam pairing while retaining the two certified cut
sides. -/
def ofSplice
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount) :
    OrderedCutSidesData RS n terminalCount faceFragmentCount where
  keep := data.keep
  left := data.left
  right := data.right
  leftCrosses := data.leftCrosses
  rightCrosses := data.rightCrosses
  leftInjective := data.leftInjective
  rightInjective := data.rightInjective
  cover := data.cover
  disjoint := data.disjoint
  outer_kept := data.outer_kept
  removed := data.removed
  removed_not_kept := data.removed_not_kept

/-- Relabel the right cut by a caller-supplied port correspondence.  All
cut-set facts are preserved by bijectivity; the new seam-endpoint condition
is deliberately *not* derived here and must be supplied by the geometry. -/
def reindexRight
    (data : OrderedCutSidesData RS n terminalCount faceFragmentCount)
    (indexing : CorridorProfileIndexing n terminalCount faceFragmentCount) :
    OrderedCutSidesData RS n terminalCount faceFragmentCount where
  keep := data.keep
  left := data.left
  right := reindexGraphCorridorCutData data.right indexing
  leftCrosses := data.leftCrosses
  rightCrosses := fun step => data.rightCrosses (indexing.crossing step)
  leftInjective := data.leftInjective
  rightInjective := by
    intro first second heq
    apply indexing.crossing.injective
    apply data.rightInjective
    exact heq
  cover := by
    intro dart
    have hcut :
        orderedCut (reindexGraphCorridorCutData data.right indexing).crossingEdge =
          orderedCut data.right.crossingEdge :=
      orderedCut_reindex data.right.crossingEdge indexing.crossing
    rw [hcut]
    exact data.cover dart
  disjoint := by
    have hcut :
        orderedCut (reindexGraphCorridorCutData data.right indexing).crossingEdge =
          orderedCut data.right.crossingEdge :=
      orderedCut_reindex data.right.crossingEdge indexing.crossing
    rw [hcut]
    exact data.disjoint
  outer_kept := data.outer_kept
  removed := data.removed
  removed_not_kept := data.removed_not_kept

end OrderedCutSidesData

namespace OrderedCutSpliceData

variable {RS : RotationSystem V E}
  {n terminalCount faceFragmentCount : Nat}

/-- The concrete shortened rotation system.  Every proof argument is retained
in the definition, so later statements cannot accidentally use a different
seam than the one certified by the data. -/
def output (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount) :
    RotationSystem (RetainedVertex data.keep)
      (orderedCutRetainedVertexRewiredDartSystem RS data.keep
        data.left.crossingEdge data.right.crossingEdge
        data.leftCrosses data.rightCrosses data.leftInjective
        data.rightInjective data.cover data.disjoint data.outer_kept
        data.seamEndpoints).Edge :=
  orderedCutRetainedVertexRotationSystem RS data.keep
    data.left.crossingEdge data.right.crossingEdge
    data.leftCrosses data.rightCrosses data.leftInjective
    data.rightInjective data.cover data.disjoint data.outer_kept
    data.seamEndpoints

/-- The size used for this local reduction is the retained vertex carrier. -/
def outputSize (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount) :
    Nat := Fintype.card (RetainedVertex data.keep)

theorem outputSize_lt (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount) :
    data.outputSize < Fintype.card V := by
  exact card_retainedVertex_lt data.keep data.removed data.removed_not_kept

/-! ## The geometric and face-safety parts of the source checklist -/

/-- The local Euler equation for this exact cut.  It is a computed equation
about the deleted annulus, not a global planarity assertion smuggled into the
splice. -/
def LocalEulerBalance
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount) : Prop :=
  RetainedSpliceLocalEulerBalance RS data.keep
    data.left.crossingEdge data.right.crossingEdge
    data.leftCrosses data.rightCrosses data.leftInjective
    data.rightInjective data.cover data.disjoint data.outer_kept

/-- Cubicity of the shortened map is a direct consequence of the concrete
ordered rewiring; it does not depend on the later semantic-profile argument. -/
theorem output_isCubic
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (hcubic : RS.IsCubic) :
    data.output.IsCubic := by
  exact orderedCutRetainedVertexRotationSystem_isCubic RS data.keep
    data.left.crossingEdge data.right.crossingEdge
    data.leftCrosses data.rightCrosses data.leftInjective
    data.rightInjective data.cover data.disjoint data.outer_kept
    data.seamEndpoints hcubic

/-- The spherical-map part of the output follows from the ambient spherical
map and the explicit local Euler balance.  This isolates the source's
topological bookkeeping from color transport. -/
theorem output_sphericalCubicMapData
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (hambient : SphericalCubicMapData RS)
    (hbalance : data.LocalEulerBalance) :
    SphericalCubicMapData data.output := by
  exact sphericalCubicMapData_orderedCutRetainedVertexRotationSystem
    RS data.keep data.left.crossingEdge data.right.crossingEdge
    data.leftCrosses data.rightCrosses data.leftInjective
    data.rightInjective data.cover data.disjoint data.outer_kept
    data.seamEndpoints hambient hbalance

/-- The seam-local face condition required by the retained splice.  The
profile is read from the old map before rewiring, so this is exactly the
source's capped partial-face bookkeeping obligation. -/
def SeamFacesMeetFive
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount) : Prop :=
  ∀ position : OrderedSeamPosition n,
    OrderedCutFaceReturnProfile.FaceMeetsFive
      (oldRotationOrderedCutFaceReturnProfile RS data.keep
        data.left.crossingEdge data.right.crossingEdge
        data.leftCrosses data.rightCrosses data.leftInjective
        data.rightInjective data.cover data.disjoint data.outer_kept)
      position

/-- Every newly sewn seam face meets the five-edge lower bound when the old
faces and the computed return profile do.  This discharges the face-bound
part of a splice without claiming anything about the still-pending semantic
completion direction. -/
theorem output_seamFace_meets_five
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (hminimum : ∀ dart : RS.D, 5 ≤ (RS.faceOrbit dart).card)
    (hprofile : data.SeamFacesMeetFive)
    (root : MatchedSeam.Dart (InternalDart RS data.keep)
      (BoundaryDartOn RS data.keep (orderedCut data.left.crossingEdge))
      (BoundaryDartOn RS data.keep (orderedCut data.right.crossingEdge))) :
    5 ≤ (data.output.faceOrbit root).card := by
  exact five_le_all_retainedVertexRotationSystem_faceOrbits_of_oldProfile
    RS data.keep data.left.crossingEdge data.right.crossingEdge
    data.leftCrosses data.rightCrosses data.leftInjective
    data.rightInjective data.cover data.disjoint data.outer_kept
    data.seamEndpoints hminimum hprofile root

/-! ## Profile identity and the forward coloring direction -/

structure EqualProfile
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount) where
  coloring : RS.EdgeColoring Color
  coloring_isTait : RS.IsTaitEdgeColoring coloring
  profile_eq : data.left.profile coloring coloring_isTait =
    data.right.profile coloring coloring_isTait

/-- The profile state is the exact finite datum consumed by the existing
ordered-cut coloring theorem; no extra boundary-color equality is hidden. -/
theorem profile_boundary_color_eq
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (profile : data.EqualProfile) (step : Fin n) :
    profile.coloring (data.left.crossingEdge step) =
      profile.coloring (data.right.crossingEdge step) := by
  exact crossingEdge_color_eq_of_profiles_eq data.left data.right
    profile.coloring profile.coloring profile.coloring_isTait
    profile.coloring_isTait profile.profile_eq step

def splicedColoring
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (profile : data.EqualProfile) : data.output.EdgeColoring Color :=
  orderedCutRetainedVertexSplicedColoring RS data.keep
    data.left.crossingEdge data.right.crossingEdge
    data.leftCrosses data.rightCrosses data.leftInjective
    data.rightInjective data.cover data.disjoint data.outer_kept
    data.seamEndpoints profile.coloring
    (fun step => profile_boundary_color_eq data profile step)

theorem splicedColoring_isTait
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (profile : data.EqualProfile) :
    data.output.IsTaitEdgeColoring (data.splicedColoring profile) := by
  exact orderedCutRetainedVertexSplicedColoring_isTait_of_profiles_eq
    RS data.keep data.left data.right data.leftCrosses data.rightCrosses
    data.leftInjective data.rightInjective data.cover data.disjoint
    data.outer_kept data.seamEndpoints profile.coloring
    profile.coloring_isTait profile.profile_eq

theorem output_taitColorable_of_equalProfile
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (profile : data.EqualProfile) :
    TaitColorable data.output :=
  ⟨data.splicedColoring profile, data.splicedColoring_isTait profile⟩

/-! ## What finite profile equality already preserves -/

/-- Equal computed profiles preserve the visible two-color connectivity of
the two candidate regions.  This is the source's matching-structure item at
the port interface, not yet a statement about every possible coloring of an
open region. -/
theorem EqualProfile.trackedPortReachability_iff
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (profile : data.EqualProfile)
    (pair : TrackedColorPair)
    (first second : CorridorPort n terminalCount) :
    (data.left.portEdge first ∈ data.left.regionEdges ∧
      data.left.portEdge second ∈ data.left.regionEdges ∧
      IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2
        (profile.coloring (data.left.portEdge first)) ∧
      IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2
        (profile.coloring (data.left.portEdge second)) ∧
      (regionalTrackedEdgeGraph RS data.left.regionEdges profile.coloring
        (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2).Reachable
          (data.left.portEdge first) (data.left.portEdge second)) ↔
    (data.right.portEdge first ∈ data.right.regionEdges ∧
      data.right.portEdge second ∈ data.right.regionEdges ∧
      IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2
        (profile.coloring (data.right.portEdge first)) ∧
      IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2
        (profile.coloring (data.right.portEdge second)) ∧
      (regionalTrackedEdgeGraph RS data.right.regionEdges profile.coloring
        (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2).Reachable
          (data.right.portEdge first) (data.right.portEdge second)) := by
  exact trackedPortReachability_iff_of_profiles_eq data.left data.right
    profile.coloring profile.coloring profile.coloring_isTait
    profile.coloring_isTait profile.profile_eq pair first second

/-- Equal profiles preserve which named regional face fragments belong to a
common ambient face.  This is the finite interface form of the splice's face
matching condition. -/
theorem EqualProfile.fragmentsPairwiseShareFace_iff
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (profile : data.EqualProfile)
    (fragments : Finset (Fin faceFragmentCount)) :
    (∀ first ∈ fragments, ∀ second ∈ fragments,
      data.left.fragmentFace first = data.left.fragmentFace second) ↔
    (∀ first ∈ fragments, ∀ second ∈ fragments,
      data.right.fragmentFace first = data.right.fragmentFace second) := by
  exact fragmentsPairwiseShareFace_iff_of_profiles_eq data.left data.right
    profile.coloring profile.coloring profile.coloring_isTait
    profile.coloring_isTait profile.profile_eq fragments

/-- Equal capped profiles preserve the minimum-five test after the same
exterior contribution is attached to a named face fragment. -/
theorem EqualProfile.five_le_fragment_length_add_iff
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (profile : data.EqualProfile)
    (fragment : Fin faceFragmentCount) (outsideLength : Nat) :
    5 ≤ (data.left.regionalFragmentEdges fragment).card + outsideLength ↔
      5 ≤ (data.right.regionalFragmentEdges fragment).card + outsideLength := by
  exact five_le_fragment_length_add_iff_of_profiles_eq data.left data.right
    profile.coloring profile.coloring profile.coloring_isTait
    profile.coloring_isTait profile.profile_eq fragment outsideLength

/-- The same face-bound preservation composes over any selected family of
fragments, as required when a seam face is assembled from several pieces. -/
theorem EqualProfile.five_le_fragment_sum_add_iff
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (profile : data.EqualProfile)
    (fragments : Finset (Fin faceFragmentCount)) (outsideLength : Nat) :
    5 ≤ (∑ fragment ∈ fragments,
      (data.left.regionalFragmentEdges fragment).card) + outsideLength ↔
      5 ≤ (∑ fragment ∈ fragments,
        (data.right.regionalFragmentEdges fragment).card) + outsideLength := by
  exact five_le_fragment_sum_add_iff_of_profiles_eq data.left data.right
    profile.coloring profile.coloring profile.coloring_isTait
    profile.coloring_isTait profile.profile_eq fragments outsideLength

/-! ## Optional reverse completion for the zero-count route -/

/-- The semantic descent obligation for an auxiliary zero-count reduction:
every Tait coloring of the shortened object can be completed back to a Tait
coloring of the original object.  This is deliberately separate from the
source's closed-web shrinking witness, whose direction is forward. -/
def ReverseCompletion
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount) : Prop :=
  ∀ coloring : data.output.EdgeColoring Color,
    data.output.IsTaitEdgeColoring coloring →
      TaitColorable (RS := RS)

theorem not_taitColorable_output_of_not_taitColorable
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (hcompletion : data.ReverseCompletion)
    (hbad : ¬ TaitColorable (RS := RS)) :
    ¬ TaitColorable data.output := by
  intro houtput
  rcases houtput with ⟨coloring, hcoloring⟩
  exact hbad (hcompletion coloring hcoloring)

/-! ## Semantic boundary profiles -/

/-- A boundary color word for an ordered `n`-port seam. -/
abbrev BoundaryColorWord (n : Nat) := Fin n → Color

/-- The semantic profile carrier: the boundary words that extend across a
region.  The concrete region and extension predicate are supplied by the
caller; this carrier is intentionally independent of the finite syntactic
`CorridorCutProfile`. -/
abbrev SemanticBoundaryProfile (n : Nat) := Set (BoundaryColorWord n)

/-- A semantic profile factors through a finite code when membership in each
region's extendable-word set is determined by the same code on the boundary
word, with only the region's target code allowed to differ.  This is the
precise bridge needed to turn a finite profile repeat into equality of
semantic profiles; it is not asserted for `CorridorCutProfile` until its
extension-invariance theorem has been proved. -/
structure SemanticProfileFactor (n : Nat) where
  Code : Type*
  code : BoundaryColorWord n → Code
  inner : SemanticBoundaryProfile n
  outer : SemanticBoundaryProfile n
  innerCode : Code
  outerCode : Code
  inner_mem_iff : ∀ word, word ∈ inner ↔ code word = innerCode
  outer_mem_iff : ∀ word, word ∈ outer ↔ code word = outerCode

theorem SemanticProfileFactor.equal_of_target_eq
    (factor : SemanticProfileFactor n)
    (htarget : factor.innerCode = factor.outerCode) :
    factor.inner = factor.outer := by
  ext word
  rw [factor.inner_mem_iff, factor.outer_mem_iff, htarget]

/-- The seam word seen by a coloring of the shortened object. -/
def seamColorWord
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (coloring : data.output.EdgeColoring Color) : BoundaryColorWord n :=
  fun step => coloring (orderedCutSeamSpliceEdge RS data.keep
    data.left.crossingEdge data.right.crossingEdge data.leftCrosses
    data.rightCrosses data.leftInjective data.rightInjective data.cover
    data.disjoint data.outer_kept data.seamEndpoints step)

/-- A semantic bridge for one concrete splice.  Its two sets are the actual
extendable boundary-word sets for the inner and outer regions.  The final
field is the genuine gluing theorem: once a shortened coloring has a word in
the outer set, it can be completed to an original coloring. -/
structure SemanticProfileBridge
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount) where
  inner : SemanticBoundaryProfile n
  outer : SemanticBoundaryProfile n
  equal : inner = outer
  shortened_word_mem_inner :
    ∀ coloring : data.output.EdgeColoring Color,
      data.output.IsTaitEdgeColoring coloring →
        seamColorWord data coloring ∈ inner
  complete_of_outer_word :
    ∀ coloring : data.output.EdgeColoring Color,
      data.output.IsTaitEdgeColoring coloring →
        seamColorWord data coloring ∈ outer →
          TaitColorable (RS := RS)

/-- Build the concrete bridge from a factorization witness.  The only
non-definitional ingredient is the region gluing theorem in
`complete_of_outer_word`; `equal` is now a proved consequence of finite-code
factorization rather than a free semantic equality field. -/
def SemanticProfileBridge.ofFactor
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (factor : SemanticProfileFactor n)
    (htarget : factor.innerCode = factor.outerCode)
    (shortened_word_mem_inner :
      ∀ coloring : data.output.EdgeColoring Color,
        data.output.IsTaitEdgeColoring coloring →
          seamColorWord data coloring ∈ factor.inner)
    (complete_of_outer_word :
      ∀ coloring : data.output.EdgeColoring Color,
        data.output.IsTaitEdgeColoring coloring →
          seamColorWord data coloring ∈ factor.outer →
            TaitColorable (RS := RS)) :
    data.SemanticProfileBridge where
  inner := factor.inner
  outer := factor.outer
  equal := factor.equal_of_target_eq htarget
  shortened_word_mem_inner := shortened_word_mem_inner
  complete_of_outer_word := complete_of_outer_word

theorem reverseCompletion_of_semanticProfileBridge
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (bridge : data.SemanticProfileBridge) :
    data.ReverseCompletion := by
  intro coloring hcoloring
  apply bridge.complete_of_outer_word coloring hcoloring
  rw [← bridge.equal]
  exact bridge.shortened_word_mem_inner coloring hcoloring

theorem not_taitColorable_output_of_semanticProfileBridge
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (bridge : data.SemanticProfileBridge)
    (hbad : ¬ TaitColorable (RS := RS)) :
    ¬ TaitColorable data.output := by
  exact data.not_taitColorable_output_of_not_taitColorable
    (reverseCompletion_of_semanticProfileBridge data bridge) hbad

/-- A completed auxiliary zero-count step has the two reductive facts needed
by that adapter: strict descent and preservation of non-colorability.  It is
not by itself the closed-web Shrinking Lemma, whose predicate additionally
records the source's good-word and closure data.  The theorem is kept at the
fixed-rotation-system level because the eventual object family must still
choose a uniform carrier for varying vertex and edge types. -/
structure CompletedStep
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount) where
  reverse_completion : data.ReverseCompletion

theorem completedStep_strict_size
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (_step : data.CompletedStep) :
    data.outputSize < Fintype.card V :=
  data.outputSize_lt

theorem completedStep_counterexample_preserved
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (step : data.CompletedStep)
    (hbad : ¬ TaitColorable (RS := RS)) :
    ¬ TaitColorable data.output :=
  data.not_taitColorable_output_of_not_taitColorable
    step.reverse_completion hbad

end OrderedCutSpliceData

namespace OrderedCutSidesData

variable {RS : RotationSystem V E}
  {n terminalCount faceFragmentCount : Nat}

/-- A source-facing profile-aligned splice.  The indexing is the intended
correspondence between the two geometric transversals; profile equality is
checked only after the right interface has been relabelled along it.  This
does not assert noncrossing or spherical output on its own: those remain the
separate local-Euler and face-return obligations of Addendum XXVII. -/
structure ProfileAlignedSplice
    (data : OrderedCutSidesData RS n terminalCount faceFragmentCount) where
  indexing : CorridorProfileIndexing n terminalCount faceFragmentCount
  seamEndpoints : ∀ step,
    RS.vertOf
        (orderedBoundaryDart RS
          (data.reindexRight indexing).keep
          (data.reindexRight indexing).left.crossingEdge
          (data.reindexRight indexing).leftCrosses step).1.1.1 ≠
      RS.vertOf
        (orderedBoundaryDart RS
          (data.reindexRight indexing).keep
          (data.reindexRight indexing).right.crossingEdge
          (data.reindexRight indexing).rightCrosses step).1.1.1
  coloring : RS.EdgeColoring Color
  coloring_isTait : RS.IsTaitEdgeColoring coloring
  profile_eq :
    (data.reindexRight indexing).left.profile coloring coloring_isTait =
      (data.reindexRight indexing).right.profile coloring coloring_isTait

/-- The concrete retained-vertex splice selected by a profile-aligned port
correspondence. -/
def ProfileAlignedSplice.spliceData
    {data : OrderedCutSidesData RS n terminalCount faceFragmentCount}
    (aligned : ProfileAlignedSplice data) :
    OrderedCutSpliceData RS n terminalCount faceFragmentCount :=
  (data.reindexRight aligned.indexing).splice aligned.seamEndpoints

/-- The aligned source profile is exactly the fixed-index equality required
by the existing concrete color-splice theorem. -/
def ProfileAlignedSplice.equalProfile
    {data : OrderedCutSidesData RS n terminalCount faceFragmentCount}
    (aligned : ProfileAlignedSplice data) :
    aligned.spliceData.EqualProfile where
  coloring := aligned.coloring
  coloring_isTait := aligned.coloring_isTait
  profile_eq := aligned.profile_eq

/-- Equal profiles along the supplied transversal correspondence transport
the existing Tait witness to the shortened rotation system.  This is the
forward coloring direction used by the closed-web shrinking step. -/
theorem ProfileAlignedSplice.output_taitColorable
    {data : OrderedCutSidesData RS n terminalCount faceFragmentCount}
    (aligned : ProfileAlignedSplice data) :
    TaitColorable aligned.spliceData.output :=
  aligned.spliceData.output_taitColorable_of_equalProfile aligned.equalProfile

/-- The same aligned splice has strict vertex-cardinality descent whenever
its raw cut sides certify a genuinely removed vertex. -/
theorem ProfileAlignedSplice.outputSize_lt
    {data : OrderedCutSidesData RS n terminalCount faceFragmentCount}
    (aligned : ProfileAlignedSplice data) :
    aligned.spliceData.outputSize < Fintype.card V :=
  aligned.spliceData.outputSize_lt

end OrderedCutSidesData

end

end GoertzelV24SpliceUnification

end Mettapedia.GraphTheory.FourColor
