import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainZeroFusionResolution
import Mettapedia.GraphTheory.FourColor.GoertzelV24RecoveredAdjacentPairData

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RecoveredAdjacentPairFusionChainNormalForm

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24FourDefectBoundary
open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- The rotation-ordered adjacent-pair datum selected from a named base
pair by the minimal counterexample. -/
abbrev RecoveredRotationOrderedData
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : AdjacentPairData G) : AdjacentPairData G :=
  baseData.rotationOrderedData graphData minimal.spherical.cubic
    minimal.vertexRotationCyclic

/-- The three terminal families of the complete sparse fusion-chain
resolution: a strict primal circuit, disjoint fusion supports, or the
single-cross residual carrying certified rebase pumping. -/
def SparseFusionChainResolution
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G
      (RecoveredRotationOrderedData graphData minimal baseData).firstVertex
      (RecoveredRotationOrderedData graphData minimal baseData).secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : (RecoveredRotationOrderedData graphData minimal
      baseData).degreeTwoBoundaryData.EvenKempeFusionLens C a b c 0 1)
    (lens23 : (RecoveredRotationOrderedData graphData minimal
      baseData).degreeTwoBoundaryData.EvenKempeFusionLens C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : Prop :=
  let data := RecoveredRotationOrderedData graphData minimal baseData
  (∃ (start : retainedVertexSet data.firstVertex data.secondVertex)
      (circuit : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).Walk start start),
      circuit.IsCircuit ∧
        (circuit.length < lens01.bRoute.ambientPath.length +
            lens23.cRoute.ambientPath.length ∨
          circuit.length < lens01.cRoute.ambientPath.length +
            lens23.bRoute.ambientPath.length ∨
          circuit.length < lens01.closedWalk.length ∨
          circuit.length < lens23.closedWalk.length ∨
          circuit.length < lens01.closedWalk.length +
            lens23.closedWalk.length)) ∨
    (lens01.bRoute.ambientPath.support ++
        lens01.cRoute.ambientPath.support).Disjoint
      (lens23.bRoute.ambientPath.support ++
        lens23.cRoute.ambientPath.support) ∨
    Nonempty (SparseSingleCrossFusionChainResidual graphData minimal
      baseData lens01 lens23 hab hac hbc)

/-- A rotation-ordered cyclic Kempe profile composed with the complete
finite fusion-chain resolution. -/
structure RotationOrderedCyclicKempeFusionChainNormalForm
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : AdjacentPairData G) where
  profile : CyclicKempeProfile graphData
    (RecoveredRotationOrderedData graphData minimal baseData)
  recoloring : (DeletedAdjacentPairGraph G
    (RecoveredRotationOrderedData graphData minimal baseData).firstVertex
    (RecoveredRotationOrderedData graphData minimal baseData).secondVertex).EdgeColoring Color
  recoloring_mem_kempeClosure : recoloring ∈
    (DeletedAdjacentPairGraph G
      (RecoveredRotationOrderedData graphData minimal baseData).firstVertex
      (RecoveredRotationOrderedData graphData minimal baseData).secondVertex).lineGraph.KempeClosure
        profile.coloring
  recoloring_isTait : IsTaitEdgeColoring
    (DeletedAdjacentPairGraph G
      (RecoveredRotationOrderedData graphData minimal baseData).firstVertex
      (RecoveredRotationOrderedData graphData minimal baseData).secondVertex)
    recoloring
  boundary_constant : ∀ port : Fin 4,
    (RecoveredRotationOrderedData graphData minimal
      baseData).degreeTwoBoundaryData.colorWord recoloring port =
        profile.firstColor
  first_ne_second : profile.firstColor ≠ profile.secondColor
  first_ne_third :
    profile.firstColor ≠ profile.firstColor + profile.secondColor
  second_ne_third :
    profile.secondColor ≠ profile.firstColor + profile.secondColor
  firstLens : (RecoveredRotationOrderedData graphData minimal
    baseData).degreeTwoBoundaryData.EvenKempeFusionLens recoloring
      profile.firstColor profile.secondColor
      (profile.firstColor + profile.secondColor) 0 1
  secondLens : (RecoveredRotationOrderedData graphData minimal
    baseData).degreeTwoBoundaryData.EvenKempeFusionLens recoloring
      profile.firstColor profile.secondColor
      (profile.firstColor + profile.secondColor) 2 3
  firstFamily_disjoint : firstLens.bRoute.ambientPath.support.Disjoint
    secondLens.bRoute.ambientPath.support
  secondFamily_disjoint : firstLens.cRoute.ambientPath.support.Disjoint
    secondLens.cRoute.ambientPath.support
  resolution : SparseFusionChainResolution graphData minimal baseData
    firstLens secondLens first_ne_second first_ne_third second_ne_third

namespace RotationOrderedCyclicKempeFusionChainNormalForm

/-- The two structural stopping branches of a rotation-ordered fusion
normal form: a strict primal circuit or disjoint total fusion support. -/
def TerminalFusionOutcome
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    (normal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData) : Prop :=
  let data := RecoveredRotationOrderedData graphData minimal baseData
  (∃ (start : retainedVertexSet data.firstVertex data.secondVertex)
      (circuit : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).Walk start start),
      circuit.IsCircuit ∧
        (circuit.length < normal.firstLens.bRoute.ambientPath.length +
            normal.secondLens.cRoute.ambientPath.length ∨
          circuit.length < normal.firstLens.cRoute.ambientPath.length +
            normal.secondLens.bRoute.ambientPath.length ∨
          circuit.length < normal.firstLens.closedWalk.length ∨
          circuit.length < normal.secondLens.closedWalk.length ∨
          circuit.length < normal.firstLens.closedWalk.length +
            normal.secondLens.closedWalk.length)) ∨
    (normal.firstLens.bRoute.ambientPath.support ++
        normal.firstLens.cRoute.ambientPath.support).Disjoint
      (normal.secondLens.bRoute.ambientPath.support ++
        normal.secondLens.cRoute.ambientPath.support)

/-- The recursive branch of a rotation-ordered fusion normal form.  It
retains the surviving cross orientation, the two exact splice equations,
and the certified finite pumping outcome launched at that cross. -/
def CertifiedRebasePumpingLaunch
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    (normal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData) : Prop :=
  let data := RecoveredRotationOrderedData graphData minimal baseData
  (∃ (site : normal.firstLens.bRoute.CrossSite
          normal.secondLens.cRoute)
      (pair : CrossCentralExactFaceCutPair graphData data site.1),
      pair.prefixTrail.edges =
          (normal.firstLens.bRoute.crossSplice
            normal.secondLens.cRoute site).support.map Subtype.val ∧
        pair.suffixTrail.edges =
          (normal.firstLens.bRoute.crossSuffixSplice
            normal.secondLens.cRoute site).support.map Subtype.val ∧
        pair.CertifiedRebasePumpingOutcome minimal baseData) ∨
    (∃ (site : normal.firstLens.cRoute.CrossSite
          normal.secondLens.bRoute)
      (pair : CrossCentralExactFaceCutPair graphData data site.1),
      pair.prefixTrail.edges =
          (normal.firstLens.cRoute.crossSplice
            normal.secondLens.bRoute site).support.map Subtype.val ∧
        pair.suffixTrail.edges =
          (normal.firstLens.cRoute.crossSuffixSplice
            normal.secondLens.bRoute site).support.map Subtype.val ∧
        pair.CertifiedRebasePumpingOutcome minimal baseData)

/-- The complete rotation-ordered fusion normal form either stops in one
of its two structural branches or launches certified exact-state pumping
at its unique surviving cross orientation. -/
theorem terminalFusion_or_certifiedRebasePumpingLaunch
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    (normal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData) :
    normal.TerminalFusionOutcome ∨
      normal.CertifiedRebasePumpingLaunch := by
  have hresolution := normal.resolution
  unfold SparseFusionChainResolution at hresolution
  dsimp only at hresolution
  unfold TerminalFusionOutcome CertifiedRebasePumpingLaunch
  dsimp only
  rcases hresolution with hstrict | hdisjoint | hresidual
  · exact Or.inl (Or.inl hstrict)
  · exact Or.inl (Or.inr hdisjoint)
  · rcases hresidual with ⟨residual⟩
    rcases residual.channel with hbc | hcb
    · rcases hbc with
        ⟨site, pair, _hbit, _htransfer, _hempty, hprefix, hsuffix,
          hpumping⟩
      exact Or.inr (Or.inl
        ⟨site, pair, hprefix, hsuffix, hpumping⟩)
    · rcases hcb with
        ⟨site, pair, _hbit, _htransfer, _hempty, hprefix, hsuffix,
          hpumping⟩
      exact Or.inr (Or.inr
        ⟨site, pair, hprefix, hsuffix, hpumping⟩)

end RotationOrderedCyclicKempeFusionChainNormalForm

/-- A cyclic Kempe profile on the literal minimality-selected rotation
ordering reaches the complete finite fusion-chain normal form. -/
theorem nonempty_rotationOrderedFusionChainNormalForm
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : AdjacentPairData G)
    (profile : CyclicKempeProfile graphData
      (RecoveredRotationOrderedData graphData minimal baseData)) :
    Nonempty (RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData) := by
  rcases profile.exists_two_sameFamilySeparatedFusionLenses_of_minimal
      minimal profile.validPair with
    ⟨recoloring, hclosure, htait, hconstant, firstLens, secondLens,
      hfirstDisjoint, hsecondDisjoint⟩
  have hthird := third_color_properties profile.validPair.1
    profile.validPair.2.1 profile.validPair.2.2
  have hfirstSecond : profile.firstColor ≠ profile.secondColor :=
    profile.validPair.2.2
  have hfirstThird :
      profile.firstColor ≠ profile.firstColor + profile.secondColor :=
    hthird.2.1.symm
  have hsecondThird :
      profile.secondColor ≠ profile.firstColor + profile.secondColor :=
    hthird.2.2.symm
  have hresolution :=
    EvenKempeFusionLens.rotationOrdered_sparseCrossFusionChainResolution_of_minimal
      graphData minimal baseData firstLens secondLens
        profile.boundaryWellFormed hfirstSecond hfirstThird hsecondThird
          hfirstDisjoint hsecondDisjoint
  exact ⟨{
    profile := profile
    recoloring := recoloring
    recoloring_mem_kempeClosure := hclosure
    recoloring_isTait := htait
    boundary_constant := hconstant
    first_ne_second := hfirstSecond
    first_ne_third := hfirstThird
    second_ne_third := hsecondThird
    firstLens := firstLens
    secondLens := secondLens
    firstFamily_disjoint := hfirstDisjoint
    secondFamily_disjoint := hsecondDisjoint
    resolution := hresolution }⟩

/-- A named adjacent pair retains the base datum whose literal
minimality-selected rotation ordering realizes the fusion-chain normal
form. -/
def HasRotationOrderedCyclicKempeFusionChainNormalForm
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (first second : V) : Prop :=
  ∃ baseData : AdjacentPairData G,
    baseData.firstVertex = first ∧
    baseData.secondVertex = second ∧
    Nonempty (RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData)

/-- A named adjacent pair realizes a rotation-ordered structural terminal
outcome or launches the certified exact-state pumping machine. -/
def HasRotationOrderedFusionTerminalOrRebasePumping
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (first second : V) : Prop :=
  ∃ baseData : AdjacentPairData G,
    baseData.firstVertex = first ∧
    baseData.secondVertex = second ∧
    ∃ normal : RotationOrderedCyclicKempeFusionChainNormalForm
        graphData minimal baseData,
      normal.TerminalFusionOutcome ∨
        normal.CertifiedRebasePumpingLaunch

/-- Forgetting no geometric data, a named rotation-ordered fusion normal
form exposes its structural terminal-or-recursive-pumping dichotomy. -/
theorem hasRotationOrderedFusionTerminalOrRebasePumping_of_normalForm
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {first second : V}
    (hnormal : HasRotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal first second) :
    HasRotationOrderedFusionTerminalOrRebasePumping
      graphData minimal first second := by
  rcases hnormal with ⟨baseData, hfirst, hsecond, ⟨normal⟩⟩
  exact ⟨baseData, hfirst, hsecond, normal,
    normal.terminalFusion_or_certifiedRebasePumpingLaunch⟩

/-- The named cyclic profile can be re-expressed with its exact
rotation-order provenance and composed through the finite fusion-chain
resolution. -/
theorem hasRotationOrderedFusionChainNormalForm_of_cyclicKempeTransferProfile
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {first second : V}
    (hprofile : HasCyclicKempeTransferProfile graphData first second) :
    HasRotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal first second := by
  rcases hprofile with ⟨baseData, hfirst, hsecond, _⟩
  rcases baseData.nonempty_rotationOrdered_cyclicKempeProfile
      graphData minimal with ⟨profile⟩
  exact ⟨baseData, hfirst, hsecond,
    nonempty_rotationOrderedFusionChainNormalForm
      graphData minimal baseData profile⟩

end

end GoertzelV24RecoveredAdjacentPairFusionChainNormalForm

end Mettapedia.GraphTheory.FourColor
