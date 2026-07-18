import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitFiniteProfileShortening

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- The two closed-trail support channels transported by an exact rebase. -/
inductive ExactClosureChannel where
  | prefix
  | suffix
  deriving DecidableEq, Fintype

/-- Edge support of one closed-trail channel at an exact state. -/
def ExactClosureChannel.edges
    {graphData : Data G} {data : AdjacentPairData G}
    (channel : ExactClosureChannel)
    (state : CrossCentralExactFaceCutState graphData data) : List (Sym2 V) :=
  match channel with
  | .prefix => (data.oppositePortClosure state.2.prefixTrail).edges
  | .suffix =>
      (data.alternateOppositePortClosure state.2.suffixTrail).edges

namespace CrossCentralExactFaceCertifiedRebaseCircuit

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

/-- One support edge lost by a constant-face block and the complementary
circuit arc that restores it on a different selected face. -/
structure OutsideClosureRecoveryWitness
    (middleFace : OrbitFace graphData.toRotationSystem)
    (source target : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic))
    (outside : List
      (CrossCentralExactFaceCertifiedRebaseArc graphData minimal
        baseData)) where
  channel : ExactClosureChannel
  edge : G.edgeSet
  edge_not_mem_middleFace :
    edge ∉ orbitFaceBoundary graphData.toRotationSystem middleFace
  edge_mem_source : edge.1 ∈ channel.edges source
  edge_not_mem_target : edge.1 ∉ channel.edges target
  recoveryArc :
    CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData
  recoveryArc_mem_outside : recoveryArc ∈ outside
  edge_not_mem_recoverySource :
    edge.1 ∉ channel.edges recoveryArc.source
  edge_mem_recoveryTarget : edge.1 ∈ channel.edges recoveryArc.target
  edge_mem_recoveryFace :
    edge ∈ orbitFaceBoundary graphData.toRotationSystem
      recoveryArc.selectedFace
  recoveryFace_ne_middleFace : recoveryArc.selectedFace ≠ middleFace

/-- Package a prefix-channel recovery as a channel-independent witness. -/
theorem OutsideClosureRecoveryWitness.exists_of_prefix
    (middleFace : OrbitFace graphData.toRotationSystem)
    (source target : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic))
    (outside : List
      (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData))
    (recovery : OutsidePrefixClosureRecovery middleFace source target
      outside) :
    Nonempty (OutsideClosureRecoveryWitness middleFace source target
      outside) := by
  rcases recovery with
    ⟨edge, hedgeOff, hsource, htarget, arc, harc, harcSource,
      harcTarget, harcFace, hfaceNe⟩
  exact ⟨{
    channel := .prefix
    edge := edge
    edge_not_mem_middleFace := hedgeOff
    edge_mem_source := hsource
    edge_not_mem_target := htarget
    recoveryArc := arc
    recoveryArc_mem_outside := harc
    edge_not_mem_recoverySource := harcSource
    edge_mem_recoveryTarget := harcTarget
    edge_mem_recoveryFace := harcFace
    recoveryFace_ne_middleFace := hfaceNe }⟩

/-- Package a suffix-channel recovery as a channel-independent witness. -/
theorem OutsideClosureRecoveryWitness.exists_of_suffix
    (middleFace : OrbitFace graphData.toRotationSystem)
    (source target : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic))
    (outside : List
      (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData))
    (recovery : OutsideSuffixClosureRecovery middleFace source target
      outside) :
    Nonempty (OutsideClosureRecoveryWitness middleFace source target
      outside) := by
  rcases recovery with
    ⟨edge, hedgeOff, hsource, htarget, arc, harc, harcSource,
      harcTarget, harcFace, hfaceNe⟩
  exact ⟨{
    channel := .suffix
    edge := edge
    edge_not_mem_middleFace := hedgeOff
    edge_mem_source := hsource
    edge_not_mem_target := htarget
    recoveryArc := arc
    recoveryArc_mem_outside := harc
    edge_not_mem_recoverySource := harcSource
    edge_mem_recoveryTarget := harcTarget
    edge_mem_recoveryFace := harcFace
    recoveryFace_ne_middleFace := hfaceNe }⟩

/-- A directed face dependency records an edge lost off the first face and
restored by a displayed circuit arc on the second face. -/
def ClosureRecoveryFaceDependency
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
    (middleFace recoveryFace : OrbitFace graphData.toRotationSystem) : Prop :=
  ∃ (channel : ExactClosureChannel) (edge : G.edgeSet)
      (arc : CrossCentralExactFaceCertifiedRebaseArc graphData minimal
        baseData),
    arc ∈ circuit.first :: circuit.rest ∧
      arc.selectedFace = recoveryFace ∧
      edge ∉ orbitFaceBoundary graphData.toRotationSystem middleFace ∧
      edge.1 ∉ channel.edges arc.source ∧
      edge.1 ∈ channel.edges arc.target ∧
      edge ∈ orbitFaceBoundary graphData.toRotationSystem recoveryFace ∧
      recoveryFace ≠ middleFace

/-- The finite set of selected faces displayed by a rebase circuit. -/
noncomputable def selectedFaces
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData) :
    Finset (OrbitFace graphData.toRotationSystem) := by
  classical
  exact Finset.univ.filter fun face =>
    ∃ arc ∈ circuit.first :: circuit.rest,
      arc.selectedFace = face

@[simp] theorem mem_selectedFaces
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
    (face : OrbitFace graphData.toRotationSystem) :
    face ∈ circuit.selectedFaces ↔
      ∃ arc ∈ circuit.first :: circuit.rest,
        arc.selectedFace = face := by
  classical
  simp [selectedFaces]

theorem selectedFaces_nonempty
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData) :
    circuit.selectedFaces.Nonempty := by
  exact ⟨circuit.first.selectedFace,
    circuit.mem_selectedFaces circuit.first.selectedFace |>.2
      ⟨circuit.first, by simp⟩⟩

/-- Every recovery witness whose outside list lies on the circuit induces
the corresponding directed face dependency. -/
theorem OutsideClosureRecoveryWitness.faceDependency
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
    {middleFace : OrbitFace graphData.toRotationSystem}
    {source target : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    {outside : List
      (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData)}
    (witness : OutsideClosureRecoveryWitness middleFace source target
      outside)
    (houtside : ∀ arc ∈ outside,
      arc ∈ circuit.first :: circuit.rest) :
    circuit.ClosureRecoveryFaceDependency middleFace
      witness.recoveryArc.selectedFace := by
  exact ⟨witness.channel, witness.edge, witness.recoveryArc,
    houtside witness.recoveryArc witness.recoveryArc_mem_outside, rfl,
    witness.edge_not_mem_middleFace,
    witness.edge_not_mem_recoverySource,
    witness.edge_mem_recoveryTarget,
    witness.edge_mem_recoveryFace,
    witness.recoveryFace_ne_middleFace⟩

/-- The complementary arc list of a displayed middle block consists only
of arcs from the original circuit. -/
theorem outside_subset_displayed_of_middleBlock_split
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
    (left middleFirst right :
      CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData)
    (before middleRest after : List
      (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData))
    (hsplit : circuit.first :: circuit.rest =
      before ++
        (left :: ((middleFirst :: middleRest) ++ (right :: after)))) :
    ∀ arc ∈ right :: (after ++ before ++ [left]),
      arc ∈ circuit.first :: circuit.rest := by
  intro arc harc
  rw [hsplit]
  simp only [List.mem_append, List.mem_cons] at harc ⊢
  aesop

/-- The shortest-circuit backtrack trichotomy with both recovery channels
collapsed to a directed dependency on a distinct face. -/
theorem IsLengthMinimal.middleBlock_nonzeroComplementProfile_or_recoveryFaceDependency
    {circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData}
    (hminimal : circuit.IsLengthMinimal)
    (firstFace secondFace : OrbitFace graphData.toRotationSystem)
    (hfaces : firstFace ≠ secondFace)
    (left middleFirst right :
      CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData)
    (before middleRest after : List
      (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData))
    (hsplit : circuit.first :: circuit.rest =
      before ++
        (left :: ((middleFirst :: middleRest) ++ (right :: after))))
    (hleftFace : left.selectedFace = firstFace)
    (hmiddleFaces : ∀ arc ∈ middleFirst :: middleRest,
      arc.selectedFace = secondFace)
    (hrightFace : right.selectedFace = firstFace) :
    MiddleBlockNonzeroComplementProfile middleFirst right middleRest ∨
      ∃ recoveryFace,
        circuit.ClosureRecoveryFaceDependency secondFace recoveryFace := by
  let outside := right :: (after ++ before ++ [left])
  have houtside : ∀ arc ∈ outside,
      arc ∈ circuit.first :: circuit.rest := by
    exact circuit.outside_subset_displayed_of_middleBlock_split left
      middleFirst right before middleRest after hsplit
  rcases
      hminimal.middleBlock_nonzeroComplementProfile_or_outside_prefixRecovery_or_suffixRecovery
        firstFace secondFace hfaces left middleFirst right before middleRest
          after hsplit hleftFace hmiddleFaces hrightFace with
    hnormal | hprefix | hsuffix
  · exact Or.inl hnormal
  · right
    rcases OutsideClosureRecoveryWitness.exists_of_prefix secondFace
        middleFirst.source right.source outside hprefix with ⟨witness⟩
    exact ⟨witness.recoveryArc.selectedFace,
      witness.faceDependency circuit houtside⟩
  · right
    rcases OutsideClosureRecoveryWitness.exists_of_suffix secondFace
        middleFirst.source right.source outside hsuffix with ⟨witness⟩
    exact ⟨witness.recoveryArc.selectedFace,
      witness.faceDependency circuit houtside⟩

/-- Recovery dependencies never loop at one face. -/
theorem ClosureRecoveryFaceDependency.ne
    {circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData}
    {middleFace recoveryFace : OrbitFace graphData.toRotationSystem}
    (dependency : circuit.ClosureRecoveryFaceDependency middleFace
      recoveryFace) :
    recoveryFace ≠ middleFace := by
  rcases dependency with
    ⟨channel, edge, arc, harc, hface, hedgeOff, hsource, htarget,
      hedgeFace, hne⟩
  exact hne

/-- The target of a recovery dependency remains in the circuit's selected
face set. -/
theorem ClosureRecoveryFaceDependency.recoveryFace_mem_selectedFaces
    {circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData}
    {middleFace recoveryFace : OrbitFace graphData.toRotationSystem}
    (dependency : circuit.ClosureRecoveryFaceDependency middleFace
      recoveryFace) :
    recoveryFace ∈ circuit.selectedFaces := by
  rcases dependency with
    ⟨channel, edge, arc, harc, hface, hedgeOff, hsource, htarget,
      hedgeFace, hne⟩
  exact circuit.mem_selectedFaces recoveryFace |>.2 ⟨arc, harc, hface⟩

/-- If every selected face has an outgoing recovery dependency, the finite
selected-face relation contains a nonempty directed cycle. -/
theorem exists_recoveryFaceDependency_cycle_of_forall_outgoing
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
    (houtgoing : ∀ middleFace ∈ circuit.selectedFaces,
      ∃ recoveryFace,
        circuit.ClosureRecoveryFaceDependency middleFace recoveryFace) :
    ∃ face,
      face ∈ circuit.selectedFaces ∧
        Relation.TransGen circuit.ClosureRecoveryFaceDependency face face := by
  classical
  rcases circuit.selectedFaces_nonempty with ⟨start, hstart⟩
  have htotal : ∀ face,
      face ∉ circuit.selectedFaces ∨
        ∃ target,
          circuit.ClosureRecoveryFaceDependency face target := by
    intro face
    by_cases hface : face ∈ circuit.selectedFaces
    · exact Or.inr (houtgoing face hface)
    · exact Or.inl hface
  have hreachableMem : ∀ {target},
      Relation.ReflTransGen circuit.ClosureRecoveryFaceDependency
          start target →
        target ∈ circuit.selectedFaces := by
    intro target reachable
    induction reachable with
    | refl => exact hstart
    | tail _ dependency _ =>
        exact dependency.recoveryFace_mem_selectedFaces
  rcases finite_reflTransGen_terminal_or_transGen_cycle
      circuit.ClosureRecoveryFaceDependency
      (fun face => face ∉ circuit.selectedFaces) htotal start with
    hterminal | hcycle
  · rcases hterminal with ⟨finish, hreachable, hfinish⟩
    exact False.elim (hfinish (hreachableMem hreachable))
  · rcases hcycle with ⟨face, hreachable, hclosed⟩
    exact ⟨face, hreachableMem hreachable, hclosed⟩

end CrossCentralExactFaceCertifiedRebaseCircuit

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
