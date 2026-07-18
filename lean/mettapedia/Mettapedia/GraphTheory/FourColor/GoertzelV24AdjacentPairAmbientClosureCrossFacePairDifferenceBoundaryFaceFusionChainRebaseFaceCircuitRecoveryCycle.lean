import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryDependency

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

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

/-- One directed recovery dependency with its concrete channel, support
edge, and restoring rebase arc. -/
structure ClosureRecoveryFaceArc
    (rebaseCircuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData) where
  sourceFace : OrbitFace graphData.toRotationSystem
  targetFace : OrbitFace graphData.toRotationSystem
  channel : ExactClosureChannel
  edge : G.edgeSet
  recoveryArc :
    CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData
  recoveryArc_mem_displayed :
    recoveryArc ∈ rebaseCircuit.first :: rebaseCircuit.rest
  recoveryArc_selectedFace : recoveryArc.selectedFace = targetFace
  edge_not_mem_sourceFace :
    edge ∉ orbitFaceBoundary graphData.toRotationSystem sourceFace
  edge_not_mem_recoverySource :
    edge.1 ∉ channel.edges recoveryArc.source
  edge_mem_recoveryTarget : edge.1 ∈ channel.edges recoveryArc.target
  edge_mem_targetFace :
    edge ∈ orbitFaceBoundary graphData.toRotationSystem targetFace
  targetFace_ne_sourceFace : targetFace ≠ sourceFace

namespace ClosureRecoveryFaceArc

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- Forgetting the concrete fields gives the directed dependency relation. -/
theorem to_dependency
    (arc : ClosureRecoveryFaceArc rebaseCircuit) :
    rebaseCircuit.ClosureRecoveryFaceDependency arc.sourceFace
      arc.targetFace := by
  exact ⟨arc.channel, arc.edge, arc.recoveryArc,
    arc.recoveryArc_mem_displayed, arc.recoveryArc_selectedFace,
    arc.edge_not_mem_sourceFace, arc.edge_not_mem_recoverySource,
    arc.edge_mem_recoveryTarget, arc.edge_mem_targetFace,
    arc.targetFace_ne_sourceFace⟩

/-- Every directed dependency admits a concrete recovery arc. -/
theorem exists_of_dependency
    {sourceFace targetFace : OrbitFace graphData.toRotationSystem}
    (dependency : rebaseCircuit.ClosureRecoveryFaceDependency sourceFace
      targetFace) :
    ∃ arc : ClosureRecoveryFaceArc rebaseCircuit,
      arc.sourceFace = sourceFace ∧ arc.targetFace = targetFace := by
  rcases dependency with
    ⟨channel, edge, recoveryArc, harc, hface, hedgeOff, hsource,
      htarget, hedgeFace, hne⟩
  exact ⟨{
    sourceFace := sourceFace
    targetFace := targetFace
    channel := channel
    edge := edge
    recoveryArc := recoveryArc
    recoveryArc_mem_displayed := harc
    recoveryArc_selectedFace := hface
    edge_not_mem_sourceFace := hedgeOff
    edge_not_mem_recoverySource := hsource
    edge_mem_recoveryTarget := htarget
    edge_mem_targetFace := hedgeFace
    targetFace_ne_sourceFace := hne }, rfl, rfl⟩

/-- A concrete recovery arc lands on a selected face of the underlying
rebase circuit. -/
theorem targetFace_mem_selectedFaces
    (arc : ClosureRecoveryFaceArc rebaseCircuit) :
    arc.targetFace ∈ rebaseCircuit.selectedFaces := by
  exact rebaseCircuit.mem_selectedFaces arc.targetFace |>.2
    ⟨arc.recoveryArc, arc.recoveryArc_mem_displayed,
      arc.recoveryArc_selectedFace⟩

/-- Consecutive recovery arcs meet at one dependency face. -/
def Follows (first second : ClosureRecoveryFaceArc rebaseCircuit) : Prop :=
  first.targetFace = second.sourceFace

end ClosureRecoveryFaceArc

/-- A nonempty cyclic list of concrete recovery dependencies. -/
structure ClosureRecoveryFaceCircuit
    (rebaseCircuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData) where
  first : ClosureRecoveryFaceArc rebaseCircuit
  rest : List (ClosureRecoveryFaceArc rebaseCircuit)
  consecutive : List.IsChain ClosureRecoveryFaceArc.Follows (first :: rest)
  closing : ClosureRecoveryFaceArc.Follows
    ((first :: rest).getLast (by simp)) first

namespace ClosureRecoveryFaceCircuit

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- A transitive dependency cycle lifts to a cyclic list retaining every
channel, support edge, and restoring arc. -/
theorem exists_of_transGen_cycle
    {face : OrbitFace graphData.toRotationSystem}
    (cycle : Relation.TransGen
      rebaseCircuit.ClosureRecoveryFaceDependency face face) :
    Nonempty (ClosureRecoveryFaceCircuit rebaseCircuit) := by
  have existsArcChain : ∀ {source target :
      OrbitFace graphData.toRotationSystem},
      Relation.TransGen rebaseCircuit.ClosureRecoveryFaceDependency
          source target →
        ∃ (first : ClosureRecoveryFaceArc rebaseCircuit)
            (rest : List (ClosureRecoveryFaceArc rebaseCircuit)),
          List.IsChain ClosureRecoveryFaceArc.Follows (first :: rest) ∧
            first.sourceFace = source ∧
            ((first :: rest).getLast (by simp)).targetFace = target := by
    intro source target run
    induction run using Relation.TransGen.head_induction_on with
    | single dependency =>
        rcases ClosureRecoveryFaceArc.exists_of_dependency dependency with
          ⟨arc, hsource, htarget⟩
        exact ⟨arc, [], List.IsChain.singleton _, hsource,
          by simpa using htarget⟩
    | @head source middle dependency run ih =>
        rcases ih with ⟨first, rest, hchain, hsource, htarget⟩
        rcases ClosureRecoveryFaceArc.exists_of_dependency dependency with
          ⟨arc, harcSource, harcTarget⟩
        refine ⟨arc, first :: rest, ?_, harcSource, ?_⟩
        · apply List.IsChain.cons_cons
          · exact harcTarget.trans hsource.symm
          · exact hchain
        · simpa using htarget
  rcases existsArcChain cycle with
    ⟨first, rest, hchain, hsource, htarget⟩
  exact ⟨{
    first := first
    rest := rest
    consecutive := hchain
    closing := htarget.trans hsource.symm }⟩

/-- The number of concrete directed dependencies in a recovery circuit. -/
def arcLength (circuit : ClosureRecoveryFaceCircuit rebaseCircuit) : Nat :=
  (circuit.first :: circuit.rest).length

@[simp] theorem arcLength_eq_rest_length_add_one
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit) :
    circuit.arcLength = circuit.rest.length + 1 := by
  simp [arcLength, Nat.add_comm]

/-- A concrete recovery circuit cannot consist of one self-dependency. -/
theorem rest_ne_nil (circuit : ClosureRecoveryFaceCircuit rebaseCircuit) :
    circuit.rest ≠ [] := by
  intro hrest
  have hclosing : circuit.first.targetFace = circuit.first.sourceFace := by
    simpa [ClosureRecoveryFaceArc.Follows, hrest] using circuit.closing
  exact circuit.first.targetFace_ne_sourceFace hclosing

theorem two_le_arcLength
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit) :
    2 ≤ circuit.arcLength := by
  rw [circuit.arcLength_eq_rest_length_add_one]
  have hlengthNe : circuit.rest.length ≠ 0 := by
    intro hzero
    exact circuit.rest_ne_nil (List.length_eq_zero_iff.mp hzero)
  omega

/-- A recovery circuit is shortest among all recovery circuits carried by
the same rebase circuit. -/
def IsLengthMinimal
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit) : Prop :=
  ∀ other : ClosureRecoveryFaceCircuit rebaseCircuit,
    circuit.arcLength ≤ other.arcLength

/-- Every nonempty family of concrete recovery circuits has a shortest
member. -/
theorem exists_lengthMinimal
    (circuits : Nonempty (ClosureRecoveryFaceCircuit rebaseCircuit)) :
    ∃ circuit : ClosureRecoveryFaceCircuit rebaseCircuit,
      circuit.IsLengthMinimal := by
  classical
  rcases circuits with ⟨seed⟩
  let occurs : Nat → Prop := fun length =>
    ∃ circuit : ClosureRecoveryFaceCircuit rebaseCircuit,
      circuit.arcLength = length
  have hexists : ∃ length, occurs length :=
    ⟨seed.arcLength, seed, rfl⟩
  rcases Nat.find_spec hexists with ⟨circuit, hcircuit⟩
  refine ⟨circuit, ?_⟩
  intro other
  rw [hcircuit]
  exact Nat.find_min' hexists ⟨other, rfl⟩

/-- Equal source faces at two displayed positions close the intervening
segment to a strictly shorter recovery circuit. -/
theorem exists_strict_subcircuit_of_split_sourceFace_eq
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit)
    (first second : ClosureRecoveryFaceArc rebaseCircuit)
    (before between after : List (ClosureRecoveryFaceArc rebaseCircuit))
    (hsplit : circuit.first :: circuit.rest =
      before ++ (first :: (between ++ (second :: after))))
    (hsource : first.sourceFace = second.sourceFace) :
    ∃ subcircuit : ClosureRecoveryFaceCircuit rebaseCircuit,
      subcircuit.arcLength < circuit.arcLength ∧
      subcircuit.first :: subcircuit.rest = first :: between := by
  let segment := first :: between
  have hfullChain : List.IsChain ClosureRecoveryFaceArc.Follows
      (before ++ (segment ++ (second :: after))) := by
    have hchain := circuit.consecutive
    rw [hsplit] at hchain
    simpa [segment, List.append_assoc] using hchain
  have hsegmentAfterChain : List.IsChain ClosureRecoveryFaceArc.Follows
      (segment ++ (second :: after)) :=
    (List.isChain_append.mp hfullChain).2.1
  have hparts := List.isChain_append.mp hsegmentAfterChain
  have hsegmentChain : List.IsChain ClosureRecoveryFaceArc.Follows segment :=
    hparts.1
  have hsegmentNe : segment ≠ [] := by simp [segment]
  let last := segment.getLast hsegmentNe
  have hlastMem : last ∈ segment.getLast? := by
    rw [List.getLast?_eq_getLast_of_ne_nil hsegmentNe]
    simp [last]
  have hlastFollows : ClosureRecoveryFaceArc.Follows last second :=
    hparts.2.2 last hlastMem second (by simp)
  let subcircuit : ClosureRecoveryFaceCircuit rebaseCircuit := {
    first := first
    rest := between
    consecutive := by simpa [segment] using hsegmentChain
    closing := by
      change last.targetFace = first.sourceFace
      exact hlastFollows.trans hsource.symm }
  refine ⟨subcircuit, ?_, rfl⟩
  change segment.length < (circuit.first :: circuit.rest).length
  rw [hsplit]
  simp [segment]
  omega

/-- The cyclic source-face list of a concrete recovery circuit. -/
def sourceFaces (circuit : ClosureRecoveryFaceCircuit rebaseCircuit) :
    List (OrbitFace graphData.toRotationSystem) :=
  (circuit.first :: circuit.rest).map ClosureRecoveryFaceArc.sourceFace

@[simp] theorem sourceFaces_length
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit) :
    circuit.sourceFaces.length = circuit.arcLength := by
  simp [sourceFaces, arcLength]

/-- Every source face on a closed recovery circuit is also selected by the
underlying rebase circuit. -/
theorem sourceFace_mem_selectedFaces_of_mem
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit)
    {arc : ClosureRecoveryFaceArc rebaseCircuit}
    (harc : arc ∈ circuit.first :: circuit.rest) :
    arc.sourceFace ∈ rebaseCircuit.selectedFaces := by
  have tailSources : ∀ (head : ClosureRecoveryFaceArc rebaseCircuit)
      (tail : List (ClosureRecoveryFaceArc rebaseCircuit)),
      List.IsChain ClosureRecoveryFaceArc.Follows (head :: tail) →
        ∀ next ∈ tail,
          next.sourceFace ∈ rebaseCircuit.selectedFaces := by
    intro head tail hchain
    induction tail generalizing head with
    | nil =>
        intro next hnext
        simp at hnext
    | cons next rest ih =>
        have hparts := List.isChain_cons_cons.mp hchain
        intro arc harc
        rcases List.mem_cons.mp harc with rfl | harc
        · rw [← hparts.1]
          exact head.targetFace_mem_selectedFaces
        · exact ih next hparts.2 arc harc
  rcases List.mem_cons.mp harc with rfl | harc
  · let last := (circuit.first :: circuit.rest).getLast (by simp)
    have hlast : last.targetFace ∈ rebaseCircuit.selectedFaces :=
      last.targetFace_mem_selectedFaces
    have hclosing : last.targetFace = circuit.first.sourceFace := by
      exact circuit.closing
    exact hclosing ▸ hlast
  · exact tailSources circuit.first circuit.rest circuit.consecutive
      arc harc

/-- A shortest concrete recovery circuit visits no source face twice. -/
theorem IsLengthMinimal.sourceFaces_nodup
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal) :
    circuit.sourceFaces.Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  unfold sourceFaces
  rw [List.pairwise_map]
  let arcs := circuit.first :: circuit.rest
  have suffixPairwise : ∀ (before suffix : List
      (ClosureRecoveryFaceArc rebaseCircuit)),
      arcs = before ++ suffix →
        List.Pairwise (fun first second =>
          first.sourceFace ≠ second.sourceFace) suffix := by
    intro before suffix
    induction suffix generalizing before with
    | nil =>
        intro _
        exact List.Pairwise.nil
    | cons first rest ih =>
        intro hsplit
        apply List.pairwise_cons.mpr
        constructor
        · intro second hsecond
          rcases List.mem_iff_append.mp hsecond with
            ⟨between, after, hrest⟩
          intro hsource
          rcases circuit.exists_strict_subcircuit_of_split_sourceFace_eq
              first second before between after (by
                simpa [arcs, hrest] using hsplit) hsource with
            ⟨subcircuit, hshorter, _⟩
          exact (Nat.not_lt_of_ge (hminimal subcircuit)) hshorter
        · apply ih (before ++ [first])
          calc
            arcs = before ++ (first :: rest) := hsplit
            _ = (before ++ [first]) ++ rest := by simp
  simpa [arcs] using suffixPairwise [] arcs (by simp)

/-- A shortest recovery cycle has at most one source occurrence per face
selected by the underlying rebase circuit. -/
theorem IsLengthMinimal.arcLength_le_selectedFaces_card
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal) :
    circuit.arcLength ≤ rebaseCircuit.selectedFaces.card := by
  classical
  have hsubset : circuit.sourceFaces.toFinset ⊆
      rebaseCircuit.selectedFaces := by
    intro face hface
    have hlist : face ∈ circuit.sourceFaces := by simpa using hface
    rcases List.mem_map.mp hlist with ⟨arc, harc, rfl⟩
    exact circuit.sourceFace_mem_selectedFaces_of_mem harc
  calc
    circuit.arcLength = circuit.sourceFaces.length :=
      circuit.sourceFaces_length.symm
    _ = circuit.sourceFaces.toFinset.card :=
      (List.toFinset_card_of_nodup hminimal.sourceFaces_nodup).symm
    _ ≤ rebaseCircuit.selectedFaces.card := Finset.card_le_card hsubset

/-- A shortest recovery cycle has no more arcs than there are ambient
faces. -/
theorem IsLengthMinimal.arcLength_le_card_faces
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal) :
    circuit.arcLength ≤
      Fintype.card (OrbitFace graphData.toRotationSystem) := by
  rw [← circuit.sourceFaces_length]
  exact hminimal.sourceFaces_nodup.length_le_card

/-- Total outgoing recovery on the selected faces therefore supplies a
shortest concrete recovery circuit. -/
theorem exists_lengthMinimal_of_forall_outgoing
    (rebaseCircuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
    (houtgoing : ∀ middleFace ∈ rebaseCircuit.selectedFaces,
      ∃ recoveryFace,
        rebaseCircuit.ClosureRecoveryFaceDependency middleFace
          recoveryFace) :
    ∃ circuit : ClosureRecoveryFaceCircuit rebaseCircuit,
      circuit.IsLengthMinimal := by
  rcases
      rebaseCircuit.exists_recoveryFaceDependency_cycle_of_forall_outgoing
        houtgoing with ⟨face, _hface, cycle⟩
  exact exists_lengthMinimal (exists_of_transGen_cycle cycle)

end ClosureRecoveryFaceCircuit

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
