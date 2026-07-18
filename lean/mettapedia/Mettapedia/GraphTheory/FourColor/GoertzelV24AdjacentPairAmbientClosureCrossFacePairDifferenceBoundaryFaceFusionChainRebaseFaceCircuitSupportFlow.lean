import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitMonodromy
import Mathlib.Data.List.Cycle

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24WalkCycleParity
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24RebaseFaceCircuit

/-- Along a nonempty composable arc list, an endpoint change from absence
to presence is already witnessed by one arc. -/
theorem exists_entry_gain_of_endpoint_gain
    {State Entry : Type*} (source target : Entry → State)
    (property : State → Prop)
    (first : Entry) (rest : List Entry)
    (chain : List.IsChain (fun left right =>
      target left = source right) (first :: rest))
    (hsource : ¬ property (source first))
    (htarget : property
      (target ((first :: rest).getLast (by simp)))) :
    ∃ entry ∈ first :: rest,
      ¬ property (source entry) ∧ property (target entry) := by
  induction rest generalizing first with
  | nil =>
      exact ⟨first, by simp, hsource, by simpa using htarget⟩
  | cons second rest ih =>
      have hparts := List.isChain_cons_cons.mp chain
      by_cases hfirstTarget : property (target first)
      · exact ⟨first, by simp, hsource, hfirstTarget⟩
      · have hsecondSource : ¬ property (source second) := by
          rw [← hparts.1]
          exact hfirstTarget
        have htailTarget : property
            (target ((second :: rest).getLast (by simp))) := by
          simpa using htarget
        rcases ih second hparts.2 hsecondSource htailTarget with
          ⟨entry, hentry, hentrySource, hentryTarget⟩
        exact ⟨entry, List.mem_cons_of_mem first hentry,
          hentrySource, hentryTarget⟩

/-- A property that is antitone across every arc is antitone across a
whole nonempty composable arc list. -/
theorem source_property_of_last_target_property
    {State Entry : Type*} (source target : Entry → State)
    (property : State → Prop)
    (first : Entry) (rest : List Entry)
    (chain : List.IsChain (fun left right =>
      target left = source right) (first :: rest))
    (step : ∀ entry ∈ first :: rest,
      property (target entry) → property (source entry))
    (hlast : property
      (target ((first :: rest).getLast (by simp)))) :
    property (source first) := by
  induction rest generalizing first with
  | nil =>
      exact step first (by simp) (by simpa using hlast)
  | cons second rest ih =>
      have hparts := List.isChain_cons_cons.mp chain
      have htailStep : ∀ entry ∈ second :: rest,
          property (target entry) → property (source entry) := by
        intro entry hentry
        exact step entry (List.mem_cons_of_mem first hentry)
      have htailLast : property
          (target ((second :: rest).getLast (by simp))) := by
        simpa using hlast
      have hsecondSource := ih second hparts.2 htailStep htailLast
      apply step first (by simp)
      rw [hparts.1]
      exact hsecondSource

end GoertzelV24RebaseFaceCircuit

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

namespace CrossCentralExactFaceCertifiedRebaseArc

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

/-- A prefix-closure edge can be gained by an exact rebase only on the
selected face of that rebase. -/
theorem selectedFace_mem_of_prefixClosure_gain
    (arc : CrossCentralExactFaceCertifiedRebaseArc graphData minimal
      baseData)
    (edge : G.edgeSet)
    (hsource : edge.1 ∉
      ((baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).oppositePortClosure
          arc.source.2.prefixTrail).edges)
    (htarget : edge.1 ∈
      ((baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).oppositePortClosure
          arc.target.2.prefixTrail).edges) :
    edge ∈ orbitFaceBoundary graphData.toRotationSystem
      arc.selectedFace := by
  by_contra hoff
  exact hsource
    (arc.transition.target_prefixClosure_offFace_subset_source edge hoff
      htarget)

/-- The analogous localization holds for suffix-closure support. -/
theorem selectedFace_mem_of_suffixClosure_gain
    (arc : CrossCentralExactFaceCertifiedRebaseArc graphData minimal
      baseData)
    (edge : G.edgeSet)
    (hsource : edge.1 ∉
      ((baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).alternateOppositePortClosure
          arc.source.2.suffixTrail).edges)
    (htarget : edge.1 ∈
      ((baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).alternateOppositePortClosure
          arc.target.2.suffixTrail).edges) :
    edge ∈ orbitFaceBoundary graphData.toRotationSystem
      arc.selectedFace := by
  by_contra hoff
  exact hsource
    (arc.transition.target_suffixClosure_offFace_subset_source edge hoff
      htarget)

end CrossCentralExactFaceCertifiedRebaseArc

/-- Even fixed-face monodromy with off-face endpoint agreement has equal
prefix-closure support everywhere, including on the selected face. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.exactSteps_prefixClosure_support_eq_of_even
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {face : OrbitFace graphData.toRotationSystem}
    {length : Nat}
    {source target : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (run : ExactRebaseRelation.ExactSteps
      (CrossCentralExactFaceCertifiedRebaseTransitionOnFace graphData
        minimal baseData face) length source target)
    (heven : Even length)
    (hoffEndpoints : ∀ edge : G.edgeSet,
      edge ∉ orbitFaceBoundary graphData.toRotationSystem face →
        (edge.1 ∈
            ((baseData.rotationOrderedData graphData minimal.spherical.cubic
              minimal.vertexRotationCyclic).oppositePortClosure
                source.2.prefixTrail).edges ↔
          edge.1 ∈
            ((baseData.rotationOrderedData graphData minimal.spherical.cubic
              minimal.vertexRotationCyclic).oppositePortClosure
                target.2.prefixTrail).edges)) :
    ∀ edge : G.edgeSet,
      edge.1 ∈
          ((baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic).oppositePortClosure
              source.2.prefixTrail).edges ↔
        edge.1 ∈
          ((baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic).oppositePortClosure
              target.2.prefixTrail).edges := by
  let data := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  have hmonodromy :=
    CrossCentralExactFaceCertifiedRebaseTransitionOnFace.exactSteps_prefixParity_monodromy
      run hoffEndpoints
  rcases heven with ⟨half, rfl⟩
  intro edge
  have hvalue := hmonodromy edge
  have hsumZero :
      walkEdgeParity
            (data.oppositePortClosure source.2.prefixTrail) edge +
          walkEdgeParity
            (data.oppositePortClosure target.2.prefixTrail) edge = 0 := by
    simpa [Nat.cast_add, zmod2_add_self] using hvalue
  have hparity :
      walkEdgeParity
          (data.oppositePortClosure source.2.prefixTrail) edge =
        walkEdgeParity
          (data.oppositePortClosure target.2.prefixTrail) edge := by
    calc
      walkEdgeParity
          (data.oppositePortClosure source.2.prefixTrail) edge =
          walkEdgeParity
              (data.oppositePortClosure source.2.prefixTrail) edge +
            (walkEdgeParity
                (data.oppositePortClosure target.2.prefixTrail) edge +
              walkEdgeParity
                (data.oppositePortClosure target.2.prefixTrail) edge) := by
                  rw [zmod2_add_self]
                  simp
      _ = (walkEdgeParity
              (data.oppositePortClosure source.2.prefixTrail) edge +
            walkEdgeParity
              (data.oppositePortClosure target.2.prefixTrail) edge) +
          walkEdgeParity
            (data.oppositePortClosure target.2.prefixTrail) edge := by
              abel
      _ = walkEdgeParity
            (data.oppositePortClosure target.2.prefixTrail) edge := by
              rw [hsumZero]
              simp
  constructor
  · intro hsource
    have hone : walkEdgeParity
        (data.oppositePortClosure target.2.prefixTrail) edge = 1 := by
      rw [← hparity]
      exact walkEdgeParity_apply_eq_one_of_isTrail_of_mem_edges
        source.2.prefixTrail_isTrail edge hsource
    exact (walkEdgeParity_apply_eq_one_iff_mem_edges_of_isTrail
      target.2.prefixTrail_isTrail edge).1 hone
  · intro htarget
    have hone : walkEdgeParity
        (data.oppositePortClosure source.2.prefixTrail) edge = 1 := by
      rw [hparity]
      exact walkEdgeParity_apply_eq_one_of_isTrail_of_mem_edges
        target.2.prefixTrail_isTrail edge htarget
    exact (walkEdgeParity_apply_eq_one_iff_mem_edges_of_isTrail
      source.2.prefixTrail_isTrail edge).1 hone

namespace CrossCentralExactFaceCertifiedRebaseCircuit

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

/-- A circuit viewed intrinsically as a cyclic list of exact rebase arcs. -/
def arcCycle
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData) :
    Cycle
      (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData) :=
  (circuit.first :: circuit.rest : List
    (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData))

/-- The intrinsic arc cycle is composable across every cyclic boundary. -/
theorem arcCycle_chain
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData) :
    circuit.arcCycle.Chain
      CrossCentralExactFaceCertifiedRebaseArc.Follows := by
  rw [arcCycle, Cycle.chain_coe_cons]
  have hcyclic : List.IsChain
      CrossCentralExactFaceCertifiedRebaseArc.Follows
        ((circuit.first :: circuit.rest) ++ [circuit.first]) := by
    apply circuit.consecutive.append (List.IsChain.singleton _)
    intro last hlast first hfirst
    have hfirstEq : first = circuit.first := by simpa using hfirst.symm
    subst first
    rcases List.mem_getLast?_eq_getLast hlast with ⟨hne, hlastEq⟩
    subst last
    exact circuit.closing
  simpa only [List.cons_append] using hcyclic

/-- Any representative of the same intrinsic arc cycle defines the same
exact rebase circuit with a different chosen first arc. -/
def rotateToRepresentative
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
    (first : CrossCentralExactFaceCertifiedRebaseArc graphData minimal
      baseData)
    (rest : List
      (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData))
    (hsameCycle : ((first :: rest : List
      (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData)) :
        Cycle _) = circuit.arcCycle) :
    CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal
      baseData := by
  have hcycleChain : Cycle.Chain
      CrossCentralExactFaceCertifiedRebaseArc.Follows
      ((first :: rest : List
        (CrossCentralExactFaceCertifiedRebaseArc graphData minimal
          baseData)) : Cycle
            (CrossCentralExactFaceCertifiedRebaseArc graphData minimal
              baseData)) := by
    rw [hsameCycle]
    exact circuit.arcCycle_chain
  have hcyclic : List.IsChain
      CrossCentralExactFaceCertifiedRebaseArc.Follows
        ((first :: rest) ++ [first]) := by
    have := (Cycle.chain_coe_cons
      CrossCentralExactFaceCertifiedRebaseArc.Follows first rest).mp
        hcycleChain
    simpa only [List.cons_append] using this
  have hparts := List.isChain_append.mp hcyclic
  refine {
    first := first
    rest := rest
    consecutive := hparts.1
    closing := ?_ }
  exact hparts.2.2 ((first :: rest).getLast (by simp))
    (by
      rw [List.getLast?_eq_getLast_of_ne_nil (by simp)]
      simp) first (by simp)

/-- Splitting the displayed arc list at any occurrence and moving its
prefix to the end gives a certified cyclic rotation. -/
def rotateAtSplit
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
    (first : CrossCentralExactFaceCertifiedRebaseArc graphData minimal
      baseData)
    (before after : List
      (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData))
    (hsplit : circuit.first :: circuit.rest =
      before ++ first :: after) :
    CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal
      baseData := by
  refine circuit.rotateToRepresentative first (after ++ before) ?_
  change (↑(first :: after ++ before) : Cycle
      (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData)) =
    ↑(circuit.first :: circuit.rest)
  apply Cycle.coe_eq_coe.mpr
  rw [hsplit]
  exact List.isRotated_append.symm

/-- The chosen first arc of a split rotation is the selected occurrence. -/
@[simp] theorem rotateAtSplit_first
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
    (first : CrossCentralExactFaceCertifiedRebaseArc graphData minimal
      baseData)
    (before after : List
      (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData))
    (hsplit : circuit.first :: circuit.rest =
      before ++ first :: after) :
    (circuit.rotateAtSplit first before after hsplit).first = first := by
  simp [rotateAtSplit, rotateToRepresentative]

/-- The remaining displayed arcs of a split rotation are the suffix
followed by the former prefix. -/
@[simp] theorem rotateAtSplit_rest
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
    (first : CrossCentralExactFaceCertifiedRebaseArc graphData minimal
      baseData)
    (before after : List
      (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData))
    (hsplit : circuit.first :: circuit.rest =
      before ++ first :: after) :
    (circuit.rotateAtSplit first before after hsplit).rest =
      after ++ before := by
  simp [rotateAtSplit, rotateToRepresentative]

/-- A prefix-closure gain between the endpoints of a composable arc list
is localized at some selected face in that list. -/
theorem exists_prefixClosure_gain
    (first : CrossCentralExactFaceCertifiedRebaseArc graphData minimal
      baseData)
    (rest : List
      (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData))
    (chain : List.IsChain
      CrossCentralExactFaceCertifiedRebaseArc.Follows (first :: rest))
    (edge : G.edgeSet)
    (hsource : edge.1 ∉
      ((baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).oppositePortClosure
          first.source.2.prefixTrail).edges)
    (htarget : edge.1 ∈
      ((baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).oppositePortClosure
          ((first :: rest).getLast (by simp)).target.2.prefixTrail).edges) :
    ∃ arc ∈ first :: rest,
      edge.1 ∉
          ((baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic).oppositePortClosure
              arc.source.2.prefixTrail).edges ∧
        edge.1 ∈
          ((baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic).oppositePortClosure
              arc.target.2.prefixTrail).edges ∧
        edge ∈ orbitFaceBoundary graphData.toRotationSystem
          arc.selectedFace := by
  let data := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  have stateChain : List.IsChain (fun left right =>
      left.target = right.source) (first :: rest) := by
    change List.IsChain (fun left right =>
      left.target = right.source) (first :: rest) at chain
    exact chain
  rcases GoertzelV24RebaseFaceCircuit.exists_entry_gain_of_endpoint_gain
      CrossCentralExactFaceCertifiedRebaseArc.source
      CrossCentralExactFaceCertifiedRebaseArc.target
      (fun state => edge.1 ∈
        (data.oppositePortClosure state.2.prefixTrail).edges)
      first rest stateChain hsource htarget with
    ⟨arc, harc, harcSource, harcTarget⟩
  exact ⟨arc, harc, harcSource, harcTarget,
    arc.selectedFace_mem_of_prefixClosure_gain edge harcSource
      harcTarget⟩

/-- A suffix-closure endpoint gain has the same selected-face
localization. -/
theorem exists_suffixClosure_gain
    (first : CrossCentralExactFaceCertifiedRebaseArc graphData minimal
      baseData)
    (rest : List
      (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData))
    (chain : List.IsChain
      CrossCentralExactFaceCertifiedRebaseArc.Follows (first :: rest))
    (edge : G.edgeSet)
    (hsource : edge.1 ∉
      ((baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).alternateOppositePortClosure
          first.source.2.suffixTrail).edges)
    (htarget : edge.1 ∈
      ((baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).alternateOppositePortClosure
          ((first :: rest).getLast (by simp)).target.2.suffixTrail).edges) :
    ∃ arc ∈ first :: rest,
      edge.1 ∉
          ((baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic).alternateOppositePortClosure
              arc.source.2.suffixTrail).edges ∧
        edge.1 ∈
          ((baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic).alternateOppositePortClosure
              arc.target.2.suffixTrail).edges ∧
        edge ∈ orbitFaceBoundary graphData.toRotationSystem
          arc.selectedFace := by
  let data := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  have stateChain : List.IsChain (fun left right =>
      left.target = right.source) (first :: rest) := by
    change List.IsChain (fun left right =>
      left.target = right.source) (first :: rest) at chain
    exact chain
  rcases GoertzelV24RebaseFaceCircuit.exists_entry_gain_of_endpoint_gain
      CrossCentralExactFaceCertifiedRebaseArc.source
      CrossCentralExactFaceCertifiedRebaseArc.target
      (fun state => edge.1 ∈
        (data.alternateOppositePortClosure state.2.suffixTrail).edges)
      first rest stateChain hsource htarget with
    ⟨arc, harc, harcSource, harcTarget⟩
  exact ⟨arc, harc, harcSource, harcTarget,
    arc.selectedFace_mem_of_suffixClosure_gain edge harcSource
      harcTarget⟩

/-- If prefix support is lost during one displayed segment of a circuit,
the complementary segment contains a localized recovery step. -/
theorem exists_outside_prefixClosure_recovery
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
    (left middleFirst right :
      CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData)
    (before middleRest after : List
      (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData))
    (hsplit : circuit.first :: circuit.rest =
      before ++
        (left :: ((middleFirst :: middleRest) ++ (right :: after))))
    (edge : G.edgeSet)
    (htarget : edge.1 ∉
      ((baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).oppositePortClosure
          right.source.2.prefixTrail).edges)
    (hsource : edge.1 ∈
      ((baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).oppositePortClosure
          middleFirst.source.2.prefixTrail).edges) :
    ∃ arc ∈ right :: (after ++ before ++ [left]),
      edge.1 ∉
          ((baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic).oppositePortClosure
              arc.source.2.prefixTrail).edges ∧
        edge.1 ∈
          ((baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic).oppositePortClosure
              arc.target.2.prefixTrail).edges ∧
        edge ∈ orbitFaceBoundary graphData.toRotationSystem
          arc.selectedFace := by
  let beforeRight := before ++ (left :: middleFirst :: middleRest)
  have hsplitRight : circuit.first :: circuit.rest =
      beforeRight ++ right :: after := by
    simpa [beforeRight, List.append_assoc] using hsplit
  let rotated := circuit.rotateAtSplit right beforeRight after hsplitRight
  let outsideRest := after ++ before ++ [left]
  have hrotatedList : rotated.first :: rotated.rest =
      (right :: outsideRest) ++ (middleFirst :: middleRest) := by
    simp [rotated, outsideRest, beforeRight, List.append_assoc]
  have houtsideChain : List.IsChain
      CrossCentralExactFaceCertifiedRebaseArc.Follows
        (right :: outsideRest) := by
    have hrotatedChain := rotated.consecutive
    rw [hrotatedList] at hrotatedChain
    exact hrotatedChain.left_of_append
  have hleftFollows :
      CrossCentralExactFaceCertifiedRebaseArc.Follows left middleFirst := by
    apply (List.isChain_iff_forall_rel_of_append_cons_cons.mp
      circuit.consecutive)
    simpa [List.append_assoc] using hsplit
  have hlastTarget : edge.1 ∈
      ((baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).oppositePortClosure
          ((right :: outsideRest).getLast
            (by simp)).target.2.prefixTrail).edges := by
    have hlastArc : (right :: outsideRest).getLast (by simp) = left := by
      simp [outsideRest]
    have hleftTarget : left.target = middleFirst.source := hleftFollows
    rw [hlastArc, hleftTarget]
    exact hsource
  simpa [outsideRest] using
    (exists_prefixClosure_gain right outsideRest houtsideChain edge
      htarget hlastTarget)

/-- A constant-face block forming a facial-dual backtrack is either even,
or it loses an off-face prefix edge that is later recovered on a certified
incident face of the complementary circuit segment. -/
theorem middleBlock_even_or_exists_outside_prefixClosure_recovery
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
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
    (Even (middleFirst :: middleRest).length ∧
      ∀ edge : G.edgeSet,
        edge.1 ∈
            ((baseData.rotationOrderedData graphData minimal.spherical.cubic
              minimal.vertexRotationCyclic).oppositePortClosure
                middleFirst.source.2.prefixTrail).edges ↔
          edge.1 ∈
            ((baseData.rotationOrderedData graphData minimal.spherical.cubic
              minimal.vertexRotationCyclic).oppositePortClosure
                right.source.2.prefixTrail).edges) ∨
    ∃ edge : G.edgeSet,
      edge ∉ orbitFaceBoundary graphData.toRotationSystem secondFace ∧
      edge.1 ∈
          ((baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic).oppositePortClosure
              middleFirst.source.2.prefixTrail).edges ∧
        edge.1 ∉
          ((baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic).oppositePortClosure
              right.source.2.prefixTrail).edges ∧
        ∃ arc ∈ right :: (after ++ before ++ [left]),
          edge.1 ∉
              ((baseData.rotationOrderedData graphData minimal.spherical.cubic
                minimal.vertexRotationCyclic).oppositePortClosure
                  arc.source.2.prefixTrail).edges ∧
            edge.1 ∈
              ((baseData.rotationOrderedData graphData minimal.spherical.cubic
                minimal.vertexRotationCyclic).oppositePortClosure
                  arc.target.2.prefixTrail).edges ∧
            edge ∈ orbitFaceBoundary graphData.toRotationSystem
              arc.selectedFace := by
  classical
  let middleArcs := middleFirst :: middleRest
  have hfullChain : List.IsChain
      CrossCentralExactFaceCertifiedRebaseArc.Follows
        (before ++ (left :: (middleArcs ++ (right :: after)))) := by
    rw [← hsplit]
    exact circuit.consecutive
  have htailChain : List.IsChain
      CrossCentralExactFaceCertifiedRebaseArc.Follows
        (left :: (middleArcs ++ (right :: after))) :=
    (List.isChain_append.mp hfullChain).2.1
  have hleftParts := List.isChain_cons_cons.mp htailChain
  have hmiddleAfterChain : List.IsChain
      CrossCentralExactFaceCertifiedRebaseArc.Follows
        (middleArcs ++ (right :: after)) := by
    simpa [middleArcs] using hleftParts.2
  have hmiddleParts := List.isChain_append.mp hmiddleAfterChain
  have hmiddleChain : List.IsChain
      CrossCentralExactFaceCertifiedRebaseArc.Follows middleArcs :=
    hmiddleParts.1
  have hmiddleNe : middleArcs ≠ [] := by simp [middleArcs]
  let middleLast := middleArcs.getLast hmiddleNe
  have hlastMem : middleLast ∈ middleArcs.getLast? := by
    rw [List.getLast?_eq_getLast_of_ne_nil hmiddleNe]
    simp [middleLast]
  have hlastFollows :
      CrossCentralExactFaceCertifiedRebaseArc.Follows middleLast right :=
    hmiddleParts.2.2 middleLast hlastMem right (by simp)
  have hmiddleRun := exactSteps_of_arc_chain_on_face secondFace
    middleFirst middleRest (by simpa [middleArcs] using hmiddleChain)
      hmiddleFaces
  have hlastEq : middleLast.target = right.source := hlastFollows
  have hrun : ExactRebaseRelation.ExactSteps
      (CrossCentralExactFaceCertifiedRebaseTransitionOnFace graphData
        minimal baseData secondFace)
      middleArcs.length middleFirst.source right.source := by
    change ExactRebaseRelation.ExactSteps
      (CrossCentralExactFaceCertifiedRebaseTransitionOnFace graphData
        minimal baseData secondFace)
      middleArcs.length middleFirst.source middleLast.target at hmiddleRun
    rw [hlastEq] at hmiddleRun
    exact hmiddleRun
  have hmiddleRightChain : List.IsChain
      CrossCentralExactFaceCertifiedRebaseArc.Follows
        (middleArcs ++ [right]) := by
    apply hmiddleChain.append (List.IsChain.singleton _)
    intro last hlast first hfirst
    have hlast' : last = middleLast := by
      rcases List.mem_getLast?_eq_getLast hlast with ⟨hne, heq⟩
      simpa [middleLast] using heq
    have hfirst' : first = right := by simpa using hfirst.symm
    simpa [hlast', hfirst'] using hlastFollows
  have hexcurChain : List.IsChain
      CrossCentralExactFaceCertifiedRebaseArc.Follows
        (left :: (middleArcs ++ [right])) := by
    exact List.IsChain.cons_cons hleftParts.1 hmiddleRightChain
  have hcross : middleFirst.source.1 = right.source.1 := by
    apply cross_eq_across_constantFace_excursion firstFace secondFace
      hfaces left middleFirst right middleRest
    · simpa [middleArcs] using hexcurChain
    · exact hleftFace
    · exact hmiddleFaces
    · exact hrightFace
  let data := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  by_cases hoffEndpoints : ∀ edge : G.edgeSet,
      edge ∉ orbitFaceBoundary graphData.toRotationSystem secondFace →
        (edge.1 ∈
            (data.oppositePortClosure
              middleFirst.source.2.prefixTrail).edges ↔
          edge.1 ∈
            (data.oppositePortClosure right.source.2.prefixTrail).edges)
  · have heven :=
      CrossCentralExactFaceCertifiedRebaseTransitionOnFace.exactSteps_length_even_of_cross_eq
        hrun hcross hoffEndpoints
    exact Or.inl ⟨heven,
      CrossCentralExactFaceCertifiedRebaseTransitionOnFace.exactSteps_prefixClosure_support_eq_of_even
        hrun heven hoffEndpoints⟩
  · right
    push Not at hoffEndpoints
    rcases hoffEndpoints with ⟨edge, hedgeOff, hnotIff⟩
    have htargetSource : edge.1 ∈
          (data.oppositePortClosure right.source.2.prefixTrail).edges →
        edge.1 ∈
          (data.oppositePortClosure
            middleFirst.source.2.prefixTrail).edges := by
      exact
        CrossCentralExactFaceCertifiedRebaseTransitionOnFace.reflTransGen_prefixClosure_offFace_subset
          hrun.to_reflTransGen edge hedgeOff
    have hloss : edge.1 ∈
          (data.oppositePortClosure
            middleFirst.source.2.prefixTrail).edges ∧
        edge.1 ∉
          (data.oppositePortClosure right.source.2.prefixTrail).edges := by
      tauto
    refine ⟨edge, hedgeOff, hloss.1, hloss.2, ?_⟩
    exact circuit.exists_outside_prefixClosure_recovery left middleFirst
      right before middleRest after hsplit edge hloss.2 hloss.1

end CrossCentralExactFaceCertifiedRebaseCircuit

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
