import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitShortening

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

/-- The retained geometry of an exact cut state: its cross and the two
retained trail walks, with all face labels forgotten. -/
abbrev CrossCentralExactFaceCutRigidCode
    (data : AdjacentPairData G) :=
  (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet ×
    (SimpleGraph.FiniteTrailWalk
        (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
        (data.retainedPort 0) (data.retainedPort 2) ×
      SimpleGraph.FiniteTrailWalk
        (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
        (data.retainedPort 1) (data.retainedPort 3))

/-- Forget the two face-label functions while retaining the exact cross and
both trail walks. -/
def CrossCentralExactFaceCutState.rigidCode
    {graphData : Data G} {data : AdjacentPairData G}
    (state : CrossCentralExactFaceCutState graphData data) :
    CrossCentralExactFaceCutRigidCode data :=
  (state.1,
    (⟨state.2.prefixTrail, state.2.prefixRetained_isTrail⟩,
      ⟨state.2.suffixTrail, state.2.suffixRetained_isTrail⟩))

/-- Equality of rigid codes is exactly equality of the retained cross and
the two retained trails. -/
theorem CrossCentralExactFaceCutState.rigidCode_eq_iff
    {graphData : Data G} {data : AdjacentPairData G}
    (first second : CrossCentralExactFaceCutState graphData data) :
    first.rigidCode = second.rigidCode ↔
      first.1 = second.1 ∧
        first.2.prefixTrail = second.2.prefixTrail ∧
        first.2.suffixTrail = second.2.suffixTrail := by
  constructor
  · intro hcode
    exact ⟨congrArg Prod.fst hcode,
      congrArg (fun code : CrossCentralExactFaceCutRigidCode data =>
        code.2.1.1) hcode,
      congrArg (fun code : CrossCentralExactFaceCutRigidCode data =>
        code.2.2.1) hcode⟩
  · rintro ⟨hcross, hprefixTrail, hsuffixTrail⟩
    apply Prod.ext
    · exact hcross
    · apply Prod.ext
      · exact Subtype.ext hprefixTrail
      · exact Subtype.ext hsuffixTrail

namespace CrossCentralExactFaceCertifiedRebaseCircuit

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

/-- The cyclically displayed source state at every certified rebase arc. -/
def sourceStates
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData) :
    List (CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)) :=
  (circuit.first :: circuit.rest).map
    CrossCentralExactFaceCertifiedRebaseArc.source

/-- The retained-geometry code at one cyclic circuit position. -/
def rigidCodeAt
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
    (position : Fin circuit.sourceStates.length) :
    CrossCentralExactFaceCutRigidCode
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic) :=
  (circuit.sourceStates.get position).rigidCode

@[simp] theorem sourceStates_length
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData) :
    circuit.sourceStates.length = circuit.arcLength := by
  simp [sourceStates, arcLength]

/-- The complete source states displayed by a length-minimal circuit have
no repetition. -/
theorem IsLengthMinimal.sourceStates_nodup
    {circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData}
    (hminimal : circuit.IsLengthMinimal) :
    circuit.sourceStates.Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  unfold sourceStates
  rw [List.pairwise_map]
  let arcs := circuit.first :: circuit.rest
  have suffixPairwise : ∀ (before suffix : List
      (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData)),
      arcs = before ++ suffix →
        List.Pairwise (fun first second =>
          first.source ≠ second.source) suffix := by
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
          apply hminimal.source_ne_of_split first second before between after
          simpa [arcs, hrest] using hsplit
        · apply ih (before ++ [first])
          calc
            arcs = before ++ (first :: rest) := hsplit
            _ = (before ++ [first]) ++ rest := by simp
  simpa [arcs, sourceStates] using suffixPairwise [] arcs (by simp)

/-- Five distinct positions of a length-minimal circuit cannot all share
one retained cross and the same two retained paths. -/
theorem IsLengthMinimal.not_five_positions_same_cross_and_trails
    {circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData}
    (hminimal : circuit.IsLengthMinimal)
    (positions : Fin 5 → Fin circuit.sourceStates.length)
    (hpositions : Function.Injective positions)
    (hcross : ∀ index,
      (circuit.sourceStates.get (positions 0)).1 =
        (circuit.sourceStates.get (positions index)).1)
    (hprefixTrail : ∀ index,
      (circuit.sourceStates.get (positions 0)).2.prefixTrail =
        (circuit.sourceStates.get (positions index)).2.prefixTrail)
    (hsuffixTrail : ∀ index,
      (circuit.sourceStates.get (positions 0)).2.suffixTrail =
        (circuit.sourceStates.get (positions index)).2.suffixTrail) :
    False := by
  let states : Fin 5 → CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic) := fun index =>
    circuit.sourceStates.get (positions index)
  rcases CrossCentralExactFaceCutState.exists_eq_of_five_same_cross_and_trails
      minimal states (by simpa [states] using hcross)
        (by simpa [states] using hprefixTrail)
        (by simpa [states] using hsuffixTrail) with
    ⟨first, second, hne, heq⟩
  have hpositionNe : positions first ≠ positions second := by
    intro hposition
    exact hne (hpositions hposition)
  have hpairwise : List.Pairwise (· ≠ ·) circuit.sourceStates :=
    List.nodup_iff_pairwise_ne.mp hminimal.sourceStates_nodup
  rcases lt_or_gt_of_ne hpositionNe with hlt | hgt
  · exact
      (List.pairwise_iff_get.mp hpairwise
        (positions first) (positions second) hlt) (by simpa [states] using heq)
  · exact
      (List.pairwise_iff_get.mp hpairwise
        (positions second) (positions first) hgt) (by
          simpa [states] using heq.symm)

/-- The circuit positions whose retained cross and both retained paths agree
with one reference position. -/
noncomputable def rigidPositionFiber
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
    (reference : Fin circuit.sourceStates.length) :
    Finset (Fin circuit.sourceStates.length) :=
  Finset.univ.filter fun position =>
    (circuit.sourceStates.get reference).1 =
        (circuit.sourceStates.get position).1 ∧
      (circuit.sourceStates.get reference).2.prefixTrail =
        (circuit.sourceStates.get position).2.prefixTrail ∧
      (circuit.sourceStates.get reference).2.suffixTrail =
        (circuit.sourceStates.get position).2.suffixTrail

@[simp] theorem mem_rigidPositionFiber
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
    (reference position : Fin circuit.sourceStates.length) :
    position ∈ circuit.rigidPositionFiber reference ↔
      (circuit.sourceStates.get reference).1 =
          (circuit.sourceStates.get position).1 ∧
        (circuit.sourceStates.get reference).2.prefixTrail =
          (circuit.sourceStates.get position).2.prefixTrail ∧
        (circuit.sourceStates.get reference).2.suffixTrail =
          (circuit.sourceStates.get position).2.suffixTrail := by
  simp [rigidPositionFiber]

/-- At most four positions of a length-minimal circuit have any fixed
retained cross and pair of retained paths. -/
theorem IsLengthMinimal.card_rigidPositionFiber_le_four
    {circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData}
    (hminimal : circuit.IsLengthMinimal)
    (reference : Fin circuit.sourceStates.length) :
    (circuit.rigidPositionFiber reference).card ≤ 4 := by
  classical
  by_contra hcard
  have hfive : 5 ≤ (circuit.rigidPositionFiber reference).card := by
    omega
  rcases Function.Embedding.exists_of_card_le_finset
      (α := Fin 5) (s := circuit.rigidPositionFiber reference)
        (by simpa using hfive) with
    ⟨positions : Fin 5 ↪ Fin circuit.sourceStates.length, hpositions⟩
  have hmem : ∀ index, positions index ∈
      circuit.rigidPositionFiber reference := by
    intro index
    exact hpositions ⟨index, rfl⟩
  apply hminimal.not_five_positions_same_cross_and_trails positions
    positions.injective
  · intro index
    exact ((circuit.mem_rigidPositionFiber reference (positions 0)).mp
      (hmem 0)).1.symm.trans
        (((circuit.mem_rigidPositionFiber reference (positions index)).mp
          (hmem index)).1)
  · intro index
    exact ((circuit.mem_rigidPositionFiber reference (positions 0)).mp
      (hmem 0)).2.1.symm.trans
        (((circuit.mem_rigidPositionFiber reference (positions index)).mp
          (hmem index)).2.1)
  · intro index
    exact ((circuit.mem_rigidPositionFiber reference (positions 0)).mp
      (hmem 0)).2.2.symm.trans
        (((circuit.mem_rigidPositionFiber reference (positions index)).mp
          (hmem index)).2.2)

/-- All circuit positions carrying one specified retained-geometry code. -/
noncomputable def rigidCodeFiber
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
    (code : CrossCentralExactFaceCutRigidCode
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)) :
    Finset (Fin circuit.sourceStates.length) := by
  classical
  exact Finset.univ.filter fun position =>
    circuit.rigidCodeAt position = code

@[simp] theorem mem_rigidCodeFiber
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
    (code : CrossCentralExactFaceCutRigidCode
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic))
    (position : Fin circuit.sourceStates.length) :
    position ∈ circuit.rigidCodeFiber code ↔
      circuit.rigidCodeAt position = code := by
  simp [rigidCodeFiber]

/-- Each retained-geometry code occurs at most four times on a
length-minimal circuit. -/
theorem IsLengthMinimal.card_rigidCodeFiber_le_four
    {circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData}
    (hminimal : circuit.IsLengthMinimal)
    (code : CrossCentralExactFaceCutRigidCode
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)) :
    (circuit.rigidCodeFiber code).card ≤ 4 := by
  classical
  by_contra hcard
  have hfive : 5 ≤ (circuit.rigidCodeFiber code).card := by
    omega
  rcases Function.Embedding.exists_of_card_le_finset
      (α := Fin 5) (s := circuit.rigidCodeFiber code)
        (by simpa using hfive) with
    ⟨positions : Fin 5 ↪ Fin circuit.sourceStates.length, hpositions⟩
  have hmem : ∀ index, positions index ∈ circuit.rigidCodeFiber code := by
    intro index
    exact hpositions ⟨index, rfl⟩
  have hgeometry : ∀ index,
      (circuit.sourceStates.get (positions 0)).1 =
          (circuit.sourceStates.get (positions index)).1 ∧
        (circuit.sourceStates.get (positions 0)).2.prefixTrail =
          (circuit.sourceStates.get (positions index)).2.prefixTrail ∧
        (circuit.sourceStates.get (positions 0)).2.suffixTrail =
          (circuit.sourceStates.get (positions index)).2.suffixTrail := by
    intro index
    apply (CrossCentralExactFaceCutState.rigidCode_eq_iff
      (circuit.sourceStates.get (positions 0))
      (circuit.sourceStates.get (positions index))).mp
    change circuit.rigidCodeAt (positions 0) =
      circuit.rigidCodeAt (positions index)
    exact ((circuit.mem_rigidCodeFiber code (positions 0)).mp
      (hmem 0)).trans
        (((circuit.mem_rigidCodeFiber code (positions index)).mp
          (hmem index)).symm)
  exact hminimal.not_five_positions_same_cross_and_trails positions
    positions.injective (fun index => (hgeometry index).1)
      (fun index => (hgeometry index).2.1)
        (fun index => (hgeometry index).2.2)

/-- A shortest circuit has at most four positions per retained-geometry
code.  In particular, its length is bounded without counting either
face-label function. -/
theorem IsLengthMinimal.arcLength_le_four_mul_card_rigidCode
    {circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData}
    (hminimal : circuit.IsLengthMinimal) :
    circuit.arcLength ≤ 4 * Fintype.card
      (CrossCentralExactFaceCutRigidCode
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic)) := by
  classical
  rw [← circuit.sourceStates_length]
  simpa [rigidCodeFiber] using
    (Finset.card_le_mul_card_image_of_maps_to
      (f := circuit.rigidCodeAt)
      (s := (Finset.univ : Finset (Fin circuit.sourceStates.length)))
      (t := (Finset.univ : Finset
        (CrossCentralExactFaceCutRigidCode
          (baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic))))
      (fun _ _ => Finset.mem_univ _) 4
      (fun code _ => hminimal.card_rigidCodeFiber_le_four code))

end CrossCentralExactFaceCertifiedRebaseCircuit

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
