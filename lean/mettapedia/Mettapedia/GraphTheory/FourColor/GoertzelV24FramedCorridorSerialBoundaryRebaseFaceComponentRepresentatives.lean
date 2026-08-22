import Mathlib.Order.Partition.Finpartition
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseFaceCappedState

/-!
# Canonical predecessor face-component representatives

The capped facial rebase state stores one predecessor cap at every occurrence
of the same old component.  A successor decoder must not add that cap once per
occurrence.  This file gives the finite state a canonical representative for
each old component and selects exactly the active representatives.

The construction is generic in the finite Boolean component matrix.  A small
semantic certificate records the equivalence, activity, and cap-coherence laws
needed by the selector.  Every literal source rebase satisfies that certificate.
The result is the deduplication interface needed by the cap decoder; it does not
yet form the overlap-corrected successor sum or the complete Cell/rebase
recurrence.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationAllFaceCutProfile
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24TerminalProfileFaceUpdate
open SimpleGraph
open SimpleGraphDartRotation

/-- The exact laws which make the predecessor component matrix a finite
partition whose activity and capped weight are constant on every part. -/
structure BoundedCappedSerialBoundaryRebaseFaceStepCode.IsComponentSemantic
    (code : BoundedCappedSerialBoundaryRebaseFaceStepCode) : Prop where
  oldComponent_refl : ∀ coordinate,
    code.oldComponent coordinate coordinate = true
  oldComponent_symm : ∀ {left right},
    code.oldComponent left right = true →
      code.oldComponent right left = true
  oldComponent_trans : ∀ {left middle right},
    code.oldComponent left middle = true →
    code.oldComponent middle right = true →
      code.oldComponent left right = true
  oldActive_constant : ∀ {left right},
    code.oldComponent left right = true →
      code.oldActive left = code.oldActive right
  oldComponentCap_constant : ∀ {left right},
    code.oldComponent left right = true →
      code.oldComponentCap left = code.oldComponentCap right

namespace BoundedCappedSerialBoundaryRebaseFaceStepCode

/-- The predecessor component relation as a setoid on the finite occurrence
carrier. -/
def oldComponentSetoid (code : BoundedCappedSerialBoundaryRebaseFaceStepCode)
    (semantic : code.IsComponentSemantic) :
    Setoid (Fin code.localCode.vertexCount.val) where
  r left right := code.oldComponent left right = true
  iseqv := {
    refl := semantic.oldComponent_refl
    symm := semantic.oldComponent_symm
    trans := semantic.oldComponent_trans }

/-- The finite partition of stable occurrences into predecessor components. -/
noncomputable def oldComponentPartition
    (code : BoundedCappedSerialBoundaryRebaseFaceStepCode)
    (semantic : code.IsComponentSemantic) :
    Finpartition
      (Finset.univ : Finset (Fin code.localCode.vertexCount.val)) := by
  letI : DecidableRel (code.oldComponentSetoid semantic).r :=
    Classical.decRel _
  exact Finpartition.ofSetoid (code.oldComponentSetoid semantic)

@[simp]
theorem mem_oldComponentPartition_part_iff
    (code : BoundedCappedSerialBoundaryRebaseFaceStepCode)
    (semantic : code.IsComponentSemantic)
    (left right : Fin code.localCode.vertexCount.val) :
    right ∈ (code.oldComponentPartition semantic).part left ↔
      code.oldComponent left right = true := by
  classical
  change right ∈
      (Finpartition.ofSetoid (code.oldComponentSetoid semantic)).part left ↔ _
  rw [Finpartition.mem_part_ofSetoid_iff_rel]
  rfl

/-- The least coordinate of one predecessor component. -/
noncomputable def oldComponentRepresentative
    (code : BoundedCappedSerialBoundaryRebaseFaceStepCode)
    (semantic : code.IsComponentSemantic)
    (coordinate : Fin code.localCode.vertexCount.val) :
    Fin code.localCode.vertexCount.val :=
  ((code.oldComponentPartition semantic).part coordinate).min'
    ⟨coordinate, (code.mem_oldComponentPartition_part_iff semantic
      coordinate coordinate).2 (semantic.oldComponent_refl coordinate)⟩

theorem oldComponentRepresentative_mem_part
    (code : BoundedCappedSerialBoundaryRebaseFaceStepCode)
    (semantic : code.IsComponentSemantic)
    (coordinate : Fin code.localCode.vertexCount.val) :
    code.oldComponentRepresentative semantic coordinate ∈
      (code.oldComponentPartition semantic).part coordinate :=
  Finset.min'_mem _ _

/-- Two coordinates have the same canonical representative exactly when they
belong to the same predecessor component. -/
theorem oldComponentRepresentative_eq_iff
    (code : BoundedCappedSerialBoundaryRebaseFaceStepCode)
    (semantic : code.IsComponentSemantic)
    (left right : Fin code.localCode.vertexCount.val) :
    code.oldComponentRepresentative semantic right =
        code.oldComponentRepresentative semantic left ↔
      code.oldComponent left right = true := by
  classical
  let partition := code.oldComponentPartition semantic
  have hmem : right ∈ partition.part left ↔
      code.oldComponent left right = true :=
    code.mem_oldComponentPartition_part_iff semantic left right
  rw [← hmem]
  constructor
  · intro hrepresentative
    apply (partition.mem_part_iff_part_eq_part
      (Finset.mem_univ right) (Finset.mem_univ left)).2
    apply partition.eq_of_mem_parts
      (partition.part_mem.2 (Finset.mem_univ right))
      (partition.part_mem.2 (Finset.mem_univ left))
    · exact code.oldComponentRepresentative_mem_part semantic right
    · rw [hrepresentative]
      exact code.oldComponentRepresentative_mem_part semantic left
  · intro hmem
    have hparts : partition.part right = partition.part left :=
      (partition.mem_part_iff_part_eq_part
        (Finset.mem_univ right) (Finset.mem_univ left)).1 hmem
    simp only [oldComponentRepresentative, partition, hparts]

/-- Active canonical representatives, one per physically present predecessor
component. -/
noncomputable def oldComponentRepresentatives
    (code : BoundedCappedSerialBoundaryRebaseFaceStepCode)
    (semantic : code.IsComponentSemantic) :
    Finset (Fin code.localCode.vertexCount.val) :=
  Finset.univ.filter fun coordinate =>
    code.oldActive coordinate = true ∧
      code.oldComponentRepresentative semantic coordinate = coordinate

@[simp]
theorem mem_oldComponentRepresentatives_iff
    (code : BoundedCappedSerialBoundaryRebaseFaceStepCode)
    (semantic : code.IsComponentSemantic)
    (coordinate : Fin code.localCode.vertexCount.val) :
    coordinate ∈ code.oldComponentRepresentatives semantic ↔
      code.oldActive coordinate = true ∧
        code.oldComponentRepresentative semantic coordinate = coordinate := by
  classical
  simp [oldComponentRepresentatives]

/-- The representative of an active coordinate is itself active. -/
theorem oldComponentRepresentative_active
    (code : BoundedCappedSerialBoundaryRebaseFaceStepCode)
    (semantic : code.IsComponentSemantic)
    (coordinate : Fin code.localCode.vertexCount.val)
    (hactive : code.oldActive coordinate = true) :
    code.oldActive (code.oldComponentRepresentative semantic coordinate) =
      true := by
  have hsame : code.oldComponent
      (code.oldComponentRepresentative semantic coordinate) coordinate = true :=
    semantic.oldComponent_symm
      ((code.mem_oldComponentPartition_part_iff semantic coordinate
        (code.oldComponentRepresentative semantic coordinate)).1
          (code.oldComponentRepresentative_mem_part semantic coordinate))
  rw [semantic.oldActive_constant hsame]
  exact hactive

/-- Taking a canonical representative twice changes nothing. -/
theorem oldComponentRepresentative_idempotent
    (code : BoundedCappedSerialBoundaryRebaseFaceStepCode)
    (semantic : code.IsComponentSemantic)
    (coordinate : Fin code.localCode.vertexCount.val) :
    code.oldComponentRepresentative semantic
        (code.oldComponentRepresentative semantic coordinate) =
      code.oldComponentRepresentative semantic coordinate := by
  rw [code.oldComponentRepresentative_eq_iff semantic]
  exact (code.mem_oldComponentPartition_part_iff semantic coordinate
    (code.oldComponentRepresentative semantic coordinate)).1
      (code.oldComponentRepresentative_mem_part semantic coordinate)

/-- Every active coordinate maps to an active canonical representative. -/
theorem oldComponentRepresentative_mem_representatives
    (code : BoundedCappedSerialBoundaryRebaseFaceStepCode)
    (semantic : code.IsComponentSemantic)
    (coordinate : Fin code.localCode.vertexCount.val)
    (hactive : code.oldActive coordinate = true) :
    code.oldComponentRepresentative semantic coordinate ∈
      code.oldComponentRepresentatives semantic := by
  rw [code.mem_oldComponentRepresentatives_iff semantic]
  exact ⟨code.oldComponentRepresentative_active semantic coordinate hactive,
    code.oldComponentRepresentative_idempotent semantic coordinate⟩

/-- A selected representative in the component of a coordinate is the
canonical representative of that coordinate. -/
theorem eq_oldComponentRepresentative_of_mem_of_same
    (code : BoundedCappedSerialBoundaryRebaseFaceStepCode)
    (semantic : code.IsComponentSemantic)
    {representative coordinate : Fin code.localCode.vertexCount.val}
    (hrepresentative : representative ∈
      code.oldComponentRepresentatives semantic)
    (hsame : code.oldComponent representative coordinate = true) :
    representative = code.oldComponentRepresentative semantic coordinate := by
  have hfixed :=
    (code.mem_oldComponentRepresentatives_iff semantic representative).1
      hrepresentative |>.2
  have hsameRepresentative :=
    (code.oldComponentRepresentative_eq_iff semantic representative coordinate
      ).2 hsame
  exact hfixed.symm.trans hsameRepresentative.symm

/-- Replacing an active coordinate by its representative preserves its stored
predecessor cap. -/
theorem oldComponentCap_representative
    (code : BoundedCappedSerialBoundaryRebaseFaceStepCode)
    (semantic : code.IsComponentSemantic)
    (coordinate : Fin code.localCode.vertexCount.val) :
    code.oldComponentCap (code.oldComponentRepresentative semantic coordinate) =
      code.oldComponentCap coordinate := by
  apply semantic.oldComponentCap_constant
  exact semantic.oldComponent_symm
    ((code.mem_oldComponentPartition_part_iff semantic coordinate
      (code.oldComponentRepresentative semantic coordinate)).1
        (code.oldComponentRepresentative_mem_part semantic coordinate))

end BoundedCappedSerialBoundaryRebaseFaceStepCode

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseFaceComponentRepresentativesEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- Every literal source rebase supplies the exact equivalence, activity, and
cap-coherence laws required by the canonical component selector. -/
theorem sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt_isComponentSemantic
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (root : embedded.cellulation.rotation.toRotationSystem.D) :
    (sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext root).IsComponentSemantic := by
  let graph := faceRegionalAmbientPositionGraph
    embedded.cellulation.rotation.toRotationSystem root
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges
  let carrier := sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
    realization hcubic hrotation htwoSided hunique offset hnext root
  let code := sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt realization
    hcubic hrotation htwoSided hunique offset hnext root
  have hcomponent (left right : Fin code.localCode.vertexCount.val) :
      code.oldComponent left right = true ↔
        graph.Reachable ((carrierCoordinate carrier).symm left).1
          ((carrierCoordinate carrier).symm right).1 := by
    exact sourceCorridorSerialBoundaryRebaseFaceStepCodeAt_oldComponent_eq_true_iff
      realization hcubic hrotation htwoSided hunique offset hnext root left right
  have hactive (coordinate : Fin code.localCode.vertexCount.val) :
      code.oldActive coordinate = true ↔
        ((carrierCoordinate carrier).symm coordinate).1 ∈ graph.support := by
    exact sourceCorridorSerialBoundaryRebaseSupportedFaceStepCodeAt_oldActive_iff
      realization hcubic hrotation htwoSided hunique offset hnext root coordinate
  refine {
    oldComponent_refl := ?_
    oldComponent_symm := ?_
    oldComponent_trans := ?_
    oldActive_constant := ?_
    oldComponentCap_constant := ?_ }
  · intro coordinate
    exact (hcomponent coordinate coordinate).2
      (SimpleGraph.Reachable.refl
        (((carrierCoordinate carrier).symm coordinate).1))
  · intro left right hsame
    exact (hcomponent right left).2 ((hcomponent left right).1 hsame).symm
  · intro left middle right hleft hright
    exact (hcomponent left right).2
      (((hcomponent left middle).1 hleft).trans
        ((hcomponent middle right).1 hright))
  · intro left right hsame
    apply Bool.eq_iff_iff.mpr
    rw [hactive left, hactive right]
    have hreachable := (hcomponent left right).1 hsame
    by_cases heq : ((carrierCoordinate carrier).symm left).1 =
        ((carrierCoordinate carrier).symm right).1
    · rw [heq]
    · constructor
      · intro _
        exact SimpleGraph.mem_support_of_reachable (Ne.symm heq)
          hreachable.symm
      · intro _
        exact SimpleGraph.mem_support_of_reachable heq hreachable
  · intro left right hsame
    exact
      sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt_oldComponentCap_eq
        realization hcubic hrotation htwoSided hunique offset hnext root left
          right hsame

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
