import Mettapedia.GraphTheory.FourColor.ClassicalCertificateFacePartition

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateContractComponents

open ClassicalCertificateConfiguration
open ClassicalCertificateFacePartition

/-- A checked quotient of face classes by the equalities imposed by a
contract.  The parent and link tables form a decreasing spanning forest in
each component. -/
structure Code where
  componentCount : Nat
  componentOfFace : Array Nat
  representative : Array Nat
  parent : Array Nat
  linkDart : Array Nat
  depth : Array Nat
  deriving DecidableEq, Repr

namespace Code

def componentAt (code : Code) (face : Nat) : Nat :=
  HypermapCode.lookup code.componentOfFace face

def representativeAt (code : Code) (component : Nat) : Nat :=
  HypermapCode.lookup code.representative component

def parentAt (code : Code) (face : Nat) : Nat :=
  HypermapCode.lookup code.parent face

def linkDartAt (code : Code) (face : Nat) : Nat :=
  HypermapCode.lookup code.linkDart face

def depthAt (code : Code) (face : Nat) : Nat :=
  HypermapCode.lookup code.depth face

end Code

/-- Raw executable contract membership for a numbered dart. -/
def InContractAt {hypermap : HypermapCode}
    (contract : Finset (Fin hypermap.dartCount)) (dart : Nat) : Prop :=
  if h : dart < hypermap.dartCount then
    InRawContract contract ⟨dart, h⟩
  else False

instance {hypermap : HypermapCode}
    (contract : Finset (Fin hypermap.dartCount)) (dart : Nat) :
    Decidable (InContractAt contract dart) := by
  unfold InContractAt
  infer_instance

/-- The finite conditions checked for a contract-component quotient. -/
def Conditions {hypermap : HypermapCode}
    {partition : ClassicalCertificateFacePartition.Code}
    (_partitionValid : ClassicalCertificateFacePartition.Valid hypermap partition)
    (contract : Finset (Fin hypermap.dartCount))
    (components : ClassicalCertificateContractComponents.Code) : Prop :=
  components.componentOfFace.size = partition.faceCount ∧
    components.representative.size = components.componentCount ∧
    components.parent.size = partition.faceCount ∧
    components.linkDart.size = partition.faceCount ∧
    components.depth.size = partition.faceCount ∧
    (∀ face : Fin partition.faceCount,
      components.componentAt face.val < components.componentCount) ∧
    (∀ component : Fin components.componentCount,
      components.representativeAt component.val < partition.faceCount) ∧
    (∀ face : Fin partition.faceCount,
      components.parentAt face.val < partition.faceCount) ∧
    (∀ face : Fin partition.faceCount,
      components.linkDartAt face.val < hypermap.dartCount) ∧
    (∀ component : Fin components.componentCount,
      components.componentAt (components.representativeAt component.val) =
        component.val) ∧
    ∀ face : Fin partition.faceCount,
      face.val = components.representativeAt
          (components.componentAt face.val) ∨
        let parent := components.parentAt face.val
        let dart := components.linkDartAt face.val
        components.depthAt parent < components.depthAt face.val ∧
          components.componentAt parent = components.componentAt face.val ∧
          InContractAt contract dart ∧
          ((partition.classAt dart = face.val ∧
              partition.classAt
                (HypermapCode.lookup hypermap.edge dart) = parent) ∨
            (partition.classAt dart = parent ∧
              partition.classAt
                (HypermapCode.lookup hypermap.edge dart) = face.val))

instance {hypermap : HypermapCode}
    {partition : ClassicalCertificateFacePartition.Code}
    (partitionValid : ClassicalCertificateFacePartition.Valid hypermap partition)
    (contract : Finset (Fin hypermap.dartCount)) (components : Code) :
    Decidable (Conditions partitionValid contract components) := by
  unfold Conditions
  infer_instance

/-- Semantic form of an accepted component-forest certificate. -/
structure Valid {hypermap : HypermapCode}
    {partition : ClassicalCertificateFacePartition.Code}
    (partitionValid : ClassicalCertificateFacePartition.Valid hypermap partition)
    (contract : Finset (Fin hypermap.dartCount)) (components : Code) : Prop where
  componentOfFaceSize :
    components.componentOfFace.size = partition.faceCount
  representativeSize :
    components.representative.size = components.componentCount
  parentSize : components.parent.size = partition.faceCount
  linkDartSize : components.linkDart.size = partition.faceCount
  depthSize : components.depth.size = partition.faceCount
  componentInRange : ∀ face : Fin partition.faceCount,
    components.componentAt face.val < components.componentCount
  representativeInRange : ∀ component : Fin components.componentCount,
    components.representativeAt component.val < partition.faceCount
  parentInRange : ∀ face : Fin partition.faceCount,
    components.parentAt face.val < partition.faceCount
  linkDartInRange : ∀ face : Fin partition.faceCount,
    components.linkDartAt face.val < hypermap.dartCount
  representativeComponent : ∀ component : Fin components.componentCount,
    components.componentAt (components.representativeAt component.val) =
      component.val
  rootOrLink : ∀ face : Fin partition.faceCount,
    face.val = components.representativeAt
        (components.componentAt face.val) ∨
      let parent := components.parentAt face.val
      let dart := components.linkDartAt face.val
      components.depthAt parent < components.depthAt face.val ∧
        components.componentAt parent = components.componentAt face.val ∧
        InContractAt contract dart ∧
        ((partition.classAt dart = face.val ∧
            partition.classAt (HypermapCode.lookup hypermap.edge dart) =
              parent) ∨
          (partition.classAt dart = parent ∧
            partition.classAt (HypermapCode.lookup hypermap.edge dart) =
              face.val))

/-- Reflected checker for a contract-component spanning forest. -/
def checker {hypermap : HypermapCode}
    {partition : ClassicalCertificateFacePartition.Code}
    (partitionValid : ClassicalCertificateFacePartition.Valid hypermap partition)
    (contract : Finset (Fin hypermap.dartCount)) (components : Code) : Bool :=
  decide (Conditions partitionValid contract components)

theorem valid_of_checker_true {hypermap : HypermapCode}
    {partition : ClassicalCertificateFacePartition.Code}
    (partitionValid : ClassicalCertificateFacePartition.Valid hypermap partition)
    (contract : Finset (Fin hypermap.dartCount)) (components : Code)
    (haccepted : checker partitionValid contract components = true) :
    Valid partitionValid contract components := by
  have hconditions : Conditions partitionValid contract components :=
    Bool.of_decide_true (by simpa [checker] using haccepted)
  rcases hconditions with
    ⟨hcomponentSize, hrepresentativeSize, hparentSize, hlinkSize,
      hdepthSize, hcomponentRange, hrepresentativeRange, hparentRange,
      hlinkRange, hrepresentativeComponent, hrootOrLink⟩
  exact ⟨hcomponentSize, hrepresentativeSize, hparentSize, hlinkSize,
    hdepthSize, hcomponentRange, hrepresentativeRange, hparentRange,
    hlinkRange, hrepresentativeComponent, hrootOrLink⟩

variable {hypermap : HypermapCode}
  {partition : ClassicalCertificateFacePartition.Code}
  {partitionValid : ClassicalCertificateFacePartition.Valid hypermap partition}
  {contract : Finset (Fin hypermap.dartCount)} {components : Code}

/-- The checked component containing a face class. -/
def component (valid : Valid partitionValid contract components)
    (face : Fin partition.faceCount) : Fin components.componentCount :=
  ⟨components.componentAt face.val, valid.componentInRange face⟩

/-- The checked representative face of a contract component. -/
def representative (valid : Valid partitionValid contract components)
    (index : Fin components.componentCount) : Fin partition.faceCount :=
  ⟨components.representativeAt index.val,
    valid.representativeInRange index⟩

/-- The parent face in the certified equality forest. -/
def parent (valid : Valid partitionValid contract components)
    (face : Fin partition.faceCount) : Fin partition.faceCount :=
  ⟨components.parentAt face.val, valid.parentInRange face⟩

/-- The selected contract dart joining a non-root face to its parent. -/
def linkDart (valid : Valid partitionValid contract components)
    (face : Fin partition.faceCount) : Fin hypermap.dartCount :=
  ⟨components.linkDartAt face.val, valid.linkDartInRange face⟩

@[simp] theorem component_representative
    (valid : Valid partitionValid contract components)
    (index : Fin components.componentCount) :
    component valid (representative valid index) = index := by
  apply Fin.ext
  exact valid.representativeComponent index

/-- Restrict a face assignment to one representative per contract component. -/
def restrictAssignment (valid : Valid partitionValid contract components)
    (assignment : Fin partition.faceCount → Color) :
    Fin components.componentCount → Color :=
  fun index => assignment (representative valid index)

/-- Pull a component coloring back to all face classes. -/
def liftAssignment (valid : Valid partitionValid contract components)
    (assignment : Fin components.componentCount → Color) :
    Fin partition.faceCount → Color :=
  fun face => assignment (component valid face)

theorem edgeTable_toFin_val
    (haccepted : hypermap.Accepted)
    (dart : Fin hypermap.dartCount) :
    ((edgeTable hypermap).toFin dart).val =
      HypermapCode.lookup hypermap.edge dart.val := by
  exact RawTable.toFin_val (edgeTable hypermap)
    haccepted.2.2.2.1 dart

private theorem assignment_eq_parent_of_not_root
    (valid : Valid partitionValid contract components)
    (assignment : Fin partition.faceCount → Color)
    (hcontract : IsContractAssignment partitionValid contract assignment)
    (face : Fin partition.faceCount)
    (hroot : face.val ≠ components.representativeAt
      (components.componentAt face.val)) :
    assignment face = assignment (parent valid face) := by
  have hlink := (valid.rootOrLink face).resolve_left hroot
  dsimp only at hlink
  rcases hlink with ⟨_, _, hinContract, hendpoints⟩
  have hinContract' : InRawContract contract (linkDart valid face) := by
    simpa [linkDart, InContractAt, valid.linkDartInRange face] using
      hinContract
  have hedge := (hcontract (linkDart valid face)).2 hinContract'
  have hedgeValue :
      ((edgeTable hypermap).toFin (linkDart valid face)).val =
        HypermapCode.lookup hypermap.edge
          (components.linkDartAt face.val) := by
    simpa [linkDart] using
      edgeTable_toFin_val partitionValid.hypermapAccepted
        (linkDart valid face)
  rcases hendpoints with hforward | hreverse
  · have hdart :
        faceClass partitionValid (linkDart valid face) = face := by
      apply Fin.ext
      exact hforward.1
    have hedgeFace :
        faceClass partitionValid
          ((edgeTable hypermap).toFin (linkDart valid face)) =
            parent valid face := by
      apply Fin.ext
      change partition.classAt
        (((edgeTable hypermap).toFin (linkDart valid face)).val) = _
      rw [hedgeValue]
      exact hforward.2
    simpa [colorOfAssignment, hdart, hedgeFace] using hedge.symm
  · have hdart :
        faceClass partitionValid (linkDart valid face) =
          parent valid face := by
      apply Fin.ext
      exact hreverse.1
    have hedgeFace :
        faceClass partitionValid
          ((edgeTable hypermap).toFin (linkDart valid face)) = face := by
      apply Fin.ext
      change partition.classAt
        (((edgeTable hypermap).toFin (linkDart valid face)).val) = _
      rw [hedgeValue]
      exact hreverse.2
    simpa [colorOfAssignment, hdart, hedgeFace] using hedge

/-- Every assignment satisfying the contract equations is constant on each
certified component. -/
theorem assignment_eq_representative
    (valid : Valid partitionValid contract components)
    (assignment : Fin partition.faceCount → Color)
    (hcontract : IsContractAssignment partitionValid contract assignment)
    (face : Fin partition.faceCount) :
    assignment face = assignment
      (representative valid (component valid face)) := by
  by_cases hroot : face.val = components.representativeAt
      (components.componentAt face.val)
  · congr 1
    apply Fin.ext
    exact hroot
  · have hlink := (valid.rootOrLink face).resolve_left hroot
    dsimp only at hlink
    have hparentDepth :
        components.depthAt (parent valid face).val <
          components.depthAt face.val := hlink.1
    have hparentComponent :
        component valid (parent valid face) = component valid face := by
      apply Fin.ext
      exact hlink.2.1
    calc
      assignment face = assignment (parent valid face) :=
        assignment_eq_parent_of_not_root valid assignment hcontract face hroot
      _ = assignment
          (representative valid (component valid (parent valid face))) :=
        assignment_eq_representative valid assignment hcontract
          (parent valid face)
      _ = assignment
          (representative valid (component valid face)) := by
        rw [hparentComponent]
termination_by components.depthAt face.val
decreasing_by exact hparentDepth

/-- Contract assignments factor exactly through the checked component
quotient. -/
theorem lift_restrictAssignment_eq
    (valid : Valid partitionValid contract components)
    (assignment : Fin partition.faceCount → Color)
    (hcontract : IsContractAssignment partitionValid contract assignment) :
    liftAssignment valid (restrictAssignment valid assignment) = assignment := by
  funext face
  exact (assignment_eq_representative valid assignment hcontract face).symm

end ClassicalCertificateContractComponents

end Mettapedia.GraphTheory.FourColor
