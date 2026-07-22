import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadata

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateHypermap
namespace FiniteHypermap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Both darts of every selected edge, retaining the contract order. -/
def edgeClosure (H : FiniteHypermap D) (contract : List D) : List D :=
  contract.flatMap fun dart => [dart, H.edge dart]

/-- The union of all face orbits represented by a list of darts. -/
def FaceBand (H : FiniteHypermap D) (darts : List D) (dart : D) : Prop :=
  ∃ representative ∈ darts, H.face.SameCycle dart representative

instance (H : FiniteHypermap D) (darts : List D) (dart : D) :
    Decidable (H.FaceBand darts dart) := by
  unfold FaceBand
  infer_instance

/-- Two darts lie on adjacent faces when some dart on the first face crosses
to the second face. -/
def FaceAdjacent (H : FiniteHypermap D) (left right : D) : Prop :=
  ∃ dart, H.face.SameCycle left dart ∧
    H.face.SameCycle (H.edge dart) right

instance (H : FiniteHypermap D) (left right : D) :
    Decidable (H.FaceAdjacent left right) := by
  unfold FaceAdjacent
  infer_instance

/-- The darts in one face orbit. -/
def faceOrbitDarts (H : FiniteHypermap D) (dart : D) : Finset D :=
  Finset.univ.filter fun other => H.face.SameCycle dart other

/-- A face sees at least three contract-band incidences but does not see all
contract-band darts. -/
def IsTriad (H : FiniteHypermap D) (band : List D) (dart : D) : Prop :=
  2 < ((H.faceOrbitDarts dart).filter fun boundary =>
    H.FaceBand band (H.edge boundary)).card ∧
  ¬ ∀ selected ∈ band, H.FaceAdjacent dart selected

instance (H : FiniteHypermap D) (band : List D) (dart : D) :
    Decidable (H.IsTriad band dart) := by
  unfold IsTriad
  infer_instance

/-- A dart list meets every vertex orbit at most once. -/
def NodeSparse (H : FiniteHypermap D) (darts : List D) : Prop :=
  darts.Pairwise fun left right => ¬ H.node.SameCycle left right

instance (H : FiniteHypermap D) (darts : List D) :
    Decidable (H.NodeSparse darts) := by
  unfold NodeSparse
  infer_instance

/-- The standard classical validity conditions for a contract inside a ring. -/
structure ValidContract (H : FiniteHypermap D)
    (ring contract : List D) : Prop where
  offRing : ring.Disjoint (H.edgeClosure contract)
  sparse : H.NodeSparse (H.edgeClosure contract)
  size : contract.length = 1 ∨ contract.length = 2 ∨
    contract.length = 3 ∨ contract.length = 4
  triad : contract.length = 4 →
    ∃ dart, ¬ H.FaceBand ring dart ∧
      H.IsTriad (H.edgeClosure contract) dart

end FiniteHypermap
end ClassicalCertificateHypermap

namespace ClassicalCertificateContractValidity

open ClassicalCertificateConfiguration
open ClassicalCertificateFacePartition
open ClassicalCertificateHypermap
open ClassicalCertificateReductionMetadata

/-- The decoded node permutation table. -/
def nodeTable (hypermap : HypermapCode) : RawTable hypermap.dartCount :=
  fun dart => HypermapCode.lookup hypermap.node dart.val

theorem iterateTable_eq_pow {n : Nat} (table : RawTable n)
    (hpermutation : table.IsPermutation) (steps : Nat) (dart : Fin n) :
    iterateTable table steps dart = (table.toPerm hpermutation ^ steps) dart := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [iterateTable, ih,
        ← RawTable.toPerm_apply table hpermutation]
      simp only [pow_succ', Equiv.Perm.mul_apply]

/-- The checked finite face quotient has exactly the same fibers as the
standard face-cycle relation. -/
theorem checkedHypermap_face_sameCycle_iff
    {hypermap : HypermapCode} {partition : ClassicalCertificateFacePartition.Code}
    (valid : ClassicalCertificateFacePartition.Valid hypermap partition)
    (left right : Fin hypermap.dartCount) :
    (checkedHypermap valid).face.SameCycle left right ↔
      faceClass valid left = faceClass valid right := by
  constructor
  · intro hsame
    exact ClassicalCertificateHypermap.FiniteHypermap.invariant_of_sameCycle
      (checkedHypermap valid).face (faceClass valid)
        (fun dart => faceClass_face valid dart) hsame
  · intro hclass
    let representative := faceRepresentative valid (faceClass valid left)
    have hleft : (checkedHypermap valid).face.SameCycle left representative := by
      apply Equiv.Perm.SameCycle.of_pow_left
      apply Eq.sameCycle
      change ((faceTable hypermap).toPerm
          valid.hypermapAccepted.2.2.2.2.2.1 ^
            partition.distanceAt left.val) left = representative
      rw [← iterateTable_eq_pow]
      exact iterateTable_distance_eq_representative valid left
    have hright : (checkedHypermap valid).face.SameCycle right representative := by
      apply Equiv.Perm.SameCycle.of_pow_left
      apply Eq.sameCycle
      change ((faceTable hypermap).toPerm
          valid.hypermapAccepted.2.2.2.2.2.1 ^
            partition.distanceAt right.val) right = representative
      rw [← iterateTable_eq_pow]
      simpa [representative, hclass] using
        iterateTable_distance_eq_representative valid right
    exact hleft.trans hright.symm

@[simp] theorem checkedHypermap_node
    {hypermap : HypermapCode} {partition : ClassicalCertificateFacePartition.Code}
    (valid : ClassicalCertificateFacePartition.Valid hypermap partition)
    (dart : Fin hypermap.dartCount) :
    (checkedHypermap valid).node dart = (nodeTable hypermap).toFin dart := by
  rfl

/-- Darts decoded from the raw contract representatives. -/
def selectedDarts (metadata : ClassicalCertificateReductionMetadata.Code) :
    List (Fin metadata.hypermap.dartCount) :=
  finsOfValues metadata.hypermap.dartCount metadata.contractValues

/-- The executable two-dart closure of the selected contract edges. -/
def edgeClosureDarts (metadata : ClassicalCertificateReductionMetadata.Code) :
    List (Fin metadata.hypermap.dartCount) :=
  (selectedDarts metadata).flatMap fun dart =>
    [dart, (edgeTable metadata.hypermap).toFin dart]

/-- Equality of checked face-class labels, used as the reflected same-face
relation. -/
def RawSameFace (metadata : ClassicalCertificateReductionMetadata.Code)
    (left right : Fin metadata.hypermap.dartCount) : Prop :=
  metadata.partition.classAt left.val =
    metadata.partition.classAt right.val

instance (metadata : ClassicalCertificateReductionMetadata.Code)
    (left right : Fin metadata.hypermap.dartCount) :
    Decidable (RawSameFace metadata left right) := by
  unfold RawSameFace
  infer_instance

/-- Reflected union of the face orbits represented by a dart list. -/
def RawFaceBand (metadata : ClassicalCertificateReductionMetadata.Code)
    (darts : List (Fin metadata.hypermap.dartCount))
    (dart : Fin metadata.hypermap.dartCount) : Prop :=
  ∃ representative ∈ darts, RawSameFace metadata dart representative

instance (metadata : ClassicalCertificateReductionMetadata.Code)
    (darts : List (Fin metadata.hypermap.dartCount))
    (dart : Fin metadata.hypermap.dartCount) :
    Decidable (RawFaceBand metadata darts dart) := by
  unfold RawFaceBand
  infer_instance

/-- Reflected adjacency of two face classes. -/
def RawFaceAdjacent (metadata : ClassicalCertificateReductionMetadata.Code)
    (left right : Fin metadata.hypermap.dartCount) : Prop :=
  ∃ dart, RawSameFace metadata left dart ∧
    RawSameFace metadata
      ((edgeTable metadata.hypermap).toFin dart) right

instance (metadata : ClassicalCertificateReductionMetadata.Code)
    (left right : Fin metadata.hypermap.dartCount) :
    Decidable (RawFaceAdjacent metadata left right) := by
  unfold RawFaceAdjacent
  infer_instance

/-- Reflected face orbit. -/
def rawFaceOrbitDarts (metadata : ClassicalCertificateReductionMetadata.Code)
    (dart : Fin metadata.hypermap.dartCount) :
    Finset (Fin metadata.hypermap.dartCount) :=
  Finset.univ.filter fun other => RawSameFace metadata dart other

/-- The exact finite triad predicate, with same-face queries reflected through
the checked face partition. -/
def RawTriad (metadata : ClassicalCertificateReductionMetadata.Code)
    (band : List (Fin metadata.hypermap.dartCount))
    (dart : Fin metadata.hypermap.dartCount) : Prop :=
  2 < ((rawFaceOrbitDarts metadata dart).filter fun boundary =>
    RawFaceBand metadata band
      ((edgeTable metadata.hypermap).toFin boundary)).card ∧
  ¬ ∀ selected ∈ band, RawFaceAdjacent metadata dart selected

instance (metadata : ClassicalCertificateReductionMetadata.Code)
    (band : List (Fin metadata.hypermap.dartCount))
    (dart : Fin metadata.hypermap.dartCount) :
    Decidable (RawTriad metadata band dart) := by
  unfold RawTriad
  infer_instance

/-- One invariant natural-number label per vertex orbit, and one actual dart
naming a triad when the contract has four edges. -/
structure Certificate where
  nodeClass : Array Nat
  triadDart : Nat
  deriving DecidableEq, Repr

namespace Certificate

def nodeClassAt (certificate : Certificate) (dart : Nat) : Nat :=
  HypermapCode.lookup certificate.nodeClass dart

def Conditions (metadata : ClassicalCertificateReductionMetadata.Code)
    (certificate : Certificate) : Prop :=
  certificate.nodeClass.size = metadata.hypermap.dartCount ∧
  (∀ dart : Fin metadata.hypermap.dartCount,
    certificate.nodeClassAt
      ((nodeTable metadata.hypermap).toFin dart).val =
        certificate.nodeClassAt dart.val) ∧
  ((edgeClosureDarts metadata).map fun dart =>
    certificate.nodeClassAt dart.val).Nodup ∧
  (∀ dart : Fin metadata.hypermap.dartCount,
    dart ∈ ring metadata → dart ∉ edgeClosureDarts metadata) ∧
  ((selectedDarts metadata).length = 1 ∨
    (selectedDarts metadata).length = 2 ∨
    (selectedDarts metadata).length = 3 ∨
    (selectedDarts metadata).length = 4) ∧
  ((selectedDarts metadata).length = 4 →
    ∃ dart : Fin metadata.hypermap.dartCount,
      dart.val = certificate.triadDart ∧
        ¬ RawFaceBand metadata (ring metadata) dart ∧
          RawTriad metadata (edgeClosureDarts metadata) dart)

instance (metadata : ClassicalCertificateReductionMetadata.Code)
    (certificate : Certificate) :
    Decidable (Conditions metadata certificate) := by
  unfold Conditions
  infer_instance

def checker (metadata : ClassicalCertificateReductionMetadata.Code)
    (certificate : Certificate) : Bool :=
  decide (Conditions metadata certificate)

theorem conditions_of_checker_true
    (metadata : ClassicalCertificateReductionMetadata.Code)
    (certificate : Certificate)
    (hchecker : certificate.checker metadata = true) :
    Conditions metadata certificate :=
  of_decide_eq_true (by simpa [checker] using hchecker)

end Certificate

theorem faceBand_iff_rawFaceBand
    {metadata : ClassicalCertificateReductionMetadata.Code}
    (valid : ClassicalCertificateReductionMetadata.Valid metadata)
    (darts : List (Fin metadata.hypermap.dartCount))
    (dart : Fin metadata.hypermap.dartCount) :
    (checkedHypermap valid.partitionValid).FaceBand darts dart ↔
      RawFaceBand metadata darts dart := by
  constructor
  · rintro ⟨representative, hrepresentative, hsame⟩
    refine ⟨representative, hrepresentative, ?_⟩
    exact congrArg Fin.val
      ((checkedHypermap_face_sameCycle_iff valid.partitionValid
        dart representative).1 hsame)
  · rintro ⟨representative, hrepresentative, hsame⟩
    refine ⟨representative, hrepresentative, ?_⟩
    apply (checkedHypermap_face_sameCycle_iff valid.partitionValid
      dart representative).2
    apply Fin.ext
    exact hsame

theorem faceAdjacent_iff_rawFaceAdjacent
    {metadata : ClassicalCertificateReductionMetadata.Code}
    (valid : ClassicalCertificateReductionMetadata.Valid metadata)
    (left right : Fin metadata.hypermap.dartCount) :
    (checkedHypermap valid.partitionValid).FaceAdjacent left right ↔
      RawFaceAdjacent metadata left right := by
  constructor
  · rintro ⟨dart, hleft, hright⟩
    refine ⟨dart, ?_, ?_⟩
    · exact congrArg Fin.val
        ((checkedHypermap_face_sameCycle_iff valid.partitionValid
          left dart).1 hleft)
    · exact congrArg Fin.val
        ((checkedHypermap_face_sameCycle_iff valid.partitionValid
          ((edgeTable metadata.hypermap).toFin dart) right).1 (by
            simpa using hright))
  · rintro ⟨dart, hleft, hright⟩
    refine ⟨dart, ?_, ?_⟩
    · apply (checkedHypermap_face_sameCycle_iff valid.partitionValid
        left dart).2
      apply Fin.ext
      exact hleft
    · simpa using
        ((checkedHypermap_face_sameCycle_iff valid.partitionValid
          ((edgeTable metadata.hypermap).toFin dart) right).2 (by
            apply Fin.ext
            exact hright))

theorem faceOrbitDarts_eq_rawFaceOrbitDarts
    {metadata : ClassicalCertificateReductionMetadata.Code}
    (valid : ClassicalCertificateReductionMetadata.Valid metadata)
    (dart : Fin metadata.hypermap.dartCount) :
    (checkedHypermap valid.partitionValid).faceOrbitDarts dart =
      rawFaceOrbitDarts metadata dart := by
  ext other
  simp only [FiniteHypermap.faceOrbitDarts, rawFaceOrbitDarts,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hsame
    exact congrArg Fin.val
      ((checkedHypermap_face_sameCycle_iff valid.partitionValid
        dart other).1 hsame)
  · intro hsame
    apply (checkedHypermap_face_sameCycle_iff valid.partitionValid
      dart other).2
    apply Fin.ext
    exact hsame

theorem isTriad_of_rawTriad
    {metadata : ClassicalCertificateReductionMetadata.Code}
    (valid : ClassicalCertificateReductionMetadata.Valid metadata)
    (band : List (Fin metadata.hypermap.dartCount))
    (dart : Fin metadata.hypermap.dartCount)
    (hraw : RawTriad metadata band dart) :
    (checkedHypermap valid.partitionValid).IsTriad band dart := by
  constructor
  · rw [faceOrbitDarts_eq_rawFaceOrbitDarts valid dart]
    have hfilter :
        ((rawFaceOrbitDarts metadata dart).filter fun boundary =>
          (checkedHypermap valid.partitionValid).FaceBand band
            ((checkedHypermap valid.partitionValid).edge boundary)) =
        ((rawFaceOrbitDarts metadata dart).filter fun boundary =>
          RawFaceBand metadata band
            ((edgeTable metadata.hypermap).toFin boundary)) := by
      ext boundary
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨horbit, hband⟩
        exact ⟨horbit, (faceBand_iff_rawFaceBand valid band _).1 (by
          simpa using hband)⟩
      · rintro ⟨horbit, hband⟩
        exact ⟨horbit, by
          simpa using (faceBand_iff_rawFaceBand valid band _).2 hband⟩
    rw [hfilter]
    exact hraw.1
  · intro hall
    apply hraw.2
    intro selected hselected
    exact (faceAdjacent_iff_rawFaceAdjacent valid dart selected).1
      (hall selected hselected)

theorem nodeSparse_of_invariant_of_map_nodup
    {D : Type*} [Fintype D] [DecidableEq D]
    (H : FiniteHypermap D) (value : D → Nat)
    (hinvariant : ∀ dart, value (H.node dart) = value dart)
    (darts : List D) (hnodup : (darts.map value).Nodup) :
    H.NodeSparse darts := by
  induction darts with
  | nil => simp [FiniteHypermap.NodeSparse]
  | cons first rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      rw [FiniteHypermap.NodeSparse, List.pairwise_cons]
      constructor
      · intro other hother hsame
        have hvalue :=
          ClassicalCertificateHypermap.FiniteHypermap.invariant_of_sameCycle
            H.node value hinvariant hsame
        apply hnodup.1
        rw [List.mem_map]
        exact ⟨other, hother, hvalue.symm⟩
      · exact ih hnodup.2

/-- A successful raw certificate proves the standard classical contract
validity predicate on the checked finite hypermap. -/
theorem validContract_of_checker_true
    (metadata : ClassicalCertificateReductionMetadata.Code)
    (valid : ClassicalCertificateReductionMetadata.Valid metadata)
    (certificate : Certificate)
    (hchecker : certificate.checker metadata = true) :
    (checkedHypermap valid.partitionValid).ValidContract
      (ring metadata) (selectedDarts metadata) := by
  have hconditions := certificate.conditions_of_checker_true metadata hchecker
  rcases hconditions with
    ⟨hnodeSize, hnodeInvariant, hnodeNodup, hoffRing, hsize, htriad⟩
  have hedgeClosure :
      (checkedHypermap valid.partitionValid).edgeClosure
          (selectedDarts metadata) = edgeClosureDarts metadata := by
    simp [FiniteHypermap.edgeClosure, edgeClosureDarts]
  refine ⟨?_, ?_, hsize, ?_⟩
  · rw [hedgeClosure]
    intro dart hring hclosure
    exact hoffRing dart hring hclosure
  · rw [hedgeClosure]
    apply nodeSparse_of_invariant_of_map_nodup
      (checkedHypermap valid.partitionValid)
      (fun dart => certificate.nodeClassAt dart.val)
    · intro dart
      simpa using hnodeInvariant dart
    · exact hnodeNodup
  · intro hfour
    obtain ⟨dart, _, hkern, hraw⟩ := htriad hfour
    refine ⟨dart, ?_, ?_⟩
    · exact fun hband => hkern
        ((faceBand_iff_rawFaceBand valid (ring metadata) dart).1 hband)
    · rw [hedgeClosure]
      exact isTriad_of_rawTriad valid (edgeClosureDarts metadata) dart hraw

end ClassicalCertificateContractValidity

end Mettapedia.GraphTheory.FourColor
