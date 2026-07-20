import Mettapedia.GraphTheory.FourColor.ClassicalCertificateHypermapColoring

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateFacePartition

open ClassicalCertificateConfiguration
open ClassicalCertificateHypermap
open ClassicalCertificateHypermapColoring

/-- A finite quotient of the darts by face cycles.  The distance entries are
proof witnesses: following the face permutation that many times must reach
the declared representative of the dart's class. -/
structure Code where
  faceCount : Nat
  classOf : Array Nat
  representative : Array Nat
  distance : Array Nat
  deriving DecidableEq, Repr

namespace Code

def classAt (code : Code) (dart : Nat) : Nat :=
  HypermapCode.lookup code.classOf dart

def representativeAt (code : Code) (face : Nat) : Nat :=
  HypermapCode.lookup code.representative face

def distanceAt (code : Code) (dart : Nat) : Nat :=
  HypermapCode.lookup code.distance dart

end Code

/-- The decoded edge table, with its dart count exposed definitionally. -/
def edgeTable (hypermap : HypermapCode) : RawTable hypermap.dartCount :=
  fun dart => HypermapCode.lookup hypermap.edge dart.val

/-- The decoded face table, with its dart count exposed definitionally. -/
def faceTable (hypermap : HypermapCode) : RawTable hypermap.dartCount :=
  fun dart => HypermapCode.lookup hypermap.face dart.val

/-- Iterate an executable permutation table. -/
def iterateTable {n : Nat} (table : RawTable n) :
    Nat → Fin n → Fin n
  | 0, dart => dart
  | steps + 1, dart => table.toFin (iterateTable table steps dart)

/-- Exact semantics of a face-partition certificate.  Class preservation
makes every class assignment face-constant.  Reachability of a representative
makes the representation complete for every face-constant dart coloring. -/
structure Valid (hypermap : HypermapCode) (partition : Code) : Prop where
  hypermapAccepted : hypermap.Accepted
  classOfSize : partition.classOf.size = hypermap.dartCount
  representativeSize : partition.representative.size = partition.faceCount
  distanceSize : partition.distance.size = hypermap.dartCount
  classInRange : ∀ dart : Fin hypermap.dartCount,
    partition.classAt dart.val < partition.faceCount
  representativeInRange : ∀ face : Fin partition.faceCount,
    partition.representativeAt face.val < hypermap.dartCount
  representativeClass : ∀ face : Fin partition.faceCount,
    partition.classAt (partition.representativeAt face.val) = face.val
  faceClassInvariant : ∀ dart : Fin hypermap.dartCount,
    partition.classAt ((faceTable hypermap).toFin dart).val =
      partition.classAt dart.val
  reachesRepresentative : ∀ dart : Fin hypermap.dartCount,
    (iterateTable (faceTable hypermap)
      (partition.distanceAt dart.val) dart).val =
      partition.representativeAt (partition.classAt dart.val)

/-- Decidable conditions reflected by the checker. -/
def Conditions (hypermap : HypermapCode) (partition : Code) : Prop :=
  hypermap.Accepted ∧
    partition.classOf.size = hypermap.dartCount ∧
    partition.representative.size = partition.faceCount ∧
    partition.distance.size = hypermap.dartCount ∧
    (∀ dart : Fin hypermap.dartCount,
      partition.classAt dart.val < partition.faceCount) ∧
    (∀ face : Fin partition.faceCount,
      partition.representativeAt face.val < hypermap.dartCount) ∧
    (∀ face : Fin partition.faceCount,
      partition.classAt (partition.representativeAt face.val) = face.val) ∧
    (∀ dart : Fin hypermap.dartCount,
      partition.classAt ((faceTable hypermap).toFin dart).val =
        partition.classAt dart.val) ∧
    ∀ dart : Fin hypermap.dartCount,
      (iterateTable (faceTable hypermap)
        (partition.distanceAt dart.val) dart).val =
        partition.representativeAt (partition.classAt dart.val)

instance (hypermap : HypermapCode) (partition : Code) :
    Decidable (Conditions hypermap partition) := by
  unfold Conditions
  infer_instance

/-- Reflected checker for an externally generated face quotient. -/
def checker (hypermap : HypermapCode) (partition : Code) : Bool :=
  decide (Conditions hypermap partition)

theorem valid_of_checker_true (hypermap : HypermapCode) (partition : Code)
    (haccepted : checker hypermap partition = true) :
    Valid hypermap partition := by
  have hconditions : Conditions hypermap partition :=
    Bool.of_decide_true (by simpa [checker] using haccepted)
  rcases hconditions with
    ⟨hmap, hclassSize, hrepresentativeSize, hdistanceSize,
      hclassRange, hrepresentativeRange, hrepresentativeClass,
      hinvariant, hrepresentative⟩
  exact ⟨hmap, hclassSize, hrepresentativeSize, hdistanceSize,
    hclassRange, hrepresentativeRange, hrepresentativeClass,
    hinvariant, hrepresentative⟩

variable {hypermap : HypermapCode} {partition : Code}

/-- The checked face class containing a dart. -/
def faceClass (valid : Valid hypermap partition)
    (dart : Fin hypermap.dartCount) : Fin partition.faceCount :=
  ⟨partition.classAt dart.val, valid.classInRange dart⟩

/-- A checked dart representative for a face class. -/
def faceRepresentative (valid : Valid hypermap partition)
    (face : Fin partition.faceCount) : Fin hypermap.dartCount :=
  ⟨partition.representativeAt face.val,
    valid.representativeInRange face⟩

theorem faceClass_face (valid : Valid hypermap partition)
    (dart : Fin hypermap.dartCount) :
    faceClass valid ((faceTable hypermap).toFin dart) = faceClass valid dart := by
  apply Fin.ext
  exact valid.faceClassInvariant dart

theorem iterateTable_color_eq
    (color : Fin hypermap.dartCount → Color)
    (hface : ∀ dart : Fin hypermap.dartCount,
      color ((faceTable hypermap).toFin dart) = color dart) :
    ∀ steps (dart : Fin hypermap.dartCount),
      color (iterateTable (faceTable hypermap) steps dart) = color dart := by
  intro steps
  induction steps with
  | zero =>
      intro dart
      rfl
  | succ steps ih =>
      intro dart
      rw [iterateTable,
        hface (iterateTable (faceTable hypermap) steps dart), ih]

theorem iterateTable_distance_eq_representative
    (valid : Valid hypermap partition)
    (dart : Fin hypermap.dartCount) :
    iterateTable (faceTable hypermap) (partition.distanceAt dart.val) dart =
      faceRepresentative valid (faceClass valid dart) := by
  apply Fin.ext
  exact valid.reachesRepresentative dart

/-- Pull a four-color assignment on face classes back to all darts. -/
def colorOfAssignment (valid : Valid hypermap partition)
    (assignment : Fin partition.faceCount → Color) :
    Fin hypermap.dartCount → Color := fun dart => assignment (faceClass valid dart)

/-- Restrict a dart coloring to the declared face representatives. -/
def representativeAssignment (valid : Valid hypermap partition)
    (color : Fin hypermap.dartCount → Color) :
    Fin partition.faceCount → Color := fun face =>
  color (faceRepresentative valid face)

theorem colorOfAssignment_face_invariant
    (valid : Valid hypermap partition)
    (assignment : Fin partition.faceCount → Color)
    (dart : Fin hypermap.dartCount) :
    colorOfAssignment valid assignment ((faceTable hypermap).toFin dart) =
      colorOfAssignment valid assignment dart := by
  unfold colorOfAssignment
  rw [faceClass_face]

/-- Every face-constant dart coloring factors through the checked quotient. -/
theorem colorOf_representativeAssignment_eq
    (valid : Valid hypermap partition)
    (color : Fin hypermap.dartCount → Color)
    (hface : ∀ dart,
      color ((faceTable hypermap).toFin dart) = color dart) :
    colorOfAssignment valid (representativeAssignment valid color) = color := by
  funext dart
  change color (faceRepresentative valid (faceClass valid dart)) = color dart
  rw [← iterateTable_distance_eq_representative valid dart]
  exact iterateTable_color_eq color hface _ dart

/-- The finite edge constraints on an assignment to face classes. -/
def IsProperAssignment (valid : Valid hypermap partition)
    (assignment : Fin partition.faceCount → Color) : Prop :=
  ∀ dart : Fin hypermap.dartCount,
    colorOfAssignment valid assignment ((edgeTable hypermap).toFin dart) ≠
      colorOfAssignment valid assignment dart

instance (valid : Valid hypermap partition)
    (assignment : Fin partition.faceCount → Color) :
    Decidable (IsProperAssignment valid assignment) := by
  unfold IsProperAssignment
  infer_instance

/-- The standard finite hypermap certified together with the partition. -/
noncomputable def checkedHypermap (valid : Valid hypermap partition) :
    FiniteHypermap (Fin hypermap.dartCount) :=
  hypermap.decode.toFiniteHypermap valid.hypermapAccepted.2.2.2

@[simp] theorem checkedHypermap_edge
    (valid : Valid hypermap partition)
    (dart : Fin hypermap.dartCount) :
    (checkedHypermap valid).edge dart = (edgeTable hypermap).toFin dart := by
  rfl

@[simp] theorem checkedHypermap_face
    (valid : Valid hypermap partition)
    (dart : Fin hypermap.dartCount) :
    (checkedHypermap valid).face dart = (faceTable hypermap).toFin dart := by
  rfl

theorem isFaceColoring_of_isProperAssignment
    (valid : Valid hypermap partition)
    (assignment : Fin partition.faceCount → Color)
    (hproper : IsProperAssignment valid assignment) :
    FiniteHypermap.IsFaceColoring (checkedHypermap valid)
      (colorOfAssignment valid assignment) := by
  constructor
  · intro dart
    simpa using hproper dart
  · intro dart
    simpa using
      colorOfAssignment_face_invariant valid assignment dart

/-- Conversely, every genuine coloring of the checked hypermap is represented
by one of the finite face-class assignments. -/
theorem everyFaceColoring_factors
    (valid : Valid hypermap partition)
    (color : Fin hypermap.dartCount → Color)
    (hcolor : FiniteHypermap.IsFaceColoring (checkedHypermap valid) color) :
    ∃ assignment : Fin partition.faceCount → Color,
      IsProperAssignment valid assignment ∧
        colorOfAssignment valid assignment = color := by
  have hface : ∀ dart : Fin hypermap.dartCount,
      color ((faceTable hypermap).toFin dart) = color dart := by
    intro dart
    simpa using hcolor.2 dart
  let assignment := representativeAssignment valid color
  have hreconstruct : colorOfAssignment valid assignment = color :=
    colorOf_representativeAssignment_eq valid color hface
  refine ⟨assignment, ?_, hreconstruct⟩
  intro dart
  simpa [hreconstruct] using hcolor.1 dart

theorem faceColorable_iff_exists_properAssignment
    (valid : Valid hypermap partition) :
    FiniteHypermap.FaceColorable (checkedHypermap valid) ↔
      ∃ assignment : Fin partition.faceCount → Color,
        IsProperAssignment valid assignment := by
  constructor
  · rintro ⟨color, hcolor⟩
    obtain ⟨assignment, hproper, _⟩ :=
      everyFaceColoring_factors valid color hcolor
    exact ⟨assignment, hproper⟩
  · rintro ⟨assignment, hproper⟩
    exact ⟨colorOfAssignment valid assignment,
      isFaceColoring_of_isProperAssignment valid assignment hproper⟩

/-- A face-orbit certificate for the first classical catalogue entry.  Its 42
darts quotient to ten face variables. -/
def firstCatalogueFacePartition : Code where
  faceCount := 10
  classOf :=
    #[0, 1, 0, 2, 0, 3, 4, 5, 4, 6, 4, 7, 5, 3, 5, 8, 5, 6, 3, 2, 3,
      8, 1, 7, 1, 9, 1, 2, 7, 6, 7, 9, 2, 9, 2, 8, 8, 9, 8, 6, 6, 9]
  representative := #[0, 1, 3, 5, 6, 7, 9, 11, 15, 25]
  distance :=
    #[0, 0, 2, 0, 1, 0, 0, 0, 2, 0, 1, 0, 3, 1, 2, 0, 1, 4, 3, 1, 2,
      4, 3, 1, 2, 0, 1, 4, 3, 1, 2, 4, 3, 1, 2, 3, 2, 2, 1, 3, 2, 3]

theorem firstCatalogueFacePartition_checker :
    checker firstCatalogueSampleCode firstCatalogueFacePartition = true := by
  decide

theorem firstCatalogue_faceColorable_iff :
    FiniteHypermap.FaceColorable
        (checkedHypermap
          (valid_of_checker_true firstCatalogueSampleCode
            firstCatalogueFacePartition firstCatalogueFacePartition_checker)) ↔
      ∃ assignment : Fin firstCatalogueFacePartition.faceCount → Color,
        IsProperAssignment
          (valid_of_checker_true firstCatalogueSampleCode
            firstCatalogueFacePartition firstCatalogueFacePartition_checker)
          assignment :=
  faceColorable_iff_exists_properAssignment _

end ClassicalCertificateFacePartition

end Mettapedia.GraphTheory.FourColor
