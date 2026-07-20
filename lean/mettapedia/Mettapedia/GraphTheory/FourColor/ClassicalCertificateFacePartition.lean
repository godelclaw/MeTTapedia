import Mettapedia.GraphTheory.FourColor.ClassicalCertificateHypermapColoring

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateFacePartition

open ClassicalCertificateConfiguration
open ClassicalCertificateColorTrace
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

/-- Raw executable membership in a selected contract edge or its mate. -/
def InRawContract (contract : Finset (Fin hypermap.dartCount))
    (dart : Fin hypermap.dartCount) : Prop :=
  dart ∈ contract ∨ (edgeTable hypermap).toFin dart ∈ contract

instance (contract : Finset (Fin hypermap.dartCount))
    (dart : Fin hypermap.dartCount) :
    Decidable (InRawContract contract dart) := by
  unfold InRawContract
  infer_instance

theorem inContract_checkedHypermap_iff
    (valid : Valid hypermap partition)
    (contract : Finset (Fin hypermap.dartCount))
    (dart : Fin hypermap.dartCount) :
    FiniteHypermap.InContract (checkedHypermap valid) contract dart ↔
      InRawContract contract dart := by
  simp [FiniteHypermap.InContract, InRawContract]

/-- Consecutive darts in the forward node order are separated by the edge at
the second dart. -/
def RawReverseBoundaryStep (hypermap : HypermapCode)
    (current next : Fin hypermap.dartCount) : Prop :=
  current = (faceTable hypermap).toFin ((edgeTable hypermap).toFin next)

instance (hypermap : HypermapCode)
    (current next : Fin hypermap.dartCount) :
    Decidable (RawReverseBoundaryStep hypermap current next) := by
  unfold RawReverseBoundaryStep
  infer_instance

instance (hypermap : HypermapCode) :
    DecidableRel (RawReverseBoundaryStep hypermap) :=
  fun _ _ => inferInstance

/-- A cyclic boundary written in forward node order. -/
def RawReverseBoundaryCycle (hypermap : HypermapCode) :
    List (Fin hypermap.dartCount) → Prop
  | [] => True
  | first :: rest =>
      List.IsChain (RawReverseBoundaryStep hypermap) (first :: rest) ∧
        rest.getLastD first =
          (faceTable hypermap).toFin ((edgeTable hypermap).toFin first)

instance (hypermap : HypermapCode)
    (ring : List (Fin hypermap.dartCount)) :
    Decidable (RawReverseBoundaryCycle hypermap ring) := by
  cases ring with
  | nil => exact isTrue trivial
  | cons first rest =>
      change Decidable
        (List.IsChain (RawReverseBoundaryStep hypermap) (first :: rest) ∧
          rest.getLastD first =
            (faceTable hypermap).toFin ((edgeTable hypermap).toFin first))
      infer_instance

/-- A contract is internal to a boundary when none of its selected edges meet
the boundary darts. -/
def ContractAvoidsBoundary (contract : Finset (Fin hypermap.dartCount))
    (ring : List (Fin hypermap.dartCount)) : Prop :=
  ∀ dart ∈ ring, ¬ InRawContract contract dart

instance (contract : Finset (Fin hypermap.dartCount))
    (ring : List (Fin hypermap.dartCount)) :
    Decidable (ContractAvoidsBoundary contract ring) := by
  unfold ContractAvoidsBoundary
  infer_instance

/-- The finite edge equations for a contract coloring on face classes. -/
def IsContractAssignment (valid : Valid hypermap partition)
    (contract : Finset (Fin hypermap.dartCount))
    (assignment : Fin partition.faceCount → Color) : Prop :=
  ∀ dart : Fin hypermap.dartCount,
    (colorOfAssignment valid assignment ((edgeTable hypermap).toFin dart) =
      colorOfAssignment valid assignment dart) ↔
        InRawContract contract dart

instance (valid : Valid hypermap partition)
    (contract : Finset (Fin hypermap.dartCount))
    (assignment : Fin partition.faceCount → Color) :
    Decidable (IsContractAssignment valid contract assignment) := by
  unfold IsContractAssignment
  infer_instance

theorem isContractAssignment_empty_iff
    (valid : Valid hypermap partition)
    (assignment : Fin partition.faceCount → Color) :
    IsContractAssignment valid ∅ assignment ↔
      IsProperAssignment valid assignment := by
  constructor
  · intro hcontract dart heq
    have hin := (hcontract dart).1 heq
    simpa [InRawContract] using hin
  · intro hproper dart
    constructor
    · intro heq
      exact (hproper dart heq).elim
    · intro hin
      simpa [InRawContract] using hin

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

theorem isContractColoring_of_isContractAssignment
    (valid : Valid hypermap partition)
    (contract : Finset (Fin hypermap.dartCount))
    (assignment : Fin partition.faceCount → Color)
    (hcontract : IsContractAssignment valid contract assignment) :
    FiniteHypermap.IsContractColoring (checkedHypermap valid) contract
      (colorOfAssignment valid assignment) := by
  constructor
  · intro dart
    rw [inContract_checkedHypermap_iff]
    simpa using hcontract dart
  · intro dart
    simpa using colorOfAssignment_face_invariant valid assignment dart

theorem color_ne_of_rawReverseBoundaryStep
    (valid : Valid hypermap partition)
    (contract : Finset (Fin hypermap.dartCount))
    (assignment : Fin partition.faceCount → Color)
    (hcontract : IsContractAssignment valid contract assignment)
    {current next : Fin hypermap.dartCount}
    (hstep : RawReverseBoundaryStep hypermap current next)
    (havoid : ¬ InRawContract contract next) :
    colorOfAssignment valid assignment current ≠
      colorOfAssignment valid assignment next := by
  intro heq
  have hface := colorOfAssignment_face_invariant valid assignment
    ((edgeTable hypermap).toFin next)
  have hedge :
      colorOfAssignment valid assignment ((edgeTable hypermap).toFin next) =
        colorOfAssignment valid assignment current := by
    rw [hstep]
    exact hface.symm
  have hin : InRawContract contract next :=
    (hcontract next).1 (hedge.trans heq)
  exact havoid hin

private theorem isChain_strengthen_right
    {D : Type*} {step : D → D → Prop} {property : D → Prop}
    {values : List D}
    (hchain : List.IsChain step values)
    (hproperty : ∀ value ∈ values, property value) :
    List.IsChain (fun current next => step current next ∧ property next)
      values := by
  induction values with
  | nil => simp
  | cons first rest ih =>
      cases rest with
      | nil => simp
      | cons next rest =>
          rw [List.isChain_cons_cons] at hchain ⊢
          exact ⟨⟨hchain.1, hproperty next (by simp)⟩,
            ih hchain.2 (by
              intro value hmem
              exact hproperty value (by simp [hmem]))⟩

private theorem adjacentDistinct_map_of_chain
    {D : Type*} {color : D → Color} {values : List D}
    (step : D → D → Prop)
    (hne : ∀ {current next}, step current next →
      color current ≠ color next)
    (hchain : List.IsChain step values) :
    AdjacentDistinct (values.map color) := by
  induction values with
  | nil => trivial
  | cons first rest ih =>
      cases rest with
      | nil => trivial
      | cons next rest =>
          rw [List.isChain_cons_cons] at hchain
          simp only [List.map_cons, AdjacentDistinct]
          exact ⟨hne hchain.1, ih hchain.2⟩

/-- An internal contract leaves the cyclic boundary word proper. -/
theorem cyclicallyDistinct_ringColorWord_of_contract
    (valid : Valid hypermap partition)
    (contract : Finset (Fin hypermap.dartCount))
    (ring : List (Fin hypermap.dartCount))
    (assignment : Fin partition.faceCount → Color)
    (hcontract : IsContractAssignment valid contract assignment)
    (hcycle : RawReverseBoundaryCycle hypermap ring)
    (havoid : ContractAvoidsBoundary contract ring) :
    CyclicallyDistinct
      (FiniteHypermap.ringColorWord ring
        (colorOfAssignment valid assignment)) := by
  cases ring with
  | nil => trivial
  | cons first rest =>
      rcases hcycle with ⟨hchain, hclose⟩
      constructor
      · have hchainAvoid := isChain_strengthen_right hchain havoid
        exact adjacentDistinct_map_of_chain
          (fun current next =>
            RawReverseBoundaryStep hypermap current next ∧
              ¬ InRawContract contract next)
          (fun hstep => color_ne_of_rawReverseBoundaryStep valid contract
            assignment hcontract hstep.1 hstep.2)
          hchainAvoid
      ·
        have hne := color_ne_of_rawReverseBoundaryStep valid contract
          assignment hcontract hclose (havoid first (by simp))
        simpa [FiniteHypermap.ringColorWord] using hne

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

/-- Every genuine contract coloring also factors through the same checked face
quotient. -/
theorem everyContractColoring_factors
    (valid : Valid hypermap partition)
    (contract : Finset (Fin hypermap.dartCount))
    (color : Fin hypermap.dartCount → Color)
    (hcolor : FiniteHypermap.IsContractColoring
      (checkedHypermap valid) contract color) :
    ∃ assignment : Fin partition.faceCount → Color,
      IsContractAssignment valid contract assignment ∧
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
  rw [← inContract_checkedHypermap_iff valid contract dart]
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

/-- Boundary trace computed directly from a face-class assignment. -/
def ringTraceOfAssignment (valid : Valid hypermap partition)
    (ring : List (Fin hypermap.dartCount))
    (assignment : Fin partition.faceCount → Color) : List Color :=
  trace (FiniteHypermap.ringColorWord ring
    (colorOfAssignment valid assignment))

theorem ringTrace_iff_exists_assignment
    (valid : Valid hypermap partition)
    (ring : List (Fin hypermap.dartCount)) (boundaryTrace : List Color) :
    FiniteHypermap.RingTrace (checkedHypermap valid) ring boundaryTrace ↔
      ∃ assignment : Fin partition.faceCount → Color,
        IsProperAssignment valid assignment ∧
          boundaryTrace = ringTraceOfAssignment valid ring assignment := by
  constructor
  · rintro ⟨color, hcolor, htrace⟩
    obtain ⟨assignment, hproper, hreconstruct⟩ :=
      everyFaceColoring_factors valid color hcolor
    refine ⟨assignment, hproper, ?_⟩
    rw [htrace]
    simp only [ringTraceOfAssignment, FiniteHypermap.ringColorWord,
      hreconstruct]
  · rintro ⟨assignment, hproper, htrace⟩
    exact ⟨colorOfAssignment valid assignment,
      isFaceColoring_of_isProperAssignment valid assignment hproper, htrace⟩

theorem contractRingTrace_iff_exists_assignment
    (valid : Valid hypermap partition)
    (contract : Finset (Fin hypermap.dartCount))
    (ring : List (Fin hypermap.dartCount)) (boundaryTrace : List Color) :
    FiniteHypermap.ContractRingTrace (checkedHypermap valid) contract ring
        boundaryTrace ↔
      ∃ assignment : Fin partition.faceCount → Color,
        IsContractAssignment valid contract assignment ∧
          boundaryTrace = ringTraceOfAssignment valid ring assignment := by
  constructor
  · rintro ⟨color, hcolor, htrace⟩
    obtain ⟨assignment, hcontract, hreconstruct⟩ :=
      everyContractColoring_factors valid contract color hcolor
    refine ⟨assignment, hcontract, ?_⟩
    rw [htrace]
    simp only [ringTraceOfAssignment, FiniteHypermap.ringColorWord,
      hreconstruct]
  · rintro ⟨assignment, hcontract, htrace⟩
    exact ⟨colorOfAssignment valid assignment,
      isContractColoring_of_isContractAssignment valid contract assignment
        hcontract,
      htrace⟩

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

def firstCataloguePartitionValid :
    Valid firstCatalogueSampleCode firstCatalogueFacePartition :=
  valid_of_checker_true firstCatalogueSampleCode
    firstCatalogueFacePartition firstCatalogueFacePartition_checker

private def firstCatalogueContractDart :
    Fin firstCatalogueSampleCode.dartCount :=
  Fin.cast (by rfl) (41 : Fin 42)

/-- The contract edge selected by catalogue entry `cf001`. -/
def firstCatalogueContract : Finset (Fin firstCatalogueSampleCode.dartCount) :=
  {firstCatalogueContractDart}

theorem firstCatalogueContract_values :
    firstCatalogueContract.toList.map Fin.val =
      firstCatalogueContractDarts := by
  rw [show firstCatalogueContract = {firstCatalogueContractDart} from rfl,
    Finset.toList_singleton]
  simp only [List.map_singleton, firstCatalogueContractDarts,
    List.cons.injEq]
  exact ⟨Fin.val_cast _ _, True.intro⟩

theorem firstCatalogueRing_reverseBoundaryCycle :
    RawReverseBoundaryCycle firstCatalogueSampleCode firstCatalogueRing := by
  decide

theorem firstCatalogueContract_avoidsBoundary :
    ContractAvoidsBoundary firstCatalogueContract firstCatalogueRing := by
  decide

theorem firstCatalogue_contractAssignment_trace_symbols
    (assignment : Fin firstCatalogueFacePartition.faceCount → Color)
    (hcontract : IsContractAssignment firstCataloguePartitionValid
      firstCatalogueContract assignment) :
    ∃! symbols : List ClassicalCertificateTraceTree.TraceSymbol,
      symbols.map ClassicalCertificateTraceTree.TraceSymbol.toColor =
        ringTraceOfAssignment firstCataloguePartitionValid
          firstCatalogueRing assignment := by
  apply existsUnique_traceSymbolWord
  exact cyclicallyDistinct_ringColorWord_of_contract
    firstCataloguePartitionValid firstCatalogueContract firstCatalogueRing
      assignment hcontract firstCatalogueRing_reverseBoundaryCycle
        firstCatalogueContract_avoidsBoundary

theorem firstCatalogue_properAssignment_trace_symbols
    (assignment : Fin firstCatalogueFacePartition.faceCount → Color)
    (hproper : IsProperAssignment firstCataloguePartitionValid assignment) :
    ∃! symbols : List ClassicalCertificateTraceTree.TraceSymbol,
      symbols.map ClassicalCertificateTraceTree.TraceSymbol.toColor =
        ringTraceOfAssignment firstCataloguePartitionValid
          firstCatalogueRing assignment := by
  apply existsUnique_traceSymbolWord
  exact cyclicallyDistinct_ringColorWord_of_contract
    firstCataloguePartitionValid ∅ firstCatalogueRing assignment
      ((isContractAssignment_empty_iff _ _).2 hproper)
      firstCatalogueRing_reverseBoundaryCycle (by
        simp [ContractAvoidsBoundary, InRawContract])

theorem firstCatalogue_faceColorable_iff :
    FiniteHypermap.FaceColorable
        (checkedHypermap
          firstCataloguePartitionValid) ↔
      ∃ assignment : Fin firstCatalogueFacePartition.faceCount → Color,
        IsProperAssignment
          firstCataloguePartitionValid
          assignment :=
  faceColorable_iff_exists_properAssignment _

end ClassicalCertificateFacePartition

end Mettapedia.GraphTheory.FourColor
