import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCompleteReductionMetadata
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateQuiz
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataData

/-!
# Catalogue quiz certificates

The classical configuration quiz is more than a list of local face arities.
On its own materialized configuration it visits exactly one dart from every
face off the outer ring.  This file reflects that finite statement and relates
the checked face classes to the standard finite-hypermap semantics.
-/

set_option autoImplicit false

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueQuiz

open ClassicalCertificateConfiguration
open ClassicalCertificateFacePartition
open ClassicalCertificateHypermap
open ClassicalCertificateQuiz
open ClassicalCertificateReductionMetadata

/-- The arities recorded by a question, in prefix traversal order. -/
def questionArities : Question → List Nat
  | .empty => []
  | .check arity => [arity]
  | .left arity next => arity :: questionArities next
  | .right arity next => arity :: questionArities next
  | .fork arity left right =>
      arity :: (questionArities left ++ questionArities right)
  | .skewLeft arity next => arity :: questionArities next
  | .skewRight arity next => arity :: questionArities next

/-- A left quiz step for arbitrary edge and node maps. -/
def qstepLWith {D : Type*} (edge node : D → D) (dart : D) : D :=
  node (edge (node dart))

/-- A right quiz step for arbitrary edge and node maps. -/
def qstepRWith {D : Type*} (edge node : D → D) (dart : D) : D :=
  node (edge dart)

/-- The darts visited by a question.  The skew-left observation includes the
face shift used by the classical quiz compiler. -/
def questionWalkWith {D : Type*} (edge node : D → D) (dart : D) :
    Question → List D
  | .empty => []
  | .check _ => [dart]
  | .left _ next =>
      dart :: questionWalkWith edge node (qstepLWith edge node dart) next
  | .right _ next =>
      dart :: questionWalkWith edge node (qstepRWith edge node dart) next
  | .fork _ left right =>
      dart :: (questionWalkWith edge node (qstepLWith edge node dart) left ++
        questionWalkWith edge node (qstepRWith edge node dart) right)
  | .skewLeft _ next =>
      let left := qstepLWith edge node dart
      edge (node left) ::
        questionWalkWith edge node (qstepLWith edge node left) next
  | .skewRight _ next =>
      let right := qstepRWith edge node dart
      right :: questionWalkWith edge node (qstepRWith edge node right) next

/-- The arities recorded by both sides of a quiz. -/
def quizArities (quiz : Quiz) : List Nat :=
  questionArities quiz.first ++ questionArities quiz.second

/-- The two question walks starting on opposite sides of the initial edge. -/
def quizWalkWith {D : Type*} (edge node : D → D) (dart : D)
    (quiz : Quiz) : List D :=
  questionWalkWith edge node dart quiz.first ++
    questionWalkWith edge node (edge dart) quiz.second

/-- The classical quiz compiler always emits a right-rooted question on each
side of its initial edge. -/
def questionIsRightRooted : Question → Bool
  | .right _ _ => true
  | _ => false

def quizIsRightRooted (quiz : Quiz) : Bool :=
  questionIsRightRooted quiz.first && questionIsRightRooted quiz.second

theorem length_questionWalkWith {D : Type*} (edge node : D → D)
    (dart : D) (question : Question) :
    (questionWalkWith edge node dart question).length =
      (questionArities question).length := by
  induction question generalizing dart with
  | empty => rfl
  | check arity => rfl
  | left arity next ih => simp [questionWalkWith, questionArities, ih]
  | right arity next ih => simp [questionWalkWith, questionArities, ih]
  | fork arity left right ihLeft ihRight =>
      simp [questionWalkWith, questionArities, ihLeft, ihRight]
  | skewLeft arity next ih =>
      simp [questionWalkWith, questionArities, ih]
  | skewRight arity next ih =>
      simp [questionWalkWith, questionArities, ih]

theorem append_eq_append_iff_of_length_eq {A : Type*}
    {left right left' right' : List A}
    (hlength : left.length = left'.length) :
    left ++ right = left' ++ right' ↔ left = left' ∧ right = right' := by
  constructor
  · intro heq
    constructor
    · have htake := congrArg (List.take left.length) heq
      simpa [hlength] using htake
    · have hdrop := congrArg (List.drop left.length) heq
      simpa [hlength] using hdrop
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Question walks commute with any map intertwining the edge and node
operations. -/
theorem map_questionWalkWith {A B : Type*} (mapDart : A → B)
    (edgeA nodeA : A → A) (edgeB nodeB : B → B)
    (hedge : ∀ dart, mapDart (edgeA dart) = edgeB (mapDart dart))
    (hnode : ∀ dart, mapDart (nodeA dart) = nodeB (mapDart dart))
    (dart : A) (question : Question) :
    (questionWalkWith edgeA nodeA dart question).map mapDart =
      questionWalkWith edgeB nodeB (mapDart dart) question := by
  induction question generalizing dart with
  | empty => rfl
  | check arity => rfl
  | left arity next ih =>
      simp [questionWalkWith, qstepLWith, ih, hedge, hnode]
  | right arity next ih =>
      simp [questionWalkWith, qstepRWith, ih, hedge, hnode]
  | fork arity left right ihLeft ihRight =>
      simp [questionWalkWith, qstepLWith, qstepRWith, ihLeft, ihRight,
        hedge, hnode]
  | skewLeft arity next ih =>
      simp [questionWalkWith, qstepLWith, ih, hedge, hnode]
  | skewRight arity next ih =>
      simp [questionWalkWith, qstepRWith, ih, hedge, hnode]

/-- The corresponding naturality theorem for a complete quiz. -/
theorem map_quizWalkWith {A B : Type*} (mapDart : A → B)
    (edgeA nodeA : A → A) (edgeB nodeB : B → B)
    (hedge : ∀ dart, mapDart (edgeA dart) = edgeB (mapDart dart))
    (hnode : ∀ dart, mapDart (nodeA dart) = nodeB (mapDart dart))
    (dart : A) (quiz : Quiz) :
    (quizWalkWith edgeA nodeA dart quiz).map mapDart =
      quizWalkWith edgeB nodeB (mapDart dart) quiz := by
  simp [quizWalkWith, List.map_append,
    map_questionWalkWith mapDart edgeA nodeA edgeB nodeB hedge hnode,
    hedge]

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- Recursive fitting is exactly equality between the recorded arities and
the arities along the explicit question walk. -/
theorem question_fits_iff_arities_eq_map
    (RS : RotationSystem V E) (dart : RS.D) (question : Question) :
    question.Fits RS dart ↔
      questionArities question =
        (questionWalkWith RS.alpha RS.rho.symm dart question).map
          (ClassicalCertificateRotationHubProfile.faceArity RS) := by
  induction question generalizing dart with
  | empty => simp [Question.Fits, questionArities, questionWalkWith]
  | check arity =>
      simp [Question.Fits, questionArities, questionWalkWith, eq_comm]
  | left arity next ih =>
      simp [Question.Fits, questionArities, questionWalkWith,
        qstepLWith, ClassicalCertificateQuiz.qstepL, ih, eq_comm]
  | right arity next ih =>
      simp [Question.Fits, questionArities, questionWalkWith,
        qstepRWith, ClassicalCertificateQuiz.qstepR, ih, eq_comm]
  | fork arity left right ihLeft ihRight =>
      have hlength : (questionArities left).length =
          (List.map (ClassicalCertificateRotationHubProfile.faceArity RS)
            (questionWalkWith RS.alpha RS.rho.symm
              (RS.rho.symm (RS.alpha (RS.rho.symm dart))) left)).length := by
        simp [length_questionWalkWith]
      simp only [Question.Fits, questionArities, questionWalkWith,
        List.map_cons, List.map_append, List.cons.injEq]
      rw [ihLeft, ihRight]
      simp only [qstepLWith, qstepRWith, ClassicalCertificateQuiz.qstepL,
        ClassicalCertificateQuiz.qstepR]
      rw [append_eq_append_iff_of_length_eq hlength]
      simp [eq_comm]
  | skewLeft arity next ih =>
      simp [Question.Fits, questionArities, questionWalkWith,
        qstepLWith, ClassicalCertificateQuiz.qstepL, ih, eq_comm]
  | skewRight arity next ih =>
      simp [Question.Fits, questionArities, questionWalkWith,
        qstepRWith, ClassicalCertificateQuiz.qstepR, ih, eq_comm]

/-- A fitting quiz similarly identifies its complete recorded arity word with
the two-sided walk in the ambient rotation system. -/
theorem quiz_fits_iff_arities_eq_map
    (RS : RotationSystem V E) (dart : RS.D) (quiz : Quiz) :
    quiz.Fits RS dart ↔
      quizArities quiz =
        (quizWalkWith RS.alpha RS.rho.symm dart quiz).map
          (ClassicalCertificateRotationHubProfile.faceArity RS) := by
  have hlength : (questionArities quiz.first).length =
      (List.map (ClassicalCertificateRotationHubProfile.faceArity RS)
        (questionWalkWith RS.alpha RS.rho.symm dart quiz.first)).length := by
    simp [length_questionWalkWith]
  simp [Quiz.Fits, quizArities, quizWalkWith, List.map_append,
    question_fits_iff_arities_eq_map,
    append_eq_append_iff_of_length_eq hlength]

/-- Raw executable edge lookup for a materialized configuration. -/
def rawEdge (code : ClassicalCertificateReductionMetadata.Code)
    (dart : Nat) : Nat :=
  HypermapCode.lookup code.hypermap.edge dart

/-- Raw executable node lookup for a materialized configuration. -/
def rawNode (code : ClassicalCertificateReductionMetadata.Code)
    (dart : Nat) : Nat :=
  HypermapCode.lookup code.hypermap.node dart

/-- The checked face class of a raw dart number. -/
def rawFaceClass (code : ClassicalCertificateReductionMetadata.Code)
    (dart : Nat) : Nat :=
  code.partition.classAt dart

/-- Cardinality of one checked face class. -/
def rawFaceArity (code : ClassicalCertificateReductionMetadata.Code)
    (dart : Nat) : Nat :=
  (Finset.univ.filter fun other : Fin code.hypermap.dartCount =>
    rawFaceClass code other.val = rawFaceClass code dart).card

/-- Raw quiz walk in a materialized catalogue configuration. -/
def rawWalk (code : ClassicalCertificateReductionMetadata.Code)
    (root : Nat) (quiz : Quiz) : List Nat :=
  quizWalkWith (rawEdge code) (rawNode code) root quiz

/-- Face classes represented by the raw quiz walk. -/
def visitedFaceClasses (code : ClassicalCertificateReductionMetadata.Code)
    (root : Nat) (quiz : Quiz) : List Nat :=
  (rawWalk code root quiz).map (rawFaceClass code)

/-- A face class belongs to the kernel precisely when no outer-ring dart has
that class. -/
def kernelFaceClasses
    (code : ClassicalCertificateReductionMetadata.Code) : List Nat :=
  (List.range code.partition.faceCount).filter fun face =>
    !(code.ringValues.any fun dart => rawFaceClass code dart = face)

/-- Executable validity of a catalogue quiz at a specified root dart. -/
def checkerAt (code : ClassicalCertificateReductionMetadata.Code)
    (root : Nat) (quiz : Quiz) : Bool :=
  decide (root < code.hypermap.dartCount) &&
    quizIsRightRooted quiz &&
      decide (quizArities quiz =
        (rawWalk code root quiz).map (rawFaceArity code)) &&
        decide (visitedFaceClasses code root quiz).Nodup &&
          decide ((visitedFaceClasses code root quiz).toFinset =
            (kernelFaceClasses code).toFinset)

/-- Semantic content reflected by `checkerAt`. -/
structure ValidAt (code : ClassicalCertificateReductionMetadata.Code)
    (root : Nat) (quiz : Quiz) : Prop where
  rootInRange : root < code.hypermap.dartCount
  rightRooted : quizIsRightRooted quiz = true
  arities : quizArities quiz =
    (rawWalk code root quiz).map (rawFaceArity code)
  simpleFaces : (visitedFaceClasses code root quiz).Nodup
  coversKernel : (visitedFaceClasses code root quiz).toFinset =
    (kernelFaceClasses code).toFinset

theorem validAt_of_checkerAt_true
    (code : ClassicalCertificateReductionMetadata.Code)
    (root : Nat) (quiz : Quiz) (hcheck : checkerAt code root quiz = true) :
    ValidAt code root quiz := by
  simp only [checkerAt, Bool.and_eq_true] at hcheck
  rcases hcheck with
    ⟨⟨⟨⟨hroot, hright⟩, harities⟩, hsimple⟩, hcover⟩
  exact ⟨of_decide_eq_true hroot, hright,
    of_decide_eq_true harities,
    of_decide_eq_true hsimple,
    of_decide_eq_true hcover⟩

noncomputable section

/-- The finite orbit of a point under a permutation. -/
def permutationOrbit {D : Type*} [Fintype D] [DecidableEq D]
    (permutation : Equiv.Perm D) (root : D) : Finset D :=
  Finset.univ.filter fun other => permutation.SameCycle root other

/-- A permutation is a single cycle on each of its actual point orbits. -/
theorem permutationOrbit_isCycleOn
    {D : Type*} [Fintype D] [DecidableEq D]
    (permutation : Equiv.Perm D) (root : D) :
    permutation.IsCycleOn (permutationOrbit permutation root) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro dart hdart
    have hdart' : permutation.SameCycle root dart := by
      simpa [permutationOrbit] using hdart
    have hnext := hdart'.trans
      (Mettapedia.GraphTheory.EquivPermSameCycle.step_right permutation dart)
    simpa [permutationOrbit] using hnext
  · intro left hleft right hright heq
    exact permutation.injective heq
  · intro dart hdart
    refine ⟨permutation.symm dart, ?_, by simp⟩
    have hdart' : permutation.SameCycle root dart := by
      simpa [permutationOrbit] using hdart
    have hprevious := hdart'.trans
      (Mettapedia.GraphTheory.EquivPermSameCycle.step_right_inv
        permutation dart)
    simpa [permutationOrbit] using hprevious
  · intro left hleft right hright
    have hleft' : permutation.SameCycle root left := by
      simpa [permutationOrbit] using hleft
    have hright' : permutation.SameCycle root right := by
      simpa [permutationOrbit] using hright
    exact hleft'.symm.trans hright'

/-- Darts in the face orbit of a standard finite hypermap dart. -/
def hypermapFaceOrbit {D : Type*} [Fintype D] [DecidableEq D]
    (H : FiniteHypermap D) (dart : D) : Finset D :=
  permutationOrbit H.face dart

def hypermapFaceArity {D : Type*} [Fintype D] [DecidableEq D]
    (H : FiniteHypermap D) (dart : D) : Nat :=
  (hypermapFaceOrbit H dart).card

theorem mem_permutationOrbit_self
    {D : Type*} [Fintype D] [DecidableEq D]
    (permutation : Equiv.Perm D) (root : D) :
    root ∈ permutationOrbit permutation root := by
  exact Finset.mem_filter.2
    ⟨Finset.mem_univ root, Equiv.Perm.SameCycle.refl permutation root⟩

/-- A chosen nonnegative exponent naming a point in one finite permutation
orbit. -/
def cycleExponent
    {D : Type*} [Fintype D] [DecidableEq D]
    (permutation : Equiv.Perm D) (root point : D)
    (hpoint : point ∈ permutationOrbit permutation root) : Nat :=
  Classical.choose
    ((by simpa [permutationOrbit] using hpoint :
      permutation.SameCycle root point).exists_nat_pow_eq)

theorem cycleExponent_spec
    {D : Type*} [Fintype D] [DecidableEq D]
    (permutation : Equiv.Perm D) (root point : D)
    (hpoint : point ∈ permutationOrbit permutation root) :
    (permutation ^ cycleExponent permutation root point hpoint) root = point :=
  Classical.choose_spec
    ((by simpa [permutationOrbit] using hpoint :
      permutation.SameCycle root point).exists_nat_pow_eq)

/-- Canonical transport between two anchored permutation cycles of equal
cardinality.  It sends a chosen source power to the same target power. -/
def cycleTransport
    {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (source : Equiv.Perm A) (target : Equiv.Perm B)
    (sourceRoot : A) (targetRoot : B)
    (_hcard : (permutationOrbit source sourceRoot).card =
      (permutationOrbit target targetRoot).card)
    (point : A) (hpoint : point ∈ permutationOrbit source sourceRoot) : B :=
  (target ^ cycleExponent source sourceRoot point hpoint) targetRoot

/-- Equal-cycle transport commutes with the two successor permutations. -/
theorem cycleTransport_apply
    {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (source : Equiv.Perm A) (target : Equiv.Perm B)
    (sourceRoot : A) (targetRoot : B)
    (hcard : (permutationOrbit source sourceRoot).card =
      (permutationOrbit target targetRoot).card)
    (point : A) (hpoint : point ∈ permutationOrbit source sourceRoot) :
    cycleTransport source target sourceRoot targetRoot hcard
        (source point)
        ((permutationOrbit_isCycleOn source sourceRoot).1.mapsTo hpoint) =
      target
        (cycleTransport source target sourceRoot targetRoot hcard
          point hpoint) := by
  let pointPower := cycleExponent source sourceRoot point hpoint
  let nextPoint := source point
  let hnext : nextPoint ∈ permutationOrbit source sourceRoot :=
    (permutationOrbit_isCycleOn source sourceRoot).1.mapsTo hpoint
  let nextPower := cycleExponent source sourceRoot nextPoint hnext
  have hsourceNext :
      (source ^ (pointPower + 1)) sourceRoot = nextPoint := by
    rw [pow_succ', Equiv.Perm.mul_apply,
      cycleExponent_spec source sourceRoot point hpoint]
  have hmod : nextPower ≡ pointPower + 1
      [MOD (permutationOrbit source sourceRoot).card] :=
    ((permutationOrbit_isCycleOn source sourceRoot).pow_apply_eq_pow_apply
      (mem_permutationOrbit_self source sourceRoot)).1 (by
        rw [cycleExponent_spec source sourceRoot nextPoint hnext]
        exact hsourceNext.symm)
  have htargetMod : nextPower ≡ pointPower + 1
      [MOD (permutationOrbit target targetRoot).card] := by
    simpa [hcard] using hmod
  have htargetPower :
      (target ^ nextPower) targetRoot =
        (target ^ (pointPower + 1)) targetRoot :=
    ((permutationOrbit_isCycleOn target targetRoot).pow_apply_eq_pow_apply
      (mem_permutationOrbit_self target targetRoot)).2 htargetMod
  change (target ^ nextPower) targetRoot =
    target ((target ^ pointPower) targetRoot)
  rw [htargetPower, pow_succ', Equiv.Perm.mul_apply]

/-- Same-cycle roots determine the same finite permutation orbit. -/
theorem permutationOrbit_eq_of_sameCycle
    {D : Type*} [Fintype D] [DecidableEq D]
    (permutation : Equiv.Perm D) {left right : D}
    (hsame : permutation.SameCycle left right) :
    permutationOrbit permutation left = permutationOrbit permutation right := by
  ext point
  simp only [permutationOrbit, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hpoint
    exact hsame.symm.trans hpoint
  · intro hpoint
    exact hsame.trans hpoint

/-- Equal-cycle transport lands in the target anchor's cycle. -/
theorem cycleTransport_mem_target
    {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (source : Equiv.Perm A) (target : Equiv.Perm B)
    (sourceRoot : A) (targetRoot : B)
    (hcard : (permutationOrbit source sourceRoot).card =
      (permutationOrbit target targetRoot).card)
    (point : A) (hpoint : point ∈ permutationOrbit source sourceRoot) :
    cycleTransport source target sourceRoot targetRoot hcard point hpoint ∈
      permutationOrbit target targetRoot := by
  simp only [permutationOrbit, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold cycleTransport
  exact (Equiv.Perm.sameCycle_pow_right).2
    (Equiv.Perm.SameCycle.refl target targetRoot)

/-- Anchors pair every source face in a face-closed domain with an equal-size
target face.  Constancy along the source face makes the induced transport a
partial face morphism. -/
structure FaceAnchorAssignment
    {Source Target : Type*}
    [Fintype Source] [DecidableEq Source]
    [Fintype Target] [DecidableEq Target]
    (source : Equiv.Perm Source) (target : Equiv.Perm Target)
    (domain : Source → Prop) where
  sourceAnchor : Source → Source
  targetAnchor : Source → Target
  domain_face : ∀ point, domain point → domain (source point)
  source_mem : ∀ point, domain point →
    point ∈ permutationOrbit source (sourceAnchor point)
  orbit_card_eq : ∀ point, domain point →
    (permutationOrbit source (sourceAnchor point)).card =
      (permutationOrbit target (targetAnchor point)).card
  sourceAnchor_face : ∀ point, domain point →
    sourceAnchor (source point) = sourceAnchor point
  targetAnchor_face : ∀ point, domain point →
    targetAnchor (source point) = targetAnchor point

namespace FaceAnchorAssignment

variable {Source Target : Type*}
  [Fintype Source] [DecidableEq Source]
  [Fintype Target] [DecidableEq Target]
  {source : Equiv.Perm Source} {target : Equiv.Perm Target}
  {domain : Source → Prop}

/-- The total function underlying the anchored partial morphism; its values
outside the declared domain are immaterial. -/
noncomputable def map (assignment : FaceAnchorAssignment source target domain)
    (point : Source) : Target := by
  classical
  exact if hpoint : domain point then
      cycleTransport source target
        (assignment.sourceAnchor point) (assignment.targetAnchor point)
        (assignment.orbit_card_eq point hpoint) point
        (assignment.source_mem point hpoint)
    else assignment.targetAnchor point

/-- The anchored map commutes with the face successor throughout its domain. -/
theorem map_source
    (assignment : FaceAnchorAssignment source target domain)
    (point : Source) (hpoint : domain point) :
    assignment.map (source point) = target (assignment.map point) := by
  classical
  have hnext := assignment.domain_face point hpoint
  unfold map
  rw [dif_pos hpoint, dif_pos hnext]
  have hsourceAnchor := assignment.sourceAnchor_face point hpoint
  have htargetAnchor := assignment.targetAnchor_face point hpoint
  simpa only [hsourceAnchor, htargetAnchor] using
    (cycleTransport_apply source target
      (assignment.sourceAnchor point) (assignment.targetAnchor point)
        (assignment.orbit_card_eq point hpoint) point
          (assignment.source_mem point hpoint))

/-- The anchored map preserves the cardinality of every source face in its
domain. -/
theorem orbit_card_map_eq
    (assignment : FaceAnchorAssignment source target domain)
    (point : Source) (hpoint : domain point) :
    (permutationOrbit source point).card =
      (permutationOrbit target (assignment.map point)).card := by
  classical
  have hsourceSame : source.SameCycle
      (assignment.sourceAnchor point) point := by
    simpa [permutationOrbit] using assignment.source_mem point hpoint
  have htargetMem := cycleTransport_mem_target source target
    (assignment.sourceAnchor point) (assignment.targetAnchor point)
      (assignment.orbit_card_eq point hpoint) point
        (assignment.source_mem point hpoint)
  have htargetSame : target.SameCycle (assignment.targetAnchor point)
      (assignment.map point) := by
    rw [map, dif_pos hpoint]
    simpa [permutationOrbit] using htargetMem
  calc
    (permutationOrbit source point).card =
        (permutationOrbit source (assignment.sourceAnchor point)).card := by
      rw [permutationOrbit_eq_of_sameCycle source hsourceSame]
    _ = (permutationOrbit target (assignment.targetAnchor point)).card :=
      assignment.orbit_card_eq point hpoint
    _ = (permutationOrbit target (assignment.map point)).card := by
      rw [permutationOrbit_eq_of_sameCycle target htargetSame]

end FaceAnchorAssignment

variable {code : ClassicalCertificateReductionMetadata.Code}

/-- Iterating the raw checked face table is iteration by the face permutation
of the resulting standard finite hypermap. -/
theorem iterateTable_eq_checkedFace_pow
    (valid : ClassicalCertificateReductionMetadata.Valid code)
    (steps : Nat) (dart : Fin code.hypermap.dartCount) :
    ClassicalCertificateFacePartition.iterateTable
        (ClassicalCertificateFacePartition.faceTable code.hypermap)
          steps dart =
      ((ClassicalCertificateFacePartition.checkedHypermap
        valid.partitionValid).face ^ steps) dart := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp only [ClassicalCertificateFacePartition.iterateTable, ih]
      rw [pow_succ']
      rfl

/-- Checked face classes coincide exactly with cycles of the standard face
permutation. -/
theorem faceClass_eq_iff_sameCycle
    (valid : ClassicalCertificateReductionMetadata.Valid code)
    (left right : Fin code.hypermap.dartCount) :
    ClassicalCertificateFacePartition.faceClass valid.partitionValid left =
        ClassicalCertificateFacePartition.faceClass valid.partitionValid right ↔
      (ClassicalCertificateFacePartition.checkedHypermap
        valid.partitionValid).face.SameCycle left right := by
  let partitionValid := valid.partitionValid
  let H := ClassicalCertificateFacePartition.checkedHypermap partitionValid
  constructor
  · intro hclass
    have hleftReach :=
      ClassicalCertificateFacePartition.iterateTable_distance_eq_representative
        partitionValid left
    have hrightReach :=
      ClassicalCertificateFacePartition.iterateTable_distance_eq_representative
        partitionValid right
    have hleftPow :
        (H.face ^ code.partition.distanceAt left.val) left =
          ClassicalCertificateFacePartition.faceRepresentative partitionValid
            (ClassicalCertificateFacePartition.faceClass partitionValid left) := by
      rw [← iterateTable_eq_checkedFace_pow valid]
      exact hleftReach
    have hrightPow :
        (H.face ^ code.partition.distanceAt right.val) right =
          ClassicalCertificateFacePartition.faceRepresentative partitionValid
            (ClassicalCertificateFacePartition.faceClass partitionValid right) := by
      rw [← iterateTable_eq_checkedFace_pow valid]
      exact hrightReach
    have hleftCycle : H.face.SameCycle left
        (ClassicalCertificateFacePartition.faceRepresentative partitionValid
          (ClassicalCertificateFacePartition.faceClass partitionValid left)) :=
      ⟨(code.partition.distanceAt left.val : Int), by simpa using hleftPow⟩
    have hrightCycle : H.face.SameCycle right
        (ClassicalCertificateFacePartition.faceRepresentative partitionValid
          (ClassicalCertificateFacePartition.faceClass partitionValid right)) :=
      ⟨(code.partition.distanceAt right.val : Int), by simpa using hrightPow⟩
    rw [hclass] at hleftCycle
    exact hleftCycle.trans hrightCycle.symm
  · intro hcycle
    apply FiniteHypermap.invariant_of_sameCycle H.face
      (ClassicalCertificateFacePartition.faceClass partitionValid)
    · intro dart
      exact ClassicalCertificateFacePartition.faceClass_face
        partitionValid dart
    · exact hcycle

/-- The checked face quotient therefore has the same face-orbit finsets as
the standard finite hypermap. -/
theorem faceClassDarts_eq_hypermapFaceOrbit
    (valid : ClassicalCertificateReductionMetadata.Valid code)
    (dart : Fin code.hypermap.dartCount) :
    (Finset.univ.filter fun other =>
      ClassicalCertificateFacePartition.faceClass valid.partitionValid other =
        ClassicalCertificateFacePartition.faceClass valid.partitionValid dart) =
      hypermapFaceOrbit
        (ClassicalCertificateFacePartition.checkedHypermap
          valid.partitionValid) dart := by
  ext other
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hypermapFaceOrbit,
    permutationOrbit]
  rw [faceClass_eq_iff_sameCycle valid]
  exact Equiv.Perm.sameCycle_comm

/-- The executable class cardinality used by quiz checking is exactly the
face arity of the standard materialized hypermap. -/
theorem rawFaceArity_eq_hypermapFaceArity
    (valid : ClassicalCertificateReductionMetadata.Valid code)
    (dart : Fin code.hypermap.dartCount) :
    rawFaceArity code dart.val =
      hypermapFaceArity
        (ClassicalCertificateFacePartition.checkedHypermap
          valid.partitionValid) dart := by
  unfold hypermapFaceArity
  rw [← faceClassDarts_eq_hypermapFaceOrbit valid dart]
  unfold rawFaceArity
  congr 1
  ext other
  simp [rawFaceClass, ClassicalCertificateFacePartition.faceClass,
    Fin.ext_iff]

/-- Semantic edge lookup agrees with the raw executable table. -/
theorem checkedHypermap_edge_val
    (valid : ClassicalCertificateReductionMetadata.Valid code)
    (dart : Fin code.hypermap.dartCount) :
    ((ClassicalCertificateFacePartition.checkedHypermap
      valid.partitionValid).edge dart).val = rawEdge code dart.val := by
  change ((ClassicalCertificateFacePartition.edgeTable code.hypermap).toFin
    dart).val = rawEdge code dart.val
  exact RawTable.toFin_val _
    valid.partitionValid.hypermapAccepted.2.2.2.1 dart

/-- Semantic node lookup agrees with the raw executable table. -/
theorem checkedHypermap_node_val
    (valid : ClassicalCertificateReductionMetadata.Valid code)
    (dart : Fin code.hypermap.dartCount) :
    ((ClassicalCertificateFacePartition.checkedHypermap
      valid.partitionValid).node dart).val = rawNode code dart.val := by
  change (RawTable.toFin (fun dart : Fin code.hypermap.dartCount =>
    HypermapCode.lookup code.hypermap.node dart.val) dart).val =
      rawNode code dart.val
  exact RawTable.toFin_val _
    valid.partitionValid.hypermapAccepted.2.2.2.2.1 dart

/-- The raw walk checked by a quiz certificate is the value projection of the
walk in its standard finite hypermap. -/
theorem map_val_quizWalk_checked_eq_raw
    (valid : ClassicalCertificateReductionMetadata.Valid code)
    (root : Fin code.hypermap.dartCount) (quiz : Quiz) :
    (quizWalkWith
      (ClassicalCertificateFacePartition.checkedHypermap
        valid.partitionValid).edge
      (ClassicalCertificateFacePartition.checkedHypermap
        valid.partitionValid).node root quiz).map Fin.val =
      rawWalk code root.val quiz := by
  exact map_quizWalkWith Fin.val
    (ClassicalCertificateFacePartition.checkedHypermap
      valid.partitionValid).edge
    (ClassicalCertificateFacePartition.checkedHypermap
      valid.partitionValid).node
    (rawEdge code) (rawNode code)
    (checkedHypermap_edge_val valid) (checkedHypermap_node_val valid)
      root quiz

/-- Standard finite-hypermap meaning of a fitting quiz. -/
def HypermapQuizFits {D : Type*} [Fintype D] [DecidableEq D]
    (H : FiniteHypermap D) (root : D) (quiz : Quiz) : Prop :=
  quizArities quiz =
    (quizWalkWith H.edge H.node root quiz).map (hypermapFaceArity H)

/-- A successful catalogue checker proves that the quiz genuinely fits its
standard materialized finite hypermap. -/
theorem ValidAt.hypermapQuizFits
    {root : Nat} {quiz : Quiz} (quizValid : ValidAt code root quiz)
    (valid : ClassicalCertificateReductionMetadata.Valid code) :
    HypermapQuizFits
      (ClassicalCertificateFacePartition.checkedHypermap
        valid.partitionValid)
      ⟨root, quizValid.rootInRange⟩ quiz := by
  let sourceRoot : Fin code.hypermap.dartCount :=
    ⟨root, quizValid.rootInRange⟩
  let H := ClassicalCertificateFacePartition.checkedHypermap
    valid.partitionValid
  unfold HypermapQuizFits
  rw [quizValid.arities]
  rw [← map_val_quizWalk_checked_eq_raw valid sourceRoot quiz]
  simp only [List.map_map]
  apply List.map_congr_left
  intro dart hdart
  exact rawFaceArity_eq_hypermapFaceArity valid dart

end

/-- Every root at which the finite catalogue quiz certificate succeeds. -/
def acceptedRoots (code : ClassicalCertificateReductionMetadata.Code)
    (quiz : Quiz) : List Nat :=
  (List.range code.hypermap.dartCount).filter fun root =>
    checkerAt code root quiz

open ClassicalCertificateReductionMetadataCatalogue
open ClassicalCertificateReductionMetadataData
open ClassicalCertificateCompleteReductionMetadata

/-- The materialized reduction records used by the nine sharp discharge
obstructions. -/
def cf001Code : ClassicalCertificateReductionMetadata.Code :=
  classicalReductionMetadataChunk00[0]

def cf003Code : ClassicalCertificateReductionMetadata.Code :=
  classicalReductionMetadataChunk00[2]

def cf006Code : ClassicalCertificateReductionMetadata.Code :=
  classicalReductionMetadataChunk00[5]

def cf009Code : ClassicalCertificateReductionMetadata.Code :=
  classicalReductionMetadataChunk00[8]

def cf024Code : ClassicalCertificateReductionMetadata.Code :=
  classicalReductionMetadataChunk01[7]

def cf139Code : ClassicalCertificateReductionMetadata.Code :=
  classicalReductionMetadataChunk08[10]

def cf182Code : ClassicalCertificateReductionMetadata.Code :=
  classicalReductionMetadataChunk11[5]

theorem cf001Code_lookup :
    classicalReductionMetadataCatalogue.codeAt? 0 = some cf001Code := by
  rfl

theorem cf003Code_lookup :
    classicalReductionMetadataCatalogue.codeAt? 2 = some cf003Code := by
  rfl

theorem cf006Code_lookup :
    classicalReductionMetadataCatalogue.codeAt? 5 = some cf006Code := by
  rfl

theorem cf009Code_lookup :
    classicalReductionMetadataCatalogue.codeAt? 8 = some cf009Code := by
  rfl

theorem cf024Code_lookup :
    classicalReductionMetadataCatalogue.codeAt? 23 = some cf024Code := by
  rfl

theorem cf139Code_lookup :
    classicalReductionMetadataCatalogue.codeAt? 138 = some cf139Code := by
  rfl

theorem cf182Code_lookup :
    classicalReductionMetadataCatalogue.codeAt? 181 = some cf182Code := by
  rfl

/-- Each selected generated quiz is valid on its own checked configuration:
the walk has the prescribed arities, is face-simple, and covers exactly the
faces off the outer ring. -/
theorem cf001_quiz_checker : checkerAt cf001Code 34 cf001 = true := by
  rfl

theorem cf003_quiz_checker : checkerAt cf003Code 47 cf003 = true := by
  rfl

theorem cf006_quiz_checker : checkerAt cf006Code 70 cf006 = true := by
  rfl

theorem cf009_quiz_checker : checkerAt cf009Code 74 cf009 = true := by
  rfl

theorem cf024_quiz_checker : checkerAt cf024Code 54 cf024 = true := by
  rfl

theorem cf139_quiz_checker : checkerAt cf139Code 82 cf139 = true := by
  rfl

theorem cf182_quiz_checker : checkerAt cf182Code 92 cf182 = true := by
  rfl

theorem cf001_quiz_valid : ValidAt cf001Code 34 cf001 :=
  validAt_of_checkerAt_true cf001Code 34 cf001 cf001_quiz_checker

theorem cf003_quiz_valid : ValidAt cf003Code 47 cf003 :=
  validAt_of_checkerAt_true cf003Code 47 cf003 cf003_quiz_checker

theorem cf006_quiz_valid : ValidAt cf006Code 70 cf006 :=
  validAt_of_checkerAt_true cf006Code 70 cf006 cf006_quiz_checker

theorem cf009_quiz_valid : ValidAt cf009Code 74 cf009 :=
  validAt_of_checkerAt_true cf009Code 74 cf009 cf009_quiz_checker

theorem cf024_quiz_valid : ValidAt cf024Code 54 cf024 :=
  validAt_of_checkerAt_true cf024Code 54 cf024 cf024_quiz_checker

theorem cf139_quiz_valid : ValidAt cf139Code 82 cf139 :=
  validAt_of_checkerAt_true cf139Code 82 cf139 cf139_quiz_checker

theorem cf182_quiz_valid : ValidAt cf182Code 92 cf182 :=
  validAt_of_checkerAt_true cf182Code 92 cf182 cf182_quiz_checker

/-- A valid quiz attached to the locally checked reduction record for the
same materialized catalogue configuration. -/
structure CertifiedAt (code : ClassicalCertificateReductionMetadata.Code)
    (root : Nat) (quiz : Quiz) : Prop extends ValidAt code root quiz where
  reduction : ∃ configuration,
    ClassicalCertificateReductionMetadata.Certified configuration code

theorem exists_certified_of_lookup
    (index : Nat) (hindex : index < 633)
    (code : ClassicalCertificateReductionMetadata.Code)
    (hlookup : classicalReductionMetadataCatalogue.codeAt? index =
      some code) :
    ∃ configuration,
      ClassicalCertificateReductionMetadata.Certified configuration code := by
  obtain ⟨configuration, inverseCode, foundCode, hconfiguration,
      hinverseCode, hfoundCode, haccepted, hcertified⟩ :=
    exists_certified_classicalReductionMetadata index hindex
  have hcode : foundCode = code :=
    Option.some.inj (hfoundCode.symm.trans hlookup)
  subst foundCode
  exact ⟨configuration, hcertified⟩

theorem cf001_certifiedQuiz : CertifiedAt cf001Code 34 cf001 := by
  refine ⟨cf001_quiz_valid, ?_⟩
  exact exists_certified_of_lookup 0 (by omega) cf001Code cf001Code_lookup

theorem cf003_certifiedQuiz : CertifiedAt cf003Code 47 cf003 := by
  refine ⟨cf003_quiz_valid, ?_⟩
  exact exists_certified_of_lookup 2 (by omega) cf003Code cf003Code_lookup

theorem cf006_certifiedQuiz : CertifiedAt cf006Code 70 cf006 := by
  refine ⟨cf006_quiz_valid, ?_⟩
  exact exists_certified_of_lookup 5 (by omega) cf006Code cf006Code_lookup

theorem cf009_certifiedQuiz : CertifiedAt cf009Code 74 cf009 := by
  refine ⟨cf009_quiz_valid, ?_⟩
  exact exists_certified_of_lookup 8 (by omega) cf009Code cf009Code_lookup

theorem cf024_certifiedQuiz : CertifiedAt cf024Code 54 cf024 := by
  refine ⟨cf024_quiz_valid, ?_⟩
  exact exists_certified_of_lookup 23 (by omega) cf024Code cf024Code_lookup

theorem cf139_certifiedQuiz : CertifiedAt cf139Code 82 cf139 := by
  refine ⟨cf139_quiz_valid, ?_⟩
  exact exists_certified_of_lookup 138 (by omega) cf139Code cf139Code_lookup

theorem cf182_certifiedQuiz : CertifiedAt cf182Code 92 cf182 := by
  refine ⟨cf182_quiz_valid, ?_⟩
  exact exists_certified_of_lookup 181 (by omega) cf182Code cf182Code_lookup

end ClassicalCertificateCatalogueQuiz

end Mettapedia.GraphTheory.FourColor
