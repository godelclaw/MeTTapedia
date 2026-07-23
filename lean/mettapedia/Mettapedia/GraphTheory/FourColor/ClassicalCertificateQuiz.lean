import Mettapedia.GraphTheory.FourColor.ClassicalCertificateDischargeRuleBound
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCubicWord
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateHypermap
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateRotationHubProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24InducedHexCorridorTypes

/-!
# Rotation-system semantics for classical configuration quizzes

The classical configuration catalogue stores a small pair of question trees
for each configuration.  A question records facial arities while walking left
and right through a cubic hypermap.  This file gives those walks direct
rotation-system semantics and begins the geometric bridge from the nine sharp
discharge obstructions to catalogue configurations.
-/

set_option autoImplicit false

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateQuiz

open ClassicalCertificateDischargeRuleBoundData
open ClassicalCertificateHypermap
open ClassicalCertificatePresentationPattern
open ClassicalCertificateRotationHubProfile
open GoertzelV24HexFaceRungType
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24FaceDualConnectedness

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- A left turn in the associated hypermap. -/
def qstepL (RS : RotationSystem V E) (dart : RS.D) : RS.D :=
  RS.toFiniteHypermap.node
    (RS.toFiniteHypermap.edge (RS.toFiniteHypermap.node dart))

/-- A right turn in the associated hypermap. -/
def qstepR (RS : RotationSystem V E) (dart : RS.D) : RS.D :=
  RS.toFiniteHypermap.node (RS.toFiniteHypermap.edge dart)

/-- The seven classical question constructors. -/
inductive Question where
  | empty
  | check (arity : Nat)
  | left (arity : Nat) (next : Question)
  | right (arity : Nat) (next : Question)
  | fork (arity : Nat) (left right : Question)
  | skewLeft (arity : Nat) (next : Question)
  | skewRight (arity : Nat) (next : Question)
deriving DecidableEq, Repr

namespace Question

/-- A question fits when every visited face has the recorded arity. -/
def Fits (RS : RotationSystem V E) (dart : RS.D) : Question → Prop
  | .empty => True
  | .check arity => faceArity RS dart = arity
  | .left arity next =>
      faceArity RS dart = arity ∧ Fits RS (qstepL RS dart) next
  | .right arity next =>
      faceArity RS dart = arity ∧ Fits RS (qstepR RS dart) next
  | .fork arity qleft qright =>
      faceArity RS dart = arity ∧
        Fits RS (qstepL RS dart) qleft ∧
          Fits RS (qstepR RS dart) qright
  | .skewLeft arity next =>
      let left := qstepL RS dart
      faceArity RS
          (RS.toFiniteHypermap.edge (RS.toFiniteHypermap.node left)) = arity ∧
        Fits RS (qstepL RS left) next
  | .skewRight arity next =>
      let right := qstepR RS dart
      faceArity RS right = arity ∧ Fits RS (qstepR RS right) next

end Question

/-- A quiz explores the two sides of one initial edge. -/
structure Quiz where
  first : Question
  second : Question
deriving DecidableEq, Repr

namespace Quiz

/-- Both question trees fit on their respective sides of the initial edge. -/
def Fits (RS : RotationSystem V E) (dart : RS.D) (quiz : Quiz) : Prop :=
  quiz.first.Fits RS dart ∧ quiz.second.Fits RS (RS.alpha dart)

end Quiz

/-- The catalogue quiz for configuration `cf001`. -/
def cf001 : Quiz where
  first := .right 5 .empty
  second := .right 5 (.left 5 (.check 5))

/-- The catalogue quiz for configuration `cf003`. -/
def cf003 : Quiz where
  first := .right 6 .empty
  second := .right 5
    (.fork 5 (.check 5) (.skewRight 5 (.left 5 (.check 5))))

/-- The catalogue quiz for configuration `cf006`. -/
def cf006 : Quiz where
  first := .right 6 .empty
  second := .right 6
    (.fork 5 (.skewLeft 5 (.right 5 (.check 5))) (.check 5))

/-- The reflected catalogue quiz for configuration `cf006`. -/
def cf006Mirror : Quiz where
  first := .right 6
    (.fork 5 (.check 5) (.skewRight 5 (.left 5 (.check 5))))
  second := .right 6 .empty

/-- The catalogue quiz for configuration `cf009`. -/
def cf009 : Quiz where
  first := .right 6 (.skewRight 6 (.left 5 (.check 5)))
  second := .right 6 (.right 5 (.check 5))

/-- The catalogue quiz for configuration `cf024`. -/
def cf024 : Quiz where
  first := .right 7 .empty
  second := .right 5 (.right 5 (.right 5 (.check 5)))

/-- The catalogue quiz for configuration `cf139`. -/
def cf139 : Quiz where
  first := .right 7 (.right 6 (.right 5 (.check 5)))
  second := .right 7 (.right 6 (.check 5))

/-- The catalogue quiz for configuration `cf182`. -/
def cf182 : Quiz where
  first := .right 7 (.right 6 (.right 6 (.right 5 (.check 5))))
  second := .right 7 (.right 6 (.check 5))

namespace Question

/-- The same question traversal, represented in the universal cubic word
algebra.  Words act on the left of the starting dart word. -/
def wordVisits
    (dart : ClassicalCertificateCubicWord.CubicWord) :
    Question → List (ClassicalCertificateCubicWord.CubicWord × Nat)
  | .empty => []
  | .check arity => [(dart, arity)]
  | .left arity next =>
      (dart, arity) ::
        wordVisits (ClassicalCertificateCubicWord.qstepL * dart) next
  | .right arity next =>
      (dart, arity) ::
        wordVisits (ClassicalCertificateCubicWord.qstepR * dart) next
  | .fork arity qleft qright =>
      (dart, arity) ::
        (wordVisits (ClassicalCertificateCubicWord.qstepL * dart) qleft ++
          wordVisits (ClassicalCertificateCubicWord.qstepR * dart) qright)
  | .skewLeft arity next =>
      let left := ClassicalCertificateCubicWord.qstepL * dart
      (ClassicalCertificateCubicWord.edge *
          ClassicalCertificateCubicWord.node * left, arity) ::
        wordVisits (ClassicalCertificateCubicWord.qstepL * left) next
  | .skewRight arity next =>
      let right := ClassicalCertificateCubicWord.qstepR * dart
      (right, arity) ::
        wordVisits (ClassicalCertificateCubicWord.qstepR * right) next

end Question

namespace Quiz

/-- Word-level arity visits made by both sides of a quiz. -/
def wordVisits (dart : ClassicalCertificateCubicWord.CubicWord)
    (quiz : Quiz) :
    List (ClassicalCertificateCubicWord.CubicWord × Nat) :=
  quiz.first.wordVisits dart ++
    quiz.second.wordVisits (ClassicalCertificateCubicWord.edge * dart)

end Quiz

@[simp] theorem node_act
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    (word : ClassicalCertificateCubicWord.CubicWord) (root : RS.D) :
    RS.rho.symm
        (ClassicalCertificateCubicWord.act RS hcubic hrotation word root) =
      ClassicalCertificateCubicWord.act RS hcubic hrotation
        (ClassicalCertificateCubicWord.node * word) root := by
  rw [ClassicalCertificateCubicWord.act_mul]
  simp [ClassicalCertificateCubicWord.act]

@[simp] theorem edge_act
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    (word : ClassicalCertificateCubicWord.CubicWord) (root : RS.D) :
    RS.alpha
        (ClassicalCertificateCubicWord.act RS hcubic hrotation word root) =
      ClassicalCertificateCubicWord.act RS hcubic hrotation
        (ClassicalCertificateCubicWord.edge * word) root := by
  rw [ClassicalCertificateCubicWord.act_mul]
  simp [ClassicalCertificateCubicWord.act]

@[simp] theorem qstepR_act
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    (word : ClassicalCertificateCubicWord.CubicWord) (root : RS.D) :
    qstepR RS
        (ClassicalCertificateCubicWord.act RS hcubic hrotation word root) =
      ClassicalCertificateCubicWord.act RS hcubic hrotation
        (ClassicalCertificateCubicWord.qstepR * word) root := by
  rw [ClassicalCertificateCubicWord.act_mul]
  simp [qstepR, ClassicalCertificateCubicWord.act,
    Equiv.Perm.mul_apply]

@[simp] theorem qstepL_act
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    (word : ClassicalCertificateCubicWord.CubicWord) (root : RS.D) :
    qstepL RS
        (ClassicalCertificateCubicWord.act RS hcubic hrotation word root) =
      ClassicalCertificateCubicWord.act RS hcubic hrotation
        (ClassicalCertificateCubicWord.qstepL * word) root := by
  rw [ClassicalCertificateCubicWord.act_mul]
  simp [qstepL, ClassicalCertificateCubicWord.act,
    Equiv.Perm.mul_apply]

/-- The word traversal is exactly the propositional semantics of a question. -/
theorem Question.fits_iff_wordVisits
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    (root : RS.D) (word : ClassicalCertificateCubicWord.CubicWord)
    (question : Question) :
    question.Fits RS
        (ClassicalCertificateCubicWord.act RS hcubic hrotation word root) ↔
      ∀ visit ∈ question.wordVisits word,
        faceArity RS
          (ClassicalCertificateCubicWord.act RS hcubic hrotation
            visit.1 root) = visit.2 := by
  induction question generalizing word with
  | empty => simp [Question.Fits, Question.wordVisits]
  | check arity => simp [Question.Fits, Question.wordVisits]
  | left arity next ih =>
      simp [Question.Fits, Question.wordVisits, ih]
  | right arity next ih =>
      simp [Question.Fits, Question.wordVisits, ih]
  | fork arity qleft qright ihLeft ihRight =>
      simp [Question.Fits, Question.wordVisits, ihLeft, ihRight,
        or_imp, forall_and]
  | skewLeft arity next ih =>
      simp [Question.Fits, Question.wordVisits, ih, mul_assoc]
  | skewRight arity next ih =>
      simp [Question.Fits, Question.wordVisits, ih]

/-- The word traversal is exactly the propositional semantics of a quiz. -/
theorem Quiz.fits_iff_wordVisits
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    (root : RS.D) (word : ClassicalCertificateCubicWord.CubicWord)
    (quiz : Quiz) :
    quiz.Fits RS
        (ClassicalCertificateCubicWord.act RS hcubic hrotation word root) ↔
      ∀ visit ∈ quiz.wordVisits word,
        faceArity RS
          (ClassicalCertificateCubicWord.act RS hcubic hrotation
            visit.1 root) = visit.2 := by
  rw [Quiz.Fits, Quiz.wordVisits, List.forall_mem_append]
  rw [edge_act]
  rw [Question.fits_iff_wordVisits, Question.fits_iff_wordVisits]

/-- The universal word that names one standard sector observation. -/
def sectorObservationWord (position : Nat) : Location →
    ClassicalCertificateCubicWord.CubicWord
  | .spoke =>
      ClassicalCertificateCubicWord.edge *
        ClassicalCertificateCubicWord.face ^ position
  | .hat =>
      ClassicalCertificateCubicWord.edge *
        ClassicalCertificateCubicWord.face ^ 2 *
          ClassicalCertificateCubicWord.edge *
            ClassicalCertificateCubicWord.face ^ position
  | .fan1 =>
      ClassicalCertificateCubicWord.edge *
        ClassicalCertificateCubicWord.face ^ 3 *
          ClassicalCertificateCubicWord.edge *
            ClassicalCertificateCubicWord.face ^ position
  | .fan2 =>
      ClassicalCertificateCubicWord.edge *
        ClassicalCertificateCubicWord.face ^ 4 *
          ClassicalCertificateCubicWord.edge *
            ClassicalCertificateCubicWord.face ^ position
  | .fan3 =>
      ClassicalCertificateCubicWord.edge *
        ClassicalCertificateCubicWord.face ^ 5 *
          ClassicalCertificateCubicWord.edge *
            ClassicalCertificateCubicWord.face ^ position

/-- Sector observation words act as the concrete rotation-system sector
locations they encode. -/
theorem sectorObservationWord_act
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    (root : RS.D) (position : Nat) (location : Location) :
    ClassicalCertificateCubicWord.act RS hcubic hrotation
        (sectorObservationWord position location) root =
      sectorLocationDart RS location ((RS.phi ^ position) root) := by
  cases location <;>
    simp [sectorObservationWord, sectorLocationDart,
      ClassicalCertificateCubicWord.act, Function.iterate_succ_apply,
      pow_succ, Equiv.Perm.mul_apply]

/-- Select the containment fact at one addressed sector location. -/
theorem SectorProfile.fits_containsAt
    {profile : SectorProfile} {sector : Sector}
    (hfits : profile.Fits sector) (location : Location) :
    (sector.rangeAt location).Contains (profile.valueAt location) := by
  rcases hfits with ⟨hspoke, hhat, hfan1, hfan2, hfan3⟩
  cases location <;> assumption

/-- Membership in a singleton face range fixes the observed arity. -/
theorem eq_of_singleton_contains {expected observed : Nat}
    (hexpected : expected < 9)
    (hcontains : (FaceRange.singleton expected).Contains observed) :
    observed = expected := by
  exact Nat.le_antisymm
    (hcontains.2.resolve_left (Nat.ne_of_lt hexpected)) hcontains.1

/-- A singleton range in a fitted sector supplies the arity of the
corresponding universal observation word. -/
theorem sectorObservationWord_arity_of_fits
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    (root : RS.D) (position : Nat) (location : Location)
    (sector : Sector) (arity : Nat)
    (hfits : (sectorProfileAt RS ((RS.phi ^ position) root)).Fits sector)
    (harity : arity < 9)
    (hrange : sector.rangeAt location = FaceRange.singleton arity) :
    faceArity RS
        (ClassicalCertificateCubicWord.act RS hcubic hrotation
          (sectorObservationWord position location) root) = arity := by
  rw [sectorObservationWord_act]
  rw [← sectorProfileAt_valueAt]
  have hcontains := SectorProfile.fits_containsAt hfits location
  rw [hrange] at hcontains
  exact eq_of_singleton_contains harity hcontains

/-- A pointwise pattern fit exposes the actual sector at any bounded hub
position. -/
theorem Pattern.Fits.sectorFitsAt
    (RS : RotationSystem V E) (root : RS.D) {pattern : Pattern}
    (hfits : Pattern.Fits (hubProfile RS root) pattern)
    (position : Nat)
    (hprofile : position < (RS.faceOrbit root).card)
    (hpattern : position < pattern.length) :
    (sectorProfileAt RS ((RS.phi ^ position) root)).Fits
      (pattern.get ⟨position, hpattern⟩) := by
  have hposition := hfits.get (i := position)
    (by simpa [hubProfile] using hprofile) hpattern
  simpa [hubProfile, faceCycleDart] using hposition

/-- A singleton pattern entry fixes the arity of its universal sector word. -/
theorem Pattern.Fits.sectorObservationWord_arity_of_singleton
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    (root : RS.D) {pattern : Pattern}
    (hfits : Pattern.Fits (hubProfile RS root) pattern)
    (position : Nat) (location : Location) (arity : Nat)
    (hprofile : position < (RS.faceOrbit root).card)
    (hpattern : position < pattern.length)
    (harity : arity < 9)
    (hrange :
      (pattern.get ⟨position, hpattern⟩).rangeAt location =
        FaceRange.singleton arity) :
    faceArity RS
        (ClassicalCertificateCubicWord.act RS hcubic hrotation
          (sectorObservationWord position location) root) = arity := by
  exact sectorObservationWord_arity_of_fits RS hcubic hrotation root
    position location _ arity
      (Pattern.Fits.sectorFitsAt RS root hfits position hprofile hpattern)
        harity hrange

/-- One checked match redirects an observed quiz word to a word whose arity
has already been supplied by a fitted presentation pattern. -/
structure VisitMatch where
  target : ClassicalCertificateCubicWord.CubicWord
  targetArity : Nat
  leftSteps : Int
  rightPeriods : Int

namespace VisitMatch

/-- Boolean check for arity agreement and equality modulo target-face motion
and the root-face period. -/
def check (hubSize : Nat)
    (visit : ClassicalCertificateCubicWord.CubicWord × Nat)
    (certificate : VisitMatch) : Bool :=
  decide (visit.2 = certificate.targetArity) &&
    ClassicalCertificateCubicWord.equalChecker visit.1
      (ClassicalCertificateCubicWord.face ^ certificate.leftSteps *
        certificate.target *
          ClassicalCertificateCubicWord.face ^
            (hubSize * certificate.rightPeriods))

end VisitMatch

/-- Pairwise checker for a complete list of quiz visits. -/
def wordCertificateChecker (hubSize : Nat) :
    List (ClassicalCertificateCubicWord.CubicWord × Nat) →
      List VisitMatch → Bool
  | [], [] => true
  | visit :: visits, certificate :: certificates =>
      certificate.check hubSize visit &&
        wordCertificateChecker hubSize visits certificates
  | _, _ => false

/-- Soundness of a complete word certificate. -/
theorem wordCertificateChecker_sound
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    (root : RS.D) (hubSize : Nat)
    (hcard : (RS.faceOrbit root).card = hubSize)
    (visits : List (ClassicalCertificateCubicWord.CubicWord × Nat))
    (certificates : List VisitMatch)
    (hcheck : wordCertificateChecker hubSize visits certificates = true)
    (htarget : ∀ certificate ∈ certificates,
      faceArity RS
          (ClassicalCertificateCubicWord.act RS hcubic hrotation
            certificate.target root) = certificate.targetArity) :
    ∀ visit ∈ visits,
      faceArity RS
          (ClassicalCertificateCubicWord.act RS hcubic hrotation
            visit.1 root) = visit.2 := by
  induction visits generalizing certificates with
  | nil => simp
  | cons visit visits ih =>
      cases certificates with
      | nil => simp [wordCertificateChecker] at hcheck
      | cons certificate certificates =>
          rcases Bool.and_eq_true_iff.mp hcheck with
            ⟨hheadCheck, htailCheck⟩
          rcases Bool.and_eq_true_iff.mp hheadCheck with
            ⟨harityCheck, hwordCheck⟩
          have harity : visit.2 = certificate.targetArity :=
            of_decide_eq_true harityCheck
          intro observed hobserved
          rcases List.mem_cons.mp hobserved with rfl | htail
          · calc
              faceArity RS
                  (ClassicalCertificateCubicWord.act RS hcubic hrotation
                    observed.1 root) =
                  faceArity RS
                    (ClassicalCertificateCubicWord.act RS hcubic hrotation
                      certificate.target root) :=
                ClassicalCertificateCubicWord.faceArity_act_eq_of_match_size
                  RS hcubic hrotation root hubSize hcard observed.1
                    certificate.target certificate.leftSteps
                      certificate.rightPeriods hwordCheck
              _ = certificate.targetArity :=
                htarget certificate (by simp)
              _ = observed.2 := harity.symm
          · exact ih certificates htailCheck
              (fun other hother => htarget other (by simp [hother]))
              observed htail

/-- A checked word certificate plus arities read from a fitted pattern proves
that the corresponding catalogue quiz fits. -/
theorem quizFits_of_wordCertificate
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    (root : RS.D) (hubSize : Nat)
    (hcard : (RS.faceOrbit root).card = hubSize)
    (anchor : ClassicalCertificateCubicWord.CubicWord)
    (quiz : Quiz) (certificates : List VisitMatch)
    (hcheck : wordCertificateChecker hubSize
      (quiz.wordVisits anchor) certificates = true)
    (htarget : ∀ certificate ∈ certificates,
      faceArity RS
          (ClassicalCertificateCubicWord.act RS hcubic hrotation
            certificate.target root) = certificate.targetArity) :
    Quiz.Fits RS
      (ClassicalCertificateCubicWord.act RS hcubic hrotation anchor root)
        quiz := by
  rw [Quiz.fits_iff_wordVisits]
  exact wordCertificateChecker_sound RS hcubic hrotation root hubSize
    hcard _ certificates hcheck htarget

/-- Facial arity is constant after one forward face step. -/
theorem faceArity_phi (RS : RotationSystem V E) (dart : RS.D) :
    faceArity RS (RS.phi dart) = faceArity RS dart := by
  unfold faceArity
  rw [RS.faceOrbit_of_mem]
  exact RS.phi_mem_faceOrbit (RS.mem_faceOrbit_self dart)

/-- Facial arity is constant after one backward face step. -/
theorem faceArity_phi_symm (RS : RotationSystem V E) (dart : RS.D) :
    faceArity RS (RS.phi.symm dart) = faceArity RS dart := by
  unfold faceArity
  rw [RS.faceOrbit_of_mem]
  exact RS.phi_symm_mem_faceOrbit (RS.mem_faceOrbit_self dart)

/-- The inverse face step crosses the inverse vertex rotation and then the
edge involution. -/
theorem phi_symm_apply (RS : RotationSystem V E) (dart : RS.D) :
    RS.phi.symm dart = RS.alpha (RS.rho.symm dart) := by
  apply RS.phi.injective
  simp [RotationSystem.phi_apply, RS.alpha_involutive]

/-- A period-three vertex rotation identifies two inverse steps with one
forward step. -/
theorem rho_symm_sq_apply_eq_rho_apply
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS) (dart : RS.D) :
    RS.rho.symm (RS.rho.symm dart) = RS.rho dart := by
  apply RS.rho.injective
  simp only [Equiv.apply_symm_apply]
  apply RS.rho.injective
  simp only [Equiv.apply_symm_apply]
  exact (rho_cube_apply_of_isCubic RS hcubic hrotation dart).symm

/-- On a five-dart face, two backward steps equal three forward steps. -/
theorem phi_symm_sq_apply_eq_phi_cube_apply_of_card_eq_five
    (RS : RotationSystem V E) (root : RS.D)
    (hcard : (RS.faceOrbit root).card = 5) :
    RS.phi.symm (RS.phi.symm root) =
      RS.phi (RS.phi (RS.phi root)) := by
  have hperiod :=
    (faceOrbit_isCycleOn RS root).pow_card_apply
      (RS.mem_faceOrbit_self root)
  rw [hcard] at hperiod
  apply RS.phi.injective
  simp only [Equiv.apply_symm_apply]
  apply RS.phi.injective
  simp only [Equiv.apply_symm_apply]
  simpa [pow_succ, Equiv.Perm.mul_apply] using hperiod.symm

/-- On a five-dart face, one backward step equals four forward steps. -/
theorem phi_symm_apply_eq_phi_four_apply_of_card_eq_five
    (RS : RotationSystem V E) (root : RS.D)
    (hcard : (RS.faceOrbit root).card = 5) :
    RS.phi.symm root =
      RS.phi (RS.phi (RS.phi (RS.phi root))) := by
  have hperiod :=
    (faceOrbit_isCycleOn RS root).pow_card_apply
      (RS.mem_faceOrbit_self root)
  rw [hcard] at hperiod
  apply RS.phi.injective
  simp only [Equiv.apply_symm_apply]
  simpa [pow_succ, Equiv.Perm.mul_apply] using hperiod.symm

/-- The first sharp discharge obstruction directly contains configuration
`cf001`: the period-five hub and period-three vertex rotations align the
three pentagonal spokes tested by its quiz. -/
theorem obstruction00_forces_cf001
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS) (root : RS.D)
    (hfits : Pattern.Fits (hubProfile RS root) obstruction00) :
    ∃ dart : RS.D, Quiz.Fits RS dart cf001 := by
  have hcard : (RS.faceOrbit root).card = 5 := by
    simpa [obstruction00] using hfits.length_eq
  have hfit0 := hfits.get (i := 0)
    (by simp [hubProfile, hcard]) (by simp [obstruction00])
  have hfit3 := hfits.get (i := 3)
    (by simp [hubProfile, hcard]) (by simp [obstruction00])
  have hfit4 := hfits.get (i := 4)
    (by simp [hubProfile, hcard]) (by simp [obstruction00])
  have hspoke0 : faceArity RS (RS.alpha root) = 5 := by
    have hcontains := hfit0.1
    simp only [hubProfile, List.get_ofFn, faceCycleDart, sectorProfileAt]
      at hcontains
    simpa [obstruction00, FaceRange.Contains, FaceRange.singleton] using
      Nat.le_antisymm (hcontains.2.resolve_left (by decide)) hcontains.1
  have hspoke3 :
      faceArity RS (RS.alpha (RS.phi (RS.phi (RS.phi root)))) = 5 := by
    have hcontains := hfit3.1
    simp only [hubProfile, List.get_ofFn, faceCycleDart, sectorProfileAt]
      at hcontains
    simpa [obstruction00, FaceRange.Contains, FaceRange.singleton, pow_succ,
      Equiv.Perm.mul_apply] using
      Nat.le_antisymm (hcontains.2.resolve_left (by decide)) hcontains.1
  have hspoke4 :
      faceArity RS
        (RS.alpha (RS.phi (RS.phi (RS.phi (RS.phi root))))) = 5 := by
    have hcontains := hfit4.1
    simp only [hubProfile, List.get_ofFn, faceCycleDart, sectorProfileAt]
      at hcontains
    simpa [obstruction00, FaceRange.Contains, FaceRange.singleton, pow_succ,
      Equiv.Perm.mul_apply] using
      Nat.le_antisymm (hcontains.2.resolve_left (by decide)) hcontains.1
  have hhub : faceArity RS root = 5 := hcard
  let dart := RS.rho root
  refine ⟨dart, ?_⟩
  change
    (faceArity RS dart = 5 ∧ True) ∧
      (faceArity RS (RS.alpha dart) = 5 ∧
        faceArity RS (qstepR RS (RS.alpha dart)) = 5 ∧
          faceArity RS (qstepL RS (qstepR RS (RS.alpha dart))) = 5)
  have hdart : dart = RS.phi (RS.alpha root) := by
    simp [dart, RotationSystem.phi_apply, RS.alpha_involutive]
  have hright : qstepR RS (RS.alpha dart) = root := by
    simp [qstepR, dart, RS.alpha_involutive]
  have hleft : qstepL RS root =
      RS.alpha (RS.phi (RS.phi (RS.phi root))) := by
    change RS.rho.symm (RS.alpha (RS.rho.symm root)) = _
    calc
      RS.rho.symm (RS.alpha (RS.rho.symm root)) =
          RS.rho.symm (RS.phi.symm root) := by
            rw [phi_symm_apply]
      _ = RS.alpha (RS.phi.symm (RS.phi.symm root)) := by
            rw [phi_symm_apply RS (RS.phi.symm root),
              RS.alpha_involutive]
      _ = RS.alpha (RS.phi (RS.phi (RS.phi root))) := by
            rw [phi_symm_sq_apply_eq_phi_cube_apply_of_card_eq_five
              RS root hcard]
  have halphaDart : RS.alpha dart =
      RS.phi.symm
        (RS.alpha (RS.phi (RS.phi (RS.phi (RS.phi root))))) := by
    change RS.alpha (RS.rho root) = _
    rw [← phi_symm_apply_eq_phi_four_apply_of_card_eq_five RS root hcard]
    rw [phi_symm_apply, phi_symm_apply, RS.alpha_involutive]
    rw [rho_symm_sq_apply_eq_rho_apply RS hcubic hrotation]
  constructor
  · constructor
    · rw [hdart, faceArity_phi]
      exact hspoke0
    · trivial
  · constructor
    · rw [halphaDart, faceArity_phi_symm]
      exact hspoke4
    constructor
    · rw [hright]
      exact hhub
    · rw [hright, hleft]
      exact hspoke3

end

end ClassicalCertificateQuiz

end Mettapedia.GraphTheory.FourColor
