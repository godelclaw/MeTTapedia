import Mettapedia.GraphTheory.FourColor.ClassicalCertificateDischargeRuleBound
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
