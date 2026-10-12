import Mettapedia.OSLF.Framework.FundedStructuralLearner

/-!
# Executable admission of complete structural questions

The checker reads the constructor permissions and every finite child of
the independently authored formula. Its Boolean result classifies the
existing inductive admission judgment. A successful check constructs the
question accepted by the funded structural protocol, retaining the whole
formula. Capability admission is independent of the offered tree and purse.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.InstrumentQuestionAdmission

open InstrumentObservations

universe u

variable {Symbols : Type u} {arity : Symbols → Nat}

def check (opened : Policy Symbols) [DecidablePred opened] : Formula Symbols arity → Bool
  | .top => true
  | .neg body => check opened body
  | .conj first second => check opened first && check opened second
  | .headed constructor arguments =>
      decide (opened constructor) && decide (∀ position, check opened (arguments position) = true)

theorem check_iff (opened : Policy Symbols) [DecidablePred opened]
    (formula : Formula Symbols arity) : check opened formula = true ↔ AdmittedFormula opened formula := by
  induction formula with
  | top => exact ⟨fun _ => .top, fun _ => rfl⟩
  | neg body inductionHypothesis =>
      change check opened body = true ↔ _
      constructor
      · exact fun checked => .neg (inductionHypothesis.mp checked)
      · intro admitted
        cases admitted with
        | neg bodyAdmitted => exact inductionHypothesis.mpr bodyAdmitted
  | conj first second firstIH secondIH =>
      change (check opened first && check opened second) = true ↔ _
      rw [Bool.and_eq_true, firstIH, secondIH]
      constructor
      · exact fun ⟨left, right⟩ => .conj left right
      · intro admitted
        cases admitted with
        | conj left right => exact ⟨left, right⟩
  | headed constructor arguments inductionHypothesis =>
      change (decide (opened constructor) &&
        decide (∀ position, check opened (arguments position) = true)) = true ↔ _
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      constructor
      · exact fun ⟨permission, children⟩ =>
          .headed constructor arguments permission (fun position => (inductionHypothesis position).mp (children position))
      · intro admitted
        cases admitted with
        | headed _ _ permission children =>
            exact ⟨permission, fun position => (inductionHypothesis position).mpr (children position)⟩

def question? (opened : Policy Symbols) [DecidablePred opened] (formula : Formula Symbols arity) :
    Option (FundedStructuralLearner.Question (arity := arity) opened) :=
  if checked : check opened formula = true then some ⟨formula, (check_iff opened formula).mp checked⟩
  else none

theorem question?_isSome_iff (opened : Policy Symbols) [DecidablePred opened]
    (formula : Formula Symbols arity) :
    (question? opened formula).isSome = true ↔ AdmittedFormula opened formula := by
  by_cases checked : check opened formula = true
  · have admitted := (check_iff opened formula).mp checked
    simp [question?, checked, admitted]
  · have excluded : ¬ AdmittedFormula opened formula :=
      fun admitted => checked ((check_iff opened formula).mpr admitted)
    simp [question?, checked, excluded]

theorem question?_readout (opened : Policy Symbols) [DecidablePred opened]
    (formula : Formula Symbols arity) (question : FundedStructuralLearner.Question (arity := arity) opened)
    (produced : question? opened formula = some question) : question.val = formula := by
  unfold question? at produced
  split_ifs at produced with checked
  · exact (congrArg Subtype.val (Option.some.inj produced)).symm

theorem check_mono {smaller larger : Policy Symbols} [DecidablePred smaller] [DecidablePred larger]
    (inclusion : ∀ constructor, smaller constructor → larger constructor)
    (formula : Formula Symbols arity) (checked : check smaller formula = true) :
    check larger formula = true := by
  apply (check_iff larger formula).mpr
  have admitted := (check_iff smaller formula).mp checked
  clear checked
  induction admitted with
  | top => exact .top
  | neg _ inductionHypothesis => exact .neg inductionHypothesis
  | conj _ _ firstIH secondIH => exact .conj firstIH secondIH
  | headed constructor arguments permission _ inductionHypothesis =>
      exact .headed constructor arguments (inclusion _ permission) inductionHypothesis

end Mettapedia.OSLF.Framework.InstrumentQuestionAdmission
