import Mettapedia.OSLF.NativeTypes.Decision.FiniteMuCalculus

/-!
# Finite modal fixed-point strategy controls

The fixture has a two-state cycle and a separate path ending at a deadlock.
Free observations, nested binders, modal vacuity, negation and recursive
positivity refusal are checked through the existing formula language.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.FiniteMuCalculus.Controls

open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.MuCalculusBoundary
open Reference.Core

abbrev State := Fin 4

def fixture : LTS State Unit where
  trans source _ target := (source = 0 ∧ target = 1) ∨
    (source = 1 ∧ target = 0) ∨ (source = 2 ∧ target = 3)

def model : Model fixture where
  successors source _ := Finset.univ.filter fun target =>
    (source = 0 ∧ target = 1) ∨ (source = 1 ∧ target = 0) ∨ (source = 2 ∧ target = 3)
  successors_exact source action target := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rfl

def empty : Environment State 0 := Fin.elim0
def observed : Environment State 1 := fun _ => {1}

def reachObservation : Formula Unit 1 :=
  .mu (.disj (.var 1) (.diamond () (.var 0)))

def infinitePath : Formula Unit 0 := .nu (.diamond () (.var 0))

/-- Outer X and inner Y are distinct de Bruijn variables; the supplied
observation moves to index two under both binders. -/
def repeatedObservation : Formula Unit 1 :=
  .nu (.mu (.disj (.conj (.var 2) (.diamond () (.var 1))) (.diamond () (.var 0))))

def innerNegative : Formula Unit 0 := .nu (.mu (.neg (.var 0)))
def doubleNegative : Formula Unit 0 := .mu (.neg (.neg (.var 0)))

theorem reachability_answers : evaluate model reachObservation observed = {0, 1} := by decide +kernel
theorem infinite_path_answers : evaluate model infinitePath empty = {0, 1} := by decide +kernel
theorem nested_answers : evaluate model repeatedObservation observed = {0, 1} := by decide +kernel
theorem outer_positive_does_not_admit_inner_negative :
    (Formula.mu (Formula.neg (Formula.var 0)) : Formula Unit 1).isPositive = true ∧
      fixedPointsPositive innerNegative = false := by decide +kernel

theorem nested_positive_semantics : satisfies fixture observed.meaning repeatedObservation 0 :=
  (evaluate_correct model repeatedObservation (by decide +kernel) observed 0).mp (by decide +kernel)

theorem nested_negative_semantics : ¬ satisfies fixture observed.meaning repeatedObservation 2 := by
  intro satisfied
  have member := (evaluate_correct model repeatedObservation (by decide +kernel) observed 2).mpr satisfied
  have absent : (2 : State) ∉ evaluate model repeatedObservation observed := by decide +kernel
  exact absent member

theorem deadlock_box_is_vacuous : satisfies fixture empty.meaning (.box () .ff) 3 :=
  (evaluate_correct model (.box () .ff) (by decide +kernel) empty 3).mp (by decide +kernel)

def run : IO Unit := do
  let enough := requiredBudget (State := State) repeatedObservation
  let checks := [
    evaluate model reachObservation observed == {0, 1},
    evaluate model infinitePath empty == {0, 1},
    evaluate model repeatedObservation observed == {0, 1},
    evaluate model (.neg infinitePath) empty == {2, 3},
    evaluate model (.box () .ff) empty == {3},
    evaluate model (.diamond () .tt) empty == {0, 1, 2},
    evaluate model (.conj (.var 0) (.neg (.var 0))) observed == ∅,
    evaluate model (.disj (.var 0) (.neg (.var 0))) observed == Finset.univ,
    evaluate model doubleNegative empty == ∅,
    fixedPointsPositive doubleNegative == true,
    fixedPointsPositive (.neg infinitePath) == true,
    fixedPointsPositive innerNegative == false,
    (check? model innerNegative empty 1000 0).isNone,
    ((check? model repeatedObservation observed 0 0).map Outcome.answer) == some none,
    ((check? model repeatedObservation observed (enough - 1) 0).map Outcome.answer) == some none,
    ((check? model repeatedObservation observed enough 0).map Outcome.answer) == some (some true),
    ((check? model repeatedObservation observed enough 2).map Outcome.answer) == some (some false),
    ((check? model repeatedObservation observed (enough + 5) 1).map Outcome.answer) == some (some true)]
  if !checks.all id then throw (IO.userError "Finite modal fixed-point control failed")
  IO.println s!"Finite modal fixed-point controls: {checks.length} passed"

#eval run

end Mettapedia.OSLF.NativeTypes.Decision.FiniteMuCalculus.Controls
