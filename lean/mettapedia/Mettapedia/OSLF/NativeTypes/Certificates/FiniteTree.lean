import Mettapedia.TypeTheory.JudgmentDerivation
import Mathlib.Data.Fintype.Defs

/-!
# Finite certificate checking for generated judgment presentations

Unchecked certificates retain a rule code and its ordered child occurrences.
The checker compares each independently computed premise judgment with the
child's conclusion. Its acceptance theorem reconstructs the original indexed
derivation and proves that erasing that derivation recovers the exact input
certificate. No semantic truth or derivability oracle is required.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Certificates

open Mettapedia.TypeTheory

universe u

structure Presentation where
  Judgment : Type u
  Rule : Type u
  conclusion : Rule → Judgment
  premises : Rule → List Judgment

def Presentation.signature (P : Presentation.{u}) : JudgmentDerivation.Signature.{u} where
  Judgment := P.Judgment
  Rule judgment := {rule : P.Rule // P.conclusion rule = judgment}
  Premise rule := ULift (Fin (P.premises rule.val).length)
  hypothesis rule position := (P.premises rule.val).get position.down

abbrev Presentation.Derivation (P : Presentation.{u}) (judgment : P.Judgment) :=
  JudgmentDerivation.Derivation P.signature judgment

/-- Premise positions are finite and ordered; equal premise judgments do not
identify their distinct certificate occurrences. -/
inductive Tree (P : Presentation.{u}) : Type u where
  | node (rule : P.Rule)
      (children : Fin (P.premises rule).length → Tree P) : Tree P

namespace Tree

variable {P : Presentation.{u}}

def root : Tree P → P.Rule
  | .node rule _ => rule

/-- Syntax equality is the only required decision operation. -/
def check [DecidableEq P.Judgment] : Tree P → P.Judgment → Bool
  | .node rule children, judgment =>
      decide (P.conclusion rule = judgment) &&
        decide (∀ position,
          check (children position) ((P.premises rule).get position) = true)

/-- Erasure keeps complete rule payloads and every ordered premise subtree. -/
def erase {judgment : P.Judgment} : P.Derivation judgment → Tree P
  | .node rule premises => .node rule.val (fun position => erase (premises ⟨position⟩))

/-- A successful check constructs a derivation of the independently supplied
indexed rules. The returned proof retains all original certificate choices. -/
def reconstruct [DecidableEq P.Judgment] : (tree : Tree P) →
    (judgment : P.Judgment) → check tree judgment = true → P.Derivation judgment
  | .node rule children, judgment, accepted => by
      have clauses : decide (P.conclusion rule = judgment) = true ∧
          decide (∀ position,
            check (children position) ((P.premises rule).get position) = true) = true := by
        simpa only [check, Bool.and_eq_true] using accepted
      have conclusion : P.conclusion rule = judgment := of_decide_eq_true clauses.1
      have premises : ∀ position,
          check (children position) ((P.premises rule).get position) = true :=
        of_decide_eq_true clauses.2
      exact .node ⟨rule, conclusion⟩
        (fun position => reconstruct (children position.down)
          ((P.premises rule).get position.down) (premises position.down))

theorem check_erase [DecidableEq P.Judgment] {judgment : P.Judgment}
    (derivation : P.Derivation judgment) : check (erase derivation) judgment = true := by
  apply JudgmentDerivation.Derivation.rec
    (motive := fun judgment derivation => check (erase derivation) judgment = true)
    (t := derivation)
  intro judgment rule premises ih
  rcases rule with ⟨rule, conclusion⟩
  cases conclusion
  simp only [erase, check, decide_true, Bool.true_and]
  apply decide_eq_true
  intro position
  exact ih ⟨position⟩

theorem erase_reconstruct [DecidableEq P.Judgment] (tree : Tree P)
    (judgment : P.Judgment) (accepted : check tree judgment = true) :
    erase (reconstruct tree judgment accepted) = tree := by
  induction tree generalizing judgment with
  | node rule children ih =>
      change Tree.node rule (fun position =>
        erase (reconstruct (children position) ((P.premises rule).get position) _)) =
        Tree.node rule children
      congr 1
      funext position
      exact ih position _ _

theorem reconstruct_erase [DecidableEq P.Judgment] {judgment : P.Judgment}
    (derivation : P.Derivation judgment) :
    reconstruct (erase derivation) judgment (check_erase derivation) = derivation := by
  apply JudgmentDerivation.Derivation.rec
    (motive := fun judgment derivation =>
      reconstruct (erase derivation) judgment (check_erase derivation) = derivation)
    (t := derivation)
  intro judgment rule premises ih
  rcases rule with ⟨rule, conclusion⟩
  cases conclusion
  change JudgmentDerivation.Derivation.node (S := P.signature) ⟨rule, rfl⟩
    (fun position => reconstruct (erase (premises position))
      ((P.premises rule).get position.down) _) =
    JudgmentDerivation.Derivation.node (S := P.signature) ⟨rule, rfl⟩ premises
  congr 1
  funext position
  exact ih position

theorem erase_injective [DecidableEq P.Judgment] {judgment : P.Judgment} :
    Function.Injective (@erase P judgment) := by
  intro first second same
  have checked := congrArg (fun tree =>
    if accepted : check tree judgment = true then
      some (reconstruct tree judgment accepted) else none) same
  simpa only [dif_pos (check_erase first), dif_pos (check_erase second),
    reconstruct_erase, Option.some.injEq] using checked

/-- Exact acceptance includes occurrence identity, rather than only existence
of some derivation with the same final judgment. -/
theorem check_exact [DecidableEq P.Judgment] (tree : Tree P) (judgment : P.Judgment) :
    check tree judgment = true ↔
      ∃ derivation : P.Derivation judgment, erase derivation = tree := by
  constructor
  · intro accepted
    exact ⟨reconstruct tree judgment accepted, erase_reconstruct tree judgment accepted⟩
  · rintro ⟨derivation, same⟩
    rw [← same]
    exact check_erase derivation

theorem check_sound [DecidableEq P.Judgment] (tree : Tree P) (judgment : P.Judgment)
    (accepted : check tree judgment = true) : Nonempty (P.Derivation judgment) :=
  ⟨reconstruct tree judgment accepted⟩

theorem check_complete [DecidableEq P.Judgment] (judgment : P.Judgment) :
    Nonempty (P.Derivation judgment) ↔ ∃ tree : Tree P, check tree judgment = true := by
  constructor
  · rintro ⟨derivation⟩
    exact ⟨erase derivation, check_erase derivation⟩
  · rintro ⟨tree, accepted⟩
    exact check_sound tree judgment accepted

theorem reconstructed_root [DecidableEq P.Judgment] (tree : Tree P)
    (judgment : P.Judgment) (accepted : check tree judgment = true) :
    root (erase (reconstruct tree judgment accepted)) = root tree := by
  rw [erase_reconstruct]

end Tree

end Mettapedia.OSLF.NativeTypes.Certificates
