import Mettapedia.GSLT.Logic.KripkeFixedPoint
import Mettapedia.Logic.RuleMulticategoryGraphs

/-!
# Finite checking of grounded circular-truth evidence

The source is the existing strong Kleene evidence calculus. Circular
specifications are permitted; certificates are finite well-founded trees.
Local rule codes are checked against their actual premises, and base leaves
are admitted under the selected system's decidable base authority.

The shared rule-witness interface supplies tree checking, graph replay and
the free proof multicategory. Finite-system decision is connected to the
same certificate authority. An ungrounded semantic verdict is different from
an unchecked certificate or an unfinished computation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.KripkeTruth.Checking

open Mettapedia.Logic

variable {J B : Type}

deriving instance DecidableEq for Formula

abbrev Signed (J B : Type) := Formula J B × Bool

/-- One original strong Kleene inference instance, before choosing a code. -/
inductive Rule (system : System J B) : List (Signed J B) → Signed J B → Prop where
  | baseHolds (fact : B) (held : system.baseHolds fact) : Rule system [] (.base fact, true)
  | baseFails (fact : B) (failed : system.baseFails fact) : Rule system [] (.base fact, false)
  | truth (judgment : J) (polarity : Bool) :
      Rule system [(system.spec judgment, polarity)] (.truth judgment, polarity)
  | neg (formula : Formula J B) (polarity : Bool) :
      Rule system [(formula, !polarity)] (.neg formula, polarity)
  | conjHolds (left right : Formula J B) :
      Rule system [(left, true), (right, true)] (.conj left right, true)
  | conjFailsLeft (left right : Formula J B) :
      Rule system [(left, false)] (.conj left right, false)
  | conjFailsRight (left right : Formula J B) :
      Rule system [(right, false)] (.conj left right, false)
  | disjHoldsLeft (left right : Formula J B) :
      Rule system [(left, true)] (.disj left right, true)
  | disjHoldsRight (left right : Formula J B) :
      Rule system [(right, true)] (.disj left right, true)
  | disjFails (left right : Formula J B) :
      Rule system [(left, false), (right, false)] (.disj left right, false)

inductive Code (J B : Type) where
  | baseHolds (fact : B)
  | baseFails (fact : B)
  | truth (judgment : J) (polarity : Bool)
  | neg (formula : Formula J B) (polarity : Bool)
  | conjHolds (left right : Formula J B)
  | conjFailsLeft (left right : Formula J B)
  | conjFailsRight (left right : Formula J B)
  | disjHoldsLeft (left right : Formula J B)
  | disjHoldsRight (left right : Formula J B)
  | disjFails (left right : Formula J B)

def Code.premises (system : System J B) : Code J B → List (Signed J B)
  | .baseHolds _ | .baseFails _ => []
  | .truth judgment polarity => [(system.spec judgment, polarity)]
  | .neg formula polarity => [(formula, !polarity)]
  | .conjHolds left right => [(left, true), (right, true)]
  | .conjFailsLeft left _ => [(left, false)]
  | .conjFailsRight _ right => [(right, false)]
  | .disjHoldsLeft left _ => [(left, true)]
  | .disjHoldsRight _ right => [(right, true)]
  | .disjFails left right => [(left, false), (right, false)]

def Code.conclusion : Code J B → Signed J B
  | .baseHolds fact => (.base fact, true)
  | .baseFails fact => (.base fact, false)
  | .truth judgment polarity => (.truth judgment, polarity)
  | .neg formula polarity => (.neg formula, polarity)
  | .conjHolds left right => (.conj left right, true)
  | .conjFailsLeft left right | .conjFailsRight left right => (.conj left right, false)
  | .disjHoldsLeft left right | .disjHoldsRight left right => (.disj left right, true)
  | .disjFails left right => (.disj left right, false)

variable (system : System J B)
variable [DecidablePred system.baseHolds] [DecidablePred system.baseFails]

def Code.admit : Code J B → Bool
  | .baseHolds fact => decide (system.baseHolds fact)
  | .baseFails fact => decide (system.baseFails fact)
  | _ => true

theorem Code.licensed (code : Code J B) (admitted : code.admit system = true) :
    Rule system (code.premises system) code.conclusion := by
  cases code with
  | baseHolds fact => exact .baseHolds fact (of_decide_eq_true admitted)
  | baseFails fact => exact .baseFails fact (of_decide_eq_true admitted)
  | truth judgment polarity => exact .truth judgment polarity
  | neg formula polarity => exact .neg formula polarity
  | conjHolds left right => exact .conjHolds left right
  | conjFailsLeft left right => exact .conjFailsLeft left right
  | conjFailsRight left right => exact .conjFailsRight left right
  | disjHoldsLeft left right => exact .disjHoldsLeft left right
  | disjHoldsRight left right => exact .disjHoldsRight left right
  | disjFails left right => exact .disjFails left right

variable [DecidableEq J] [DecidableEq B]

/-- The exact local interface; it performs no search for a rule or a proof. -/
def interface : RuleWitness (Rule system) where
  W := Code J B
  isInstance code premises conclusion := code.admit system &&
    decide (premises = code.premises system ∧ conclusion = code.conclusion)
  sound code premises conclusion accepted := by
    simp only [Bool.and_eq_true] at accepted
    obtain ⟨admitted, matching⟩ := accepted
    obtain ⟨rfl, rfl⟩ := of_decide_eq_true matching
    exact code.licensed system admitted
  complete premises conclusion licensed := by
    cases licensed with
    | baseHolds fact held => exact ⟨.baseHolds fact, by simp [Code.admit, held, Code.premises, Code.conclusion]⟩
    | baseFails fact failed => exact ⟨.baseFails fact, by simp [Code.admit, failed, Code.premises, Code.conclusion]⟩
    | truth judgment polarity => exact ⟨.truth judgment polarity, by simp [Code.admit, Code.premises, Code.conclusion]⟩
    | neg formula polarity => exact ⟨.neg formula polarity, by simp [Code.admit, Code.premises, Code.conclusion]⟩
    | conjHolds left right => exact ⟨.conjHolds left right, by simp [Code.admit, Code.premises, Code.conclusion]⟩
    | conjFailsLeft left right => exact ⟨.conjFailsLeft left right, by simp [Code.admit, Code.premises, Code.conclusion]⟩
    | conjFailsRight left right => exact ⟨.conjFailsRight left right, by simp [Code.admit, Code.premises, Code.conclusion]⟩
    | disjHoldsLeft left right => exact ⟨.disjHoldsLeft left right, by simp [Code.admit, Code.premises, Code.conclusion]⟩
    | disjHoldsRight left right => exact ⟨.disjHoldsRight left right, by simp [Code.admit, Code.premises, Code.conclusion]⟩
    | disjFails left right => exact ⟨.disjFails left right, by simp [Code.admit, Code.premises, Code.conclusion]⟩

omit [DecidablePred system.baseHolds] [DecidablePred system.baseFails]
    [DecidableEq J] [DecidableEq B] in
theorem evidence_derives {formula : Formula J B} {polarity : Bool}
    (evidence : system.Evidence formula polarity) : Derives (Rule system) (formula, polarity) := by
  induction evidence with
  | baseHolds held => exact .node [] _ (.baseHolds _ held) (by simp)
  | baseFails failed => exact .node [] _ (.baseFails _ failed) (by simp)
  | truth body ih => exact .node [_] _ (.truth _ _) (by simpa using ih)
  | neg body ih => exact .node [_] _ (.neg _ _) (by simpa using ih)
  | conjHolds left right ihLeft ihRight =>
      exact .node [_, _] _ (.conjHolds _ _) (by simpa using And.intro ihLeft ihRight)
  | conjFailsLeft left ih => exact .node [_] _ (.conjFailsLeft _ _) (by simpa using ih)
  | conjFailsRight right ih => exact .node [_] _ (.conjFailsRight _ _) (by simpa using ih)
  | disjHoldsLeft left ih => exact .node [_] _ (.disjHoldsLeft _ _) (by simpa using ih)
  | disjHoldsRight right ih => exact .node [_] _ (.disjHoldsRight _ _) (by simpa using ih)
  | disjFails left right ihLeft ihRight =>
      exact .node [_, _] _ (.disjFails _ _) (by simpa using And.intro ihLeft ihRight)

omit [DecidablePred system.baseHolds] [DecidablePred system.baseFails]
    [DecidableEq J] [DecidableEq B] in
theorem derives_evidence {claim : Signed J B} (derived : Derives (Rule system) claim) :
    Nonempty (system.Evidence claim.1 claim.2) := by
  apply Derives.least (fun claim => Nonempty (system.Evidence claim.1 claim.2)) ?_ derived
  intro premises conclusion licensed children
  cases licensed with
  | baseHolds fact held => exact ⟨.baseHolds held⟩
  | baseFails fact failed => exact ⟨.baseFails failed⟩
  | truth judgment polarity =>
      obtain ⟨body⟩ := children (system.spec judgment, polarity) (by simp)
      exact ⟨.truth body⟩
  | neg formula polarity =>
      obtain ⟨body⟩ := children (formula, !polarity) (by simp)
      exact ⟨.neg body⟩
  | conjHolds left right =>
      obtain ⟨first⟩ := children (left, true) (by simp)
      obtain ⟨second⟩ := children (right, true) (by simp)
      exact ⟨.conjHolds first second⟩
  | conjFailsLeft left right =>
      obtain ⟨body⟩ := children (left, false) (by simp)
      exact ⟨.conjFailsLeft body⟩
  | conjFailsRight left right =>
      obtain ⟨body⟩ := children (right, false) (by simp)
      exact ⟨.conjFailsRight body⟩
  | disjHoldsLeft left right =>
      obtain ⟨body⟩ := children (left, true) (by simp)
      exact ⟨.disjHoldsLeft body⟩
  | disjHoldsRight left right =>
      obtain ⟨body⟩ := children (right, true) (by simp)
      exact ⟨.disjHoldsRight body⟩
  | disjFails left right =>
      obtain ⟨first⟩ := children (left, false) (by simp)
      obtain ⟨second⟩ := children (right, false) (by simp)
      exact ⟨.disjFails first second⟩

abbrev Certificate := Derivation (Signed J B) (Code J B)

def check (claim : Signed J B) (certificate : Certificate (J := J) (B := B)) : Bool :=
  certificate.valid (interface system) && decide (certificate.concl = claim)

theorem check_sound {claim : Signed J B} {certificate : Certificate (J := J) (B := B)}
    (accepted : check system claim certificate = true) :
    Nonempty (system.Evidence claim.1 claim.2) := by
  simp only [check, Bool.and_eq_true] at accepted
  obtain ⟨valid, matching⟩ := accepted
  have derived : Derives (Rule system) certificate.concl :=
    certificate.valid_sound (interface system) valid
  have same : certificate.concl = claim := of_decide_eq_true matching
  exact derives_evidence system (Eq.mp (congrArg (Derives (Rule system)) same) derived)

theorem coverage (claim : Signed J B) :
    (∃ certificate, check system claim certificate = true) ↔
      Nonempty (system.Evidence claim.1 claim.2) := by
  constructor
  · rintro ⟨certificate, accepted⟩
    exact check_sound system accepted
  · rintro ⟨evidence⟩
    obtain ⟨certificate, valid, same⟩ :=
      (evidence_derives system evidence).exists_derivation (interface system)
    have sameClaim : certificate.concl = claim := by simpa only [Prod.eta] using same
    refine ⟨certificate, ?_⟩
    simp only [check, Bool.and_eq_true, valid, true_and, decide_eq_true_eq]
    exact sameClaim

/-- The circular specification is unfolded only at explicit truth nodes. -/
theorem judgment_coverage (judgment : J) (polarity : Bool) :
    (∃ certificate, check system (system.spec judgment, polarity) certificate = true) ↔
      system.least.Mem judgment polarity :=
  (coverage system _).trans system.mem_least_iff_evidence.symm

/-- This profile participates in the same proof category, without a cursor. -/
theorem closed_proof_iff_grounded (judgment : J) (polarity : Bool) :
    RuleSignature.Derivable (RuleWitness.signature (interface system))
        (system.spec judgment, polarity) ↔ system.least.Mem judgment polarity := by
  rw [RuleWitness.derivable_iff_derives]
  constructor
  · intro derived
    exact system.mem_least_iff_evidence.mpr (derives_evidence system derived)
  · intro grounded
    obtain ⟨evidence⟩ := system.mem_least_iff_evidence.mp grounded
    exact evidence_derives system evidence

/-- The finite decision procedure and exported evidence have the same
positive and negative authority. Its iteration bound is mathematical, not a
fixed implementation limit or a claim about physical evaluation time. -/
theorem finite_decision_iff_certificate [Fintype J] (judgment : J) (polarity : Bool) :
    (if polarity then (system.groundedDecide judgment).1
      else (system.groundedDecide judgment).2) = true ↔
      ∃ certificate, check system (system.spec judgment, polarity) certificate = true := by
  rw [judgment_coverage]
  cases polarity with
  | false => exact (system.groundedDecide_spec judgment).2
  | true => exact (system.groundedDecide_spec judgment).1

/-- A completed finite unknown verdict excludes both certificate polarities.
An intermediate unknown value has no such authority. -/
theorem finite_undetermined_iff_no_certificates [Fintype J] (judgment : J) :
    system.groundedDecide judgment = (false, false) ↔
      (¬ ∃ certificate, check system (system.spec judgment, true) certificate = true) ∧
      (¬ ∃ certificate, check system (system.spec judgment, false) certificate = true) := by
  have positive := finite_decision_iff_certificate system judgment true
  have negative := finite_decision_iff_certificate system judgment false
  change (system.groundedDecide judgment).1 = true ↔
    (∃ certificate, check system (system.spec judgment, true) certificate = true) at positive
  change (system.groundedDecide judgment).2 = true ↔
    (∃ certificate, check system (system.spec judgment, false) certificate = true) at negative
  constructor
  · intro undecided
    constructor
    · intro accepted
      have settled := positive.mpr accepted
      simp [undecided] at settled
    · intro accepted
      have settled := negative.mpr accepted
      simp [undecided] at settled
  · rintro ⟨noPositive, noNegative⟩
    have first : (system.groundedDecide judgment).1 = false := by
      cases value : (system.groundedDecide judgment).1 with
      | false => rfl
      | true => exact False.elim (noPositive (positive.mp value))
    have second : (system.groundedDecide judgment).2 = false := by
      cases value : (system.groundedDecide judgment).2 with
      | false => rfl
      | true => exact False.elim (noNegative (negative.mp value))
    exact Prod.ext first second

namespace Controls

open Example

private def fact : Certificate (J := Sentence) (B := Unit) :=
  .node (.base (), true) (.baseHolds ()) 0 Fin.elim0

theorem fact_accepts : check Example.system (Example.system.spec .fact, true) fact = true := by decide

theorem forged_false_refuses : check Example.system (Example.system.spec .fact, false) fact = false := by decide

theorem absent_premise_refuses :
    (interface Example.system).isInstance (.truth .teller true) [] (.truth .teller, true) = false := by decide

theorem false_base_leaf_refuses :
    check Example.system (.base (), false)
      (.node (.base (), false) (.baseFails ()) 0 Fin.elim0) = false := by decide

theorem cyclic_graph_refuses :
    DerivationGraph.replay (interface Example.system)
      [⟨(.truth .teller, true), .truth .teller true, [0], (0 : Nat)⟩] = none := by decide

theorem liar_has_no_certificate (polarity : Bool) :
    ¬ ∃ certificate, check Example.system (Example.system.spec .liar, polarity) certificate = true := by
  rw [coverage]
  exact fun ⟨evidence⟩ => (Example.system.liar_noEvidence (liar := .liar) rfl polarity).false evidence

def verdicts : List (String × Bool) :=
  [("grounded fact certificate", check Example.system (Example.system.spec .fact, true) fact),
   ("forged negative certificate", !check Example.system (Example.system.spec .fact, false) fact),
   ("self citation without a premise", !(interface Example.system).isInstance
      (.truth .teller true) [] (.truth .teller, true)),
   ("unadmitted negative base leaf", !check Example.system (.base (), false)
      (.node (.base (), false) (.baseFails ()) 0 Fin.elim0)),
   ("cyclic graph reference", (DerivationGraph.replay (interface Example.system)
      [⟨(.truth .teller, true), .truth .teller true, [0], (0 : Nat)⟩]).isNone),
   ("completed liar is ungrounded", decide (Example.system.groundedDecide .liar = (false, false))),
   ("initial unknown can later be true", decide
      (Example.system.stageDecide 0 .fact = (false, false) ∧
        Example.system.groundedDecide .fact = (true, false)))]

end Controls
end Mettapedia.GSLT.KripkeTruth.Checking
