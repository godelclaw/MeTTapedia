import Mettapedia.GSLT.Logic.PropositionalLRAT
import Mettapedia.Logic.RuleMulticategoryGraphs

/-!
# LRAT refutations at the level of their actions

The existing LRAT adapter calls the standard-library checker on a whole proof.
This module retains each action. A reverse-unit-propagation addition is a
multi-premise rule instance: its premises are the hinted clauses, in hint order
and with repetition, and its conclusion is the added clause. Input clauses are
premise-free instances. A refutation compiles to a derivation graph of these
instances, with LRAT identifiers resolved to graph positions; deletion removes an
identifier, so a deleted clause can no longer be cited.

* `rupCheck_sound`: an accepted RUP instance is a semantic consequence of its
  premises; `interface` is the exact rule-instance interface.
* `check_sound`: an accepted action stream refutes the formula.
* `check_graph`: the accepted stream is an accepted derivation graph, so every
  action denotes a closed morphism of the free multicategory on RUP instances
  (`RuleWitness.unfold_root`).
* `rat_not_implied`: a resolution-asymmetric addition need not be a consequence of
  the formula. RAT preserves satisfiability, not implication, so it is an
  extension step rather than a rule instance of this calculus; the adapter refuses
  it and leaves it to the whole-proof checker.

The action checker is an independent checker of the RUP fragment. Agreement with
the standard-library checker is tested on shared controls, not proved.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Logic.PropositionalLRATActions

open Mettapedia.GSLT.Logic.PropositionalFormula
open Mettapedia.GSLT.Logic.PropositionalResolution (Unsat)
open Mettapedia.Logic

/-! ## Reverse unit propagation -/

/-- The literals of a hint not falsified by the assumed literals. -/
def openLiterals (assigned : List Literal) (hint : Clause) : List Literal :=
  hint.filter fun literal => decide (literal.complement ∉ assigned)

/-- Follow the hints in order: each must be unit or conflicting. -/
def propagate (assigned : List Literal) : List Clause → Bool
  | [] => false
  | hint :: rest =>
      match openLiterals assigned hint with
      | [] => true
      | [unit] => propagate (unit :: assigned) rest
      | _ :: _ :: _ => false

/-- A clause is RUP from its hinted premises. -/
def rupCheck (premises : List Clause) (clause : Clause) : Bool :=
  propagate (clause.map Literal.complement) premises

theorem sat_complement (v : Nat → Bool) (literal : Literal) :
    Literal.sat v literal.complement = !Literal.sat v literal := by
  cases literal <;> simp [Literal.complement, Literal.sat]

theorem propagate_sound (v : Nat → Bool) :
    ∀ (assigned : List Literal) (hints : List Clause), propagate assigned hints = true →
      (∀ literal ∈ assigned, Literal.sat v literal = true) →
      (∀ hint ∈ hints, Clause.sat v hint = true) → False
  | _, [], accepted, _, _ => by simp [propagate] at accepted
  | assigned, hint :: rest, accepted, trueAssigned, trueHints => by
      have hintTrue := trueHints hint List.mem_cons_self
      obtain ⟨literal, member, literalTrue⟩ := List.any_eq_true.mp hintTrue
      simp only [propagate] at accepted
      cases opened : openLiterals assigned hint with
      | nil =>
          have falsified : literal.complement ∈ assigned := by
            by_contra notAssigned
            have : literal ∈ openLiterals assigned hint := by
              simp [openLiterals, member, notAssigned]
            rw [opened] at this
            cases this
          have := trueAssigned _ falsified
          rw [sat_complement, literalTrue] at this
          cases this
      | cons unit more =>
          cases more with
          | nil =>
              rw [opened] at accepted
              apply propagate_sound v (unit :: assigned) rest accepted
              · intro chosen chosenMember
                rcases List.mem_cons.mp chosenMember with rfl | chosenMember
                · by_cases falsified : literal.complement ∈ assigned
                  · have := trueAssigned _ falsified
                    rw [sat_complement, literalTrue] at this
                    cases this
                  · have : literal ∈ openLiterals assigned hint := by
                      simp [openLiterals, member, falsified]
                    rw [opened] at this
                    rcases List.mem_singleton.mp this with rfl
                    exact literalTrue
                · exact trueAssigned chosen chosenMember
              · exact fun other otherMember => trueHints other (List.mem_cons_of_mem _ otherMember)
          | cons second rest' =>
              rw [opened] at accepted
              cases accepted

/-- **RUP is sound.** An accepted instance is a consequence of its premises. -/
theorem rupCheck_sound {premises : List Clause} {clause : Clause}
    (accepted : rupCheck premises clause = true) (v : Nat → Bool)
    (premisesTrue : ∀ premise ∈ premises, Clause.sat v premise = true) :
    Clause.sat v clause = true := by
  by_contra clauseFalse
  apply propagate_sound v (clause.map Literal.complement) premises accepted _ premisesTrue
  intro complement member
  obtain ⟨literal, literalMember, rfl⟩ := List.mem_map.mp member
  rw [sat_complement]
  have : Literal.sat v literal = false := by
    by_contra literalTrue
    exact clauseFalse (List.any_eq_true.mpr ⟨literal, literalMember, by simpa using literalTrue⟩)
  simp [this]

/-! ## The action calculus -/

/-- Input clauses and RUP additions. -/
inductive ActionRule (formula : CNF) : List Clause → Clause → Prop where
  | input {clause : Clause} : clause ∈ formula → ActionRule formula [] clause
  | rup {premises : List Clause} {clause : Clause} :
      rupCheck premises clause = true → ActionRule formula premises clause

inductive ActionCode where
  | input (index : Nat)
  | rup
  deriving DecidableEq, Repr

def checkAction (formula : CNF) : ActionCode → List Clause → Clause → Bool
  | .input index, premises, clause => premises.isEmpty && decide (formula[index]? = some clause)
  | .rup, premises, clause => rupCheck premises clause

/-- The exact rule-instance interface of the action calculus. -/
def interface (formula : CNF) : RuleWitness (ActionRule formula) where
  W := ActionCode
  isInstance := checkAction formula
  sound := by
    intro code premises clause accepted
    cases code with
    | input index =>
        simp only [checkAction, Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at accepted
        obtain ⟨rfl, found⟩ := accepted
        exact .input (List.mem_of_getElem? found)
    | rup => exact .rup accepted
  complete := by
    intro premises clause rule
    cases rule with
    | input member =>
        obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
        exact ⟨.input index, by simp [checkAction, found]⟩
    | rup accepted => exact ⟨.rup, accepted⟩

theorem derives_sound (formula : CNF) {clause : Clause}
    (derived : Derives (ActionRule formula) clause) (v : Nat → Bool)
    (formulaTrue : CNF.sat v formula = true) : Clause.sat v clause = true := by
  apply Derives.least (fun clause => Clause.sat v clause = true) ?_ derived
  intro premises conclusion rule earlier
  cases rule with
  | input member => exact List.all_eq_true.mp formulaTrue conclusion member
  | rup accepted => exact rupCheck_sound accepted v earlier

/-- Deriving the empty clause refutes the formula. -/
theorem derives_empty_unsat (formula : CNF) (derived : Derives (ActionRule formula) []) :
    Unsat formula := by
  intro v
  cases formulaTrue : CNF.sat v formula with
  | false => rfl
  | true =>
      have := derives_sound formula derived v formulaTrue
      simp [Clause.sat] at this

/-! ## Retained actions -/

/-- LRAT actions over native clauses. -/
inductive Action where
  | rup (id : Nat) (clause : Clause) (hints : List Nat)
  | rat (id : Nat) (clause : Clause)
  | delete (ids : List Nat)

/-- Standard-library integer literals, with variables shifted by one. -/
def decodeLiteral (value : Int) : Literal :=
  if 0 < value then .pos (value.natAbs - 1) else .neg (value.natAbs - 1)

def ofIntAction : Std.Tactic.BVDecide.LRAT.IntAction → Action
  | .addEmpty id hints => .rup id [] hints.toList
  | .addRup id clause hints => .rup id (clause.toList.map decodeLiteral) hints.toList
  | .addRat id clause _ _ _ => .rat id (clause.toList.map decodeLiteral)
  | .del ids => .delete ids.toList

/-- Live identifiers with their graph positions, and the emitted graph. -/
structure Retained where
  live : List (Nat × Nat)
  nodes : List (DerivationGraph.Node Clause ActionCode Nat)

def lookupId (live : List (Nat × Nat)) (id : Nat) : Option Nat :=
  (live.find? fun entry => entry.1 == id).map Prod.snd

/-- Input clauses carry identifiers `1, 2, ...` in order. -/
def start (formula : CNF) : Retained :=
  ⟨(List.range formula.length).map (fun index => (index + 1, index)),
    formula.mapIdx fun index clause => ⟨clause, .input index, [], index + 1⟩⟩

def compileStep (retained : Retained) : Action → Option Retained
  | .rup id clause hints =>
      if (lookupId retained.live id).isSome then none else
        match hints.mapM (lookupId retained.live) with
        | none => none
        | some parents =>
            some ⟨(id, retained.nodes.length) :: retained.live,
              retained.nodes ++ [⟨clause, .rup, parents, id⟩]⟩
  | .rat _ _ => none
  | .delete ids => some ⟨retained.live.filter fun entry => !(ids.contains entry.1), retained.nodes⟩

def compile (formula : CNF) (actions : List Action) : Option Retained :=
  actions.foldlM compileStep (start formula)

/-- The action checker: compile, replay the retained graph, and require an
empty clause. -/
def check (formula : CNF) (actions : List Action) : Bool :=
  match compile formula actions with
  | none => false
  | some retained =>
      match DerivationGraph.replay (interface formula) retained.nodes with
      | none => false
      | some cache => decide ([] ∈ cache.toList)

/-- An accepted stream is an accepted derivation graph containing the empty clause. -/
theorem check_graph {formula : CNF} {actions : List Action} (accepted : check formula actions = true) :
    ∃ retained cache, compile formula actions = some retained ∧
      DerivationGraph.replay (interface formula) retained.nodes = some cache ∧ [] ∈ cache.toList := by
  unfold check at accepted
  split at accepted
  · cases accepted
  · rename_i retained compiled
    split at accepted
    · cases accepted
    · rename_i cache replayed
      exact ⟨retained, cache, compiled, replayed, of_decide_eq_true accepted⟩

/-- **The action checker is sound.** -/
theorem check_sound {formula : CNF} {actions : List Action} (accepted : check formula actions = true) :
    Unsat formula := by
  obtain ⟨retained, cache, -, replayed, member⟩ := check_graph accepted
  apply derives_empty_unsat formula
  exact DerivationGraph.replay_sound (interface formula) replayed [] (by simpa using member)

/-- Every action of an accepted stream denotes a closed morphism of the free
multicategory on RUP instances. -/
theorem check_unfolds {formula : CNF} {actions : List Action} (accepted : check formula actions = true) :
    ∃ retained terms, compile formula actions = some retained ∧
      DerivationGraph.replayWith
          (RuleWitness.termStep (interface formula) (Γ := CartesianMulticategory.closedContext))
          #[] retained.nodes = some terms := by
  obtain ⟨retained, cache, compiled, replayed, -⟩ := check_graph accepted
  obtain ⟨terms, unfolded, -⟩ := RuleWitness.unfold_root (interface formula) replayed
  exact ⟨retained, terms, compiled, unfolded⟩

/-! ## Resolution-asymmetric additions are extensions -/

/-- A RAT addition with a pure pivot: no clause of the formula contains the
pivot's complement, so the addition is RAT, yet it is not a consequence. -/
theorem rat_not_implied :
    CNF.sat (fun atom => atom == 0) [[.pos 0]] = true ∧
      Clause.sat (fun atom => atom == 0) [.pos 1] = false := by
  constructor <;> decide

/-- Hence no checker sound for implication accepts that addition as a rule
instance of the action calculus. -/
theorem rat_not_rule_instance (premises : List Clause) (fromFormula : ∀ premise ∈ premises, premise ∈ [[Literal.pos 0]]) :
    rupCheck premises [.pos 1] = false := by
  cases accepted : rupCheck premises [.pos 1] with
  | false => rfl
  | true =>
      have := rupCheck_sound accepted (fun atom => atom == 0) (by
        intro premise member
        rw [List.mem_singleton.mp (fromFormula premise member)]
        decide)
      simp [Clause.sat, Literal.sat] at this

namespace Controls

open PropositionalLRAT.Controls

def actions (proof : PropositionalLRAT.Proof) : List Action := proof.toList.map ofIntAction

theorem clash_accepted : check PropositionalResolution.clash (actions clashProof) = true := by decide

theorem xor_accepted : check xorFormula (actions xorProof) = true := by decide

theorem missing_hint_refused : check xorFormula (actions #[.addEmpty 5 #[1]]) = false := by decide

theorem unknown_hint_refused : check PropositionalResolution.clash (actions #[.addEmpty 3 #[17]]) = false := by
  decide

theorem deleted_premise_refused :
    check PropositionalResolution.clash (actions #[.del #[1], .addEmpty 3 #[1, 2]]) = false := by decide

theorem satisfiable_refused : check [[.pos 0]] (actions clashProof) = false := by decide

theorem rat_refused : check ratFormula (actions ratProof) = false := by decide

/-- Runtime comparison with the whole-proof standard-library checker. The RAT
proof is accepted there and classified as an extension here. -/
def verdicts : List (String × Bool) :=
  [("actions: complementary units", check PropositionalResolution.clash (actions clashProof) ==
      PropositionalLRAT.checker.check PropositionalResolution.clash clashProof),
   ("actions: nonempty RUP addition", check xorFormula (actions xorProof) ==
      PropositionalLRAT.checker.check xorFormula xorProof),
   ("actions: missing hint", check xorFormula (actions #[.addEmpty 5 #[1]]) ==
      PropositionalLRAT.checker.check xorFormula #[.addEmpty 5 #[1]]),
   ("actions: deleted premise", check PropositionalResolution.clash (actions #[.del #[1], .addEmpty 3 #[1, 2]]) ==
      PropositionalLRAT.checker.check PropositionalResolution.clash #[.del #[1], .addEmpty 3 #[1, 2]]),
   ("actions: RAT classified as extension", !(check ratFormula (actions ratProof)) &&
      PropositionalLRAT.checker.check ratFormula ratProof)]

end Controls

end Mettapedia.GSLT.Logic.PropositionalLRATActions
