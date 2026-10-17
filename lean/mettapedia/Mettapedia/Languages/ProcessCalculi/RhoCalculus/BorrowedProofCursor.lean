import Mettapedia.Languages.ProcessCalculi.RhoCalculus.NativeKernel
import Mettapedia.OSLF.NativeTypes.Certificates.DerivationGraph
import Mettapedia.Logic.DerivationGraph.CheckedCursor

/-!
# Borrowed proof rows for the original rho evidence presentation

This instance reuses the complete raw `Pattern` presentation in `NativeEvidence`.
It adds neither inference rules nor a substitute rho calculus. The generic
cursor checks source rows and their actual ordered premise occurrences. Root
admission separately executes `NativeKernel.checkAdmission` with the literal
requested context and endpoint sort.

This is the raw COMM profile: computing its rule conclusion calls the original
`semanticCommSubst`. Substitution work has not disappeared into a constant-cost
instruction, and no explicit computation receipt is supplied here. The scoped
intrinsic rho services, explicit COMM receipts, textual module front end and
native ownership implementation retain their independent qualification.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.BorrowedProofCursor

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Certificates
open NativeEvidence
open NativeKernel (Context SourceSort Admission checkAdmission)

local instance : DecidableEq NativeEvidence.presentation.Judgment :=
  inferInstanceAs (DecidableEq Judgment)

abbrev interface := NativeEvidence.presentation.ruleWitness

abbrev Store := Mettapedia.Logic.DerivationGraph.BorrowedCursor.Store
  Judgment NativeEvidence.presentation.Rule Nat

abbrev StoredNode := Mettapedia.Logic.DerivationGraph.BorrowedCursor.StoredNode
  Judgment NativeEvidence.presentation.Rule Nat

abbrev Cursor (source : Store) :=
  Mettapedia.Logic.DerivationGraph.BorrowedCursor.CheckedCursor interface source

def begin (source : Store) : Cursor source :=
  Mettapedia.Logic.DerivationGraph.BorrowedCursor.CheckedCursor.begin interface source

/-- Generic checked evidence retains exactly the independently specified rho
relation. Formation is deliberately a separate root obligation. -/
theorem checked_judgment_meaning
    (evidence : Mettapedia.Logic.DerivationGraph.CheckedJudgment NativeEvidence.presentation.rules) :
    NativeEvidence.Meaning evidence.judgment := by
  obtain ⟨tree⟩ := (Presentation.nonempty_derivation_iff_derives
    NativeEvidence.presentation evidence.judgment).mpr evidence.valid
  exact NativeEvidence.derivation_sound tree

/-- The context and role cannot be relabelled without another admission check.
Private Lean construction establishes the invariant, not native unforgeability. -/
structure CheckedClaim (context : Context) (sort : SourceSort) where
  private mk ::
  judgment : Judgment
  admitted : Admission context sort judgment
  valid : NativeEvidence.Meaning judgment

def admitRoot {source : Store} (cursor : Cursor source)
    (context : Context) (sort : SourceSort) (address : Nat) : Option (CheckedClaim context sort) := do
  let evidence ← cursor.root address
  if accepted : checkAdmission context sort evidence.judgment = true then
    some ⟨evidence.judgment, (NativeKernel.checkAdmission_exact context sort _).mp accepted,
      checked_judgment_meaning evidence⟩
  else none

/-- Root inspection is literal: neither variable freshening nor sort coercion
is performed. Even an already valid proof is subjected to source admission. -/
theorem admitRoot_judgment {source : Store} (cursor : Cursor source)
    (context : Context) (sort : SourceSort) (address : Nat) :
    (admitRoot cursor context sort address).map CheckedClaim.judgment =
      (Mettapedia.Logic.DerivationGraph.BorrowedCursor.rootAt cursor.state address).bind
        (fun judgment => if checkAdmission context sort judgment then some judgment else none) := by
  have root := Mettapedia.Logic.DerivationGraph.BorrowedCursor.CheckedCursor.root_judgment cursor address
  cases projected : cursor.root address with
  | none =>
      simp only [projected, Option.map_none] at root
      simp [admitRoot, projected, ← root]
      rfl
  | some evidence =>
      simp only [projected, Option.map_some] at root
      by_cases admitted : checkAdmission context sort evidence.judgment = true
      · simp [admitRoot, projected, ← root, admitted]
        rfl
      · simp [admitRoot, projected, ← root, admitted]
        rfl

/-- Exact requested-root admission: source proof validity alone cannot turn a
process proof into a name proof or bypass the caller's binding context. -/
theorem admitRoot_exact {source : Store} (cursor : Cursor source)
    (context : Context) (sort : SourceSort) (address : Nat) (goal : Judgment) :
    (admitRoot cursor context sort address).map CheckedClaim.judgment = some goal ↔
      Mettapedia.Logic.DerivationGraph.BorrowedCursor.rootAt cursor.state address = some goal ∧
        Admission context sort goal := by
  rw [admitRoot_judgment]
  cases found : Mettapedia.Logic.DerivationGraph.BorrowedCursor.rootAt cursor.state address with
  | none => simp
  | some actual =>
      by_cases admitted : checkAdmission context sort actual = true
      · simp only [Option.bind_some, if_pos admitted]
        constructor
        · intro equal
          have same := Option.some.inj equal
          subst goal
          exact ⟨rfl, (NativeKernel.checkAdmission_exact context sort actual).mp admitted⟩
        · exact And.left
      · simp only [Option.bind_some, if_neg admitted]
        constructor
        · intro impossible
          cases impossible
        · rintro ⟨equal, formed⟩
          have same := Option.some.inj equal
          subst goal
          exact (admitted ((NativeKernel.checkAdmission_exact context sort actual).mpr formed)).elim

theorem admitRoot_sound {source : Store} (cursor : Cursor source)
    (context : Context) (sort : SourceSort) (address : Nat)
    (goal : Judgment) (accepted : (admitRoot cursor context sort address).map CheckedClaim.judgment = some goal) :
    NativeKernel.Meaning ⟨context, sort, goal⟩ := by
  obtain ⟨evidence, _found, same⟩ := Option.map_eq_some_iff.mp accepted
  subst goal
  exact ⟨evidence.admitted, evidence.valid⟩

/-- Rho source meaning, original finite derivations and the common graph
machine agree at the declared context-and-sort boundary. -/
theorem meaning_iff_graph (context : Context) (sort : SourceSort) (goal : Judgment) :
    NativeKernel.Meaning ⟨context, sort, goal⟩ ↔
      Admission context sort goal ∧
        ∃ (nodes : List (Mettapedia.Logic.DerivationGraph.Node Judgment
          NativeEvidence.presentation.Rule Nat)) (cache : Array Judgment) (root : Nat),
          Mettapedia.Logic.DerivationGraph.replay interface nodes = some cache ∧
            cache[root]? = some goal := by
  change (Admission context sort goal ∧ NativeEvidence.Meaning goal) ↔ _
  rw [NativeEvidence.meaning_iff_derivation]
  rw [PresentationGraph.nonempty_derivation_iff_graph
    (P := NativeEvidence.presentation) (0 : Nat) goal]
  rfl

namespace Controls

abbrev zero : Pattern := .apply "PZero" []
abbrev channel : Pattern := .apply "NQuote" [zero]
abbrev emptyContext : Context := ⟨[], []⟩

def commRule : Rule := .comm channel zero zero []
def commClaim : Judgment := NativeEvidence.conclusion commRule

def commStore : Store :=
  ⟨3, fun address => if address = 40 then some ⟨commClaim, commRule, [], 40⟩ else none⟩

def freeCommRule : Rule := .comm (.fvar "n") zero zero []
def freeCommClaim : Judgment := NativeEvidence.conclusion freeCommRule

def freeCommStore : Store :=
  ⟨3, fun address => if address = 40 then some ⟨freeCommClaim, freeCommRule, [], 40⟩ else none⟩

def repeatedStore : Store :=
  ⟨4, fun address => match address with
    | 9 => some ⟨.structural zero zero, .structuralRefl zero, [], 9⟩
    | 20 => some ⟨.structural zero zero, .structuralTrans zero zero zero, [9, 9], 20⟩
    | _ => none⟩

private def checkedRoot (source : Store) (schedule : List Nat) (context : Context)
    (sort : SourceSort) (address : Nat) : Option Judgment := do
  let cursor ← (begin source).advance schedule
  (admitRoot cursor context sort address).map CheckedClaim.judgment

theorem communication_accepts :
    checkedRoot commStore [40] emptyContext .proc 40 = some commClaim := by decide +kernel

theorem process_as_name_refused :
    checkedRoot commStore [40] emptyContext .name 40 = none := by decide +kernel

theorem declared_channel_accepts :
    checkedRoot freeCommStore [40] ⟨[("n", .name)], []⟩ .proc 40 = some freeCommClaim := by decide +kernel

theorem missing_channel_context_refused :
    checkedRoot freeCommStore [40] emptyContext .proc 40 = none := by decide +kernel

theorem wrong_channel_sort_refused :
    checkedRoot freeCommStore [40] ⟨[("n", .proc)], []⟩ .proc 40 = none := by decide +kernel

theorem repeated_premises_accept :
    checkedRoot repeatedStore [9, 20] emptyContext .proc 20 = some (.structural zero zero) := by decide +kernel

theorem repeated_before_parent_refused :
    checkedRoot repeatedStore [20, 9] emptyContext .proc 20 = none := by decide +kernel

theorem malformed_binder_refused :
    checkedRoot
      ⟨5, fun _ => some ⟨.structural (.bvar 0) (.bvar 0), .structuralRefl (.bvar 0), [], 0⟩⟩
      [0] emptyContext .proc 0 = none := by decide +kernel

theorem wrong_comm_conclusion_refused :
    checkedRoot ⟨3, fun _ => some ⟨.step zero zero, commRule, [], 40⟩⟩
      [40] emptyContext .proc 40 = none := by decide +kernel

end Controls

#print axioms checked_judgment_meaning
#print axioms admitRoot_judgment
#print axioms admitRoot_exact
#print axioms admitRoot_sound
#print axioms meaning_iff_graph

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.BorrowedProofCursor
