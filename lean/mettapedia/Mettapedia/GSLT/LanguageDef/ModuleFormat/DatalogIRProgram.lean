import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRJoin
import Mettapedia.Languages.Datalog.LPBridge
import Mettapedia.Languages.Datalog.ProgramStaticControls

/-! Program preparation for the independent IR compiler. The input vocabulary
contains source literals and the current fact snapshot. Every source fact and
clause compiles at its original statement position; declarations and directives
neither become rewrite rules nor renumber later statements. Preparation does
not compute joins, ground instances or a fixed point. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Join.Program

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL.Syntax

def argumentValues : Argument → List Value
  | .literal value => [value]
  | _ => []
def premiseValues : Mettapedia.Languages.Datalog.Premise → List Value
  | .atom atom => atom.arguments.flatMap argumentValues
  | .comparison comparison => [comparison.left,comparison.right].flatMap argumentValues
def statementValues : Statement → List Value
  | .fact fact => fact.values
  | .rule clause => clause.head.arguments.flatMap argumentValues ++ clause.body.flatMap premiseValues
  | _ => []
def statementRelations : Statement → List QualifiedName
  | .declaration declaration => [declaration.name]
  | .fact fact => [fact.relation]
  | .input name | .output name => [name]
  | .rule clause => clause.head.relation :: clause.positiveAtoms.map (·.relation)

def pools (program : Mettapedia.Languages.Datalog.Program) (known : List GroundFact) : Pools :=
  ⟨(program.statements.flatMap statementRelations ++ known.map (·.relation)).dedup,
   (program.statements.flatMap statementValues ++ known.flatMap (·.values)).dedup⟩

def compileClauses? (pools : Pools) : List (Nat × Clause) → Option (List RewriteRule)
  | [] => some []
  | (index,clause) :: rest => do
      let rule ← compileClause? pools index clause
      let remaining ← compileClauses? pools rest
      pure (rule :: remaining)

theorem compileClauses?_rows (pools : Pools) (clauses : List (Nat × Clause)) (rules : List RewriteRule)
    (compiled : compileClauses? pools clauses = some rules) :
    List.Forall₂ (fun entry rule => compileClause? pools entry.1 entry.2 = some rule) clauses rules := by
  induction clauses generalizing rules with
  | nil =>
    have same : rules = [] := by simpa [compileClauses?] using compiled.symm
    subst rules
    exact .nil
  | cons entry rest ih =>
    rcases entry with ⟨index,clause⟩
    cases first : compileClause? pools index clause with
    | none => simp [compileClauses?,first] at compiled
    | some rule =>
      cases remaining : compileClauses? pools rest with
      | none => simp [compileClauses?,first,remaining] at compiled
      | some tail =>
        have same : rule :: tail = rules := by simpa [compileClauses?,first,remaining] using compiled
        subst rules
        exact .cons first (ih tail remaining)

structure Prepared where
  vocabulary : Pools
  rules : List RewriteRule

def prepare? (program : Mettapedia.Languages.Datalog.Program) (known : List GroundFact) : Option Prepared := do
  if !ProgramStatic.checkProgram program then none else
    if !known.all (StaticTyping.checkFact (ProgramStatic.signature program)) then none else
      let vocabulary := pools program known
      let rules ← compileClauses? vocabulary (LPBridge.numberedClauses program)
      pure ⟨vocabulary,rules⟩

theorem prepare?_sound (program : Mettapedia.Languages.Datalog.Program) (known : List GroundFact)
    (prepared : Prepared) (success : prepare? program known = some prepared) :
    ProgramStatic.ProgramTyped program ∧
      known.all (StaticTyping.checkFact (ProgramStatic.signature program)) = true ∧
      prepared.vocabulary = pools program known ∧
      List.Forall₂ (fun entry rule => compileClause? prepared.vocabulary entry.1 entry.2 = some rule)
        (LPBridge.numberedClauses program) prepared.rules := by
  unfold prepare? at success
  split at success
  · cases success
  · rename_i static
    have typed : ProgramStatic.checkProgram program = true := by simpa using static
    split at success
    · cases success
    · rename_i facts
      have checked : known.all (StaticTyping.checkFact (ProgramStatic.signature program)) = true := by simpa using facts
      cases compiled : compileClauses? (pools program known) (LPBridge.numberedClauses program) with
      | none => simp [compiled] at success
      | some rules =>
        have same : Prepared.mk (pools program known) rules = prepared := by simpa [compiled] using success
        cases same
        exact ⟨(ProgramStatic.checkProgram_iff program).mp typed,checked,rfl,
          compileClauses?_rows _ _ _ compiled⟩

theorem prepared_rule_count (program : Mettapedia.Languages.Datalog.Program) (known : List GroundFact)
    (prepared : Prepared) (success : prepare? program known = some prepared) :
    prepared.rules.length = (LPBridge.numberedClauses program).length :=
  (prepare?_sound program known prepared success).2.2.2.length_eq.symm

#guard (prepare? ProgramStatic.Controls.cyclicGraph []).isSome
#guard (prepare? ProgramStatic.Controls.pointsTo []).isSome
#guard (prepare? ProgramStatic.Controls.cyclicGraph
  [⟨["Edge"],[.symbol "a",.symbol "b"]⟩]).isSome
#guard (prepare? ProgramStatic.Controls.cyclicGraph
  [⟨["Edge"],[.number 1,.symbol "b"]⟩]).isNone
#guard (prepare? ProgramStatic.Controls.cyclicGraph
  [⟨["Unknown"],[.symbol "a",.symbol "b"]⟩]).isNone

#print axioms compileClauses?_rows
#print axioms prepare?_sound
#print axioms prepared_rule_count

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Join.Program
