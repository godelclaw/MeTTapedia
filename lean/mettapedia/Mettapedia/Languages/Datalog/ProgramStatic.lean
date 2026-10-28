import Mettapedia.Languages.Datalog.TypeInference

/-! Static checking for structured source programs. This checks relation
declarations, finite primitive values, clause typing and declared interfaces.
Lexical recognition and packed-forest selection remain separate boundaries. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Datalog.ProgramStatic

open StaticTyping

def declarations (program : Program) : List RelationDeclaration :=
  program.statements.filterMap fun statement => match statement with
    | .declaration declaration => some declaration
    | _ => none

def signature (program : Program) : Signature :=
  fun name => ((declarations program).map fun declaration =>
    (declaration.name, declaration.attributes.map (·.type))).lookup name

def DeclarationValid (declaration : RelationDeclaration) : Prop :=
  declaration.name ≠ [] ∧ (∀ part ∈ declaration.name, part ≠ "") ∧
    (declaration.attributes.map (·.name)).Nodup ∧
    ∀ entry ∈ declaration.attributes, entry.name ≠ ""

def checkDeclaration (declaration : RelationDeclaration) : Bool :=
  decide (declaration.name ≠ []) && declaration.name.all (fun part => decide (part ≠ "")) &&
    decide (declaration.attributes.map (·.name)).Nodup &&
    declaration.attributes.all (fun entry => decide (entry.name ≠ ""))

theorem checkDeclaration_iff (declaration : RelationDeclaration) :
    checkDeclaration declaration = true ↔ DeclarationValid declaration := by
  simp [checkDeclaration, DeclarationValid, List.all_eq_true, and_assoc]

def Declared (signature : Signature) (name : QualifiedName) : Prop :=
  ∃ types, signature name = some types

def StatementTyped (signature : Signature) : Statement → Prop
  | .declaration declaration => DeclarationValid declaration
  | .fact fact => FactTyped signature fact
  | .rule clause => ∃ context, ClauseTyped signature context clause
  | .input name | .output name => Declared signature name

def checkStatement (signature : Signature) : Statement → Bool
  | .declaration declaration => checkDeclaration declaration
  | .fact fact => checkFact signature fact
  | .rule clause => inferClause signature clause
  | .input name | .output name => (signature name).isSome

theorem checkStatement_iff (signature : Signature) (statement : Statement) :
    checkStatement signature statement = true ↔ StatementTyped signature statement := by
  cases statement <;>
    simp [checkStatement, StatementTyped, checkDeclaration_iff, checkFact_iff,
      inferClause_iff, Declared, Option.isSome_iff_exists]

def ProgramTyped (program : Program) : Prop :=
  ((declarations program).map (·.name)).Nodup ∧
    ∀ statement ∈ program.statements, StatementTyped (signature program) statement

def checkProgram (program : Program) : Bool :=
  decide ((declarations program).map (·.name)).Nodup &&
    program.statements.all (checkStatement (signature program))

theorem checkProgram_iff (program : Program) :
    checkProgram program = true ↔ ProgramTyped program := by
  simp [checkProgram, ProgramTyped, List.all_eq_true, checkStatement_iff]

inductive Issue where
  | duplicateRelations
  | invalidDeclaration (statementIndex : Nat)
  | illTypedFact (statementIndex : Nat)
  | illTypedClause (statementIndex : Nat)
  | undeclaredInterface (statementIndex : Nat)
  deriving Repr, DecidableEq

def statementIssue? (signature : Signature) (statementIndex : Nat) (statement : Statement) : Option Issue :=
  if checkStatement signature statement then none else some (match statement with
    | .declaration _ => .invalidDeclaration statementIndex
    | .fact _ => .illTypedFact statementIndex
    | .rule _ => .illTypedClause statementIndex
    | .input _ | .output _ => .undeclaredInterface statementIndex)

theorem statementIssue?_none_iff (signature : Signature) (statementIndex : Nat) (statement : Statement) :
    statementIssue? signature statementIndex statement = none ↔
      checkStatement signature statement = true := by
  cases checked : checkStatement signature statement <;> simp [statementIssue?, checked]

/-- Diagnostics keep original statement positions; declaration extraction
does not renumber rules or silently resolve duplicate declarations. -/
def diagnose (program : Program) : List Issue :=
  (if ((declarations program).map (·.name)).Nodup then [] else [.duplicateRelations]) ++
    program.statements.zipIdx.filterMap fun (statement, index) =>
      statementIssue? (signature program) index statement

theorem diagnose_empty_iff (program : Program) :
    diagnose program = [] ↔ ProgramTyped program := by
  have declarationsClear :
      (if ((declarations program).map (·.name)).Nodup then [] else [Issue.duplicateRelations]) = [] ↔
        ((declarations program).map (·.name)).Nodup := by
    split <;> simp_all
  have statementsClear :
      (program.statements.zipIdx.filterMap fun (statement, index) =>
        statementIssue? (signature program) index statement) = [] ↔
      ∀ statement ∈ program.statements, StatementTyped (signature program) statement := by
    rw [List.filterMap_eq_nil_iff]
    constructor
    · intro clear statement inside
      have indexed : statement ∈ program.statements.zipIdx.map Prod.fst := by
        simpa only [List.zipIdx_map_fst] using inside
      obtain ⟨⟨actual, index⟩, present, same⟩ := List.mem_map.mp indexed
      change actual = statement at same
      subst actual
      exact (checkStatement_iff _ _).mp ((statementIssue?_none_iff _ _ _).mp
        (clear (statement, index) present))
    · intro typed pair present
      have inside : pair.1 ∈ program.statements := by
        have mapped : pair.1 ∈ program.statements.zipIdx.map Prod.fst :=
          List.mem_map.mpr ⟨pair, present, rfl⟩
        simpa only [List.zipIdx_map_fst] using mapped
      exact (statementIssue?_none_iff _ _ _).mpr ((checkStatement_iff _ _).mpr (typed pair.1 inside))
  exact (List.append_eq_nil_iff.trans (and_congr declarationsClear statementsClear))

def checkedProgram? (program : Program) : Option {source : Program // ProgramTyped source} :=
  if checked : checkProgram program = true then some ⟨program, (checkProgram_iff program).mp checked⟩
  else none

theorem checkedProgram?_isSome_iff (program : Program) :
    (checkedProgram? program).isSome = true ↔ ProgramTyped program := by
  by_cases checked : checkProgram program = true
  · simp [checkedProgram?, checked, (checkProgram_iff program).mp checked]
  · simp [checkedProgram?, checked, ← checkProgram_iff program]

#print axioms checkProgram_iff
#print axioms diagnose_empty_iff
#print axioms checkedProgram?_isSome_iff

end Mettapedia.Languages.Datalog.ProgramStatic
