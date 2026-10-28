import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRLookup
import Mettapedia.Languages.Datalog.RangeRestriction
import Mettapedia.Languages.Datalog.IRCodec

/-! Clause compilation for the independent IR. Relation names and literal
values are bound by the request's explicit pools, before body matching.
Clause variables share one environment across all positive body premises.
Scalar comparisons are retained as declared provider queries. This file
defines compilation, not a fixed-point completion certificate. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat

namespace DatalogJoinAuthoring
open DatalogAuthoring DatalogLookupAuthoring
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
#module_file "../../../../../../metta/gslt/module/DatalogIRJoin.module"
#module_roundtrip DatalogIRJoin
end DatalogJoinAuthoring

namespace DatalogIR.Join

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.Datalog
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.ComputedViews

private instance : DecidableEq LanguageDef := fun first second => by
  cases first
  cases second
  exact decidable_of_iff' _ (Iff.of_eq (LanguageDef.mk.injEq _ _ _ _ _ _ _ _ _ _))

def baseLanguage? : Option LanguageDef := DatalogJoinAuthoring.DatalogIRJoin.language.toOption
def baseLanguage : LanguageDef := module_language_view% baseLanguage?
theorem baseLanguage_exact : baseLanguage? = some baseLanguage := by decide +kernel

structure Pools where
  relations : List QualifiedName
  literals : List Value
  deriving Repr, DecidableEq

def relationSlot (index : Nat) : String := "pool:relation:" ++ toString index
def literalSlot (index : Nat) : String := "pool:literal:" ++ toString index
def logicalVariable (name : String) : String := "variable:" ++ name
def anonymousVariable (bodyPosition argumentPosition : Nat) : String :=
  "anonymous:" ++ toString bodyPosition ++ ":" ++ toString argumentPosition

def vector (items : List Pattern) : Pattern := .collection .vec items none
def poolPattern (names : List String) : Pattern := vector (names.map .fvar)
def relationSlots (pools : Pools) : List String := (List.range pools.relations.length).map relationSlot
def literalSlots (pools : Pools) : List String := (List.range pools.literals.length).map literalSlot
def call (relations literals facts : List Pattern) : Pattern := .apply "Infer"
  [vector relations,vector literals,vector facts]

def relation? (pools : Pools) (name : QualifiedName) : Option Pattern :=
  (pools.relations.idxOf? name).map fun index => .fvar (relationSlot index)

def literal? (pools : Pools) (value : Value) : Option Pattern :=
  (pools.literals.idxOf? value).map fun index => .fvar (literalSlot index)

def argument? (pools : Pools) (bodyPosition argumentPosition : Nat) : Argument → Option Pattern
  | .literal value => literal? pools value
  | .var name => some (.fvar (logicalVariable name))
  | .anonymous => some (.fvar (anonymousVariable bodyPosition argumentPosition))

def atom? (pools : Pools) (bodyPosition : Nat) (atom : Mettapedia.Languages.Datalog.Atom) : Option Pattern := do
  let name ← relation? pools atom.relation
  let arguments ← atom.arguments.zipIdx.mapM fun (argument,index) => argument? pools bodyPosition index argument
  pure (.apply "GroundFact" [name,.apply "GroundTuple" [vector arguments]])

def comparisonName : ComparisonOperator → String
  | .equal => "dl-compare:equal"
  | .different => "dl-compare:different"
  | .less => "dl-compare:less"
  | .lessEqual => "dl-compare:less-equal"
  | .greater => "dl-compare:greater"
  | .greaterEqual => "dl-compare:greater-equal"

def bodyPremise? (pools : Pools) (position : Nat) : Mettapedia.Languages.Datalog.Premise → Option Syntax.Premise
  | .atom atom => do
      let target ← atom? pools position atom
      pure (.congruence (.apply "LookupFact" [.fvar "facts"]) target)
  | .comparison comparison => do
      let left ← argument? pools position 0 comparison.left
      let right ← argument? pools position 1 comparison.right
      pure (.relationQuery (comparisonName comparison.operator) [left,right])

def orderedBody (clause : Clause) : List Mettapedia.Languages.Datalog.Premise :=
  clause.body.filter (fun premise => match premise with | .atom _ => true | _ => false) ++
  clause.body.filter (fun premise => match premise with | .comparison _ => true | _ => false)

def variableContext (pools : Pools) (clause : Clause) : List (String × TypeExpr) :=
  [("facts",.collection .vec (.base "DlStatement"))] ++
  (relationSlots pools).map (fun name => (name,.base "DlRelation")) ++
  (literalSlots pools).map (fun name => (name,.base "DlValue")) ++
  (clause.providedVariables.map logicalVariable).dedup.map (fun name => (name,.base "DlValue")) ++
  (orderedBody clause).zipIdx.flatMap fun (premise,position) => match premise with
    | .comparison _ => []
    | .atom atom => atom.arguments.zipIdx.filterMap fun (argument,index) =>
        if argument.isAnonymous then some (anonymousVariable position index,.base "DlValue") else none

/-- Failure is explicit: range-unsafe clauses or absent pool entries never
acquire a partial interpretation. Statement positions remain rule identities. -/
def compileClause? (pools : Pools) (statementIndex : Nat) (clause : Clause) : Option RewriteRule := do
  if !clause.checkRangeRestriction then none else
    let right ← atom? pools clause.body.length clause.head
    let premises ← (orderedBody clause).zipIdx.mapM fun (premise,index) => bodyPremise? pools index premise
    pure {
      name := "datalog-clause:" ++ toString statementIndex
      typeContext := variableContext pools clause
      premises
      left := .apply "Infer" [poolPattern (relationSlots pools),poolPattern (literalSlots pools),.fvar "facts"]
      right }

def language (rules : List RewriteRule) : LanguageDef :=
  {baseLanguage with name := "DatalogIRJoin",rewrites := baseLanguage.rewrites ++ rules}

theorem unsafe_clause_refused (pools : Pools) (statementIndex : Nat) (clause : Clause)
    (rejected : clause.checkRangeRestriction = false) : compileClause? pools statementIndex clause = none := by
  simp [compileClause?,rejected]

theorem lookup_rules_retained (rules : List RewriteRule) :
    (language rules).rewrites.take baseLanguage.rewrites.length = baseLanguage.rewrites := by
  simp [language]

#guard baseLanguage.rewrites.length == 2
#guard baseLanguage.validate.isEmpty

#print axioms baseLanguage_exact
#print axioms unsafe_clause_refused

end DatalogIR.Join
end Mettapedia.GSLT.LanguageDef.ModuleFormat
