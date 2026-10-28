import Mettapedia.Languages.Datalog.Syntax
import Mettapedia.Logic.LP.FunctionFree
import Mathlib.Data.List.OfFn

/-! Function-free Datalog syntax enters the existing LP kernel. Comparisons
use distinct relation symbols; their interpretation is supplied separately.
Anonymous arguments receive separate clause-local positional variables. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Datalog.LPBridge

open Mettapedia.Logic

inductive Variable where
  | named (name : String)
  | anonymous (site position : Nat)
  deriving Repr, DecidableEq, BEq

inductive RelationSymbol where
  | user (name : QualifiedName) (arity : Nat)
  | comparison (operator : ComparisonOperator)
  deriving Repr, DecidableEq, BEq

def RelationSymbol.arity : RelationSymbol → Nat
  | .user _ arity => arity
  | .comparison _ => 2

def signature : LP.LPSignature where
  constants := Value
  vars := Variable
  relationSymbols := RelationSymbol
  relationArity := RelationSymbol.arity
  functionSymbols := Empty
  functionArity := Empty.elim

instance : IsEmpty signature.functionSymbols := inferInstanceAs (IsEmpty Empty)

def encodeArgument (site position : Nat) : Argument → LP.Term signature
  | .literal value => .const value
  | .var name => .var (.named name)
  | .anonymous => .var (.anonymous site position)

def encodeAtom (site : Nat) (atom : Atom) : LP.Atom signature where
  symbol := .user atom.relation atom.arguments.length
  args := fun index => encodeArgument site index.val atom.arguments[index.val]

def encodeComparison (site : Nat) (comparison : Comparison) : LP.Atom signature where
  symbol := .comparison comparison.operator
  args := fun index => if index.val = 0 then encodeArgument site 0 comparison.left
    else encodeArgument site 1 comparison.right

def encodePremise (site : Nat) : Premise → LP.Atom signature
  | .atom atom => encodeAtom site atom
  | .comparison comparison => encodeComparison site comparison

def encodeClause (clause : Clause) : LP.Clause signature where
  head := encodeAtom 0 clause.head
  body := clause.body.mapIdx fun index premise => encodePremise (index + 1) premise

def encodeFact (fact : GroundFact) : LP.GroundAtom signature where
  symbol := .user fact.relation fact.values.length
  args := fun index => .const fact.values[index.val]

def decodeFact (fact : LP.GroundAtom signature) : Option GroundFact :=
  match fact with
  | ⟨.user name arity, arguments⟩ =>
      some ⟨name,List.ofFn fun index : Fin arity => (arguments index).toConst⟩
  | ⟨.comparison _, _⟩ => none

@[simp] theorem decode_encode_fact (fact : GroundFact) :
    decodeFact (encodeFact fact) = some fact := by
  cases fact with
  | mk relation values =>
      simp only [decodeFact,encodeFact,LP.GroundTerm.toConst]
      congr 2
      exact List.ofFn_getElem

theorem encode_fact_injective : Function.Injective encodeFact := by
  intro first second same
  have decoded := congrArg decodeFact same
  simpa only [decode_encode_fact,Option.some.injEq] using decoded

def groundClause (fact : GroundFact) : Clause :=
  ⟨⟨fact.relation,fact.values.map Argument.literal⟩,[]⟩

def numberedClauses (program : Program) : List (Nat × Clause) :=
  program.statements.zipIdx.filterMap fun (statement,index) => match statement with
    | .rule clause => some (index,clause)
    | .fact fact => some (index,groundClause fact)
    | _ => none

def encodeProgram (program : Program) : LP.Program signature :=
  (numberedClauses program).map fun entry => encodeClause entry.2

theorem anonymous_positions_are_distinct (site first second : Nat) (different : first ≠ second) :
    encodeArgument site first .anonymous ≠ encodeArgument site second .anonymous := by
  intro same
  have positions : first = second := by cases same; rfl
  exact different positions

theorem anonymous_is_not_a_named_variable (site position : Nat) (name : String) :
    encodeArgument site position .anonymous ≠ encodeArgument site position (.var name) := by
  intro same
  cases same

theorem function_free : signature.isFunctionFree := by
  change IsEmpty signature.functionSymbols
  infer_instance

theorem guard_is_not_a_user_relation (operator : ComparisonOperator) (name : QualifiedName) (arity : Nat) :
    RelationSymbol.comparison operator ≠ .user name arity := by
  intro same
  cases same

#print axioms decode_encode_fact
#print axioms encode_fact_injective
#print axioms anonymous_positions_are_distinct
#print axioms anonymous_is_not_a_named_variable
#print axioms function_free
#print axioms guard_is_not_a_user_relation

end Mettapedia.Languages.Datalog.LPBridge
