import Mettapedia.Logic.LP.RuntimeQuery

/-!
# Demand-driven query regressions

These fixtures discriminate source-order DFS from reordered search and verify
that a cut in one predicate frame removes both a nested call's alternatives and
later clauses of that predicate.  Both runs also close back to the query-entry
heap and trail.
-/

namespace Mettapedia.Logic.LP.RuntimeQueryRegression

open RuntimeTerm RuntimeQuery

inductive QConst where
  | a | b | c
deriving BEq, DecidableEq, Repr

inductive QVar where
  | x
deriving DecidableEq, Repr

inductive QRel where
  | p | choose | cut
deriving DecidableEq, Repr

inductive QFun
deriving DecidableEq, Repr

def qSig : LPSignature where
  constants := QConst
  vars := QVar
  relationSymbols := QRel
  relationArity
    | .p => 1
    | .choose => 1
    | .cut => 0
  functionSymbols := QFun
  functionArity := fun symbol => nomatch symbol

instance : DecidableEq qSig.vars := inferInstanceAs (DecidableEq QVar)
instance : DecidableEq qSig.constants := inferInstanceAs (DecidableEq QConst)
instance : DecidableEq qSig.functionSymbols := inferInstanceAs (DecidableEq QFun)
instance : DecidableEq qSig.relationSymbols := inferInstanceAs (DecidableEq QRel)
instance : DecidableEq qSig.scoped.vars :=
  inferInstanceAs (DecidableEq (ScopedVar QVar))
instance : DecidableEq qSig.scoped.constants := inferInstanceAs (DecidableEq QConst)
instance : DecidableEq qSig.scoped.functionSymbols := inferInstanceAs (DecidableEq QFun)
instance : DecidableEq qSig.scoped.relationSymbols := inferInstanceAs (DecidableEq QRel)

def unary (symbol : QRel) (term : Term qSig) : Atom qSig where
  symbol := symbol
  args := fun _ => term

def cutAtom : Atom qSig where
  symbol := .cut
  args := fun index => nomatch index

def fact (symbol : QRel) (term : Term qSig) : Clause qSig where
  head := unary symbol term
  body := []

def program : Program qSig := [
  fact .p (.const .a),
  fact .p (.const .b),
  {
    head := unary .choose (.var .x)
    body := [unary .p (.var .x), cutAtom]
  },
  fact .choose (.const .c)
]

def builtins : Builtins qSig where
  isCut
    | .cut => true
    | _ => false
  cut_arity_zero := by
    intro symbol h
    cases symbol <;> simp_all [qSig]

def queryP : List (Atom qSig) := [unary .p (.var .x)]
def queryChoose : List (Atom qSig) := [unary .choose (.var .x)]

/-- Read the one source query variable through the live rational-term heap. -/
def answerConstant? (answer : Answer qSig) : Option QConst :=
  match answer.queryVarMap with
  | [(_, address)] =>
      match answer.memory.heap.deref address with
      | .ok (.root root) =>
          match answer.memory.heap[root]? with
          | some (.const symbol) => some symbol
          | _ => none
      | _ => none
  | _ => none

/-- Pull a bounded number of answers.  Each individual pull has a separate
step budget; an open boundary is reported as test failure, never completion. -/
def collect (answerBudget : Nat) (state : State qSig) :
    Option (List QConst × Nat × Nat) :=
  match answerBudget with
  | 0 => none
  | answerBudget + 1 =>
      match pull builtins program 64 state with
      | .open _ => none
      | .terminal (.runtimeError _ _) => none
      | .terminal (.completed memory) =>
          some ([], memory.heap.size, memory.trail.size)
      | .answer answer next =>
          match answerConstant? answer, collect answerBudget next with
          | some symbol, some (symbols, heapSize, trailSize) =>
              some (symbol :: symbols, heapSize, trailSize)
          | _, _ => none

def run (goals : List (Atom qSig)) : Option (List QConst × Nat × Nat) :=
  match openQuery (Memory.empty qSig.scoped) 0 1 goals with
  | .error _ => none
  | .ok state => collect 4 state

/-! The following are executable anti-regression gates rather than theorem
claims about an external implementation.  The reusable control facts they
exercise are `step_cut_of_dispatch`, `step_cut_choice_count`, and
`step_empty_backtrack_completes` in the runtime module. -/

-- Clause order and multiplicity are observable: both facts survive in their
-- source order, and closing the exhausted query restores its entry state.
#guard run queryP == some ([.a, .b], 0, 0)

-- `choose(X) :- p(X), !.` commits after `p(a)`: it removes the retained
-- `p(b)` choice and the later `choose(c)` clause in the same frame.
#guard run queryChoose == some ([.a], 0, 0)

end Mettapedia.Logic.LP.RuntimeQueryRegression
