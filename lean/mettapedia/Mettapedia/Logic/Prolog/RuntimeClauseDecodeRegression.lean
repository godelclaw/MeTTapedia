import Mettapedia.Logic.Prolog.RuntimeClauseDecode

/-!
# Dynamic clause-decoder canaries

The fixtures begin with canonical source terms, standardize and materialize
them in the real LP heap, and decode the resulting root.  They discriminate
head/body sharing, separation of same-spelled identities from different
runtime activations, source control reuse, and rejection of non-clause forms.
-/

namespace Mettapedia.Logic.Prolog.RuntimeClauseDecodeRegression

open Mettapedia.Logic
open LP.RuntimeTerm LP.RuntimeMaterialize
open SourceSignature RuntimeClauseDecode

def x : SourceSignature.Term := var "X" 0
def y : SourceSignature.Term := var "X" 1

def ruleTerm : SourceSignature.Term :=
  compound ":-" [
    compound "p" [x, x],
    compound "," [compound "q" [x], compound "r" [x]]
  ]

def distinctTerm : SourceSignature.Term :=
  compound "p" [x, y]

def decodeMaterialized (term : SourceSignature.Term) :
    Except RuntimeClauseDecode.Error SourceSignature.Clause := do
  let materialized ←
    match materializeTerm (Memory.empty RuntimeClauseDecode.Sigma.scoped)
        (term.atScope 7) with
    | .error _ => .error (.readback .notFinite)
    | .ok result => .ok result
  RuntimeClauseDecode.decodeClause materialized.memory.heap materialized.root

def sharedVariablePreserved : Bool :=
  match decodeMaterialized ruleTerm with
  | .ok clause =>
      match List.ofFn clause.head.args, clause.body with
      | [.var first, .var second],
          .conj (.call left) (.call right) =>
          match List.ofFn left.args, List.ofFn right.args with
          | [.var leftIdentity], [.var rightIdentity] =>
              first == second && first == leftIdentity &&
                first == rightIdentity
          | _, _ => false
      | _, _ => false
  | .error _ => false

def sameSpellingDifferentIdentitySeparated : Bool :=
  match decodeMaterialized distinctTerm with
  | .ok clause =>
      match List.ofFn clause.head.args with
      | [.var first, .var second] =>
          first.spelling == second.spelling && first != second &&
          first.occurrence < 2 && second.occurrence < 2
      | _ => false
  | .error _ => false

def directiveRejected : Bool :=
  match decodeMaterialized (compound ":-" [compound "dynamic" [atom "p"]]) with
  | .error .notClause => true
  | _ => false

def cyclicHeap : Heap RuntimeClauseDecode.Sigma.scoped :=
  #[.app { name := "loop", arity := 1 } #[0]]

def cyclicClauseRejectedWithoutTruncation : Bool :=
  match RuntimeClauseDecode.decodeClause cyclicHeap 0 with
  | .error (.readback .notFinite) => true
  | _ => false

#guard sharedVariablePreserved
#guard sameSpellingDifferentIdentitySeparated
#guard directiveRejected
#guard cyclicClauseRejectedWithoutTruncation

end Mettapedia.Logic.Prolog.RuntimeClauseDecodeRegression
