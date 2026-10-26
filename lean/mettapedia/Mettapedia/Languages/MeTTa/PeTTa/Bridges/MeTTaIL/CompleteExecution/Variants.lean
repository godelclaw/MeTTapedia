import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Positions

/-!
# Orders and variants in the complete machine

`gslt:complete:perms` lists every order of a list as `Complete.Inversion.perms` does, by
inserting each head at every position of every order of its tail. `gslt:complete:variants` lists
the display-erased terms an instance of an equation side can stand for, as
`Complete.Inversion.variants`: the instance, with the elements of each bag pattern in any order.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.GSLT.LanguageDef CettaWire InferenceCettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.MeTTaIL.Complete.Inversion (insertions perms variants variantsList)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Effects (State)
open Eval
open BridgeKit WireKit

/-- Lists of patterns, as the MeTTa holds them. -/
abbrev rowsValue (rows : List (List Pattern)) : Atom := encoded (CettaWire.encodeList encodePatterns rows)

theorem complete_append_rows (state : State) (left right : List (List Pattern)) :
    PureReturns runtime [] state (apply "gslt:automata:append" [rowsValue left, rowsValue right]) state
      (rowsValue (left ++ right)) :=
  complete_append_returns encodePatterns state left right

theorem complete_append_patterns (state : State) (left right : List Pattern) :
    PureReturns runtime [] state (apply "gslt:automata:append" [patternsValue left, patternsValue right]) state
      (patternsValue (left ++ right)) := by
  simpa only [patternsValue, encodePatterns_eq_encodeList] using complete_append_returns encodePattern state left right

/-- `gslt:complete:cons-each` puts an item in front of every list. -/
@[metta_head "gslt:complete:cons-each"]
theorem cons_each_returns (state : State) (item : Pattern) : ∀ rows : List (List Pattern),
    PureReturns runtime [] state (apply "gslt:complete:cons-each" [patternValue item, rowsValue rows]) state
      (rowsValue (rows.map (item :: ·)))
  | [] => by
    metta_call_in completeProof_checked using completeProof_agreement
    metta_eval with completeProof_checked in completeProof_agreement unfolding [rowsValue]
  | row :: rest => by
    metta_call_in completeProof_checked using completeProof_agreement
    metta_eval [cons_each_returns state item rest] with completeProof_checked in completeProof_agreement
      unfolding [rowsValue, patternValue, encodePatterns]

/-- `gslt:complete:append-each` puts the same tail after every list. -/
@[metta_head "gslt:complete:append-each"]
theorem append_each_returns (state : State) (back : List Pattern) : ∀ rows : List (List Pattern),
    PureReturns runtime [] state (apply "gslt:complete:append-each" [rowsValue rows, patternsValue back]) state
      (rowsValue (rows.map (· ++ back)))
  | [] => by
    metta_call_in completeProof_checked using completeProof_agreement
    metta_eval with completeProof_checked in completeProof_agreement unfolding [rowsValue]
  | row :: rest => by
    metta_call_in completeProof_checked using completeProof_agreement
    metta_eval [complete_append_patterns state row back, append_each_returns state back rest] with completeProof_checked in completeProof_agreement
      unfolding [rowsValue, patternsValue, encodePatterns, List.map_cons]

/-- `gslt:complete:insertions` is `Inversion.insertions`. -/
@[metta_head "gslt:complete:insertions"]
theorem insertions_returns (state : State) (item : Pattern) : ∀ items : List Pattern,
    PureReturns runtime [] state (apply "gslt:complete:insertions" [patternValue item, patternsValue items]) state
      (rowsValue (insertions item items))
  | [] => by
    metta_call_in completeProof_checked using completeProof_agreement
    metta_eval with completeProof_checked in completeProof_agreement unfolding [rowsValue, patternValue, patternsValue, encodePatterns, insertions]
  | first :: rest => by
    metta_call_in completeProof_checked using completeProof_agreement
    metta_eval [insertions_returns state item rest, cons_each_returns state first (insertions item rest)]
      with completeProof_checked in completeProof_agreement
      unfolding [rowsValue, patternValue, patternsValue, encodePatterns, insertions]

/-- `gslt:complete:insert-all` inserts an item at every position of every order. -/
@[metta_head "gslt:complete:insert-all"]
theorem insert_all_returns (state : State) (item : Pattern) : ∀ orders : List (List Pattern),
    PureReturns runtime [] state (apply "gslt:complete:insert-all" [patternValue item, rowsValue orders]) state
      (rowsValue (orders.flatMap (insertions item)))
  | [] => by
    metta_call_in completeProof_checked using completeProof_agreement
    metta_eval with completeProof_checked in completeProof_agreement unfolding [rowsValue]
  | order :: rest => by
    metta_call_in completeProof_checked using completeProof_agreement
    metta_eval [insertions_returns state item order, insert_all_returns state item rest,
        complete_append_rows state (insertions item order) (rest.flatMap (insertions item))]
      with completeProof_checked in completeProof_agreement
      unfolding [rowsValue, patternValue, patternsValue, List.flatMap_cons]

/-- `gslt:complete:perms` is `Inversion.perms`. -/
@[metta_head "gslt:complete:perms"]
theorem perms_returns (state : State) : ∀ items : List Pattern,
    PureReturns runtime [] state (apply "gslt:complete:perms" [patternsValue items]) state (rowsValue (perms items))
  | [] => by
    metta_call_in completeProof_checked using completeProof_agreement
    metta_eval with completeProof_checked in completeProof_agreement unfolding [rowsValue, patternsValue, encodePatterns, perms]
  | first :: rest => by
    metta_call_in completeProof_checked using completeProof_agreement
    metta_eval [perms_returns state rest, insert_all_returns state first (perms rest)] with completeProof_checked in completeProof_agreement
      unfolding [rowsValue, patternValue, patternsValue, encodePatterns, perms]

/-- `gslt:complete:perms-all` lists every order of every list. -/
@[metta_head "gslt:complete:perms-all"]
theorem perms_all_returns (state : State) : ∀ rows : List (List Pattern),
    PureReturns runtime [] state (apply "gslt:complete:perms-all" [rowsValue rows]) state
      (rowsValue (rows.flatMap perms))
  | [] => by
    metta_call_in completeProof_checked using completeProof_agreement
    metta_eval with completeProof_checked in completeProof_agreement unfolding [rowsValue]
  | row :: rest => by
    metta_call_in completeProof_checked using completeProof_agreement
    metta_eval [perms_returns state row, perms_all_returns state rest,
        complete_append_rows state (perms row) (rest.flatMap perms)]
      with completeProof_checked in completeProof_agreement
      unfolding [rowsValue, patternsValue, List.flatMap_cons]

/-- How `gslt:complete:wrap-each` builds a term from a list of arguments. -/
inductive Shape where
  | apply (label : String)
  | collection (kind : CollType)

def Shape.term : Shape → Term
  | .apply label => .application "ApplyShape" [.string label]
  | .collection kind => .application "CollectionShape" [encodeCollectionType kind]

def Shape.build : Shape → List Pattern → Pattern
  | .apply label, elements => .apply label elements
  | .collection kind, elements => .collection kind elements none

@[metta_head "gslt:complete:wrap-each"]
theorem wrap_each_returns (state : State) (shape : Shape) : ∀ rows : List (List Pattern),
    PureReturns runtime [] state (apply "gslt:complete:wrap-each" [encoded shape.term, rowsValue rows]) state
      (patternsValue (rows.map shape.build))
  | [] => by
    metta_call_in completeProof_checked using completeProof_agreement
    metta_eval with completeProof_checked in completeProof_agreement unfolding [rowsValue, patternsValue, encodePatterns]
  | row :: rest => by
    have tail := wrap_each_returns state shape rest
    cases shape <;>
    · metta_call_in completeProof_checked using completeProof_agreement
      metta_eval [tail] with completeProof_checked in completeProof_agreement
        unfolding [rowsValue, patternsValue, encodePatterns, Shape.term, Shape.build, encodePattern, encodeRest]

@[metta_head "gslt:complete:lambda-each"]
theorem lambda_each_returns (state : State) : ∀ bodies : List Pattern,
    PureReturns runtime [] state (apply "gslt:complete:lambda-each" [patternsValue bodies]) state
      (patternsValue (bodies.map (.lambda none)))
  | [] => by
    metta_call_in completeProof_checked using completeProof_agreement
    metta_eval with completeProof_checked in completeProof_agreement unfolding [patternsValue, encodePatterns]
  | body :: rest => by
    metta_call_in completeProof_checked using completeProof_agreement
    metta_eval [lambda_each_returns state rest] with completeProof_checked in completeProof_agreement
      unfolding [patternsValue, encodePatterns, encodePattern, encodeBinder]

@[metta_head "gslt:complete:multi-lambda-each"]
theorem multi_lambda_each_returns (state : State) (arity : Nat) : ∀ bodies : List Pattern,
    PureReturns runtime [] state (apply "gslt:complete:multi-lambda-each" [number arity, patternsValue bodies]) state
      (patternsValue (bodies.map (.multiLambda arity [])))
  | [] => by
    metta_call_in completeProof_checked using completeProof_agreement
    metta_eval with completeProof_checked in completeProof_agreement unfolding [patternsValue, encodePatterns]
  | body :: rest => by
    metta_call_in completeProof_checked using completeProof_agreement
    metta_eval [multi_lambda_each_returns state arity rest] with completeProof_checked in completeProof_agreement
      unfolding [patternsValue, encodePatterns, encodePattern, InferenceCettaWire.encodeList]

/-- `gslt:complete:product` puts every head in front of every tail. -/
@[metta_head "gslt:complete:product"]
theorem product_returns (state : State) (tails : List (List Pattern)) : ∀ heads : List Pattern,
    PureReturns runtime [] state (apply "gslt:complete:product" [patternsValue heads, rowsValue tails]) state
      (rowsValue (heads.flatMap fun first => tails.map (first :: ·)))
  | [] => by
    metta_call_in completeProof_checked using completeProof_agreement
    metta_eval with completeProof_checked in completeProof_agreement unfolding [rowsValue, patternsValue, encodePatterns]
  | head :: rest => by
    metta_call_in completeProof_checked using completeProof_agreement
    metta_eval [cons_each_returns state head tails, product_returns state tails rest,
        complete_append_rows state (tails.map (head :: ·)) (rest.flatMap fun first => tails.map (first :: ·))]
      with completeProof_checked in completeProof_agreement
      unfolding [rowsValue, patternsValue, encodePatterns, List.flatMap_cons]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.complete_append_rows
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.complete_append_patterns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.cons_each_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.append_each_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.insertions_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.insert_all_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.perms_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.perms_all_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.wrap_each_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.lambda_each_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.multi_lambda_each_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.product_returns
