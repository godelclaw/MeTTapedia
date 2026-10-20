import Mettapedia.OSLF.MeTTaIL.OrientationCongruence

/-!
# Position predicates with a condition at constructor nodes

`FrameAll dataOk variableOk` asks a predicate of the positions a walk visits: data and occurrences of
the body sort. `FrameAllNodes` asks a third, `nodeOk`, of every constructor node the walk rebuilds,
knowing its type: that it is no action node, that a collection of a flattening kind sits at its own sort,
and the like. Without the node predicate it is `FrameAll` (`frameAllNodes_true`).

The facts about it are proved once:
- `frameAllNodes_mapFrame`: a walk keeps the predicates when its functions do at data and occurrences and
  the rebuilt node keeps the node predicate;
- `frameAllNodes_mono`, `frameAllNodes_and`: weakening and conjunction;
- `frameAllNodes_forget`: dropping the node predicate gives `FrameAll`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Orientation

open Syntax

variable (language : LanguageDef) (decl : OrientationDecl)

mutual
  /-- **The position predicates and a node predicate**: `dataOk` at data, `variableOk` at occurrences of the
  body sort, and `nodeOk` at every other node the walk rebuilds, with the node's type. -/
  def FrameAllNodes (dataOk variableOk : Nat → Pattern → Prop) (nodeOk : Nat → TypeExpr → Pattern → Prop)
      (depth : Nat) (type : TypeExpr) (pattern : Pattern) : Prop :=
    if type = .base decl.dataSort then dataOk depth pattern
    else if (decorated? decl pattern).isSome ∧ actionType language decl = some type then variableOk depth pattern
    else
      nodeOk depth type pattern ∧
        match pattern with
        | .apply label arguments =>
            match paramTypes language label with
            | some types => FrameAllNodesArgs dataOk variableOk nodeOk depth types arguments
            | none => True
        | .lambda _ body =>
            match type with
            | .arrow _ codomain => FrameAllNodes dataOk variableOk nodeOk (depth + 1) codomain body
            | _ => True
        | .multiLambda arity _ body =>
            match type with
            | .arrow _ codomain => FrameAllNodes dataOk variableOk nodeOk (depth + arity) codomain body
            | _ => True
        | .collection kind elements _ =>
            match elementType language type kind with
            | some element => FrameAllNodesList dataOk variableOk nodeOk depth element elements
            | none => True
        | _ => True
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  def FrameAllNodesArgs (dataOk variableOk : Nat → Pattern → Prop) (nodeOk : Nat → TypeExpr → Pattern → Prop)
      (depth : Nat) : List TypeExpr → List Pattern → Prop
    | type :: types, argument :: arguments =>
        FrameAllNodes dataOk variableOk nodeOk depth type argument ∧
          FrameAllNodesArgs dataOk variableOk nodeOk depth types arguments
    | [], _ => True
    | _ :: _, [] => True
  termination_by _ arguments => sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec

  def FrameAllNodesList (dataOk variableOk : Nat → Pattern → Prop) (nodeOk : Nat → TypeExpr → Pattern → Prop)
      (depth : Nat) (element : TypeExpr) : List Pattern → Prop
    | [] => True
    | pattern :: patterns =>
        FrameAllNodes dataOk variableOk nodeOk depth element pattern ∧
          FrameAllNodesList dataOk variableOk nodeOk depth element patterns
  termination_by patterns => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

end Mettapedia.OSLF.MeTTaIL.Orientation
