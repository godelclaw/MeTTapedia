import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# Executable tree-node counts for the shared pattern syntax

Every constructor contributes one node. Constructor arguments and collection
elements contribute their full subtree counts, including repeated elements.
Binder metadata and variable spellings do not affect the count.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.PatternTreeSize

open Syntax

mutual
  def nodes : Pattern → Nat
    | .bvar _ => 1
    | .fvar _ => 1
    | .apply _ arguments => 1 + listNodes arguments
    | .lambda _ body => 1 + nodes body
    | .multiLambda _ _ body => 1 + nodes body
    | .subst body replacement => 1 + nodes body + nodes replacement
    | .collection _ elements _ => 1 + listNodes elements

  def listNodes : List Pattern → Nat
    | [] => 0
    | first :: rest => nodes first + listNodes rest
end

theorem nodes_positive (pattern : Pattern) : 0 < nodes pattern := by
  cases pattern <;> simp only [nodes] <;> omega

theorem member_nodes_le {pattern : Pattern} {patterns : List Pattern}
    (member : pattern ∈ patterns) : nodes pattern ≤ listNodes patterns := by
  induction patterns with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with same | tail
    · rw [same, listNodes]
      omega
    · have smaller := ih tail
      simp only [listNodes]
      omega

theorem member_nodes_lt_apply {pattern : Pattern} {constructor : String}
    {arguments : List Pattern} (member : pattern ∈ arguments) :
    nodes pattern < nodes (.apply constructor arguments) := by
  have smaller := member_nodes_le member
  simp only [nodes]
  omega

theorem member_nodes_lt_collection {pattern : Pattern} {kind : CollType}
    {elements : List Pattern} {rest : Option String} (member : pattern ∈ elements) :
    nodes pattern < nodes (.collection kind elements rest) := by
  have smaller := member_nodes_le member
  simp only [nodes]
  omega

end Mettapedia.OSLF.MeTTaIL.PatternTreeSize
