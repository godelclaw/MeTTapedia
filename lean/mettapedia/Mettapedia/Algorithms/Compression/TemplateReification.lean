import Mettapedia.Algorithms.Compression.ConstructorTrees

/-!
# Reifying fixed library bodies as ranked templates

A checked catalogue can classify nullary operators as parameter occurrences.
Reification preserves the exported parameter indices; it neither generalizes
from a receiving program nor renumbers ports by its traversal order. Applying
the resulting template agrees with an independent recursive instantiation of
the marked body. Matching therefore reconstructs a new receiving tree.

Physical source decoding, ready/delayed classification and the source-context
walker are separate interfaces. No text label or declared type supplies the
marker function's permission, and this is not a C-refinement theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Compression.TemplateReification

open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierRoleAntiUnification
open Mettapedia.GSLT.LanguageDef.GauthierCanonicalSchema
open TemplateMatching

mutual
def reify (marker : Nat → Option Nat) (role : HoleRole) : Prog → SchemaPattern
  | .node op [] => match marker op with
      | some index => .hole role index
      | none => .node op []
  | .node op (first :: rest) => .node op (reifyList marker (first :: rest))

def reifyList (marker : Nat → Option Nat) : List Prog → List SchemaPattern
  | [] => []
  | first :: rest => reify marker .value first :: reifyList marker rest
end

mutual
def instantiate (marker : Nat → Option Nat) (arguments : Environment)
    (role : HoleRole) : Prog → Option Prog
  | .node op [] => match marker op with
      | some index => arguments (role, index)
      | none => some (.node op [])
  | .node op (first :: rest) => (instantiateList marker arguments (first :: rest)).map (.node op)

def instantiateList (marker : Nat → Option Nat) (arguments : Environment) : List Prog → Option (List Prog)
  | [] => some []
  | first :: rest => do
      let value ← instantiate marker arguments .value first
      let values ← instantiateList marker arguments rest
      pure (value :: values)
end

mutual
theorem expand_reify (marker : Nat → Option Nat) (arguments : Environment) (role : HoleRole) :
    ∀ body, expand arguments (reify marker role body) = instantiate marker arguments role body
  | .node op [] => by
      cases present : marker op <;> simp [reify, instantiate, expand, expandList, present]
  | .node op (first :: rest) => by
      simp only [reify, expand, instantiate, expandList_reify]

theorem expandList_reify (marker : Nat → Option Nat) (arguments : Environment) :
    ∀ bodies, expandList arguments (reifyList marker bodies) = instantiateList marker arguments bodies
  | [] => rfl
  | first :: rest => by
      simp only [reifyList, expandList, instantiateList, expand_reify, expandList_reify]
end

theorem matched_body_reconstructs (marker : Nat → Option Nat) (before after : Environment)
    (role : HoleRole) (body target : Prog)
    (matched : matchPattern before (reify marker role body) target = some after) :
    instantiate marker after role body = some target := by
  rw [← expand_reify]
  exact (matchPattern_sound before after _ target matched).2

theorem matched_tree_reconstructs (marker : Nat → Option Nat) (before after : Environment)
    (role : HoleRole) (body : Prog) (table : List ConstructorTrees.Key)
    (target : FramedTree.Tree) (covered : ConstructorTrees.Covers table target)
    (matched : matchPattern before (reify marker role body) (ConstructorTrees.encode table target) = some after) :
    (instantiate marker after role body).bind (ConstructorTrees.decode table (FramedTree.size target)) = some target := by
  rw [matched_body_reconstructs marker before after role body _ matched]
  exact ConstructorTrees.decode_encode table target _ (by omega) covered

namespace Controls

def marker (op : Nat) : Option Nat :=
  if op = 7 then some 1 else if op = 6 then some 0 else none

theorem exported_port_order_is_not_reassigned :
    reify marker .root (.node 9 [.node 7 [], .node 6 []]) =
      .node 9 [.hole .value 1, .hole .value 0] := by rfl

theorem application_is_not_misread_as_a_nullary_port :
    reify marker .root (.node 7 [.node 8 []]) = .node 7 [.node 8 []] := by rfl

theorem missing_parameter_does_not_get_a_default :
    instantiate marker empty .value (.node 7 []) = none := by rfl

theorem repeated_parameter_disagreement_is_rejected :
    (matchPattern empty (reify marker .root (.node 9 [.node 7 [], .node 7 []]))
      (.node 9 [.node 2 [], .node 3 []])).isSome = false := by
  simp [reify, reifyList, marker, matchPattern, matchList, assign, empty]

theorem repeated_parameter_agreement_is_accepted :
    (matchPattern empty (reify marker .root (.node 9 [.node 7 [], .node 7 []]))
      (.node 9 [.node 2 [], .node 2 []])).isSome = true := by
  simp [reify, reifyList, marker, matchPattern, matchList, assign, empty]

end Controls
end Mettapedia.Algorithms.Compression.TemplateReification
