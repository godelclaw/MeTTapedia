import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionReference

/-! Source-order and accumulator laws for structural ProgramData projection.
The laws quantify over arbitrary tails and preserve the complete source
literal subtrees. They do not interpret numeric values or source aliases. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.Reference

open Mettapedia.OSLF.MeTTaIL.Syntax

theorem literal_subtrees_retained (symbol integer unsigned floating : Pattern) :
    constant? (.apply "dl-src:constant-symbol" [symbol]) = some (.apply "SymbolValue" [symbol]) ∧
      constant? (.apply "dl-src:constant-integer" [integer]) = some (.apply "IntegerValue" [integer]) ∧
      constant? (.apply "dl-src:constant-unsigned" [unsigned]) = some (.apply "UnsignedValue" [unsigned]) ∧
      constant? (.apply "dl-src:constant-float" [floating]) = some (.apply "FloatValue" [floating]) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem relationsInto_append (source : Pattern) (attributes first second : List Pattern) :
    relationsInto? source attributes (first ++ second) =
      (relationsInto? source attributes first).map (· ++ second) := by
  unfold relationsInto?
  split
  · simp
  · rename_i identifier before after rest
    rw [relationsInto_append rest attributes first second]
    cases relationsInto? rest attributes first <;> rfl
  · rfl
termination_by sizeOf source
decreasing_by simp_all; omega

theorem itemInto_append (source : Pattern) (first second : List Pattern) :
    itemInto? source (first ++ second) = (itemInto? source first).map (· ++ second) := by
  unfold itemInto?
  split
  · rename_i space relations before start attributes
    cases fields : attributes? attributes with
    | none => rfl
    | some values => simpa only [Option.bind_eq_bind, Option.bind_some] using
        relationsInto_append relations values first second
  · cases fact? _ <;> rfl
  · cases rule? _ <;> rfl
  · rfl
  · rfl
  · rfl

theorem itemsInto_append (source : Pattern) (first second : List Pattern) :
    itemsInto? source (first ++ second) = (itemsInto? source first).map (· ++ second) := by
  unfold itemsInto?
  split
  · rfl
  · rename_i head gap rest
    rw [itemsInto_append rest first second]
    cases projected : itemsInto? rest first with
    | none => rfl
    | some values => simpa only [Option.map_some, Option.bind_eq_bind, Option.bind_some] using
        itemInto_append head values second
  · rfl
termination_by sizeOf source
decreasing_by simp_all; omega

theorem relationsInto_order (first second before after : Pattern)
    (attributes tail : List Pattern) :
    relationsInto? (.apply "dl-src:relations-more"
      [first, before, after, .apply "dl-src:relations-one" [second]]) attributes tail =
        some (declaration first attributes :: declaration second attributes :: tail) := rfl

theorem trivia_does_not_change_relation_order (first second : Pattern)
    (before after otherBefore otherAfter : Pattern) (attributes tail : List Pattern) :
    relationsInto? (.apply "dl-src:relations-more"
      [first,before,after,.apply "dl-src:relations-one" [second]]) attributes tail =
    relationsInto? (.apply "dl-src:relations-more"
      [first,otherBefore,otherAfter,.apply "dl-src:relations-one" [second]]) attributes tail := rfl

#print axioms literal_subtrees_retained
#print axioms relationsInto_append
#print axioms itemInto_append
#print axioms itemsInto_append
#print axioms relationsInto_order

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.Reference
