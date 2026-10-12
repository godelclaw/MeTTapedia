import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContexts

/-!
# Logical equality in the common native grammar

Equality uses quantified first-class predicates, application and implication.
Its syntax requires no new primitive relation. The scoped construction commutes
with renaming and substitution, including the protected predicate binder.
Agreement with diagonal predicates is a separate semantic comparison.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.NativeEquality

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

universe u
variable {S : Symbols.{u}}

def predicateType {n : Nat} (carrier : TypeExpr S n) : TypeExpr S n :=
  .pi carrier .propositions

def equal {n : Nat} (carrier : TypeExpr S n) (first second : TermExpr S n) : PropExpr S n :=
  .all (predicateType carrier)
    (.implies
      (.holds (.app (carrier.rename Fin.succ) .propositions (.var 0) (first.rename Fin.succ)))
      (.holds (.app (carrier.rename Fin.succ) .propositions (.var 0) (second.rename Fin.succ))))

theorem equal_rename {n m : Nat} (mapping : Renaming n m)
    (carrier : TypeExpr S n) (first second : TermExpr S n) :
    (equal carrier first second).rename mapping =
      equal (carrier.rename mapping) (first.rename mapping) (second.rename mapping) := by
  simp only [equal, predicateType, PropExpr.rename, TypeExpr.rename, TermExpr.rename,
    TypeExpr.rename_comp, TermExpr.rename_comp, liftRenaming_zero]
  rfl

theorem equal_substitute {n m : Nat} (substitution : Substitution S n m)
    (carrier : TypeExpr S n) (first second : TermExpr S n) :
    (equal carrier first second).substitute substitution =
      equal (carrier.substitute substitution) (first.substitute substitution) (second.substitute substitution) := by
  simp only [equal, predicateType, PropExpr.substitute, TypeExpr.substitute, TermExpr.substitute,
    TypeExpr.substitute_rename, TermExpr.substitute_rename, TypeExpr.rename_substitute,
    TermExpr.rename_substitute, liftSubstitution_zero]
  rfl

end Mettapedia.OSLF.NativeTypes.Generation.NativeEquality
