import Mettapedia.TypeTheory.IndexedPolynomialAdjunction
import Mettapedia.TypeTheory.IndexedPolynomialFreeMapInjective
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# First-order signatures for deterministic operational rules

The signature records output sorts, individually addressed finite argument
positions, and each argument's sort. Its free terms and categorical monad
are the existing indexed polynomial construction. Variables range over
arbitrary families; neither variable sets nor action sets are finite here.
The empty family is initial, and terms over it are the closed terms.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.DeterministicGSOS

open CategoryTheory Mettapedia.TypeTheory

universe u

/-- A finite-arity many-sorted first-order signature. -/
structure Signature where
  Srt : Type u
  Operator : Srt → Type u
  Position : {sort : Srt} → Operator sort → Type u
  argument : {sort : Srt} → (operator : Operator sort) →
    Position operator → Srt
  finite : ∀ {sort : Srt} (operator : Operator sort),
    Finite (Position operator)

namespace Signature

variable (S : Signature.{u})

/-- The first-order polynomial, with one base object and the supplied sorts. -/
abbrev polynomial : IndexedPolynomial.{u, u, u, u}
    PUnit.{u + 1} (fun _ => S.Srt) where
  Shape := fun _ sort => S.Operator sort
  Position := S.Position
  next := S.argument

/-- Families of variables, retaining the original indexed-polynomial category. -/
abbrev Families := IndexedPolynomial.Family PUnit.{u + 1} (fun _ => S.Srt)

/-- The actual constructor endofunctor. -/
abbrev syntaxFunctor : S.Families ⥤ S.Families := S.polynomial.endofunctor

/-- The categorical free monad derived from the free-algebra adjunction. -/
noncomputable abbrev termMonad : CategoryTheory.Monad S.Families :=
  IndexedPolynomial.FreeAdjunction.monad S.polynomial

/-- Free syntax in an arbitrary family of typed variables. -/
abbrev Term (holes : S.Families) (sort : S.Srt) :=
  S.polynomial.Free holes PUnit.unit sort

/-- Relabel variables, retaining every constructor and argument position. -/
noncomputable abbrev rename {X Y : S.Families} (mapping : X ⟶ Y)
    {sort : S.Srt} : S.Term X sort → S.Term Y sort :=
  IndexedPolynomial.Free.map S.polynomial
    (fun base index => mapping base index) PUnit.unit sort

/-- Individually typed original arguments of one constructor. -/
abbrev Arguments (X : S.Families) {sort : S.Srt}
    (operator : S.Operator sort) :=
  (position : S.Position operator) → X PUnit.unit (S.argument operator position)

/-- No variables at any sort. -/
abbrev noVariables : S.Families := fun _ _ => PEmpty.{u + 1}

/-- The empty family is initial among families. -/
def noVariablesInitial : Limits.IsInitial S.noVariables :=
  Limits.IsInitial.ofUniqueHom (fun _ _ _ => ↾(fun value => PEmpty.elim value))
    (fun _ _ => by
      funext base sort
      apply ConcreteCategory.hom_ext
      intro value
      exact PEmpty.elim value)

/-- Closed terms: free syntax over no variables. -/
abbrev ClosedTerm (sort : S.Srt) := S.Term S.noVariables sort

end Signature

end Mettapedia.OSLF.DeterministicGSOS
