import PolyFun.IPFunctor.Free.Family
import Mettapedia.OSLF.Syntax.SortedConstructorContexts

/-!
# Sorted constructor signatures as indexed polynomials

A sorted constructor signature is an endomorphic indexed polynomial over its
sorts, in the sense of PolyFun's `IPFunctor`:

* the heads at a sort are the constructors whose declared output is that sort;
* the directions of a head are its argument positions;
* each direction lands at the declared input sort of its position.

Closed constructor terms are then exactly the free monad of this polynomial
with no variables: `closedTermEquiv` is an equivalence in both directions, so
every closed term is one free-monad tree and every such tree is one closed term.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Poly

open Mettapedia.OSLF.SortedConstructors

universe u v

namespace SortedSignature

/-- The indexed polynomial of a sorted signature. -/
def polynomial (signature : Signature.{u, v}) :
    IPFunctor.Endo.{u, v, 0} signature.Srt where
  A sort := {constructor : signature.Constructor // signature.output constructor = sort}
  B _ head := Fin (signature.arity head.1)
  src _ head position := signature.input head.1 position

/-- Free-monad trees of the signature's polynomial with no variables. -/
abbrev ClosedFree (signature : Signature.{u, v}) (sort : signature.Srt) :=
  IPFunctor.IFreeM (polynomial signature) (fun _ => PEmpty.{1}) sort

variable {signature : Signature.{u, v}}

/-- A closed constructor term as a free-monad tree: each node becomes one head
with one continuation per argument position. -/
def toFree : {sort : signature.Srt} → Term signature sort → ClosedFree signature sort
  | _, .node constructor arguments =>
      .liftBind ⟨constructor, rfl⟩ (fun position => toFree (arguments position))

/-- A free-monad tree without variables as a closed constructor term. A leaf would
carry a variable, and there are none. -/
def ofFree : {sort : signature.Srt} → ClosedFree signature sort → Term signature sort
  | _, .pure leaf => leaf.elim
  | _, .liftBind ⟨constructor, rfl⟩ continuation =>
      .node constructor (fun position => ofFree (continuation position))

theorem ofFree_toFree {sort : signature.Srt} (term : Term signature sort) :
    ofFree (toFree term) = term := by
  induction term with
  | node constructor arguments ih =>
      simp only [toFree, ofFree]
      exact congrArg (Term.node constructor) (funext ih)

theorem toFree_ofFree {sort : signature.Srt} (free : ClosedFree signature sort) :
    toFree (ofFree free) = free := by
  induction free with
  | pure leaf => exact leaf.elim
  | liftBind head continuation ih =>
      obtain ⟨constructor, rfl⟩ := head
      simp only [ofFree, toFree]
      exact congrArg (IPFunctor.IFreeM.liftBind _) (funext ih)

/-- Closed constructor terms are the free monad of the signature's polynomial
with no variables. -/
def closedTermEquiv (signature : Signature.{u, v}) (sort : signature.Srt) :
    Term signature sort ≃ ClosedFree signature sort where
  toFun := toFree
  invFun := ofFree
  left_inv := ofFree_toFree
  right_inv := toFree_ofFree

end SortedSignature

end Mettapedia.GSLT.Poly
