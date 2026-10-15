import Mettapedia.GSLT.Poly.SortedSignature

/-!
# Controls for sorted signatures as indexed polynomials

Positive: the numeral two of the signature `zero, succ` becomes the free-monad tree
whose spine of heads is `succ, succ, zero`, and the round trip returns the numeral.

Negative: a signature whose only constructor is `succ` has no closed terms, and its
polynomial has no free-monad trees without variables either. The equivalence carries
the absence across; it does not create trees.

Two sorts: in a signature with `drop : name → proc` and `quote : proc → name`, the
tree of `drop (quote nil)` changes sort at each head exactly as the term does,
because each direction lands at the declared input sort.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Poly.SortedSignatureControls

open Mettapedia.OSLF.SortedConstructors
open Mettapedia.GSLT.Poly.SortedSignature

/-- The heads along the first argument of every node, each with the sort it sits at. -/
def spine {signature : Signature.{0, 0}} :
    {sort : signature.Srt} → ClosedFree signature sort →
      List (signature.Constructor × signature.Srt)
  | _, .pure leaf => leaf.elim
  | sort, .liftBind head continuation =>
      (head.1, sort) ::
        if first : 0 < signature.arity head.1 then spine (continuation ⟨0, first⟩) else []

/-! ## Positive: numerals -/

inductive PeanoConstructor where
  | zero
  | succ
  deriving DecidableEq

def peano : Signature.{0, 0} where
  Srt := Unit
  Constructor := PeanoConstructor
  arity
    | .zero => 0
    | .succ => 1
  input _ _ := ()
  output _ := ()

def zeroTerm : Term peano () :=
  @Term.node peano PeanoConstructor.zero (fun position => Fin.elim0 position)

def succTerm (term : Term peano ()) : Term peano () :=
  @Term.node peano PeanoConstructor.succ (fun _ => term)

def two : Term peano () := succTerm (succTerm zeroTerm)

example : spine (toFree two) =
    [(PeanoConstructor.succ, ()), (PeanoConstructor.succ, ()), (PeanoConstructor.zero, ())] :=
  rfl

example : ofFree (toFree two) = two := ofFree_toFree two

/-! ## Negative: no constant, no closed term on either side -/

def succOnly : Signature.{0, 0} where
  Srt := Unit
  Constructor := Unit
  arity _ := 1
  input _ _ := ()
  output _ := ()

theorem succOnly_term_absurd : {sort : Unit} → Term succOnly sort → False
  | _, .node _ arguments => succOnly_term_absurd (arguments ⟨0, Nat.zero_lt_one⟩)

instance succOnly_no_closed_term (sort : Unit) : IsEmpty (Term succOnly sort) :=
  ⟨succOnly_term_absurd⟩

theorem succOnly_no_closed_tree : IsEmpty (ClosedFree succOnly ()) :=
  (closedTermEquiv succOnly ()).symm.isEmpty

/-! ## Two sorts: each direction lands at its input sort -/

inductive RhoSort where
  | proc
  | name
  deriving DecidableEq

inductive RhoConstructor where
  | nil
  | drop
  | quote
  deriving DecidableEq

def rhoFragment : Signature.{0, 0} where
  Srt := RhoSort
  Constructor := RhoConstructor
  arity
    | .nil => 0
    | .drop => 1
    | .quote => 1
  input
    | .nil, position => position.elim0
    | .drop, _ => .name
    | .quote, _ => .proc
  output
    | .nil => .proc
    | .drop => .proc
    | .quote => .name

def nilTerm : Term rhoFragment RhoSort.proc :=
  @Term.node rhoFragment RhoConstructor.nil (fun position => Fin.elim0 position)

def quoteTerm (process : Term rhoFragment RhoSort.proc) : Term rhoFragment RhoSort.name :=
  @Term.node rhoFragment RhoConstructor.quote (fun _ => process)

def dropTerm (name : Term rhoFragment RhoSort.name) : Term rhoFragment RhoSort.proc :=
  @Term.node rhoFragment RhoConstructor.drop (fun _ => name)

def dropQuoteNil : Term rhoFragment RhoSort.proc := dropTerm (quoteTerm nilTerm)

example : spine (toFree dropQuoteNil) =
    [(RhoConstructor.drop, RhoSort.proc), (RhoConstructor.quote, RhoSort.name),
      (RhoConstructor.nil, RhoSort.proc)] :=
  rfl

/-- The direction of `drop` lands at sort `name`. -/
example (position : Fin 1) :
    (polynomial rhoFragment).src RhoSort.proc ⟨RhoConstructor.drop, rfl⟩ position =
      RhoSort.name := rfl

/-- `quote` is not a head at sort `proc`: its declared output is `name`. -/
example : ¬ ∃ head : (polynomial rhoFragment).A RhoSort.proc, head.1 = RhoConstructor.quote := by
  rintro ⟨⟨constructor, output⟩, rfl⟩
  exact RhoSort.noConfusion output

end Mettapedia.GSLT.Poly.SortedSignatureControls
