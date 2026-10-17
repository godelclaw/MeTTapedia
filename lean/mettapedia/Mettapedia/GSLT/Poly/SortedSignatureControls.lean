import Mettapedia.GSLT.Poly.SortedSignature
import Mettapedia.GSLT.Poly.BindingSignature
import Mettapedia.GSLT.Poly.SortedTraversal

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

Derived frames preserve hole occurrences even when filling either occurrence
produces the same completed term. The binding-signature instance also retains
the lambda body's extended scope and rejects reading it at the empty scope.

Dissection controls use different processed/source families and an actual
stateful child service. Repeated payloads remain distinct requests; resumption
retains both the partial tuple and the provider's history, while restart repeats
the wrong occurrence.
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

/-! ## Derived frames retain sorts, arity and occurrence identity -/

def dropFrame : Frame rhoFragment RhoSort.name RhoSort.proc :=
  @Frame.slot rhoFragment RhoConstructor.drop ⟨0, by decide⟩ (fun other different => by
    have bound : other.val < 1 := other.isLt
    have zero : other.val = 0 := by omega
    exact False.elim (different (Fin.ext zero)))

example : derivativeToFrame (frameToDerivative dropFrame) = dropFrame :=
  derivativeToFrame_frameToDerivative dropFrame

example : assemble (fillDerivative (frameToDerivative dropFrame) (quoteTerm nilTerm)) =
    Frame.fill dropFrame (quoteTerm nilTerm) :=
  assemble_fillDerivative dropFrame (quoteTerm nilTerm)

/-- A nullary constructor has no input occurrence to turn into a hole. -/
theorem no_nil_derivative (source : RhoSort) :
    ¬ ∃ head : (derivative rhoFragment).A (source, RhoSort.proc),
      head.constructor = RhoConstructor.nil := by
  rintro ⟨⟨constructor, position, _, _⟩, rfl⟩
  exact position.elim0

/-- The hole of drop is a name, independently of its process result. -/
theorem no_process_hole_in_drop :
    ¬ ∃ head : (derivative rhoFragment).A (RhoSort.proc, RhoSort.proc),
      head.constructor = RhoConstructor.drop := by
  rintro ⟨⟨constructor, _, input, _⟩, rfl⟩
  exact RhoSort.noConfusion input

inductive PairConstructor where
  | leaf
  | pair
  deriving DecidableEq

abbrev pairs : Signature.{0, 0} where
  Srt := Unit
  Constructor := PairConstructor
  arity
    | .leaf => 0
    | .pair => 2
  input _ _ := ()
  output _ := ()

def leaf : Term pairs () := @Term.node pairs PairConstructor.leaf (fun position => position.elim0)

def leftFrame : Frame pairs () () := @Frame.slot pairs PairConstructor.pair 0 (fun _ _ => leaf)

def rightFrame : Frame pairs () () := @Frame.slot pairs PairConstructor.pair 1 (fun _ _ => leaf)

/-- Equal-looking children remain separate occurrences in the derivative. -/
theorem equal_payloads_distinct_positions : leftFrame ≠ rightFrame := by
  intro same
  have positions := congrArg (fun frame : Frame pairs () () =>
    (frameToDerivative frame).1.position.val) same
  simp [leftFrame, rightFrame, frameToDerivative] at positions

/-- Filling with the same payload may hide which occurrence was selected.
Therefore a completed-value observer cannot recover a continuation's hole. -/
theorem equal_filled_values : Frame.fill leftFrame leaf = Frame.fill rightFrame leaf := by
  simp only [leftFrame, rightFrame, Frame.fill_slot]
  congr 1
  funext position
  have bound : position.val < 2 := position.isLt
  have cases : position.val = 0 ∨ position.val = 1 := by omega
  rcases cases with first | second
  · have same : position = 0 := Fin.ext first
    subst position
    simp
  · have same : position = 1 := Fin.ext second
    subst position
    simp

example : toFree (Frame.fill leftFrame leaf) =
    let node := fillDerivative
      ((derivative pairs).map (fun _ => toFree) (frameToDerivative leftFrame)) (toFree leaf)
    IPFunctor.IFreeM.liftBind node.1 node.2 := toFree_fill leftFrame leaf

/-! ## A binder changes the hole's scope, not the enclosing result's scope -/

open Mettapedia.OSLF.Binding.ScopedEncoding (signature Constructor)

def lambdaBodyFrame :
    Frame (signature BindingSignature.demo)
      ([BindingSignature.DemoSort.star], BindingSignature.DemoSort.star)
      ([], BindingSignature.DemoSort.star) :=
  @Frame.slot (signature BindingSignature.demo)
    (Constructor.operation [] BindingSignature.DemoSort.star BindingSignature.DemoOp.lam)
    ⟨0, by decide⟩ (fun other different => by
    have bound : other.val < 1 := other.isLt
    have zero : other.val = 0 := by omega
    exact False.elim (different (Fin.ext zero)))

/-- Filling the derived binder frame reconstructs the independently scoped
lambda, including its bound variable's position. -/
theorem lambda_body_fill :
    assemble (fillDerivative (frameToDerivative lambdaBodyFrame)
      (BindingSignature.toScoped BindingSignature.demoBody)) =
      BindingSignature.toScoped BindingSignature.demoLam := by
  rw [assemble_fillDerivative]
  unfold lambdaBodyFrame BindingSignature.demoLam
  unfold BindingSignature.demo
  rw [Frame.fill_slot, BindingSignature.toScoped_op]
  congr 1
  funext position
  change Fin 1 at position
  have zero : position = 0 := Fin.eq_zero position
  subst position
  rfl

/-- A lambda-body hole cannot be read at the enclosing empty scope. Even
though both scopes end in the same sort, the bound slot must remain live. -/
theorem no_closed_scope_lambda_body :
    ¬ ∃ head : (derivative (signature BindingSignature.demo)).A
      (([], BindingSignature.DemoSort.star), ([], BindingSignature.DemoSort.star)),
      head.constructor = .operation [] .star .lam := by
  rintro ⟨⟨constructor, position, input, _⟩, rfl⟩
  change Fin 1 at position
  have zero : position = 0 := Fin.eq_zero position
  subst position
  have scopes := congrArg Prod.fst input
  cases scopes

/-! ## Completed and pending sides have different payload families -/

def stringArguments : SortedTraversal.Arguments (signature := pairs) (fun _ => String)
    PairConstructor.pair := fun position => if position.val = 0 then "aa" else "bbb"

def stringCursor : ArgumentCursor pairs (fun _ => Nat) (fun _ => String)
    PairConstructor.pair := ArgumentCursor.start stringArguments

def measuredFirst : ArgumentCursor pairs (fun _ => Nat) (fun _ => String)
    PairConstructor.pair := stringCursor.accept (by decide) 2

theorem mixed_frame_retains_completed_and_pending :
    measuredFirst.position.val = 1 ∧
      (measuredFirst.focus (by decide)).before ⟨0, by decide⟩ (by decide) = 2 ∧
      measuredFirst.current (by decide) = "bbb" := by decide

theorem dissection_diagonal_retains_hole :
    (Dissection.diagonalEquiv (Term pairs) () ()).symm (frameToDerivative leftFrame) ≠
      (Dissection.diagonalEquiv (Term pairs) () ()).symm (frameToDerivative rightFrame) := by
  intro same
  have derivatives := (Dissection.diagonalEquiv (Term pairs) () ()).symm.injective same
  have frames := congrArg derivativeToFrame derivatives
  rw [derivativeToFrame_frameToDerivative, derivativeToFrame_frameToDerivative] at frames
  exact equal_payloads_distinct_positions frames

/-- A processed result is retained even when it differs from applying the
current processor to the original source. Restarting would overwrite it. -/
def retainedDifferent : ArgumentCursor pairs (fun _ => Nat) (fun _ => String)
    PairConstructor.pair := stringCursor.accept (by decide) 70

theorem completed_slot_is_not_reprocessed :
    retainedDifferent.denote (fun _ text => text.length) 0 = 70 ∧
      retainedDifferent.denote (fun _ text => text.length) 1 = 3 ∧
      retainedDifferent.denote (fun _ text => text.length) 0 ≠ (stringArguments 0).length := by
  decide

/-! ## The common cursor driver retains provider state as well as the frame -/

open Mettapedia.Machines.Cursor

def numberArguments : SortedTraversal.Arguments (signature := pairs) (fun _ => Nat)
    PairConstructor.pair := fun _ => 7

def numberCursor : ArgumentCursor pairs (fun _ => Nat) (fun _ => Nat)
    PairConstructor.pair := ArgumentCursor.start numberArguments

def numberClient := SortedTraversal.client (signature := pairs)
  (fun _ => Nat) (fun _ => Nat) PairConstructor.pair

/-- This service records occurrence positions. Replies depend on the service's
retained state, so replay or loss of that state changes the resulting tuple. -/
def recordedProvider : Provider (SortedTraversal.protocol (signature := pairs)
    (fun _ => Nat) (fun _ => Nat) PairConstructor.pair) where
  State _ _ := List Nat
  step seen request := ⟨request.2 + seen.length, seen ++ [request.1.val]⟩

def recordedStart : Packet recordedProvider numberClient () :=
  SortedTraversal.packet recordedProvider numberCursor []

def recordedSeen : Outcome recordedProvider numberClient () → List Nat
  | .paused saved => saved.2.2
  | .done returned => returned.2.2

def recordedValues : Outcome recordedProvider numberClient () → Option (Nat × Nat)
  | .paused _ => none
  | .done returned => some (returned.2.1 0, returned.2.1 1)

theorem equal_sources_are_two_requests :
    recordedSeen (advance recordedProvider numberClient (fun _ _ => 1) 3 recordedStart).2 =
        [0, 1] ∧
      recordedValues (advance recordedProvider numberClient (fun _ _ => 1) 3 recordedStart).2 =
        some (7, 8) ∧
      (advance recordedProvider numberClient (fun _ _ => 1) 3 recordedStart).1 = 2 := by decide

theorem early_pause_leaves_second_occurrence_pending :
    recordedSeen (advance recordedProvider numberClient (fun _ _ => 1) 1 recordedStart).2 =
        [0] ∧
      recordedValues (advance recordedProvider numberClient (fun _ _ => 1) 1 recordedStart).2 =
        none := by decide

theorem resume_keeps_stateful_replies :
    resume recordedProvider numberClient (fun _ _ => 1) 2
        (advance recordedProvider numberClient (fun _ _ => 1) 1 recordedStart) =
      advance recordedProvider numberClient (fun _ _ => 1) 3 recordedStart :=
  SortedTraversal.resume_exact recordedProvider (fun _ _ => 1) 1 2 numberCursor []

/-- Keeping the provider state but restarting the original traversal repeats
the first occurrence instead of continuing with the second. -/
theorem restart_replays_the_wrong_occurrence :
    recordedSeen (advance recordedProvider numberClient (fun _ _ => 1) 1
      (SortedTraversal.packet recordedProvider numberCursor [0])).2 = [0, 0] ∧
    recordedSeen (resume recordedProvider numberClient (fun _ _ => 1) 1
      (advance recordedProvider numberClient (fun _ _ => 1) 1 recordedStart)).2 = [0, 1] := by
  decide

theorem all_replies_received_is_not_yet_returned :
    recordedSeen (advance recordedProvider numberClient (fun _ _ => 1) 2 recordedStart).2 =
        [0, 1] ∧
      recordedValues (advance recordedProvider numberClient (fun _ _ => 1) 2 recordedStart).2 =
        none := by decide

/-! ## The dissection retains the scope of a binder's child request -/

def lambdaBodyCursor : ArgumentCursor (signature BindingSignature.demo)
    (Term (signature BindingSignature.demo)) (Term (signature BindingSignature.demo))
    (Constructor.operation [] BindingSignature.DemoSort.star BindingSignature.DemoOp.lam) :=
  ArgumentCursor.start (fun position => by
    change Fin 1 at position
    have zero : position = 0 := Fin.eq_zero position
    subst position
    exact BindingSignature.toScoped BindingSignature.demoBody)

theorem lambda_request_keeps_extended_scope :
    (lambdaBodyCursor.focus (by decide)).head.constructor =
        Constructor.operation [] BindingSignature.DemoSort.star BindingSignature.DemoOp.lam ∧
      lambdaBodyCursor.current (by decide) =
        BindingSignature.toScoped BindingSignature.demoBody := ⟨rfl, rfl⟩

end Mettapedia.GSLT.Poly.SortedSignatureControls
