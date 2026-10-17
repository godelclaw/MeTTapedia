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

The partial derivative selects one argument of its declared hole sort and
retains exactly the other arguments. Its object at constructor terms is
equivalent to the existing sorted frame type. Filling and payload transport
commute with that equivalence. This derives frame structure; evaluation
permission, ownership and observation policy remain separate obligations.

Dissections retain completed and pending siblings in separate sorted families.
Their diagonal is equivalent to the derivative. An argument cursor advances
the cut by accepting one reply, preserving all other slots; its focused frame
and independent pointwise readback agree.
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

/-! ## Partial derivatives and the existing frame representation -/

/-- A constructor with one distinguished input occurrence. The input and
output sorts need not coincide. -/
structure DerivativeHead (signature : Signature.{u, v})
    (source target : signature.Srt) where
  constructor : signature.Constructor
  position : Fin (signature.arity constructor)
  input_eq : signature.input constructor position = source
  output_eq : signature.output constructor = target

/-- The partial derivative of the signature polynomial. Its output index
records the hole sort and result sort. Directions are precisely the remaining
occurrences, even when several occurrences have equal values or sorts. -/
abbrev derivative (signature : Signature.{u, v}) :
    IPFunctor signature.Srt (signature.Srt × signature.Srt) where
  A index := DerivativeHead signature index.1 index.2
  B _ head := {other : Fin (signature.arity head.constructor) // other ≠ head.position}
  src _ head other := signature.input head.constructor other.val

/-- Fill a derivative with one value, yielding an ordinary polynomial node.
No interpretation of either the siblings or the supplied value takes place. -/
def fillDerivative {Value : signature.Srt → Type*} {source target : signature.Srt}
    (context : (derivative signature).Obj Value (source, target)) (value : Value source) :
    (polynomial signature).Obj Value target := by
  refine ⟨⟨context.1.constructor, context.1.output_eq⟩, ?_⟩
  change (other : Fin (signature.arity context.1.constructor)) →
    Value (signature.input context.1.constructor other)
  exact fun other =>
    if same : other = context.1.position then
      same.symm ▸ (context.1.input_eq.symm ▸ value)
    else context.2 ⟨other, same⟩

/-- Pointwise transport preserves a focused occurrence and all its siblings. -/
theorem fillDerivative_map {Value Other : signature.Srt → Type*}
    (transform : (sort : signature.Srt) → Value sort → Other sort)
    {source target : signature.Srt}
    (context : (derivative signature).Obj Value (source, target)) (value : Value source) :
    fillDerivative ((derivative signature).map transform context) (transform source value) =
      (polynomial signature).map transform (fillDerivative context value) := by
  dsimp only [derivative, IPFunctor.Obj] at context
  rcases context with ⟨⟨constructor, position, rfl, rfl⟩, siblings⟩
  simp only [fillDerivative, IPFunctor.map, polynomial]
  congr 1
  funext other
  by_cases same : other = position
  · subst other; simp
  · simp [same]

/-- Read an existing sorted frame as the derivative's head and siblings. -/
def frameToDerivative {source target : signature.Srt} :
    Frame signature source target → (derivative signature).Obj (Term signature) (source, target)
  | .slot constructor position siblings =>
      ⟨⟨constructor, position, rfl, rfl⟩, fun other => siblings other.val other.property⟩

/-- Construct a sorted frame from a polynomial derivative. -/
def derivativeToFrame {source target : signature.Srt}
    (context : (derivative signature).Obj (Term signature) (source, target)) :
    Frame signature source target := by
  dsimp only [derivative, IPFunctor.Obj] at context
  rcases context with ⟨⟨constructor, position, rfl, rfl⟩, siblings⟩
  exact .slot constructor position (fun other different => siblings ⟨other, different⟩)

theorem derivativeToFrame_frameToDerivative {source target : signature.Srt}
    (frame : Frame signature source target) :
    derivativeToFrame (frameToDerivative frame) = frame := by
  cases frame
  rfl

theorem frameToDerivative_derivativeToFrame {source target : signature.Srt}
    (context : (derivative signature).Obj (Term signature) (source, target)) :
    frameToDerivative (derivativeToFrame context) = context := by
  dsimp only [derivative, IPFunctor.Obj] at context
  rcases context with ⟨⟨constructor, position, rfl, rfl⟩, siblings⟩
  rfl

/-- The actual constructor-frame carrier is the partial derivative, with no
quotienting of equal sibling payloads or erasure of the selected occurrence. -/
def frameDerivativeEquiv (signature : Signature.{u, v}) (source target : signature.Srt) :
    Frame signature source target ≃
      (derivative signature).Obj (Term signature) (source, target) where
  toFun := frameToDerivative
  invFun := derivativeToFrame
  left_inv := derivativeToFrame_frameToDerivative
  right_inv := frameToDerivative_derivativeToFrame

/-- Fold one ordinary polynomial node into the independently defined syntax. -/
def assemble {sort : signature.Srt}
    (node : (polynomial signature).Obj (Term signature) sort) : Term signature sort := by
  rcases node with ⟨⟨constructor, rfl⟩, children⟩
  exact .node constructor children

/-- The derivative's fill agrees with the original constructor-context action. -/
theorem assemble_fillDerivative {source target : signature.Srt}
    (frame : Frame signature source target) (value : Term signature source) :
    assemble (fillDerivative (frameToDerivative frame) value) = Frame.fill frame value := by
  cases frame
  rfl

/-- The polynomial/free-tree decoder also commutes with a frame fill. -/
theorem toFree_fill {source target : signature.Srt}
    (frame : Frame signature source target) (value : Term signature source) :
    toFree (Frame.fill frame value) =
      let node := fillDerivative
        ((derivative signature).map (fun _ => toFree) (frameToDerivative frame)) (toFree value)
      IPFunctor.IFreeM.liftBind node.1 node.2 := by
  cases frame with
  | slot constructor position siblings =>
    simp only [Frame.fill, toFree, fillDerivative, frameToDerivative, IPFunctor.map, polynomial]
    congr 1
    funext other
    by_cases same : other = position
    · subst other; simp
    · simp [same]

/-! ## Dissections and a retained argument frontier

The constructor's positional order splits siblings into completed and pending
families. They may have different representations at each sort. This is a
structural traversal order, not permission to evaluate a language operand.
-/

/-- A sorted one-hole context with completed siblings before the hole and
pending siblings after it. The selected occurrence has no stored payload. -/
structure Dissection (signature : Signature.{u, v})
    (Done Pending : signature.Srt → Type*) (source target : signature.Srt) where
  head : DerivativeHead signature source target
  before : (other : Fin (signature.arity head.constructor)) →
    other.val < head.position.val → Done (signature.input head.constructor other)
  after : (other : Fin (signature.arity head.constructor)) →
    head.position.val < other.val → Pending (signature.input head.constructor other)

namespace Dissection

variable {Done Pending : signature.Srt → Type*} {source target : signature.Srt}

/-- Completed and pending sides can change representation independently. -/
def map {Done' Pending' : signature.Srt → Type*}
    (done : (sort : signature.Srt) → Done sort → Done' sort)
    (pending : (sort : signature.Srt) → Pending sort → Pending' sort)
    (frame : Dissection signature Done Pending source target) :
    Dissection signature Done' Pending' source target where
  head := frame.head
  before other earlier := done _ (frame.before other earlier)
  after other later := pending _ (frame.after other later)

@[simp] theorem map_id (frame : Dissection signature Done Pending source target) :
    frame.map (fun _ value => value) (fun _ value => value) = frame := by
  cases frame
  rfl

theorem map_comp {Done' Pending' Done'' Pending'' : signature.Srt → Type*}
    (firstDone : (sort : signature.Srt) → Done sort → Done' sort)
    (firstPending : (sort : signature.Srt) → Pending sort → Pending' sort)
    (secondDone : (sort : signature.Srt) → Done' sort → Done'' sort)
    (secondPending : (sort : signature.Srt) → Pending' sort → Pending'' sort)
    (frame : Dissection signature Done Pending source target) :
    (frame.map firstDone firstPending).map secondDone secondPending =
      frame.map (fun sort value => secondDone sort (firstDone sort value))
        (fun sort value => secondPending sort (firstPending sort value)) := rfl

/-- Interpret completed and pending payloads independently, preserving the
selected constructor occurrence. No interpretation is applied to the hole. -/
def toDerivative {Common : signature.Srt → Type*}
    (done : (sort : signature.Srt) → Done sort → Common sort)
    (pending : (sort : signature.Srt) → Pending sort → Common sort)
    (frame : Dissection signature Done Pending source target) :
    (derivative signature).Obj Common (source, target) :=
  ⟨frame.head, fun other =>
    if left : other.val.val < frame.head.position.val then
      done _ (frame.before other.val left)
    else pending _ (frame.after other.val (by
      have different : other.val.val ≠ frame.head.position.val :=
        fun equal => other.property (Fin.ext equal)
      omega))⟩

/-- The diagonal of a dissection is an ordinary derivative. -/
def ofDerivative {Common : signature.Srt → Type*}
    (frame : (derivative signature).Obj Common (source, target)) :
    Dissection signature Common Common source target where
  head := frame.1
  before other before := frame.2 ⟨other, fun equal => by
    subst other
    exact (Nat.lt_irrefl _ before)⟩
  after other after := frame.2 ⟨other, fun equal => by
    subst other
    exact (Nat.lt_irrefl _ after)⟩

theorem toDerivative_ofDerivative {Common : signature.Srt → Type*}
    (frame : (derivative signature).Obj Common (source, target)) :
    toDerivative (fun _ value => value) (fun _ value => value)
        (ofDerivative frame) = frame := by
  rcases frame with ⟨head, siblings⟩
  apply congrArg (Sigma.mk head)
  funext other
  rcases other with ⟨other, different⟩
  dsimp only [ofDerivative]
  by_cases left : other.val < head.position.val
  · simp [left]
  · simp [left]

theorem ofDerivative_toDerivative {Common : signature.Srt → Type*}
    (frame : Dissection signature Common Common source target) :
    ofDerivative (toDerivative (fun _ value => value) (fun _ value => value) frame) =
      frame := by
  rcases frame with ⟨head, before, after⟩
  dsimp only [ofDerivative, toDerivative]
  congr 1
  · funext other left
    simp [left]
  · funext other right
    have notLeft : ¬ other.val < head.position.val := by omega
    simp [notLeft]

/-- Both representations retain precisely the same hole and sibling data. -/
def diagonalEquiv (Common : signature.Srt → Type*) (source target : signature.Srt) :
    Dissection signature Common Common source target ≃
      (derivative signature).Obj Common (source, target) where
  toFun := toDerivative (fun _ value => value) (fun _ value => value)
  invFun := ofDerivative
  left_inv := ofDerivative_toDerivative
  right_inv := toDerivative_ofDerivative

end Dissection

/-- A cut between already processed and pending constructor arguments.
Every position occurs on exactly one side; the final cut has no pending input.
This functional carrier specifies slots, not their native memory layout. -/
structure ArgumentCursor (signature : Signature.{u, v})
    (Done Pending : signature.Srt → Type*) (constructor : signature.Constructor) where
  position : Fin (signature.arity constructor + 1)
  before : (other : Fin (signature.arity constructor)) →
    other.val < position.val → Done (signature.input constructor other)
  pending : (other : Fin (signature.arity constructor)) →
    position.val ≤ other.val → Pending (signature.input constructor other)

namespace ArgumentCursor

variable {Done Pending : signature.Srt → Type*} {constructor : signature.Constructor}

def start (arguments : (position : Fin (signature.arity constructor)) →
    Pending (signature.input constructor position)) :
    ArgumentCursor signature Done Pending constructor where
  position := ⟨0, Nat.zero_lt_succ _⟩
  before _ impossible := False.elim (Nat.not_lt_zero _ impossible)
  pending other _ := arguments other

/-- Focus the next actual occurrence. The frame keeps the exact input sort,
which may include a binder's extended scope. -/
def focus (cursor : ArgumentCursor signature Done Pending constructor)
    (more : cursor.position.val < signature.arity constructor) :
    Dissection signature Done Pending
      (signature.input constructor ⟨cursor.position.val, more⟩)
      (signature.output constructor) where
  head := ⟨constructor, ⟨cursor.position.val, more⟩, rfl, rfl⟩
  before := cursor.before
  after other later := cursor.pending other (Nat.le_of_lt later)

def current (cursor : ArgumentCursor signature Done Pending constructor)
    (more : cursor.position.val < signature.arity constructor) :
    Pending (signature.input constructor ⟨cursor.position.val, more⟩) :=
  cursor.pending ⟨cursor.position.val, more⟩ (Nat.le_refl _)

/-- Accept one reply into its own slot and move the cut once. Earlier replies
and later source payloads are retained without invoking their processors. -/
def accept (cursor : ArgumentCursor signature Done Pending constructor)
    (more : cursor.position.val < signature.arity constructor)
    (value : Done (signature.input constructor ⟨cursor.position.val, more⟩)) :
    ArgumentCursor signature Done Pending constructor where
  position := ⟨cursor.position.val + 1, Nat.add_lt_add_right more 1⟩
  before other earlier := if previous : other.val < cursor.position.val then
    cursor.before other previous
  else (show (⟨cursor.position.val, more⟩ : Fin (signature.arity constructor)) = other from
    Fin.ext (by
      change other.val < cursor.position.val + 1 at earlier
      change cursor.position.val = other.val
      omega)) ▸ value
  pending other later := cursor.pending other (by
    change cursor.position.val + 1 ≤ other.val at later
    omega)

/-- The reply is stored at the selected occurrence, without interpreting it. -/
theorem accept_current (cursor : ArgumentCursor signature Done Pending constructor)
    (more : cursor.position.val < signature.arity constructor)
    (value : Done (signature.input constructor ⟨cursor.position.val, more⟩)) :
    (cursor.accept more value).before ⟨cursor.position.val, more⟩
        (by exact Nat.lt_succ_self _) = value := by
  simp [accept]

theorem accept_before (cursor : ArgumentCursor signature Done Pending constructor)
    (more : cursor.position.val < signature.arity constructor)
    (value : Done (signature.input constructor ⟨cursor.position.val, more⟩))
    (other : Fin (signature.arity constructor)) (earlier : other.val < cursor.position.val) :
    (cursor.accept more value).before other (by
        change other.val < cursor.position.val + 1
        omega) = cursor.before other earlier := by
  simp [accept, earlier]

theorem accept_pending (cursor : ArgumentCursor signature Done Pending constructor)
    (more : cursor.position.val < signature.arity constructor)
    (value : Done (signature.input constructor ⟨cursor.position.val, more⟩))
    (other : Fin (signature.arity constructor)) (later : cursor.position.val + 1 ≤ other.val) :
    (cursor.accept more value).pending other later = cursor.pending other (by omega) := rfl

/-- Read a completed cursor without processing any child again. -/
def finish (cursor : ArgumentCursor signature Done Pending constructor)
    (complete : cursor.position.val = signature.arity constructor) :
    (other : Fin (signature.arity constructor)) → Done (signature.input constructor other) :=
  fun other => cursor.before other (by rw [complete]; exact other.isLt)

/-- Independent full result represented by a partial cursor, relative to an
explicit pure child map. This map is used only for pending positions. -/
def denote (process : (sort : signature.Srt) → Pending sort → Done sort)
    (cursor : ArgumentCursor signature Done Pending constructor) :
    (other : Fin (signature.arity constructor)) → Done (signature.input constructor other) :=
  fun other => if previous : other.val < cursor.position.val then
    cursor.before other previous
  else process _ (cursor.pending other (Nat.le_of_not_gt previous))

theorem denote_start (process : (sort : signature.Srt) → Pending sort → Done sort)
    (arguments : (position : Fin (signature.arity constructor)) →
      Pending (signature.input constructor position)) :
    denote process (start arguments) = fun other => process _ (arguments other) := by
  funext other
  simp [denote, start]

theorem denote_accept (process : (sort : signature.Srt) → Pending sort → Done sort)
    (cursor : ArgumentCursor signature Done Pending constructor)
    (more : cursor.position.val < signature.arity constructor) :
    denote process (cursor.accept more (process _ (cursor.current more))) =
      denote process cursor := by
  funext other
  by_cases before : other.val < cursor.position.val
  · have earlier : other.val < cursor.position.val + 1 := by omega
    simp [denote, accept, before, earlier]
  · by_cases same : other.val = cursor.position.val
    · have equal : other = ⟨cursor.position.val, more⟩ := Fin.ext same
      subst other
      simp [denote, accept, current]
    · have later : ¬ other.val < cursor.position.val + 1 := by omega
      simp [denote, accept, before, later]

theorem denote_finish (process : (sort : signature.Srt) → Pending sort → Done sort)
    (cursor : ArgumentCursor signature Done Pending constructor)
    (complete : cursor.position.val = signature.arity constructor) :
    cursor.finish complete = cursor.denote process := by
  funext other
  have before : other.val < cursor.position.val := by rw [complete]; exact other.isLt
  simp [finish, denote, before]

/-- The mixed frame and active pending child reconstruct the same full
polynomial node as the cursor decoder. -/
theorem focus_fill (process : (sort : signature.Srt) → Pending sort → Done sort)
    (cursor : ArgumentCursor signature Done Pending constructor)
    (more : cursor.position.val < signature.arity constructor) :
    fillDerivative ((cursor.focus more).toDerivative (fun _ value => value) process)
        (process _ (cursor.current more)) =
      (⟨⟨constructor, rfl⟩, cursor.denote process⟩ :
        (polynomial signature).Obj Done (signature.output constructor)) := by
  dsimp only [fillDerivative, focus, Dissection.toDerivative]
  congr 1
  funext other
  dsimp only [id, polynomial, derivative] at other ⊢
  by_cases same : other = ⟨cursor.position.val, more⟩
  · subst other
    simp [denote, current]
  · by_cases before : other.val < cursor.position.val
    · simp [denote, same, before]
    · simp [denote, same, before]

end ArgumentCursor

end SortedSignature

end Mettapedia.GSLT.Poly
