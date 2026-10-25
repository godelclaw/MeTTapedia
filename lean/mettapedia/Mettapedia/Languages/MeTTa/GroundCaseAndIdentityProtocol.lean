import Mathlib.Data.List.Basic

/-!
# Ground constructor cases and identity type protocols

This module isolates two compilation laws used by the shared MeTTa evaluator.

* A ground algebraic value can be eliminated by inspecting its root
  constructor and borrowing its fields.  Open values, repeated-variable
  equality, ownership, and logical-list equivalence are separate admission
  obligations of the runtime.
* A type protocol with one signature and no rejecting guard may erase the
  singleton dispatch.  Raw versus translated argument preparation remains,
  as does the body observation, including its effect trace.

The optimality result is deliberately about the opaque-root query model.  It
does not claim that parsing, evaluation, allocation, or the surrounding
scheduler has zero cost.
-/

namespace Mettapedia.Languages.MeTTa.GroundCaseAndIdentityProtocol

/-! ## Ground constructor elimination -/

inductive GroundValue (Tag Field : Type) where
  | atom (value : Field)
  | node (tag : Tag) (fields : List Field)
  deriving DecidableEq

def directFields [DecidableEq Tag] (wanted : Tag) :
    GroundValue Tag Field → Option (List Field)
  | .atom _ => none
  | .node actual fields => if actual = wanted then some fields else none

/-- Independent relational specification of a successful constructor arm. -/
def RootMatches (wanted : Tag) (value : GroundValue Tag Field)
    (fields : List Field) : Prop :=
  value = .node wanted fields

theorem directFields_iff [DecidableEq Tag] (wanted : Tag)
    (value : GroundValue Tag Field) (fields : List Field) :
    directFields wanted value = some fields ↔ RootMatches wanted value fields := by
  cases value with
  | atom value => simp [directFields, RootMatches]
  | node actual actualFields =>
      simp only [directFields, RootMatches]
      split <;> rename_i h
      · subst actual
        simp
      · constructor
        · intro impossible
          simp at impossible
        · intro equality
          cases equality
          exact (h rfl).elim

/-- Programs in the opaque-root model either return without reading the
value, or inspect its root once. -/
inductive RootProgram (Tag Field : Type) where
  | constant (answer : Bool)
  | inspect (decision : GroundValue Tag Field → Bool)

def RootProgram.run : RootProgram Tag Field → GroundValue Tag Field → Bool
  | .constant answer, _ => answer
  | .inspect decision, value => decision value

def RootProgram.rootReads : RootProgram Tag Field → Nat
  | .constant _ => 0
  | .inspect _ => 1

def recognizes [DecidableEq Tag] (wanted : Tag)
    (value : GroundValue Tag Field) : Bool :=
  (directFields wanted value).isSome

def RootProgram.Correct [DecidableEq Tag] (wanted : Tag)
    (program : RootProgram Tag Field) : Prop :=
  ∀ value, program.run value = recognizes wanted value

def directRoot [DecidableEq Tag] (wanted : Tag) : RootProgram Tag Field :=
  .inspect (recognizes wanted)

theorem directRoot_correct [DecidableEq Tag] (wanted : Tag) :
    (directRoot (Field := Field) wanted).Correct wanted := by
  intro value
  rfl

theorem directRoot_one_read [DecidableEq Tag] (wanted : Tag) :
    (directRoot (Field := Field) wanted).rootReads = 1 := rfl

/-- A correct recognizer cannot use zero root reads: a matching node and an
atom require different answers. -/
theorem correct_rootReads_lower_bound [DecidableEq Tag]
    (wanted : Tag) (field : Field) (program : RootProgram Tag Field)
    (correct : program.Correct wanted) :
    1 ≤ program.rootReads := by
  cases program with
  | inspect decision => simp [RootProgram.rootReads]
  | constant answer =>
      have accepts := correct (.node wanted [])
      have rejects := correct (.atom field)
      simp [RootProgram.run, recognizes, directFields] at accepts rejects
      cases answer <;> simp_all

theorem directRoot_optimal [DecidableEq Tag]
    (wanted : Tag) (field : Field) :
    (directRoot (Field := Field) wanted).Correct wanted ∧
      (directRoot (Field := Field) wanted).rootReads = 1 ∧
      ∀ program : RootProgram Tag Field, program.Correct wanted →
        (directRoot (Field := Field) wanted).rootReads ≤ program.rootReads := by
  refine ⟨directRoot_correct wanted, directRoot_one_read wanted, ?_⟩
  intro program correct
  rw [directRoot_one_read]
  exact correct_rootReads_lower_bound wanted field program correct

/-! ## Groundness licenses borrowed descendants -/

/-- A small model of the runtime boundary: cells may dereference through a
live environment, while atoms and algebraic nodes are immutable values. -/
inductive AlgebraicTerm (Tag Leaf : Type) where
  | cell (index : Nat)
  | atom (value : Leaf)
  | node (tag : Tag) (children : List (AlgebraicTerm Tag Leaf))

def AlgebraicTerm.Ground : AlgebraicTerm Tag Leaf → Prop
  | .cell _ => False
  | .atom _ => True
  | .node _ children => ∀ child ∈ children, child.Ground

/-- Only a cell consults the live environment. -/
def derefRoot (environment : Nat → AlgebraicTerm Tag Leaf) :
    AlgebraicTerm Tag Leaf → AlgebraicTerm Tag Leaf
  | .cell index => environment index
  | term => term

inductive AlgebraicTerm.OccursCell (wanted : Nat) :
    AlgebraicTerm Tag Leaf → Prop where
  | here : OccursCell wanted (.cell wanted)
  | child {tag children child} : child ∈ children →
      OccursCell wanted child → OccursCell wanted (.node tag children)

/-- Once whole-term groundness has been established, every descendant of an
algebraic node is ground too. -/
theorem AlgebraicTerm.ground_child
    {tag : Tag} {children : List (AlgebraicTerm Tag Leaf)}
    {child : AlgebraicTerm Tag Leaf}
    (ground : (AlgebraicTerm.node tag children).Ground)
    (member : child ∈ children) : child.Ground := by
  have allGround : ∀ item ∈ children, item.Ground := by
    simpa [AlgebraicTerm.Ground] using ground
  exact allGround child member

/-- Dereferencing a ground node is the identity.  Together with
`ground_child`, one root check licenses borrowed descent without repeating a
cell lookup at every child. -/
theorem derefRoot_eq_self_of_ground
    (environment : Nat → AlgebraicTerm Tag Leaf)
    (term : AlgebraicTerm Tag Leaf) (ground : term.Ground) :
    derefRoot environment term = term := by
  cases term <;> simp_all [AlgebraicTerm.Ground, derefRoot]

/-- A ground value cannot contain the cell being bound.  A unifier may skip
its occurs walk precisely on this certified branch. -/
theorem AlgebraicTerm.not_occursCell_of_ground
    (wanted : Nat) (term : AlgebraicTerm Tag Leaf)
    (ground : term.Ground) : ¬term.OccursCell wanted := by
  intro occurs
  induction occurs with
  | here => simp [AlgebraicTerm.Ground] at ground
  | child member childOccurs childIH =>
      exact childIH (AlgebraicTerm.ground_child ground member)

/-- Positive control: nested algebraic data is ground. -/
example :
    (AlgebraicTerm.node "Cons"
      [AlgebraicTerm.atom (1 : Nat),
       AlgebraicTerm.node "Nil" []]).Ground := by
  simp [AlgebraicTerm.Ground]

/-- Negative control: a nested live cell prevents the optimization. -/
example :
    ¬(AlgebraicTerm.node "Cons"
      [AlgebraicTerm.cell 0,
       AlgebraicTerm.node "Nil" []] :
      AlgebraicTerm String Nat).Ground := by
  simp [AlgebraicTerm.Ground]

/-! ## Exact algebraic length folds -/

inductive Spine (Element : Type) where
  | nil
  | cons (head : Element) (tail : Spine Element)

def Spine.length : Spine Element → Nat
  | .nil => 0
  | .cons _ tail => tail.length + 1

/-- Reusing an input binder for its case tail adds a real equality
constraint. A finite spine cannot equal its own proper tail, so this is not
the ordinary structural-length recurrence. -/
theorem Spine.cons_ne_tail (head : Element) (tail : Spine Element) :
    Spine.cons head tail ≠ tail := by
  intro equal
  have lengths := congrArg Spine.length equal
  simp only [Spine.length] at lengths
  exact Nat.add_one_ne_self tail.length lengths

/-- The direct loop reads one constructor root per element and the final nil
root. -/
def Spine.rootReads : Spine Element → Nat
  | .nil => 1
  | .cons _ tail => tail.rootReads + 1

def Spine.ofLength : Nat → Spine Unit
  | 0 => .nil
  | n + 1 => .cons () (ofLength n)

/-- What a sequential observer knows after at most `fuel` constructor-root
reads. -/
def Spine.observedPrefix : Nat → Spine Element → List Bool
  | 0, _ => []
  | _ + 1, .nil => [false]
  | fuel + 1, .cons _ tail => true :: observedPrefix fuel tail

theorem Spine.length_ofLength (n : Nat) : (ofLength n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ofLength, length, ih]

theorem Spine.rootReads_ofLength (n : Nat) :
    (ofLength n).rootReads = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ofLength, rootReads, ih, Nat.add_assoc]

/-- After only `n` root reads, a spine of length `n` is indistinguishable
from one of length `n+1`; their exact answers differ.  Thus the final nil
inspection is necessary, and `rootReads_ofLength` attains this lower bound. -/
theorem Spine.length_prefix_adversary (n : Nat) :
    observedPrefix n (ofLength n) =
        observedPrefix n (ofLength (n + 1)) ∧
      (ofLength n).length ≠ (ofLength (n + 1)).length := by
  constructor
  · induction n with
    | zero => rfl
    | succ n ih => simp [ofLength, observedPrefix, ih]
  · simp [length_ofLength]

/-- Negative control for the source recognizer: replacing successor by two
does not implement structural length. -/
def Spine.lengthByTwo : Spine Element → Nat
  | .nil => 0
  | .cons _ tail => tail.lengthByTwo + 2

example : (Spine.ofLength 1).lengthByTwo ≠ (Spine.ofLength 1).length := by
  decide

def Spine.append : Spine Element → Spine Element → Spine Element
  | .nil, right => right
  | .cons head tail, right => .cons head (tail.append right)

/-- A persistent append derivation records exactly the constructor nodes it
allocates while sharing the right operand. -/
inductive Spine.SharesAppend :
    Spine Element → Spine Element → Spine Element → Nat → Prop where
  | nil (right) : SharesAppend .nil right right 0
  | cons (head) {left right result cost} :
      SharesAppend left right result cost →
      SharesAppend (.cons head left) right (.cons head result) (cost + 1)

theorem Spine.sharesAppend_result
    {left right result : Spine Element} {cost : Nat}
    (derivation : SharesAppend left right result cost) :
    result = left.append right := by
  induction derivation with
  | nil => rfl
  | cons head derivation ih => simp [append, ih]

/-- Every persistent constructor derivation preserving the left prefix and
sharing the right operand allocates exactly one node per left element.  The
direct append attains that bound. -/
theorem Spine.sharesAppend_cost
    {left right result : Spine Element} {cost : Nat}
    (derivation : SharesAppend left right result cost) :
    cost = left.length := by
  induction derivation with
  | nil => rfl
  | cons head derivation ih => simp [length, ih]

theorem Spine.direct_append_certificate (left right : Spine Element) :
    SharesAppend left right (left.append right) left.length := by
  induction left with
  | nil => exact .nil right
  | cons head tail ih => exact .cons head ih

def Spine.map (project : Input → Output) : Spine Input → Spine Output
  | .nil => .nil
  | .cons head tail => .cons (project head) (tail.map project)

inductive Spine.SharesMap (project : Input → Output) :
    Spine Input → Spine Output → Nat → Prop where
  | nil : SharesMap project .nil .nil 0
  | cons (head) {tail result cost} :
      SharesMap project tail result cost →
      SharesMap project (.cons head tail)
        (.cons (project head) result) (cost + 1)

theorem Spine.sharesMap_result
    {project : Input → Output} {source : Spine Input}
    {result : Spine Output} {cost : Nat}
    (derivation : SharesMap project source result cost) :
    result = source.map project := by
  induction derivation with
  | nil => rfl
  | cons head derivation ih => simp [map, ih]

/-- Projection-map has the same tight persistent-spine cost: inspect and
rebuild one constructor per source element. -/
theorem Spine.sharesMap_cost
    {project : Input → Output} {source : Spine Input}
    {result : Spine Output} {cost : Nat}
    (derivation : SharesMap project source result cost) :
    cost = source.length := by
  induction derivation with
  | nil => rfl
  | cons head derivation ih => simp [length, ih]

theorem Spine.direct_map_certificate
    (project : Input → Output) (source : Spine Input) :
    SharesMap project source (source.map project) source.length := by
  induction source with
  | nil => exact .nil
  | cons head tail ih => exact .cons head ih

def Spine.any (predicate : Element → Bool) : Spine Element → Bool
  | .nil => false
  | .cons head tail => predicate head || tail.any predicate

def Spine.anyRootReads (predicate : Element → Bool) : Spine Element → Nat
  | .nil => 1
  | .cons head tail =>
      if predicate head then 1 else tail.anyRootReads predicate + 1

inductive Spine.ShortCircuitAny (predicate : Element → Bool) :
    Spine Element → Bool → Nat → Prop where
  | nil : ShortCircuitAny predicate .nil false 1
  | hit (head tail) : predicate head = true →
      ShortCircuitAny predicate (.cons head tail) true 1
  | miss (head) {tail answer cost} : predicate head = false →
      ShortCircuitAny predicate tail answer cost →
      ShortCircuitAny predicate (.cons head tail) answer (cost + 1)

theorem Spine.shortCircuitAny_result
    {predicate : Element → Bool} {source : Spine Element}
    {answer : Bool} {cost : Nat}
    (derivation : ShortCircuitAny predicate source answer cost) :
    answer = source.any predicate := by
  induction derivation with
  | nil => rfl
  | hit head tail yes => simp [any, yes]
  | miss head no derivation ih => simp [any, no, ih]

/-- The admitted contains loop performs exactly the observations required by
short-circuit evaluation: through the first hit, or through the final nil. -/
theorem Spine.shortCircuitAny_cost
    {predicate : Element → Bool} {source : Spine Element}
    {answer : Bool} {cost : Nat}
    (derivation : ShortCircuitAny predicate source answer cost) :
    cost = source.anyRootReads predicate := by
  induction derivation with
  | nil => rfl
  | hit head tail yes => simp [anyRootReads, yes]
  | miss head no derivation ih => simp [anyRootReads, no, ih]

/-! ## Guard-free singleton protocols -/

inductive Demand where
  | raw
  | translated
  deriving DecidableEq

structure Contract (Value : Type) where
  demands : List Demand
  accepts : List Value → Bool

structure Observation (Value Effect : Type) where
  value : Value
  effects : List Effect
  deriving DecidableEq

def prepareArgument (translate : Value → Value) : Demand → Value → Value
  | .raw, value => value
  | .translated, value => translate value

def prepare (translate : Value → Value) (contract : Contract Value)
    (arguments : List Value) : List Value :=
  List.zipWith (prepareArgument translate) contract.demands arguments

/-- The source protocol: enumerate signatures in order, retain each accepting
branch, prepare according to that signature, and run its body once. -/
def dispatch (translate : Value → Value)
    (catalog : List (Contract Value)) (arguments : List Value)
    (body : List Value → Observation Result Effect) :
    List (Observation Result Effect) :=
  catalog.flatMap fun contract =>
    if contract.accepts arguments then
      [body (prepare translate contract arguments)]
    else
      []

def executeDirect (translate : Value → Value) (contract : Contract Value)
    (arguments : List Value)
    (body : List Value → Observation Result Effect) :
    Observation Result Effect :=
  body (prepare translate contract arguments)

/-- Erasing a guard-free singleton dispatch preserves the value and the full
effect trace.  Argument preparation is shared by the two sides. -/
theorem singleton_identity_erasure
    (translate : Value → Value) (contract : Contract Value)
    (arguments : List Value)
    (body : List Value → Observation Result Effect)
    (accepts : contract.accepts arguments = true) :
    dispatch translate [contract] arguments body =
      [executeDirect translate contract arguments body] := by
  simp [dispatch, executeDirect, accepts]

theorem raw_preparation (translate : Value → Value) (value : Value) :
    prepareArgument translate .raw value = value := rfl

theorem translated_preparation (translate : Value → Value) (value : Value) :
    prepareArgument translate .translated value = translate value := rfl

/-- A length recurrence with `branches` accepting signatures at every
recursive call, retaining their answer occurrences. -/
def recursiveLengthAnswers (branches : Nat) : Nat → List Nat
  | 0 => List.replicate branches 0
  | depth + 1 =>
      (List.replicate branches
        ((recursiveLengthAnswers branches depth).map Nat.succ)).flatten

theorem recursiveLengthAnswers_count (branches depth : Nat) :
    (recursiveLengthAnswers branches depth).length = branches ^ (depth + 1) := by
  induction depth with
  | zero => simp [recursiveLengthAnswers]
  | succ depth ih =>
      simp [recursiveLengthAnswers, List.length_flatten, ih,
            Nat.pow_succ, Nat.mul_comm]

/-- With exactly one accepting protocol at every recursive entry, the
ordinary answer family is precisely the direct fold's singleton result. -/
theorem recursiveLengthAnswers_one (depth : Nat) :
    recursiveLengthAnswers 1 depth = [depth] := by
  induction depth with
  | zero => rfl
  | succ depth ih => simp [recursiveLengthAnswers, ih]

/-- A protocol which refuses the recursive entry has no answer, including
at the base case. Source-body shape cannot justify replacing that refusal. -/
theorem recursiveLengthAnswers_zero (depth : Nat) :
    recursiveLengthAnswers 0 depth = [] := by
  cases depth <;> simp [recursiveLengthAnswers]

/-- An outer dispatch alone cannot replace dispatch at every recursive
entry: two signatures on a two-node spine produce eight occurrences. -/
example : recursiveLengthAnswers 2 2 = List.replicate 8 2 := by decide

/-- A rejecting guard cannot be erased. -/
example :
    let reject : Contract Nat := ⟨[.raw], fun _ => false⟩
    dispatch id [reject] [7] (fun values => ⟨values.length, ["ran"]⟩) = [] := by
  decide

/-- An overload wrapper is observable through multiplicity even when both
signatures accept and compute the same answer. -/
example :
    let accept : Contract Nat := ⟨[.raw], fun _ => true⟩
    (dispatch id [accept, accept] [7]
      (fun values => ⟨values.length, ["ran"]⟩)).length = 2 := by
  decide

def Catalog (Revision Value : Type) := Revision → List (Contract Value)

/-- Erasure is revision-scoped: the captured catalog must still be the same
singleton contract at the revision where the call runs. -/
theorem revision_scoped_erasure
    (catalog : Catalog Revision Value) (revision : Revision)
    (translate : Value → Value) (contract : Contract Value)
    (arguments : List Value)
    (body : List Value → Observation Result Effect)
    (current : catalog revision = [contract])
    (accepts : contract.accepts arguments = true) :
    dispatch translate (catalog revision) arguments body =
      [executeDirect translate contract arguments body] := by
  rw [current]
  exact singleton_identity_erasure translate contract arguments body accepts

/-- Reusing an old erasure after a catalog update can invent an answer. -/
example :
    let accept : Contract Nat := ⟨[.raw], fun _ => true⟩
    let reject : Contract Nat := ⟨[.raw], fun _ => false⟩
    let catalog : Catalog Bool Nat := fun revision =>
      if revision then [reject] else [accept]
    dispatch id (catalog true) [7]
        (fun values => ⟨values.length, ["ran"]⟩) ≠
      [executeDirect id accept [7]
        (fun values => ⟨values.length, ["ran"]⟩)] := by
  decide

end Mettapedia.Languages.MeTTa.GroundCaseAndIdentityProtocol
