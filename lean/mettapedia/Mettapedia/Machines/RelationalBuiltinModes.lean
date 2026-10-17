import Mathlib.Data.List.Basic
import Mettapedia.Machines.AnswerCardinality
import Mettapedia.Machines.OrderedDependencyStore
import Mettapedia.Machines.ReadOnlyQuery

/-!
# Binding-sensitive modes for finite relational primitives

A parameter's carrier type does not say whether its value has been bound.
Reading an unbound input enumerates the primitive's finite domain and writes
the choice into a branch-local environment. Reading that variable again uses
the same choice. An inductive relation independently specifies these reads;
the list implementation preserves their witnesses and answer occurrences.

This is a finite-domain operational model, not native C adequacy. It separates
the hypotheses needed to replace relational enumeration by a functional call:
both inputs are bound, and the primitive's definition has no extra equations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RelationalBuiltinModes

universe u v w

inductive Input (Var : Type u) (Value : Type v) where
  | literal (value : Value)
  | var (name : Var)
  deriving DecidableEq

abbrev Store (Var : Type u) (Value : Type v) := Var → Option Value

variable {Var : Type u} {Value : Type v} {Result : Type w}
variable [DecidableEq Var]

def resolve (store : Store Var Value) : Input Var Value → Option Value
  | .literal value => some value
  | .var name => store name

def bind (store : Store Var Value) (name : Var) (value : Value) : Store Var Value :=
  fun query => if query = name then some value else store query

inductive Read (domain : List Value) (store : Store Var Value) :
    Input Var Value → Value → Store Var Value → Prop where
  | literal (value : Value) : Read domain store (.literal value) value store
  | bound (name : Var) (value : Value) (known : store name = some value) :
      Read domain store (.var name) value store
  | fresh (name : Var) (value : Value) (unknown : store name = none)
      (member : value ∈ domain) :
      Read domain store (.var name) value (bind store name value)

def read (domain : List Value) (store : Store Var Value) :
    Input Var Value → List (Value × Store Var Value)
  | .literal value => [(value, store)]
  | .var name => match store name with
      | some value => [(value, store)]
      | none => domain.map (fun value => (value, bind store name value))

/-- Enumeration is both sound and complete for the independent read rules. -/
theorem mem_read_iff (domain : List Value) (store : Store Var Value)
    (input : Input Var Value) (value : Value) (next : Store Var Value) :
    (value, next) ∈ read domain store input ↔ Read domain store input value next := by
  constructor
  · intro member
    cases input with
    | literal literal =>
        simp only [read, List.mem_singleton, Prod.mk.injEq] at member
        rcases member with ⟨rfl, rfl⟩
        exact .literal _
    | var name =>
        cases known : store name with
        | none =>
            simp only [read, known, List.mem_map, Prod.mk.injEq] at member
            obtain ⟨chosen, inDomain, equality⟩ := member
            rcases equality with ⟨rfl, rfl⟩
            exact .fresh _ _ known inDomain
        | some chosen =>
            simp only [read, known, List.mem_singleton, Prod.mk.injEq] at member
            rcases member with ⟨rfl, rfl⟩
            exact .bound _ _ known
  · intro derivation
    cases derivation with
    | literal => simp [read]
    | bound name value known => simp [read, known]
    | fresh name value unknown member =>
        simp only [read, unknown, List.mem_map]
        exact ⟨value, member, rfl⟩

theorem read_of_bound (domain : List Value) (store : Store Var Value)
    (input : Input Var Value) (value : Value)
    (known : resolve store input = some value) :
    read domain store input = [(value, store)] := by
  cases input with
  | literal literal =>
      simp only [resolve, Option.some.injEq] at known
      subst literal
      rfl
  | var name =>
      change store name = some value at known
      simp [read, known]

/-- A read establishes a bound value in the branch that carries its witness. -/
theorem read_binds {domain : List Value} {store next : Store Var Value}
    {input : Input Var Value} {value : Value}
    (derivation : Read domain store input value next) :
    resolve next input = some value := by
  cases derivation with
  | literal => rfl
  | bound name value known => exact known
  | fresh => simp [resolve, bind]

/-- Choosing a fresh value never redirects a previously bound variable. -/
theorem read_preserves {domain : List Value} {store next : Store Var Value}
    {input : Input Var Value} {value old : Value} {name : Var}
    (derivation : Read domain store input value next)
    (known : store name = some old) : next name = some old := by
  cases derivation with
  | literal => exact known
  | bound => exact known
  | fresh chosen value unknown member =>
      have different : name ≠ chosen := by
        intro equality
        subst name
        simp [unknown] at known
      simp [bind, different, known]

/-- Repeated occurrences of a variable reuse the chosen value; they do not
enumerate an independent Cartesian factor. -/
theorem reread_singleton {domain : List Value} {store next : Store Var Value}
    {input : Input Var Value} {value : Value}
    (derivation : Read domain store input value next) :
    read domain next input = [(value, next)] :=
  read_of_bound domain next input value (read_binds derivation)

structure Answer (Var : Type u) (Value : Type v) (Result : Type w) where
  left : Value
  right : Value
  result : Result
  store : Store Var Value

def binary (domain : List Value) (operation : Value → Value → Result)
    (store : Store Var Value) (left right : Input Var Value) :
    List (Answer Var Value Result) :=
  (read domain store left).flatMap fun first =>
    (read domain first.2 right).map fun second =>
      ⟨first.1, second.1, operation first.1 second.1, second.2⟩

inductive Binary (domain : List Value) (operation : Value → Value → Result)
    (store : Store Var Value) (left right : Input Var Value) :
    Answer Var Value Result → Prop where
  | intro {a b : Value} {middle next : Store Var Value}
      (first : Read domain store left a middle)
      (second : Read domain middle right b next) :
      Binary domain operation store left right ⟨a, b, operation a b, next⟩

theorem mem_binary_iff (domain : List Value) (operation : Value → Value → Result)
    (store : Store Var Value) (left right : Input Var Value)
    (answer : Answer Var Value Result) :
    answer ∈ binary domain operation store left right ↔
      Binary domain operation store left right answer := by
  constructor
  · intro member
    simp only [binary, List.mem_flatMap, List.mem_map] at member
    obtain ⟨⟨a, middle⟩, first, ⟨b, next⟩, second, rfl⟩ := member
    exact .intro ((mem_read_iff ..).mp first) ((mem_read_iff ..).mp second)
  · intro derivation
    cases derivation with
    | @intro a b middle next first second =>
        simp only [binary, List.mem_flatMap, List.mem_map]
        exact ⟨(a, middle), (mem_read_iff ..).mpr first,
          (b, next), (mem_read_iff ..).mpr second, rfl⟩

/-- The fast functional interpretation is exact when both operands are bound. -/
theorem binary_of_bound (domain : List Value) (operation : Value → Value → Result)
    (store : Store Var Value) (left right : Input Var Value) (a b : Value)
    (leftBound : resolve store left = some a)
    (rightBound : resolve store right = some b) :
    binary domain operation store left right = [⟨a, b, operation a b, store⟩] := by
  simp [binary, read_of_bound domain store left a leftBound,
    read_of_bound domain store right b rightBound]

/-- Aliasing preserves the first input's occurrence list exactly, including
order and duplicate domain entries. Membership equivalence alone would not
establish this multiplicity law. -/
theorem binary_repeated_input (domain : List Value)
    (operation : Value → Value → Result) (store : Store Var Value)
    (input : Input Var Value) :
    binary domain operation store input input =
      (read domain store input).map
        (fun first => ⟨first.1, first.1, operation first.1 first.1, first.2⟩) := by
  unfold binary
  rw [List.map_eq_flatMap]
  apply List.flatMap_congr
  intro first member
  rw [reread_singleton ((mem_read_iff ..).mp member)]
  rfl

/-! ## Derived calling modes and checked workers

The operation and domain here are the complete pure primitive meaning. Actual
additional source equations remain in the source result, and prevent builtin-only
specialization. Operand preparation creates only private candidate bindings;
the selected worker publishes the bindings produced by the source relation.
These rules do not authorize effects, concurrency or mutable native cache reuse.
-/

def readCount (domain : List Value) (store : Store Var Value)
    (input : Input Var Value) : Nat :=
  if (resolve store input).isSome then 1 else domain.length

theorem read_length (domain : List Value) (store : Store Var Value)
    (input : Input Var Value) :
    (read domain store input).length = readCount domain store input := by
  cases input with
  | literal value => rfl
  | var name => cases known : store name <;> simp [read, readCount, resolve, known]

def aliases : Input Var Value → Input Var Value → Bool
  | .var first, .var second => decide (first = second)
  | _, _ => false

/-- Reading a different input preserves absence as well as known values. -/
theorem read_other_resolve {domain : List Value} {store next : Store Var Value}
    {left right : Input Var Value} {value : Value}
    (derivation : Read domain store left value next) (distinct : aliases left right = false) :
    resolve next right = resolve store right := by
  cases derivation with
  | literal => rfl
  | bound => rfl
  | fresh name value unknown member =>
      cases right with
      | literal value => rfl
      | var other =>
          have different : other ≠ name := by
            simpa [aliases, eq_comm] using distinct
          simp [resolve, bind, different]

def binaryCount (domain : List Value) (store : Store Var Value)
    (left right : Input Var Value) : Nat :=
  if aliases left right then readCount domain store left
  else readCount domain store left * readCount domain store right

/-- The count is derived from bindings and alias identity. Two occurrences
of a free variable contribute one domain factor, not its square. -/
theorem binary_length (domain : List Value) (operation : Value → Value → Result)
    (store : Store Var Value) (left right : Input Var Value) :
    (binary domain operation store left right).length = binaryCount domain store left right := by
  cases same : aliases left right with
  | true =>
      cases left <;> cases right <;> simp [aliases] at same
      rename_i name other
      subst other
      rw [binary_repeated_input]
      simp [binaryCount, aliases, read_length]
  | false =>
      unfold binary
      rw [List.length_flatMap]
      have lengths :
          (read domain store left).map
            (fun first => ((read domain first.2 right).map
              (fun second => (⟨first.1, second.1, operation first.1 second.1, second.2⟩ :
                Answer Var Value Result))).length) =
          (read domain store left).map (fun _ => readCount domain store right) := by
        apply List.map_congr_left
        intro first member
        simp only [List.length_map, read_length, readCount,
          read_other_resolve ((mem_read_iff ..).mp member) same]
      rw [lengths]
      simp [binaryCount, same, read_length]

def binaryGrade (domain : List Value) (store : Store Var Value)
    (left right : Input Var Value) : AnswerCardinality.Grade :=
  AnswerCardinality.ofCount (binaryCount domain store left right)

theorem binaryGrade_sound (domain : List Value) (operation : Value → Value → Result)
    (store : Store Var Value) (left right : Input Var Value) :
    AnswerCardinality.Allows (binaryGrade domain store left right)
      (binary domain operation store left right).length := by
  rw [binary_length]
  exact AnswerCardinality.ofCount_sound _

/-- Prepare one read without constructing the general occurrence list. -/
def readOne? (domain : List Value) (store : Store Var Value) :
    Input Var Value → Option (Value × Store Var Value)
  | .literal value => some (value, store)
  | .var name => match store name with
    | some value => some (value, store)
    | none => match domain with
      | [value] => some (value, bind store name value)
      | _ => none

theorem readOne_sound (domain : List Value) (store : Store Var Value)
    (input : Input Var Value) (value : Value) (next : Store Var Value)
    (prepared : readOne? domain store input = some (value, next)) :
    read domain store input = [(value, next)] := by
  cases input with
  | literal literal =>
      simp only [readOne?, Option.some.injEq, Prod.mk.injEq] at prepared
      rcases prepared with ⟨rfl, rfl⟩
      rfl
  | var name =>
      cases known : store name with
      | some chosen =>
          simp only [readOne?, known, Option.some.injEq, Prod.mk.injEq] at prepared
          rcases prepared with ⟨rfl, rfl⟩
          simp [read, known]
      | none =>
          cases domain with
          | nil => simp [readOne?, known] at prepared
          | cons chosen rest =>
              cases rest with
              | cons _ _ => simp [readOne?, known] at prepared
              | nil =>
                  simp only [readOne?, known, Option.some.injEq, Prod.mk.injEq] at prepared
                  rcases prepared with ⟨rfl, rfl⟩
                  simp [read, known]

structure Prepared (Var : Type u) (Value : Type v) where
  left : Value
  right : Value
  middle : Store Var Value
  store : Store Var Value

def prepareBinary? (domain : List Value) (store : Store Var Value)
    (left right : Input Var Value) : Option (Prepared Var Value) :=
  match readOne? domain store left with
  | none => none
  | some first => match readOne? domain first.2 right with
    | none => none
    | some second => some ⟨first.1, second.1, first.2, second.2⟩

/-- The direct worker computes from its prepared operands and retained bindings. -/
def direct (operation : Value → Value → Result) (prepared : Prepared Var Value) :
    Answer Var Value Result :=
  ⟨prepared.left, prepared.right, operation prepared.left prepared.right, prepared.store⟩

theorem prepareBinary_sound (domain : List Value) (operation : Value → Value → Result)
    (store : Store Var Value) (left right : Input Var Value) (prepared : Prepared Var Value)
    (accepted : prepareBinary? domain store left right = some prepared) :
    binary domain operation store left right = [direct operation prepared] := by
  unfold prepareBinary? at accepted
  cases firstRead : readOne? domain store left with
  | none => simp [firstRead] at accepted
  | some first =>
      cases secondRead : readOne? domain first.2 right with
      | none => simp [firstRead, secondRead] at accepted
      | some second =>
          have firstExact := readOne_sound domain store left first.1 first.2 firstRead
          have secondExact := readOne_sound domain first.2 right second.1 second.2 secondRead
          simp only [firstRead, secondRead, Option.some.injEq] at accepted
          subst prepared
          simp [binary, firstExact, secondExact, direct]

/-- Preparation retains the intermediate binding world needed by a second
read's dependency, coefficient or ownership interpretation. -/
theorem prepareBinary_reads (domain : List Value) (store : Store Var Value)
    (left right : Input Var Value) (prepared : Prepared Var Value)
    (accepted : prepareBinary? domain store left right = some prepared) :
    read domain store left = [(prepared.left, prepared.middle)] ∧
      read domain prepared.middle right = [(prepared.right, prepared.store)] := by
  unfold prepareBinary? at accepted
  cases firstRead : readOne? domain store left with
  | none => simp [firstRead] at accepted
  | some first =>
      cases secondRead : readOne? domain first.2 right with
      | none => simp [firstRead, secondRead] at accepted
      | some second =>
          simp only [firstRead, secondRead, Option.some.injEq] at accepted
          subst prepared
          exact ⟨readOne_sound domain store left first.1 first.2 firstRead,
            readOne_sound domain first.2 right second.1 second.2 secondRead⟩

/-- Actual extra equation bodies, not an annotation about their absence. Native
admission must obtain this complete source family from its validated world. -/
abbrev ExtraEquation (Var : Type u) (Value : Type v) (Result : Type w) :=
  Store Var Value → List (Answer Var Value Result)

def completeSource (domain : List Value) (operation : Value → Value → Result)
    (equations : List (ExtraEquation Var Value Result)) (store : Store Var Value)
    (left right : Input Var Value) : List (Answer Var Value Result) :=
  binary domain operation store left right ++ equations.flatMap (fun equation => equation store)

inductive Worker where
  | direct
  | optional
  | producer
  deriving DecidableEq, Repr

inductive OutputCheck (Var : Type u) (Value : Type v) (Result : Type w) where
  | unconstrained
  | checked (accept : Answer Var Value Result → Bool)

def OutputCheck.accepts : OutputCheck Var Value Result → Answer Var Value Result → Bool
  | .unconstrained, _ => true
  | .checked accept, answer => accept answer

omit [DecidableEq Var] in
@[simp] theorem OutputCheck.accepts_unconstrained :
    (OutputCheck.unconstrained : OutputCheck Var Value Result).accepts = fun _ => true := rfl

omit [DecidableEq Var] in
@[simp] theorem OutputCheck.accepts_checked (accept : Answer Var Value Result → Bool) :
    (OutputCheck.checked accept).accepts = accept := rfl

def chooseWorker (equations : List (ExtraEquation Var Value Result))
    (prepared : Option (Prepared Var Value)) (output : OutputCheck Var Value Result) : Worker :=
  if equations.isEmpty then
    match prepared, output with
    | some _, .unconstrained => .direct
    | some _, .checked _ => .optional
    | _, _ => .producer
  else .producer

/-- Mode inference does not execute the primitive or an additional equation.
Its source family, finite domain, bindings and output constraint are explicit. -/
def inferMode (domain : List Value) (equations : List (ExtraEquation Var Value Result))
    (store : Store Var Value) (left right : Input Var Value)
    (output : OutputCheck Var Value Result) : AnswerCardinality.Grade :=
  if equations.isEmpty then
    match output with
    | .unconstrained => binaryGrade domain store left right
    | .checked _ => AnswerCardinality.constrained (binaryGrade domain store left right)
  else .any

theorem inferMode_sound (domain : List Value) (operation : Value → Value → Result)
    (equations : List (ExtraEquation Var Value Result)) (store : Store Var Value)
    (left right : Input Var Value) (output : OutputCheck Var Value Result) :
    AnswerCardinality.Allows (inferMode domain equations store left right output)
      ((completeSource domain operation equations store left right).filter output.accepts).length := by
  cases equations with
  | cons equation rest => trivial
  | nil =>
      cases output with
      | unconstrained =>
          simpa [inferMode, completeSource, List.filter_cons, OutputCheck.accepts] using
            binaryGrade_sound domain operation store left right
      | checked accept =>
          simpa [inferMode, completeSource, OutputCheck.accepts] using
            AnswerCardinality.filter_sound (binaryGrade domain store left right)
              (binary domain operation store left right) accept
              (binaryGrade_sound domain operation store left right)

/-- Independent specialized interpretation. Refusal executes the original
source family with its complete occurrence list; it never prunes extra equations. -/
def executeSelected (domain : List Value) (operation : Value → Value → Result)
    (equations : List (ExtraEquation Var Value Result)) (store : Store Var Value)
    (left right : Input Var Value) (output : OutputCheck Var Value Result) :
    List (Answer Var Value Result) :=
  let prepared := prepareBinary? domain store left right
  match chooseWorker equations prepared output, prepared with
  | .direct, some ready => [direct operation ready]
  | .optional, some ready =>
      let answer := direct operation ready
      if output.accepts answer then [answer] else []
  | _, _ => (completeSource domain operation equations store left right).filter output.accepts

/-- Worker selection is derived from the actual preparation and full source
equation family. It preserves complete bindings, order and duplicate occurrences. -/
theorem executeSelected_refines_source (domain : List Value)
    (operation : Value → Value → Result) (equations : List (ExtraEquation Var Value Result))
    (store : Store Var Value) (left right : Input Var Value)
    (output : OutputCheck Var Value Result) :
    executeSelected domain operation equations store left right output =
      (completeSource domain operation equations store left right).filter output.accepts := by
  cases equations with
  | cons equation rest => rfl
  | nil =>
      cases prepared : prepareBinary? domain store left right with
      | none => simp [executeSelected, chooseWorker, prepared]
      | some ready =>
          have source := prepareBinary_sound domain operation store left right ready prepared
          cases output with
          | unconstrained =>
              simp [executeSelected, chooseWorker, prepared, completeSource, source]
          | checked accept =>
              cases checked : accept (direct operation ready) <;>
                simp [executeSelected, chooseWorker, prepared, completeSource, source,
                  OutputCheck.accepts, checked]

theorem selected_worker_has_inferred_mode (domain : List Value)
    (operation : Value → Value → Result) (equations : List (ExtraEquation Var Value Result))
    (store : Store Var Value) (left right : Input Var Value)
    (output : OutputCheck Var Value Result) :
    AnswerCardinality.Allows (inferMode domain equations store left right output)
      (executeSelected domain operation equations store left right output).length := by
  rw [executeSelected_refines_source]
  exact inferMode_sound domain operation equations store left right output

section BindingCertificates

def inputQuery : Input Var Value → ReadOnlyQuery.Program Var (Option Value) (Option Value)
  | .literal value => .pure (some value)
  | .var name => .read name (fun observed => .pure observed)

omit [DecidableEq Var] in
theorem inputQuery_answer (bindings : Store Var Value) (input : Input Var Value) :
    (ReadOnlyQuery.run bindings (inputQuery input)).answer = resolve bindings input := by
  cases input <;> rfl

/-- Analysis reads aliasing inputs only once and retains absent lookups. It
does not enumerate answers, execute the operation or publish candidate binds. -/
def countQuery (domain : List Value) (left right : Input Var Value) :
    ReadOnlyQuery.Program Var (Option Value) Nat :=
  ReadOnlyQuery.bind (inputQuery left) fun first =>
    let count := if first.isSome then 1 else domain.length
    if aliases left right then .pure count
    else ReadOnlyQuery.map (fun second => count * (if second.isSome then 1 else domain.length))
      (inputQuery right)

theorem countQuery_answer (domain : List Value) (bindings : Store Var Value)
    (left right : Input Var Value) :
    (ReadOnlyQuery.run bindings (countQuery domain left right)).answer =
      binaryCount domain bindings left right := by
  cases same : aliases left right <;>
    simp [countQuery, same, ReadOnlyQuery.run_bind, ReadOnlyQuery.run_map,
      ReadOnlyQuery.run, inputQuery_answer, binaryCount, readCount]

def modeQuery (domain : List Value) (equations : List (ExtraEquation Var Value Result))
    (left right : Input Var Value) (output : OutputCheck Var Value Result) :
    ReadOnlyQuery.Program Var (Option Value) AnswerCardinality.Grade :=
  if equations.isEmpty then
    ReadOnlyQuery.map (fun count => match output with
      | .unconstrained => AnswerCardinality.ofCount count
      | .checked _ => AnswerCardinality.constrained (AnswerCardinality.ofCount count))
      (countQuery domain left right)
  else .pure .any

theorem modeQuery_answer (domain : List Value) (equations : List (ExtraEquation Var Value Result))
    (bindings : Store Var Value) (left right : Input Var Value)
    (output : OutputCheck Var Value Result) :
    (ReadOnlyQuery.run bindings (modeQuery domain equations left right output)).answer =
      inferMode domain equations bindings left right output := by
  cases empty : equations.isEmpty <;> cases output <;>
    simp [modeQuery, empty, ReadOnlyQuery.run_map, ReadOnlyQuery.run,
      countQuery_answer, inferMode, binaryGrade]

theorem modeQuery_sound (domain : List Value) (operation : Value → Value → Result)
    (equations : List (ExtraEquation Var Value Result)) (bindings : Store Var Value)
    (left right : Input Var Value) (output : OutputCheck Var Value Result) :
    AnswerCardinality.Allows
      (ReadOnlyQuery.run bindings (modeQuery domain equations left right output)).answer
      ((completeSource domain operation equations bindings left right).filter output.accepts).length := by
  rw [modeQuery_answer]
  exact inferMode_sound domain operation equations bindings left right output

/-- Checked read evidence transports the summary to current bindings. This is
conditional on the same primitive, domain and complete source equation family;
the separate world stamp validates that family after source mutations. -/
theorem validated_binding_mode [DecidableEq Value]
    (domain : List Value) (equations : List (ExtraEquation Var Value Result))
    (before current : Store Var Value) (left right : Input Var Value)
    (output : OutputCheck Var Value Result)
    (valid : ReadOnlyQuery.checkReads current
      (ReadOnlyQuery.run before (modeQuery domain equations left right output)).reads = true) :
    inferMode domain equations current left right output =
      inferMode domain equations before left right output := by
  rw [← modeQuery_answer, ← modeQuery_answer]
  exact congrArg ReadOnlyQuery.Observation.answer
    (ReadOnlyQuery.run_eq_of_agrees before current (modeQuery domain equations left right output)
      ((ReadOnlyQuery.checkReads_iff _ _).mp valid))

end BindingCertificates

section MutableEquations

variable {size : Nat}

/-- Equation evidence is read from the complete ordered dependency view. The
caller supplies its current binding store; an old prepared binding snapshot is
not installed merely because the equation stamp remains valid. -/
def workerInWorld (domain : List Value)
    (world : OrderedDependencyStore.Store (ExtraEquation Var Value Result) size)
    (reader : Fin size) (bindings : Store Var Value) (left right : Input Var Value)
    (output : OutputCheck Var Value Result) : Worker :=
  chooseWorker (OrderedDependencyStore.query world reader)
    (prepareBinary? domain bindings left right) output

theorem validated_world_worker (domain : List Value)
    (world : OrderedDependencyStore.Store (ExtraEquation Var Value Result) size)
    (invariant : OrderedDependencyStore.ObserverInvariant world)
    (actions : List (OrderedDependencyStore.Action (ExtraEquation Var Value Result) size))
    (reader : Fin size) (bindings : Store Var Value) (left right : Input Var Value)
    (output : OutputCheck Var Value Result)
    (valid : OrderedDependencyStore.checkRead (OrderedDependencyStore.execute world actions)
      (OrderedDependencyStore.readStamp world reader) = true) :
    workerInWorld domain (OrderedDependencyStore.execute world actions) reader
        bindings left right output =
      workerInWorld domain world reader bindings left right output := by
  unfold workerInWorld
  rw [OrderedDependencyStore.validated_query world invariant actions reader valid]

/-- Validating a full source view transports the derived summary, including a
previously empty equation family. A retained-prefix stamp is insufficient. -/
theorem validated_world_mode (domain : List Value)
    (world : OrderedDependencyStore.Store (ExtraEquation Var Value Result) size)
    (invariant : OrderedDependencyStore.ObserverInvariant world)
    (actions : List (OrderedDependencyStore.Action (ExtraEquation Var Value Result) size))
    (reader : Fin size) (bindings : Store Var Value) (left right : Input Var Value)
    (output : OutputCheck Var Value Result)
    (valid : OrderedDependencyStore.checkRead (OrderedDependencyStore.execute world actions)
      (OrderedDependencyStore.readStamp world reader) = true) :
    inferMode domain (OrderedDependencyStore.query (OrderedDependencyStore.execute world actions)
        reader) bindings left right output =
      inferMode domain (OrderedDependencyStore.query world reader) bindings left right output := by
  rw [OrderedDependencyStore.validated_query world invariant actions reader valid]

/-- The selected worker after mutation still executes the actual current
relation. A valid source stamp permits reuse of its full equation family, while
live bindings continue to determine the worker and its returned world. -/
theorem validated_world_execution (domain : List Value) (operation : Value → Value → Result)
    (world : OrderedDependencyStore.Store (ExtraEquation Var Value Result) size)
    (invariant : OrderedDependencyStore.ObserverInvariant world)
    (actions : List (OrderedDependencyStore.Action (ExtraEquation Var Value Result) size))
    (reader : Fin size) (bindings : Store Var Value) (left right : Input Var Value)
    (output : OutputCheck Var Value Result)
    (valid : OrderedDependencyStore.checkRead (OrderedDependencyStore.execute world actions)
      (OrderedDependencyStore.readStamp world reader) = true) :
    executeSelected domain operation (OrderedDependencyStore.query world reader)
        bindings left right output =
      (completeSource domain operation
        (OrderedDependencyStore.query (OrderedDependencyStore.execute world actions) reader)
        bindings left right).filter output.accepts := by
  rw [OrderedDependencyStore.validated_query world invariant actions reader valid]
  exact executeSelected_refines_source domain operation _ bindings left right output

/-- Two existing validators check different dependencies: the complete equation
view and the binding reads performed by analysis. The captured answer is a
derived summary, never a user-supplied determinism assertion. -/
def validatedGrade? [DecidableEq Value] (domain : List Value)
    (beforeWorld currentWorld : OrderedDependencyStore.Store (ExtraEquation Var Value Result) size)
    (reader : Fin size) (beforeBindings currentBindings : Store Var Value)
    (left right : Input Var Value) (output : OutputCheck Var Value Result) :
    Option AnswerCardinality.Grade :=
  let observation := ReadOnlyQuery.run beforeBindings
    (modeQuery domain (OrderedDependencyStore.query beforeWorld reader) left right output)
  if OrderedDependencyStore.checkRead currentWorld
      (OrderedDependencyStore.readStamp beforeWorld reader) &&
      ReadOnlyQuery.checkReads currentBindings observation.reads
    then some observation.answer else none

/-- On actual dependency-store updates, accepted evidence is the summary of
the current relation and current bindings. Unrelated mutations may validate;
new equations and changed observed bindings must use a newly analyzed or general
call. Primitive identity, domain and output policy are held fixed here. -/
theorem validatedGrade_sound [DecidableEq Value]
    (domain : List Value) (operation : Value → Value → Result)
    (world : OrderedDependencyStore.Store (ExtraEquation Var Value Result) size)
    (invariant : OrderedDependencyStore.ObserverInvariant world)
    (actions : List (OrderedDependencyStore.Action (ExtraEquation Var Value Result) size))
    (reader : Fin size) (before current : Store Var Value) (left right : Input Var Value)
    (output : OutputCheck Var Value Result) (grade : AnswerCardinality.Grade)
    (accepted : validatedGrade? domain world (OrderedDependencyStore.execute world actions)
      reader before current left right output = some grade) :
    AnswerCardinality.Allows grade
      ((completeSource domain operation
        (OrderedDependencyStore.query (OrderedDependencyStore.execute world actions) reader)
        current left right).filter output.accepts).length := by
  unfold validatedGrade? at accepted
  dsimp only at accepted
  split at accepted
  next valid =>
    have both := Bool.and_eq_true_iff.mp valid
    have bindingsSame := validated_binding_mode domain (OrderedDependencyStore.query world reader)
      before current left right output both.2
    have equationsSame := OrderedDependencyStore.validated_query world invariant actions reader both.1
    have summary : inferMode domain (OrderedDependencyStore.query world reader) before
        left right output = grade := by
      simpa only [Option.some.injEq, modeQuery_answer] using accepted
    rw [← summary, ← bindingsSame, ← equationsSame]
    exact inferMode_sound domain operation _ current left right output
  next refused => simp at accepted

end MutableEquations

namespace Controls

def unbound : Store Nat Bool := fun _ => none
def boolDomain : List Bool := [true, false]

/-- All values have carrier Bool, yet a free input still produces two answers. -/
theorem typed_carrier_is_not_boundness :
    (binary boolDomain Bool.or unbound (.literal true) (.var 0)).length = 2 := by
  rfl

/-- Equal results are separate occurrences carrying different input bindings. -/
theorem equal_results_keep_bindings :
    (binary boolDomain Bool.or unbound (.literal true) (.var 0)).map
      (fun answer => (answer.result, answer.store 0)) =
      [(true, some true), (true, some false)] := by
  rfl

/-- Repeated variables do not behave as independently chosen inputs. -/
theorem repeated_input_keeps_alias :
    (binary boolDomain Bool.and unbound (.var 0) (.var 0)).map
      (fun answer => (answer.left, answer.right, answer.result)) =
      [(true, true, true), (false, false, false)] := by
  rfl

/-- An extra source alternative defeats a builtin-only cardinality proof. -/
theorem extra_equation_defeats_singleton :
    ((binary boolDomain Bool.and unbound (.literal true) (.literal true)).map
      Answer.result ++ [false]).length = 2 := by
  rfl

def bound : Store Nat Bool := bind unbound 0 true

theorem bound_call_derives_det_worker :
    inferMode boolDomain ([] : List (ExtraEquation Nat Bool Bool)) bound
      (.var 0) (.literal false) .unconstrained = .one ∧
      chooseWorker ([] : List (ExtraEquation Nat Bool Bool))
        (prepareBinary? boolDomain bound (.var 0) (.literal false)) .unconstrained = .direct := by
  decide

theorem output_constraint_derives_semidet_worker :
    inferMode boolDomain ([] : List (ExtraEquation Nat Bool Bool)) bound
      (.var 0) (.literal false) (.checked fun answer => answer.result) = .optional ∧
      chooseWorker ([] : List (ExtraEquation Nat Bool Bool))
        (prepareBinary? boolDomain bound (.var 0) (.literal false))
        (.checked fun answer => answer.result) = .optional := by decide

theorem free_input_derives_multi_producer :
    inferMode boolDomain ([] : List (ExtraEquation Nat Bool Bool)) unbound
      (.var 0) (.literal true) .unconstrained = .nonempty ∧
      chooseWorker ([] : List (ExtraEquation Nat Bool Bool))
        (prepareBinary? boolDomain unbound (.var 0) (.literal true)) .unconstrained = .producer := by
  decide

theorem constrained_free_input_derives_nondet :
    inferMode boolDomain ([] : List (ExtraEquation Nat Bool Bool)) unbound
      (.var 0) (.literal true) (.checked fun answer => answer.result) = .any := by decide

/-- Clearing a binding changes the same call's mode and worker. A cached
det annotation cannot replace revalidation of the actual live input. -/
theorem clearing_binding_changes_mode :
    inferMode boolDomain ([] : List (ExtraEquation Nat Bool Bool)) bound
      (.var 0) (.literal false) .unconstrained ≠
    inferMode boolDomain ([] : List (ExtraEquation Nat Bool Bool)) unbound
      (.var 0) (.literal false) .unconstrained := by decide

theorem alias_count_is_not_an_independent_product :
    binaryCount boolDomain unbound (.var 0) (.var 0) = 2 ∧
      binaryCount boolDomain unbound (.var 0) (.var 1) = 4 := by decide

/-- A sole domain occurrence can bind an input on the direct path. The
returned store carries that binding, just as the relational read does. -/
theorem singleton_domain_direct_worker_retains_binding :
    (executeSelected [true] Bool.and ([] : List (ExtraEquation Nat Bool Bool)) unbound
      (.var 0) (.var 0) .unconstrained).map
      (fun answer => (answer.result, answer.store 0)) = [(true, some true)] ∧
      chooseWorker ([] : List (ExtraEquation Nat Bool Bool))
        (prepareBinary? [true] unbound (.var 0) (.var 0)) .unconstrained = .direct := by
  decide

def additional : ExtraEquation Nat Bool Bool :=
  fun store => [⟨true, true, true, store⟩]

theorem additional_equation_blocks_direct_worker :
    chooseWorker [additional]
      (prepareBinary? boolDomain bound (.var 0) (.literal true)) .unconstrained = .producer ∧
      (executeSelected boolDomain Bool.and [additional] bound
        (.var 0) (.literal true) .unconstrained).map Answer.result = [true, true] := by decide

theorem optional_constraint_can_reject_a_det_answer :
    (executeSelected boolDomain Bool.and ([] : List (ExtraEquation Nat Bool Bool)) bound
      (.var 0) (.literal false) (.checked fun answer => answer.result)).length = 0 := by decide

theorem source_duplicates_block_direct_worker :
    chooseWorker ([] : List (ExtraEquation Nat Bool Bool))
      (prepareBinary? [true, true] unbound (.var 0) (.var 0)) .unconstrained = .producer ∧
      (executeSelected [true, true] Bool.and ([] : List (ExtraEquation Nat Bool Bool)) unbound
        (.var 0) (.var 0) .unconstrained).map Answer.result = [true, true] := by decide

def equationWorld : OrderedDependencyStore.Store (ExtraEquation Nat Bool Bool) 2 :=
  OrderedDependencyStore.initial 901 (fun _ => [])

theorem added_equation_invalidates_a_det_summary :
    workerInWorld boolDomain equationWorld 0 bound (.var 0) (.literal true)
        .unconstrained = .direct ∧
      workerInWorld boolDomain (OrderedDependencyStore.appendOwn equationWorld 0 [additional])
        0 bound (.var 0) (.literal true) .unconstrained = .producer ∧
      OrderedDependencyStore.checkRead (OrderedDependencyStore.appendOwn equationWorld 0 [additional])
        (OrderedDependencyStore.readStamp equationWorld 0) = false := by decide

theorem unrelated_equation_update_retains_the_mode :
    workerInWorld boolDomain (OrderedDependencyStore.appendOwn equationWorld 1 [additional])
        0 bound (.var 0) (.literal true) .unconstrained = .direct ∧
      OrderedDependencyStore.checkRead (OrderedDependencyStore.appendOwn equationWorld 1 [additional])
        (OrderedDependencyStore.readStamp equationWorld 0) = true := by decide

theorem equation_stamp_does_not_freeze_bindings :
    OrderedDependencyStore.checkRead equationWorld
        (OrderedDependencyStore.readStamp equationWorld 0) = true ∧
      workerInWorld boolDomain equationWorld 0 unbound (.var 0) (.literal true)
        .unconstrained = .producer := by decide

theorem retaining_an_old_prefix_does_not_authorize_det :
    OrderedDependencyStore.checkPrefix (OrderedDependencyStore.appendOwn equationWorld 0 [additional])
        (OrderedDependencyStore.prefixStamp equationWorld 0) = true ∧
      workerInWorld boolDomain (OrderedDependencyStore.appendOwn equationWorld 0 [additional])
        0 bound (.var 0) (.literal true) .unconstrained = .producer := by decide

theorem alias_analysis_reads_one_binding :
    (ReadOnlyQuery.run unbound (modeQuery boolDomain ([] : List (ExtraEquation Nat Bool Bool))
      (.var 0) (.var 0) .unconstrained)).reads = [(0, none)] := rfl

theorem absent_binding_becoming_bound_expires_the_certificate :
    ReadOnlyQuery.checkReads bound
      (ReadOnlyQuery.run unbound (modeQuery boolDomain ([] : List (ExtraEquation Nat Bool Bool))
        (.var 0) (.literal false) .unconstrained)).reads = false := by decide

theorem unrelated_binding_write_preserves_the_certificate :
    ReadOnlyQuery.checkReads (bind unbound 1 true)
      (ReadOnlyQuery.run unbound (modeQuery boolDomain ([] : List (ExtraEquation Nat Bool Bool))
        (.var 0) (.literal false) .unconstrained)).reads = true := by decide

theorem joined_evidence_refuses_a_changed_observed_binding :
    validatedGrade? boolDomain equationWorld equationWorld 0 bound unbound
      (.var 0) (.literal true) .unconstrained = none := by decide

theorem joined_evidence_refuses_an_added_equation :
    validatedGrade? boolDomain equationWorld
      (OrderedDependencyStore.appendOwn equationWorld 0 [additional]) 0 bound bound
      (.var 0) (.literal true) .unconstrained = none := by decide

theorem joined_evidence_accepts_unrelated_mutations :
    validatedGrade? boolDomain equationWorld
      (OrderedDependencyStore.appendOwn equationWorld 1 [additional]) 0 bound (bind bound 1 false)
      (.var 0) (.literal true) .unconstrained = some .one := by decide

end Controls
end Mettapedia.Machines.RelationalBuiltinModes
