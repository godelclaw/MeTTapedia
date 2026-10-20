import Mettapedia.TypeTheory.ContextualCBPVScopedNeedComplete
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedSyntax
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedNaturalSemantics
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedEmbedding
import Mathlib.Logic.Function.Basic

/-!
# PolarizedNeed's value layer in the contextual model

PolarizedNeed's value layer has first-class thunks, value lambdas and native
packages, untyped, and a need cell may cache any answer, a thunk or a
computation function among them.  The scoped-need reading
(`ContextualCBPVScopedNeed`) takes code to programs of the contextual model,
`Program`, over a store of cached outcomes.

**What no reading can do.**  Two Cantor arguments bound how that reading
extends to the value layer.

* No reflexive value domain (`no_reflexive_domain`).  A compositional
  reading of untyped value lambdas needs a type of values `D` of which every
  function from values to programs is a value, an injection
  `(D → Program State D Intent) → D`.  There is none.
* No state that caches its programs (`no_state_caching_programs`).  A store
  that caches a thunk or a function as a program of the same model needs an
  injection `Program State Answer Intent → State`.  There is none, because
  `read` already embeds `State → Program State Answer Intent`.

Both rest on one fact: for a type `X` with two distinct elements, no type `D`
injects `D → X` into itself (`no_injection_from_functions`).  So a reading of
the value layer either reads it at types, with only data in the store, or
keeps run-time values and caches as syntax and bounds how far it unfolds
them.

**The value layer at its shapes.**  `Shaped.Value` and `Shaped.Computation`
are the value layer with every term at its shape, PolarizedNeed's types with
the native types forgotten (`VShape`, `CShape`), and need cells that cache
native answers; `erase` forgets the shapes into PolarizedNeed's raw syntax.
Their reading (`readValue`, `readComputation`) is call-by-push-value in the
contextual model: a thunk is its computation, a function shape is a function
space with its effects pointwise (`bindAt`), and a returner is a program over
the store of native caches.  The cells are those of the natural semantics:
`letNeed` allocates a cell that `forceNeed` demands, and sequencing and choice
allocate a cell demanded at once.  A cell caches a native answer; a thunk or
package answer stays out of the store (`cellAt`), which nothing reads again.
The CBPV laws for thunks, lambdas and packages hold by definition
(`read_forceThunk_thunk`, `read_valueApply_valueLambda`,
`read_nativeApply_nativeLambda`, `read_unpackNative_pack`).

**Scoped need is the native fragment.**  Scoped need code embeds at native
shapes (`embed`, whose erasure is PolarizedNeed's `ofScopedNeed`), and there
the reading is the scoped-need reading, program for program (`read_embed`).
So on scoped need code it agrees exactly with the scoped-need natural
semantics, from every fresh heap (`embed_agreement`, by
`ContextualCBPVScopedNeedComplete`).

**Examples.**  A thunk runs again at every force; a need cell that a thunk
captures is demanded once, however often the thunk is forced; a value lambda
passes a thunk on; a package keeps its index with its payload.  The raw
syntax's higher-order example, outside the scoped-need image, is the erasure
of a shaped term (`Examples.applyThunked_erase`).

**Higher-order agreement without need cells.**  For a closed native
returner without need cells (`NeedFree`: no `letNeed` or `forceNeed`;
sequencing and choice still allocate the cells of the natural semantics),
every natural outcome other than a retry the machine raises itself is an
answer of the reading (`needFree_sound`), with first-class thunks, value and
native lambdas, packages, sequencing and choice.  The exclusion is necessary:
from a heap whose next allocation collides, the natural semantics derives a
retry no answer of the reading is (`Examples.raised_necessary`).  The proof is a logical
relation between run-time and semantic values (`RelValue`, `GoodFrom`), which
reads a function shape through its applications, and its fundamental lemma
(`fundamental_computation`), which also covers every selected occurrence of a
cell's producer.  `Examples.applied_natural` and `Examples.thunkedCoin_natural`
apply it.

**Further results.**  Later modules extend this one.
`ContextualCBPVPolarizedNeedCells` adds need cells to the higher-order
soundness, with choice at every shape.  `ContextualCBPVPolarizedFresh` reads
the relation from fresh heaps, where no outcome is excluded, for every
primitive.  `ContextualCBPVPolarizedComplete` proves the converse direction
without need cells, so that the two agree exactly from every fresh heap.
Not yet covered: the converse direction with need cells, and need cells that
cache thunks or functions.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualCBPV.PolarizedValues

open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.TypeTheory.ContextualDependentSequencing
open Mettapedia.Machines.BranchLocalNeed
open Mettapedia.Machines.BranchLocalNeed.NeedReference
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

/-- For a type with two distinct elements, the functions into it from a type
`D` do not inject into `D`. -/
theorem no_injection_from_functions {D X : Type} {first second : X} (distinct : first ≠ second)
    (fold : (D → X) → D) : ¬ Function.Injective fold := by
  classical
  intro injective
  let indicator : Set D → D → X := fun set point => if point ∈ set then first else second
  have indicatorInjective : Function.Injective indicator := by
    intro set set' equal
    ext point
    have atPoint := congrFun equal point
    by_cases inSet : point ∈ set <;> by_cases inSet' : point ∈ set' <;>
      simp_all [indicator]
  exact Function.cantor_injective (fold ∘ indicator) (injective.comp indicatorInjective)

/-- Two programs that differ: an answer and a choice between it and itself. -/
theorem pure_ne_choose {State Answer Intent : Type} (answer : Answer) :
    (Program.pure answer : Program State Answer Intent) ≠ .choose (.pure answer) (.pure answer) := by
  intro equal
  cases equal

/-- **No reflexive value domain.**  No type of values contains every function
from values to programs answering values. -/
theorem no_reflexive_domain {State Intent D : Type} (fold : (D → Program State D Intent) → D) :
    ¬ Function.Injective fold :=
  no_injection_from_functions (pure_ne_choose (fold fun value => .pure value)) fold

/-- **No state that caches its programs.**  No store contains every program
over itself, for any answer type with an element. -/
theorem no_state_caching_programs {State Answer Intent : Type} (answer : Answer)
    (cache : Program State Answer Intent → State) : ¬ Function.Injective cache := by
  intro injective
  have readInjective : Function.Injective
      (Program.read : (State → Program State Answer Intent) → Program State Answer Intent) := by
    intro next next' equal
    cases equal
    rfl
  exact no_injection_from_functions (pure_ne_choose (State := State) (Intent := Intent) answer)
    (cache ∘ Program.read) (injective.comp readInjective)

#print axioms no_reflexive_domain
#print axioms no_state_caching_programs

/-! ## The value layer at its shapes -/

mutual
  /-- Value shapes: PolarizedNeed's value types with the native types
  forgotten. -/
  inductive VShape where
    | native
    | thunk (body : CShape)
    | pack (payload : VShape)

  /-- Computation shapes. -/
  inductive CShape where
    | returns (answer : VShape)
    | nativePi (body : CShape)
    | arrow (domain : VShape) (body : CShape)
end

/-- A value variable of a given shape. -/
inductive Member : List VShape → VShape → Type where
  | zero {scope : List VShape} {shape : VShape} : Member (shape :: scope) shape
  | succ {scope : List VShape} {shape other : VShape} : Member scope shape → Member (other :: scope) shape

/-- The position of a member. -/
def Member.index : {scope : List VShape} → {shape : VShape} → Member scope shape → Fin scope.length
  | _ :: _, _, .zero => 0
  | _ :: _, _, .succ inner => inner.index.succ

namespace Shaped

mutual
  /-- Values of the value layer at their shapes.  Native terms live in the
  native scope `n`, value variables in `scope`, references in `k`. -/
  inductive Value (Head Operation Effect : Type) : Nat → List VShape → Nat → VShape → Type where
    | native {n k : Nat} {scope : List VShape} (term : Tm Head n) : Value Head Operation Effect n scope k .native
    | var {n k : Nat} {scope : List VShape} {shape : VShape} (index : Member scope shape) :
        Value Head Operation Effect n scope k shape
    | thunk {n k : Nat} {scope : List VShape} {shape : CShape}
        (body : Computation Head Operation Effect n scope k shape) : Value Head Operation Effect n scope k (.thunk shape)
    | pack {n k : Nat} {scope : List VShape} {payload : VShape} (index : Tm Head n)
        (value : Value Head Operation Effect n scope k payload) : Value Head Operation Effect n scope k (.pack payload)

  /-- Computations of the value layer at their shapes.  A need cell caches a
  native answer. -/
  inductive Computation (Head Operation Effect : Type) : Nat → List VShape → Nat → CShape → Type where
    | returnValue {n k : Nat} {scope : List VShape} {shape : VShape}
        (value : Value Head Operation Effect n scope k shape) : Computation Head Operation Effect n scope k (.returns shape)
    | bindNative {n k : Nat} {scope : List VShape} {shape : CShape}
        (first : Computation Head Operation Effect n scope k (.returns .native))
        (body : Computation Head Operation Effect (n + 1) scope k shape) : Computation Head Operation Effect n scope k shape
    | bindValue {n k : Nat} {scope : List VShape} {bound : VShape} {shape : CShape}
        (first : Computation Head Operation Effect n scope k (.returns bound))
        (body : Computation Head Operation Effect n (bound :: scope) k shape) :
        Computation Head Operation Effect n scope k shape
    | sequenceSigma {n k : Nat} {scope : List VShape}
        (first : Computation Head Operation Effect n scope k (.returns .native))
        (body : Computation Head Operation Effect (n + 1) scope k (.returns .native)) :
        Computation Head Operation Effect n scope k (.returns .native)
    | nativeLambda {n k : Nat} {scope : List VShape} {shape : CShape}
        (body : Computation Head Operation Effect (n + 1) scope k shape) :
        Computation Head Operation Effect n scope k (.nativePi shape)
    | nativeApply {n k : Nat} {scope : List VShape} {shape : CShape}
        (function : Computation Head Operation Effect n scope k (.nativePi shape)) (argument : Tm Head n) :
        Computation Head Operation Effect n scope k shape
    | valueLambda {n k : Nat} {scope : List VShape} {domain : VShape} {shape : CShape}
        (body : Computation Head Operation Effect n (domain :: scope) k shape) :
        Computation Head Operation Effect n scope k (.arrow domain shape)
    | valueApply {n k : Nat} {scope : List VShape} {domain : VShape} {shape : CShape}
        (function : Computation Head Operation Effect n scope k (.arrow domain shape))
        (argument : Value Head Operation Effect n scope k domain) : Computation Head Operation Effect n scope k shape
    | forceThunk {n k : Nat} {scope : List VShape} {shape : CShape}
        (value : Value Head Operation Effect n scope k (.thunk shape)) : Computation Head Operation Effect n scope k shape
    | unpackNative {n k : Nat} {scope : List VShape} {payload : VShape} {shape : CShape}
        (value : Value Head Operation Effect n scope k (.pack payload))
        (body : Computation Head Operation Effect (n + 1) (payload :: scope) k shape) :
        Computation Head Operation Effect n scope k shape
    | choose {n k : Nat} {scope : List VShape} {shape : CShape}
        (left right : Computation Head Operation Effect n scope k shape) : Computation Head Operation Effect n scope k shape
    | call {n k : Nat} {scope : List VShape} (operation : Operation) (argument : Tm Head n) :
        Computation Head Operation Effect n scope k (.returns .native)
    | emit {n k : Nat} {scope : List VShape} {shape : CShape} (effect : Effect)
        (next : Computation Head Operation Effect n scope k shape) : Computation Head Operation Effect n scope k shape
    | letNeed {n k : Nat} {scope : List VShape} {shape : CShape}
        (suspended : Computation Head Operation Effect n scope k (.returns .native))
        (body : Computation Head Operation Effect n scope (k + 1) shape) : Computation Head Operation Effect n scope k shape
    | forceNeed {n k : Nat} {scope : List VShape} (reference : Fin k) :
        Computation Head Operation Effect n scope k (.returns .native)
end

variable {Head Operation Effect : Type}

mutual
  /-- Forget the shapes: PolarizedNeed's raw syntax. -/
  def Value.erase : {n k : Nat} → {scope : List VShape} → {shape : VShape} →
      Value Head Operation Effect n scope k shape → PolarizedNeed.Value Head Operation Effect n scope.length k
    | _, _, _, _, .native term => .native term
    | _, _, _, _, .var index => .variable index.index
    | _, _, _, _, .thunk body => .thunk body.erase
    | _, _, _, _, .pack index value => .packNative index value.erase

  def Computation.erase : {n k : Nat} → {scope : List VShape} → {shape : CShape} →
      Computation Head Operation Effect n scope k shape →
        PolarizedNeed.Computation Head Operation Effect n scope.length k
    | _, _, _, _, .returnValue value => .returnValue value.erase
    | _, _, _, _, .bindNative first body => .bindNative first.erase body.erase
    | _, _, _, _, .bindValue first body => .bindValue first.erase body.erase
    | _, _, _, _, .sequenceSigma first body => .sequenceSigma first.erase body.erase
    | _, _, _, _, .nativeLambda body => .nativeLambda body.erase
    | _, _, _, _, .nativeApply function argument => .nativeApply function.erase argument
    | _, _, _, _, .valueLambda body => .valueLambda body.erase
    | _, _, _, _, .valueApply function argument => .valueApply function.erase argument.erase
    | _, _, _, _, .forceThunk value => .forceThunk value.erase
    | _, _, _, _, .unpackNative value body => .unpackNative value.erase body.erase
    | _, _, _, _, .choose left right => .choose left.erase right.erase
    | _, _, _, _, .call operation argument => .call operation argument
    | _, _, _, _, .emit effect next => .emit effect next.erase
    | _, _, _, _, .letNeed suspended body => .letNeed suspended.erase body.erase
    | _, _, _, _, .forceNeed reference => .forceNeed reference
end

end Shaped

/-! ## The reading at shapes -/

section Reading

open ScopedNeed (Store Run Ref alloc demand)
open ScopedNeedNaturalSemantics (pairOutcome)

variable (Head Effect StableFault NativeFault : Type) (m : Nat)

mutual
  /-- What a value of a shape means: a native term, a computation (a thunk
  is its computation), or a native index with a payload. -/
  def SemValue : VShape → Type
    | .native => Tm Head m
    | .thunk shape => SemComputation shape
    | .pack payload => Tm Head m × SemValue payload

  /-- What a computation of a shape means: a returner is a program over the
  store of native caches; a function is a function. -/
  def SemComputation : CShape → Type
    | .returns shape =>
        Program (Store Head StableFault NativeFault m)
          (Produced (SemValue shape) StableFault (ScopedNeedMachine.Fault NativeFault)) Effect
    | .nativePi shape => Tm Head m → SemComputation shape
    | .arrow domain shape => SemValue domain → SemComputation shape
end

variable {Head Effect StableFault NativeFault m}

/-- Run a program first, pointwise at function shapes: the algebra structure
of each shape. -/
def bindAt : (shape : CShape) → {Other : Type} →
    Program (Store Head StableFault NativeFault m) Other Effect →
      (Other → SemComputation Head Effect StableFault NativeFault m shape) →
        SemComputation Head Effect StableFault NativeFault m shape
  | .returns _, _, program, next => program.bind next
  | .nativePi shape, _, program, next => fun argument => bindAt shape program fun other => next other argument
  | .arrow _ shape, _, program, next => fun argument => bindAt shape program fun other => next other argument

/-- A fault at any shape: a returner ends in it; a function ends in it at
every argument. -/
def failAt : (shape : CShape) → Produced Empty StableFault (ScopedNeedMachine.Fault NativeFault) →
    SemComputation Head Effect StableFault NativeFault m shape
  | .returns _, .stableFault fault => .pure (.stableFault fault)
  | .returns _, .retryableFault reason => .pure (.retryableFault reason)
  | .returns _, .value nothing => nothing.elim
  | .nativePi shape, fault => fun _ => failAt shape fault
  | .arrow _ shape, fault => fun _ => failAt shape fault

/-- Sequencing: continue with a returned value; a fault ends the
computation. -/
def sequenceAt (shape : CShape) {Other : Type}
    (first : Program (Store Head StableFault NativeFault m)
      (Produced Other StableFault (ScopedNeedMachine.Fault NativeFault)) Effect)
    (next : Other → SemComputation Head Effect StableFault NativeFault m shape) :
    SemComputation Head Effect StableFault NativeFault m shape :=
  bindAt shape first fun
    | .value value => next value
    | .stableFault fault => failAt shape (.stableFault fault)
    | .retryableFault reason => failAt shape (.retryableFault reason)

/-- Allocate a pending cell, at any shape. -/
def allocAt (shape : CShape) (next : Nat → SemComputation Head Effect StableFault NativeFault m shape) :
    SemComputation Head Effect StableFault NativeFault m shape :=
  bindAt shape (.read fun store => .write (store ++ [none]) (.pure store.length)) next

/-- Run the producer of a cell that is demanded at once.  A native answer is
cached.  Any other answer is a thunk or a package, which the store of data
cannot hold (`no_state_caching_programs`); the cell, which nothing reads
again, stays pending. -/
def cellAt : (shape : VShape) → Nat → SemComputation Head Effect StableFault NativeFault m (.returns shape) →
    SemComputation Head Effect StableFault NativeFault m (.returns shape)
  | .native, cell, producer => demand cell producer
  | .thunk _, _, producer => producer
  | .pack _, _, producer => producer

/-- A choice, pointwise at function shapes. -/
def chooseAt (shape : CShape) (left right : SemComputation Head Effect StableFault NativeFault m shape) :
    SemComputation Head Effect StableFault NativeFault m shape :=
  bindAt shape (.choose (.pure false) (.pure true)) fun right? => cond right? right left

/-- A choice in its own cell: a returner selects an alternative when its cell
is first demanded; at a function shape the choice is made at application. -/
def chooseCell : (shape : CShape) → Nat → SemComputation Head Effect StableFault NativeFault m shape →
    SemComputation Head Effect StableFault NativeFault m shape →
      SemComputation Head Effect StableFault NativeFault m shape
  | .returns answer, cell, left, right => cellAt answer cell (.choose left right)
  | .nativePi shape, _, left, right => chooseAt (.nativePi shape) left right
  | .arrow domain shape, _, left, right => chooseAt (.arrow domain shape) left right

/-- Environments of value variables. -/
abbrev SemEnv (scope : List VShape) :=
  (shape : VShape) → Member scope shape → SemValue Head Effect StableFault NativeFault m shape

def SemEnv.cons {scope : List VShape} {shape : VShape} (value : SemValue Head Effect StableFault NativeFault m shape)
    (env : SemEnv (Head := Head) (Effect := Effect) (StableFault := StableFault) (NativeFault := NativeFault)
      (m := m) scope) :
    SemEnv (Head := Head) (Effect := Effect) (StableFault := StableFault) (NativeFault := NativeFault) (m := m)
      (shape :: scope)
  | _, .zero => value
  | _, .succ index => env _ index

/-- The environment of the empty scope. -/
def SemEnv.empty : SemEnv (Head := Head) (Effect := Effect) (StableFault := StableFault)
    (NativeFault := NativeFault) (m := m) [] :=
  fun _ index => nomatch index

variable {Operation : Type} (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)

mutual
  /-- **The reading of a value.** -/
  def readValue : {n k : Nat} → {scope : List VShape} → {shape : VShape} →
      Shaped.Value Head Operation Effect n scope k shape → Sub Head n m →
      SemEnv (Head := Head) (Effect := Effect) (StableFault := StableFault) (NativeFault := NativeFault) (m := m)
        scope →
      (Fin k → Ref Head Effect StableFault NativeFault m) → SemValue Head Effect StableFault NativeFault m shape
    | _, _, _, _, .native term, native, _, _ => subst native term
    | _, _, _, _, .var index, _, env, _ => env _ index
    | _, _, _, _, .thunk body, native, env, refs => (readComputation body native env refs).1
    | _, _, _, _, .pack index value, native, env, refs => (subst native index, readValue value native env refs)

  /-- **The reading of a computation**: call-by-push-value in the contextual
  model, with the cells of the natural semantics.  The first component is the
  computation; the second is what its cell runs when it is a cell's producer
  (a choice selects an alternative, without a cell of its own). -/
  def readComputation : {n k : Nat} → {scope : List VShape} → {shape : CShape} →
      Shaped.Computation Head Operation Effect n scope k shape → Sub Head n m →
      SemEnv (Head := Head) (Effect := Effect) (StableFault := StableFault) (NativeFault := NativeFault) (m := m)
        scope →
      (Fin k → Ref Head Effect StableFault NativeFault m) →
        SemComputation Head Effect StableFault NativeFault m shape ×
          SemComputation Head Effect StableFault NativeFault m shape
    | _, _, _, _, .returnValue value, native, env, refs =>
        (.pure (.value (readValue value native env refs)), .pure (.value (readValue value native env refs)))
    | _, _, _, shape, .bindNative first body, native, env, refs =>
        (allocAt shape fun cell => sequenceAt shape (cellAt .native cell (readComputation first native env refs).2)
            fun value => (readComputation body (Fin.cases value native) env refs).1,
         allocAt shape fun cell => sequenceAt shape (cellAt .native cell (readComputation first native env refs).2)
            fun value => (readComputation body (Fin.cases value native) env refs).1)
    | _, _, _, shape, .bindValue (bound := bound) first body, native, env, refs =>
        (allocAt shape fun cell => sequenceAt shape (cellAt bound cell (readComputation first native env refs).2)
            fun value => (readComputation body native (SemEnv.cons value env) refs).1,
         allocAt shape fun cell => sequenceAt shape (cellAt bound cell (readComputation first native env refs).2)
            fun value => (readComputation body native (SemEnv.cons value env) refs).1)
    | _, _, _, _, .sequenceSigma first body, native, env, refs =>
        (allocAt (.returns .native) fun cell =>
            sequenceAt (.returns .native) (cellAt .native cell (readComputation first native env refs).2) fun value =>
              Program.map (pairOutcome value) (readComputation body (Fin.cases value native) env refs).1,
         allocAt (.returns .native) fun cell =>
            sequenceAt (.returns .native) (cellAt .native cell (readComputation first native env refs).2) fun value =>
              Program.map (pairOutcome value) (readComputation body (Fin.cases value native) env refs).1)
    | _, _, _, _, .nativeLambda body, native, env, refs =>
        (fun argument => (readComputation body (Fin.cases argument native) env refs).1,
         fun argument => (readComputation body (Fin.cases argument native) env refs).1)
    | _, _, _, _, .nativeApply function argument, native, env, refs =>
        ((readComputation function native env refs).1 (subst native argument),
         (readComputation function native env refs).1 (subst native argument))
    | _, _, _, _, .valueLambda body, native, env, refs =>
        (fun argument => (readComputation body native (SemEnv.cons argument env) refs).1,
         fun argument => (readComputation body native (SemEnv.cons argument env) refs).1)
    | _, _, _, _, .valueApply function argument, native, env, refs =>
        ((readComputation function native env refs).1 (readValue argument native env refs),
         (readComputation function native env refs).1 (readValue argument native env refs))
    | _, _, _, _, .forceThunk value, native, env, refs =>
        (readValue value native env refs, readValue value native env refs)
    | _, _, _, _, .unpackNative value body, native, env, refs =>
        ((readComputation body (Fin.cases (readValue value native env refs).1 native)
            (SemEnv.cons (readValue value native env refs).2 env) refs).1,
         (readComputation body (Fin.cases (readValue value native env refs).1 native)
            (SemEnv.cons (readValue value native env refs).2 env) refs).1)
    | _, _, _, shape, .choose left right, native, env, refs =>
        (allocAt shape fun cell =>
            chooseCell shape cell (readComputation left native env refs).1 (readComputation right native env refs).1,
         chooseAt shape (readComputation left native env refs).1 (readComputation right native env refs).1)
    | _, _, _, _, .call operation argument, native, _, _ =>
        (.pure (ScopedNeedMachine.liftOutcome (primitive operation (subst native argument))),
         .pure (ScopedNeedMachine.liftOutcome (primitive operation (subst native argument))))
    | _, _, _, shape, .emit effect next, native, env, refs =>
        (bindAt shape (.intent effect (.pure ())) fun _ => (readComputation next native env refs).1,
         bindAt shape (.intent effect (.pure ())) fun _ => (readComputation next native env refs).1)
    | _, _, _, shape, .letNeed suspended body, native, env, refs =>
        (allocAt shape fun cell =>
            (readComputation body native env (Fin.cases (cell, (readComputation suspended native env refs).2) refs)).1,
         allocAt shape fun cell =>
            (readComputation body native env (Fin.cases (cell, (readComputation suspended native env refs).2) refs)).1)
    | _, _, _, _, .forceNeed reference, _, _, refs =>
        (demand (refs reference).1 (refs reference).2, demand (refs reference).1 (refs reference).2)
end

/-- The answers of a closed native returner, from the empty store. -/
def answers (computation : Shaped.Computation Head Operation Effect 0 [] 0 (.returns .native)) (native : Sub Head 0 m) :
    List (Produced (Tm Head m) StableFault (ScopedNeedMachine.Fault NativeFault)) :=
  (runWorlds (readComputation primitive computation native SemEnv.empty Fin.elim0).1 []).map WorldResult.answer

end Reading

/-! ## The CBPV laws of the reading -/

section Laws

open Shaped

variable {Head Operation Effect StableFault NativeFault : Type} {m n k : Nat} {scope : List VShape}
  (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
  (native : Sub Head n m)
  (env : SemEnv (Head := Head) (Effect := Effect) (StableFault := StableFault) (NativeFault := NativeFault)
    (m := m) scope)
  (refs : Fin k → ScopedNeed.Ref Head Effect StableFault NativeFault m)

/-- Forcing a thunk runs its body. -/
theorem read_forceThunk_thunk {shape : CShape} (body : Computation Head Operation Effect n scope k shape) :
    (readComputation primitive (.forceThunk (.thunk body)) native env refs).1 =
      (readComputation primitive body native env refs).1 := rfl

/-- Applying a value lambda runs its body with the argument bound. -/
theorem read_valueApply_valueLambda {domain : VShape} {shape : CShape}
    (body : Computation Head Operation Effect n (domain :: scope) k shape)
    (argument : Value Head Operation Effect n scope k domain) :
    (readComputation primitive (.valueApply (.valueLambda body) argument) native env refs).1 =
      (readComputation primitive body native (SemEnv.cons (readValue primitive argument native env refs) env)
        refs).1 :=
  rfl

/-- Applying a native lambda runs its body with the native argument bound. -/
theorem read_nativeApply_nativeLambda {shape : CShape} (body : Computation Head Operation Effect (n + 1) scope k shape)
    (argument : Tm Head n) :
    (readComputation primitive (.nativeApply (.nativeLambda body) argument) native env refs).1 =
      (readComputation primitive body (Fin.cases (subst native argument) native) env refs).1 := rfl

/-- Unpacking a package binds its index and its payload. -/
theorem read_unpackNative_pack {payload : VShape} {shape : CShape} (index : Tm Head n)
    (value : Value Head Operation Effect n scope k payload)
    (body : Computation Head Operation Effect (n + 1) (payload :: scope) k shape) :
    (readComputation primitive (.unpackNative (.pack index value) body) native env refs).1 =
      (readComputation primitive body (Fin.cases (subst native index) native)
        (SemEnv.cons (readValue primitive value native env refs) env) refs).1 := rfl

end Laws

/-! ## Scoped need is the native fragment -/

section ScopedNeedFragment

open ScopedNeedComputation (Code)

variable {Head Operation Effect StableFault NativeFault : Type} {m : Nat}

/-- Scoped need code at its shapes: every computation returns a native value. -/
def embed : {n k : Nat} → Code Head Operation Effect n k →
    Shaped.Computation Head Operation Effect n [] k (.returns .native)
  | _, _, .returnValue term => .returnValue (.native term)
  | _, _, .call operation argument => .call operation argument
  | _, _, .emit effect next => .emit effect (embed next)
  | _, _, .choose left right => .choose (embed left) (embed right)
  | _, _, .sequence first body => .bindNative (embed first) (embed body)
  | _, _, .sequenceSigma first body => .sequenceSigma (embed first) (embed body)
  | _, _, .letNeed suspended body => .letNeed (embed suspended) (embed body)
  | _, _, .force reference => .forceNeed reference

/-- Its erasure is PolarizedNeed's embedding of scoped need code. -/
theorem embed_erase {n k : Nat} (code : Code Head Operation Effect n k) :
    (embed code).erase = PolarizedNeed.Computation.ofScopedNeed (v := 0) code := by
  induction code <;>
    simp_all [embed, Shaped.Computation.erase, Shaped.Value.erase, PolarizedNeed.Computation.ofScopedNeed]

theorem sequenceAt_native (first : SemComputation Head Effect StableFault NativeFault m (.returns .native))
    (next : SemValue Head Effect StableFault NativeFault m .native →
      SemComputation Head Effect StableFault NativeFault m (.returns .native)) :
    sequenceAt (.returns .native) first next = Program.bind first (ScopedNeed.onValue next) := by
  show Program.bind first _ = Program.bind first _
  congr 1
  funext outcome
  cases outcome <;> rfl

/-- A native sequencing reads as in the scoped-need reading. -/
theorem allocAt_sequenceAt_native (producer : SemComputation Head Effect StableFault NativeFault m (.returns .native))
    (next : SemValue Head Effect StableFault NativeFault m .native →
      SemComputation Head Effect StableFault NativeFault m (.returns .native)) :
    (allocAt (.returns .native) fun cell => sequenceAt (.returns .native) (cellAt .native cell producer) next) =
      ScopedNeed.alloc fun cell => Program.bind (ScopedNeed.demand cell producer) (ScopedNeed.onValue next) := by
  show Program.read _ = Program.read _
  congr 1
  funext store
  show Program.write _ _ = Program.write _ _
  congr 1
  exact sequenceAt_native _ next

variable (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)

/-- **The reading of the value layer extends the scoped-need reading**: on
scoped need code the two are the same programs. -/
theorem read_embed {n k : Nat} (code : Code Head Operation Effect n k) (values : Sub Head n m)
    (refs : Fin k → ScopedNeed.Ref Head Effect StableFault NativeFault m) :
    readComputation primitive (embed code) values SemEnv.empty refs = ScopedNeed.reading primitive code values refs := by
  induction code with
  | returnValue term => rfl
  | call operation argument => rfl
  | emit effect next ih => simp only [embed, readComputation, ScopedNeed.reading, ih]; rfl
  | choose left right ihLeft ihRight =>
      simp only [embed, readComputation, ScopedNeed.reading, ihLeft, ihRight]; rfl
  | sequence first body ihFirst ihBody =>
      simp only [embed, readComputation, ScopedNeed.reading, ihFirst, ihBody]
      have equal := allocAt_sequenceAt_native (ScopedNeed.reading primitive first values refs).2
        fun value => (ScopedNeed.reading primitive body (Fin.cases value values) refs).1
      exact Prod.ext equal equal
  | sequenceSigma first body ihFirst ihBody =>
      simp only [embed, readComputation, ScopedNeed.reading, ihFirst, ihBody]
      have equal := allocAt_sequenceAt_native (ScopedNeed.reading primitive first values refs).2
        fun value => Program.map (ScopedNeedNaturalSemantics.pairOutcome value)
          (ScopedNeed.reading primitive body (Fin.cases value values) refs).1
      exact Prod.ext equal equal
  | letNeed suspended body ihSuspended ihBody =>
      simp only [embed, readComputation, ScopedNeed.reading, ihSuspended, ihBody]; rfl
  | force reference => rfl

theorem embed_answers (code : Code Head Operation Effect 0 0) (values : Sub Head 0 m) :
    answers primitive (embed code) values = ScopedNeed.answers (Effect := Effect) primitive code values := by
  unfold answers ScopedNeed.answers
  exact congrArg (fun run => (runWorlds run.1 []).map WorldResult.answer) (read_embed primitive code values Fin.elim0)

/-- **On scoped need code the reading of the value layer agrees exactly with
the natural semantics**, from every fresh heap. -/
theorem embed_agreement (code : Code Head Operation Effect 0 0) (values : Sub Head 0 m)
    (world : ScopedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m)
    (fresh : ScopedNeed.Fresh world) (outcome : ScopedNeed.Outcome Head StableFault NativeFault m) :
    outcome ∈ answers primitive (embed code) values ↔
      ∃ final, Nonempty (ScopedNeedNaturalSemantics.Eval primitive ⟨0, 0, code, values, Fin.elim0⟩ world outcome
        final) := by
  rw [embed_answers]
  exact ScopedNeed.closed_agreement (Effect := Effect) primitive code values world fresh outcome

#print axioms read_embed
#print axioms embed_agreement

end ScopedNeedFragment

/-! ## Agreement with the natural semantics without need cells -/

section NeedFree

open Shaped
open PolarizedNeedMachine (RuntimeValue)
open PolarizedNeedNaturalSemantics (Eval Force Selection)

variable {Head Operation Effect StableFault NativeFault : Type} {m : Nat}

mutual
  /-- Values whose thunks use no need cell. -/
  inductive Shaped.Value.NeedFree : {n k : Nat} → {scope : List VShape} → {shape : VShape} →
      Value Head Operation Effect n scope k shape → Prop where
    | native {n k : Nat} {scope : List VShape} (term : Tm Head n) :
        Shaped.Value.NeedFree (Value.native (Operation := Operation) (Effect := Effect) (k := k) (scope := scope) term)
    | var {n k : Nat} {scope : List VShape} {shape : VShape} (index : Member scope shape) :
        Shaped.Value.NeedFree (Value.var (Head := Head) (Operation := Operation) (Effect := Effect) (n := n) (k := k) index)
    | thunk {n k : Nat} {scope : List VShape} {shape : CShape} {body : Computation Head Operation Effect n scope k shape} :
        body.NeedFree → Shaped.Value.NeedFree (Value.thunk body)
    | pack {n k : Nat} {scope : List VShape} {payload : VShape} (index : Tm Head n)
        {value : Value Head Operation Effect n scope k payload} :
        value.NeedFree → Shaped.Value.NeedFree (Value.pack index value)

  /-- Computations that use no need cell: `letNeed` and `forceNeed` do not
  occur.  Sequencing and choice still allocate the cells of the natural
  semantics, which nothing reads again. -/
  inductive Shaped.Computation.NeedFree : {n k : Nat} → {scope : List VShape} → {shape : CShape} →
      Computation Head Operation Effect n scope k shape → Prop where
    | returnValue {n k : Nat} {scope : List VShape} {shape : VShape} {value : Value Head Operation Effect n scope k shape} :
        value.NeedFree → Shaped.Computation.NeedFree (Computation.returnValue value)
    | bindNative {n k : Nat} {scope : List VShape} {shape : CShape}
        {first : Computation Head Operation Effect n scope k (.returns .native)}
        {body : Computation Head Operation Effect (n + 1) scope k shape} :
        first.NeedFree → body.NeedFree → Shaped.Computation.NeedFree (Computation.bindNative first body)
    | bindValue {n k : Nat} {scope : List VShape} {bound : VShape} {shape : CShape}
        {first : Computation Head Operation Effect n scope k (.returns bound)}
        {body : Computation Head Operation Effect n (bound :: scope) k shape} :
        first.NeedFree → body.NeedFree → Shaped.Computation.NeedFree (Computation.bindValue first body)
    | sequenceSigma {n k : Nat} {scope : List VShape}
        {first : Computation Head Operation Effect n scope k (.returns .native)}
        {body : Computation Head Operation Effect (n + 1) scope k (.returns .native)} :
        first.NeedFree → body.NeedFree → Shaped.Computation.NeedFree (Computation.sequenceSigma first body)
    | nativeLambda {n k : Nat} {scope : List VShape} {shape : CShape}
        {body : Computation Head Operation Effect (n + 1) scope k shape} :
        body.NeedFree → Shaped.Computation.NeedFree (Computation.nativeLambda body)
    | nativeApply {n k : Nat} {scope : List VShape} {shape : CShape}
        {function : Computation Head Operation Effect n scope k (.nativePi shape)} (argument : Tm Head n) :
        function.NeedFree → Shaped.Computation.NeedFree (Computation.nativeApply function argument)
    | valueLambda {n k : Nat} {scope : List VShape} {domain : VShape} {shape : CShape}
        {body : Computation Head Operation Effect n (domain :: scope) k shape} :
        body.NeedFree → Shaped.Computation.NeedFree (Computation.valueLambda body)
    | valueApply {n k : Nat} {scope : List VShape} {domain : VShape} {shape : CShape}
        {function : Computation Head Operation Effect n scope k (.arrow domain shape)}
        {argument : Value Head Operation Effect n scope k domain} :
        function.NeedFree → argument.NeedFree → Shaped.Computation.NeedFree (Computation.valueApply function argument)
    | forceThunk {n k : Nat} {scope : List VShape} {shape : CShape}
        {value : Value Head Operation Effect n scope k (.thunk shape)} :
        value.NeedFree → Shaped.Computation.NeedFree (Computation.forceThunk value)
    | unpackNative {n k : Nat} {scope : List VShape} {payload : VShape} {shape : CShape}
        {value : Value Head Operation Effect n scope k (.pack payload)}
        {body : Computation Head Operation Effect (n + 1) (payload :: scope) k shape} :
        value.NeedFree → body.NeedFree → Shaped.Computation.NeedFree (Computation.unpackNative value body)
    | choose {n k : Nat} {scope : List VShape} {shape : CShape}
        {left right : Computation Head Operation Effect n scope k shape} :
        left.NeedFree → right.NeedFree → Shaped.Computation.NeedFree (Computation.choose left right)
    | call {n k : Nat} {scope : List VShape} (operation : Operation) (argument : Tm Head n) :
        Shaped.Computation.NeedFree
          (Computation.call (Head := Head) (Effect := Effect) (k := k) (scope := scope) operation argument)
    | emit {n k : Nat} {scope : List VShape} {shape : CShape} (effect : Effect)
        {next : Computation Head Operation Effect n scope k shape} :
        next.NeedFree → Shaped.Computation.NeedFree (Computation.emit effect next)
end

/-- A retryable fault the machine raises itself, not one a primitive reports. -/
def MachineRaised : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m → Prop
  | .retryableFault (.domain _) => False
  | .retryableFault _ => True
  | _ => False

/-- A freshly allocated cell is suspended with its origin. -/
theorem allocated_suspended {Origin Rule Value StableFault' RetryableFault Effect' : Type}
    {world next : World Origin Rule Value StableFault' RetryableFault Effect'} {origin : Origin} {cell : CellId}
    (allocated : world.allocate? origin = some (next, cell)) :
    next.heap.lookup cell = some ⟨origin, .suspended⟩ := by
  unfold World.allocate? at allocated
  dsimp only at allocated
  split at allocated
  · contradiction
  · rename_i heap allocatedHeap
    cases allocated
    unfold Heap.allocate? at allocatedHeap
    split at allocatedHeap
    · contradiction
    · cases allocatedHeap
      simp [World.record, Heap.lookup]

/-- Finalization answers the producer's outcome, or a retry the machine raises. -/
theorem finalize_raised_or (world : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m)
    (cell : CellId) (owner : EvaluatorId)
    (outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m) :
    MachineRaised (PolarizedNeedNaturalSemantics.finalize world cell owner outcome).1 ∨
      (PolarizedNeedNaturalSemantics.finalize world cell owner outcome).1 = outcome := by
  unfold PolarizedNeedNaturalSemantics.finalize
  split
  · left; simp [PolarizedNeedNaturalSemantics.retryResult, MachineRaised]
  · split
    · split
      · right; cases outcome <;> rfl
      · left; simp [PolarizedNeedNaturalSemantics.retryResult, MachineRaised]
    · left; simp [PolarizedNeedNaturalSemantics.retryResult, MachineRaised]

variable (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)

mutual
  /-- A run-time value of the natural semantics and a value of the reading
  agree at a shape. -/
  def RelValue : (shape : VShape) → RuntimeValue Head Operation Effect m →
      SemValue Head Effect StableFault NativeFault m shape → Prop
    | .native, value, semantic => value = .native semantic
    | .thunk shape, value, semantic =>
        ∃ (n v k : Nat) (code : PolarizedNeed.Computation Head Operation Effect n v k) (native : Sub Head n m)
          (values : Fin v → RuntimeValue Head Operation Effect m) (needs : Fin k → CellId),
          value = .thunk code native values needs ∧
            ∀ world outcome final, Eval primitive ⟨n, v, k, code, native, values, needs⟩ world outcome final →
              ∀ store branch, GoodFrom shape outcome semantic store branch
    | .pack payload, value, semantic =>
        ∃ inner, value = .packNative semantic.1 inner ∧ RelValue payload inner semantic.2

  /-- A natural outcome is good for a computation of the reading run from a
  store.  For a returner, the machine raised a retry of its own, or a world of
  the reading answers it.  For a function, every application is good: a
  function answer's body is, and a fault is the application's outcome. -/
  def GoodFrom : (shape : CShape) → PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m →
      SemComputation Head Effect StableFault NativeFault m shape → ScopedNeed.Store Head StableFault NativeFault m →
        BranchTrace → Prop
    | .returns answer, outcome, program, store, branch =>
        MachineRaised outcome ∨
          ∃ result ∈ runWorldsAt program store branch,
            match outcome, result.answer with
            | .value (.returned value), .value semantic => RelValue answer value semantic
            | .stableFault fault, .stableFault fault' => fault = fault'
            | .retryableFault reason, .retryableFault reason' => reason = PolarizedNeedEmbedding.retry reason'
            | _, _ => False
    | .nativePi shape, outcome, function, store, branch =>
        ∀ argument,
          match outcome with
          | .value (.nativeFunction body) =>
              ∀ world outcome' final, Eval primitive (body.open argument) world outcome' final →
                GoodFrom shape outcome' (function argument) store branch
          | .value _ => False
          | fault => GoodFrom shape fault (function argument) store branch
    | .arrow domain shape, outcome, function, store, branch =>
        ∀ argument semantic, RelValue domain argument semantic →
          match outcome with
          | .value (.valueFunction body) =>
              ∀ world outcome' final, Eval primitive (body.open argument) world outcome' final →
                GoodFrom shape outcome' (function semantic) store branch
          | .value _ => False
          | fault => GoodFrom shape fault (function semantic) store branch
end

/-- Good from every store. -/
def Good (shape : CShape) (outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m)
    (semantic : SemComputation Head Effect StableFault NativeFault m shape) : Prop :=
  ∀ store branch, GoodFrom primitive shape outcome semantic store branch

theorem GoodFrom.raised : (shape : CShape) →
    {outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m} →
    {semantic : SemComputation Head Effect StableFault NativeFault m shape} →
    {store : ScopedNeed.Store Head StableFault NativeFault m} → {branch : BranchTrace} →
    MachineRaised outcome → GoodFrom primitive shape outcome semantic store branch
  | .returns _, _, _, _, _, raised => .inl raised
  | .nativePi shape, outcome, _, _, _, raised => fun _ => by
      cases outcome with
      | value _ => exact raised.elim
      | stableFault _ => exact raised.elim
      | retryableFault _ => exact GoodFrom.raised shape raised
  | .arrow _ shape, outcome, _, _, _, raised => fun _ _ _ => by
      cases outcome with
      | value _ => exact raised.elim
      | stableFault _ => exact raised.elim
      | retryableFault _ => exact GoodFrom.raised shape raised

/-- **Running a program first keeps an outcome good**, if some world of the
program continues into a good run. -/
theorem GoodFrom.bind : (shape : CShape) → {Other : Type} →
    {outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m} →
    (program : Program (ScopedNeed.Store Head StableFault NativeFault m) Other Effect) →
    (next : Other → SemComputation Head Effect StableFault NativeFault m shape) →
    {store : ScopedNeed.Store Head StableFault NativeFault m} → {branch : BranchTrace} →
    (∃ prior ∈ runWorldsAt program store branch,
      GoodFrom primitive shape outcome (next prior.answer) prior.state prior.branch) →
    GoodFrom primitive shape outcome (bindAt shape program next) store branch
  | .returns _, _, _, _, _, _, _, ⟨_, _, .inl raised⟩ => .inl raised
  | .returns _, _, _, _, _, _, _, ⟨_, member, .inr ⟨_, resultMember, agrees⟩⟩ =>
      .inr ⟨_, ScopedNeed.mem_bind member resultMember, agrees⟩
  | .nativePi shape, _, outcome, program, next, _, _, ⟨prior, member, good⟩ => fun argument => by
      have atArgument := good argument
      cases outcome with
      | value answer =>
          cases answer with
          | nativeFunction body =>
              exact fun world outcome' final derivation =>
                GoodFrom.bind shape program (fun other => next other argument)
                  ⟨prior, member, atArgument world outcome' final derivation⟩
          | returned _ => exact atArgument.elim
          | valueFunction _ => exact atArgument.elim
      | stableFault _ => exact GoodFrom.bind shape program (fun other => next other argument) ⟨prior, member, atArgument⟩
      | retryableFault _ =>
          exact GoodFrom.bind shape program (fun other => next other argument) ⟨prior, member, atArgument⟩
  | .arrow _ shape, _, outcome, program, next, _, _, ⟨prior, member, good⟩ => fun argument semantic related => by
      have atArgument := good argument semantic related
      cases outcome with
      | value answer =>
          cases answer with
          | valueFunction body =>
              exact fun world outcome' final derivation =>
                GoodFrom.bind shape program (fun other => next other semantic)
                  ⟨prior, member, atArgument world outcome' final derivation⟩
          | returned _ => exact atArgument.elim
          | nativeFunction _ => exact atArgument.elim
      | stableFault _ => exact GoodFrom.bind shape program (fun other => next other semantic) ⟨prior, member, atArgument⟩
      | retryableFault _ =>
          exact GoodFrom.bind shape program (fun other => next other semantic) ⟨prior, member, atArgument⟩

theorem GoodFrom.failStable : (shape : CShape) → (fault : StableFault) →
    {store : ScopedNeed.Store Head StableFault NativeFault m} → {branch : BranchTrace} →
    GoodFrom primitive shape (.stableFault fault)
      (failAt (Head := Head) (Effect := Effect) shape (.stableFault fault)) store branch
  | .returns _, _, _, _ => .inr ⟨_, List.mem_singleton_self _, rfl⟩
  | .nativePi shape, fault, _, _ => fun _ => GoodFrom.failStable shape fault
  | .arrow _ shape, fault, _, _ => fun _ _ _ => GoodFrom.failStable shape fault

theorem GoodFrom.failRetry : (shape : CShape) → (reason : RetryReason (ScopedNeedMachine.Fault NativeFault)) →
    {store : ScopedNeed.Store Head StableFault NativeFault m} → {branch : BranchTrace} →
    GoodFrom primitive shape (.retryableFault (PolarizedNeedEmbedding.retry reason))
      (failAt (Head := Head) (Effect := Effect) shape (.retryableFault reason)) store branch
  | .returns _, _, _, _ => .inr ⟨_, List.mem_singleton_self _, rfl⟩
  | .nativePi shape, reason, _, _ => fun _ => GoodFrom.failRetry shape reason
  | .arrow _ shape, reason, _, _ => fun _ _ _ => GoodFrom.failRetry shape reason

/-- The allocation of the reading appends a pending cell. -/
theorem alloc_world (store : ScopedNeed.Store Head StableFault NativeFault m) (branch : BranchTrace) :
    (⟨branch, store.length, store ++ [none], []⟩ : WorldResult _ _ Effect) ∈
      runWorldsAt (.read fun store => .write (store ++ [none]) (.pure store.length)) store branch :=
  List.mem_singleton_self _

/-- A cell demanded at once answers what its producer answers. -/
theorem cellAt_world (shape : VShape)
    (producer : SemComputation Head Effect StableFault NativeFault m (.returns shape))
    (store : ScopedNeed.Store Head StableFault NativeFault m) (branch : BranchTrace)
    {result : WorldResult (ScopedNeed.Store Head StableFault NativeFault m)
      (Produced (SemValue Head Effect StableFault NativeFault m shape) StableFault
        (ScopedNeedMachine.Fault NativeFault)) Effect}
    (member : result ∈ runWorldsAt producer (store ++ [none]) branch) :
    ∃ prior ∈ runWorldsAt (cellAt shape store.length producer) (store ++ [none]) branch,
      prior.answer = result.answer := by
  cases shape with
  | native =>
      have pending : (store ++ [none]).getD store.length none = none := by simp
      have pendingRun := ScopedNeed.demand_pending (Effect := Effect) store.length
        (producer : ScopedNeed.Run Head Effect StableFault NativeFault m) (store ++ [none]) branch pending
      refine ⟨WorldResult.prependIntents result.intents
        ⟨result.branch, result.answer, ScopedNeed.settled store.length result.answer result.state, []⟩, ?_, rfl⟩
      show _ ∈ runWorldsAt (ScopedNeed.demand store.length
        (producer : ScopedNeed.Run Head Effect StableFault NativeFault m)) (store ++ [none]) branch
      rw [pendingRun]
      refine ScopedNeed.mem_bind member ?_
      rw [ScopedNeed.settle_run]
      exact List.mem_singleton_self _
  | thunk _ => exact ⟨result, member, rfl⟩
  | pack _ => exact ⟨result, member, rfl⟩

/-- **The force of a fresh cell is good for its producer**, if every
selected occurrence of its origin is. -/
theorem forced_good {shape : CShape} {producer : SemComputation Head Effect StableFault NativeFault m shape}
    {origin : PolarizedNeedMachine.Closure Head Operation Effect m}
    (selectedGood : ∀ position rule selected, Selection origin position rule selected →
      ∀ world outcome final, Eval primitive selected world outcome final → Good primitive shape outcome producer)
    {world next : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m} {cell : CellId}
    (allocated : world.allocate? origin = some (next, cell))
    {outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m}
    {final : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m}
    (forced : Force primitive cell next outcome final) : Good primitive shape outcome producer := by
  have present := allocated_suspended allocated
  cases forced with
  | cachedValue found => rw [present] at found; cases found
  | cachedStable found => rw [present] at found; cases found
  | missing found => rw [present] at found; cases found
  | evaluating found => rw [present] at found; cases found
  | suspended found selection body =>
      rw [present] at found
      cases found
      rcases finalize_raised_or _ _ _ _ with raised | equal
      · exact fun _ _ => GoodFrom.raised primitive shape raised
      · rw [equal]
        exact selectedGood _ _ _ selection _ _ _ body

/-- A choice is good where its left alternative is. -/
theorem Good.chooseLeft {shape : CShape} {outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m}
    {left right : SemComputation Head Effect StableFault NativeFault m shape} (good : Good primitive shape outcome left) :
    Good primitive shape outcome (chooseAt shape left right) := fun store branch =>
  GoodFrom.bind primitive shape _ _ ⟨⟨false :: branch, false, store, []⟩, List.mem_append_left _ (List.mem_singleton_self _),
    good store (false :: branch)⟩

theorem Good.chooseRight {shape : CShape} {outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m}
    {left right : SemComputation Head Effect StableFault NativeFault m shape} (good : Good primitive shape outcome right) :
    Good primitive shape outcome (chooseAt shape left right) := fun store branch =>
  GoodFrom.bind primitive shape _ _ ⟨⟨true :: branch, true, store, []⟩, List.mem_append_right _ (List.mem_singleton_self _),
    good store (true :: branch)⟩

/-- Only a choice has an occurrence other than itself. -/
theorem entry_only {n v k : Nat} {code : PolarizedNeed.Computation Head Operation Effect n v k} {native : Sub Head n m}
    {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
    (notChoice : ∀ left right, code ≠ .choose left right)
    {Goal : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m → Prop}
    (good : ∀ world outcome final, Eval primitive ⟨n, v, k, code, native, values, needs⟩ world outcome final → Goal outcome) :
    ∀ position rule selected, Selection ⟨n, v, k, code, native, values, needs⟩ position rule selected →
      ∀ world outcome final, Eval primitive selected world outcome final → Goal outcome := by
  intro position rule selected selection
  cases selection with
  | entry _ => exact good
  | left left right _ _ _ => exact absurd rfl (notChoice left right)
  | right left right _ _ _ => exact absurd rfl (notChoice left right)

/-- Run-time and semantic environments agree variable by variable. -/
def RelEnv {scope : List VShape} (values : Fin scope.length → RuntimeValue Head Operation Effect m)
    (env : SemEnv (Head := Head) (Effect := Effect) (StableFault := StableFault) (NativeFault := NativeFault)
      (m := m) scope) : Prop :=
  ∀ shape (index : Member scope shape), RelValue primitive shape (values index.index) (env shape index)

theorem RelEnv.cons {scope : List VShape} {shape : VShape}
    {values : Fin scope.length → RuntimeValue Head Operation Effect m}
    {env : SemEnv (Head := Head) (Effect := Effect) (StableFault := StableFault) (NativeFault := NativeFault)
      (m := m) scope}
    (related : RelEnv primitive values env) {value : RuntimeValue Head Operation Effect m}
    {semantic : SemValue Head Effect StableFault NativeFault m shape}
    (head : RelValue primitive shape value semantic) :
    RelEnv primitive (scope := shape :: scope) (Fin.cases value values) (SemEnv.cons semantic env) := by
  intro shape' index
  cases index with
  | zero => exact head
  | succ index => exact related _ index

mutual
  /-- **A value reads as its run-time value**, in agreeing environments. -/
  theorem fundamental_value : {n k : Nat} → {scope : List VShape} → {shape : VShape} →
      {value : Value Head Operation Effect n scope k shape} → value.NeedFree →
      (native : Sub Head n m) → (values : Fin scope.length → RuntimeValue Head Operation Effect m) →
      (needs : Fin k → CellId) →
      (env : SemEnv (Head := Head) (Effect := Effect) (StableFault := StableFault) (NativeFault := NativeFault)
        (m := m) scope) →
      (refs : Fin k → ScopedNeed.Ref Head Effect StableFault NativeFault m) → RelEnv primitive values env →
      RelValue primitive shape (PolarizedNeedMachine.captureValue native values needs value.erase)
        (readValue primitive value native env refs)
    | _, _, _, _, _, .native _, _, _, _, _, _, _ => rfl
    | _, _, _, _, _, .var index, _, _, _, _, _, related => related _ index
    | _, _, _, _, _, .thunk (body := body) bodyFree, native, values, needs, env, refs, related =>
        ⟨_, _, _, body.erase, native, values, needs, rfl,
          (fundamental_computation bodyFree native values needs env refs related).1⟩
    | _, _, _, _, _, .pack _ (value := value) valueFree, native, values, needs, env, refs, related =>
        ⟨_, rfl, fundamental_value valueFree native values needs env refs related⟩

  /-- **The fundamental lemma**: every natural derivation of a computation
  without need cells is good for its reading, and every derivation of a
  selected occurrence is good for its reading as a cell's producer. -/
  theorem fundamental_computation : {n k : Nat} → {scope : List VShape} → {shape : CShape} →
      {computation : Computation Head Operation Effect n scope k shape} → computation.NeedFree →
      (native : Sub Head n m) → (values : Fin scope.length → RuntimeValue Head Operation Effect m) →
      (needs : Fin k → CellId) →
      (env : SemEnv (Head := Head) (Effect := Effect) (StableFault := StableFault) (NativeFault := NativeFault)
        (m := m) scope) →
      (refs : Fin k → ScopedNeed.Ref Head Effect StableFault NativeFault m) → RelEnv primitive values env →
      (∀ world outcome final,
        Eval primitive ⟨n, scope.length, k, computation.erase, native, values, needs⟩ world outcome final →
          Good primitive shape outcome (readComputation primitive computation native env refs).1) ∧
      (∀ position rule selected,
        Selection ⟨n, scope.length, k, computation.erase, native, values, needs⟩ position rule selected →
          ∀ world outcome final, Eval primitive selected world outcome final →
            Good primitive shape outcome (readComputation primitive computation native env refs).2)
    | _, _, _, _, _, .returnValue (value := value) valueFree, native, values, needs, env, refs, related => by
        have good : ∀ world outcome final, Eval primitive ⟨_, _, _, (Computation.returnValue value).erase, native,
            values, needs⟩ world outcome final →
              Good primitive _ outcome (readComputation primitive (.returnValue value) native env refs).1 := by
          intro world outcome final derivation
          cases derivation
          exact fun store branch =>
            .inr ⟨_, List.mem_singleton_self _, fundamental_value valueFree native values needs env refs related⟩
        exact ⟨good, entry_only primitive (fun _ _ equal => by cases equal) good⟩
    | _, _, _, shape, _, .bindNative (first := first) (body := body) firstFree bodyFree, native, values, needs, env,
        refs, related => by
        have good : ∀ world outcome final, Eval primitive ⟨_, _, _, (Computation.bindNative first body).erase, native,
            values, needs⟩ world outcome final →
              Good primitive shape outcome (readComputation primitive (.bindNative first body) native env refs).1 := by
          intro world outcome final derivation
          have producer := (fundamental_computation firstFree native values needs env refs related).2
          cases derivation with
          | bindNativeValue allocated forced bodyDerivation =>
              have firstGood := forced_good primitive producer allocated forced
              have bodyGood := (fundamental_computation bodyFree _ values needs env refs related).1 _ _ _
                bodyDerivation
              intro store branch
              refine GoodFrom.bind primitive shape _ _ ⟨_, alloc_world store branch, ?_⟩
              rcases firstGood (store ++ [none]) branch with raised | ⟨result, member, agrees⟩
              · exact raised.elim
              obtain ⟨prior, priorMember, answer⟩ := cellAt_world .native _ store branch member
              refine GoodFrom.bind primitive shape _ _ ⟨prior, priorMember, ?_⟩
              rw [answer]
              revert agrees
              cases result.answer with
              | value semantic =>
                  intro agrees
                  simp only [RelValue] at agrees
                  injection agrees with agrees
                  subst agrees
                  exact bodyGood _ _
              | stableFault _ => intro agrees; exact agrees.elim
              | retryableFault _ => intro agrees; exact agrees.elim
          | bindNativeMismatch _ allocated forced notNative =>
              rename_i answer
              have firstGood := forced_good primitive producer allocated forced
              rcases firstGood [] [] with raised | ⟨result, resultMember, agrees⟩
              · exact raised.elim
              exfalso
              clear resultMember
              revert agrees
              cases answer with
              | returned returned =>
                  cases result.answer with
                  | value semantic =>
                      intro agrees
                      simp only [RelValue] at agrees
                      exact notNative semantic (by rw [agrees])
                  | stableFault _ => intro agrees; exact agrees
                  | retryableFault _ => intro agrees; exact agrees
              | nativeFunction _ => intro agrees; cases result.answer <;> exact agrees
              | valueFunction _ => intro agrees; cases result.answer <;> exact agrees
          | bindNativeFault _ allocated forced fault =>
              have firstGood := forced_good primitive producer allocated forced
              intro store branch
              refine GoodFrom.bind primitive shape _ _ ⟨_, alloc_world store branch, ?_⟩
              rcases firstGood (store ++ [none]) branch with raised | ⟨result, member, agrees⟩
              · exact GoodFrom.raised primitive shape raised
              obtain ⟨prior, priorMember, answer⟩ := cellAt_world .native _ store branch member
              refine GoodFrom.bind primitive shape _ _ ⟨prior, priorMember, ?_⟩
              rw [answer]
              revert agrees
              cases fault with
              | stableFault fault =>
                  cases result.answer with
                  | stableFault fault' => intro agrees; subst agrees; exact GoodFrom.failStable primitive shape fault
                  | value _ => intro agrees; exact agrees.elim
                  | retryableFault _ => intro agrees; exact agrees.elim
              | retryableFault reason =>
                  cases result.answer with
                  | retryableFault reason' =>
                      intro agrees; subst agrees; exact GoodFrom.failRetry primitive shape reason'
                  | value _ => intro agrees; exact agrees.elim
                  | stableFault _ => intro agrees; exact agrees.elim
          | bindNativeAllocationFailure _ _ =>
              exact fun _ _ => GoodFrom.raised primitive shape (by
                simp [PolarizedNeedNaturalSemantics.allocationFailure, PolarizedNeedNaturalSemantics.retryResult,
                  MachineRaised])
        exact ⟨good, entry_only primitive (fun _ _ equal => by cases equal) good⟩
    | _, _, _, shape, _, .bindValue (first := first) (body := body) firstFree bodyFree, native, values, needs, env,
        refs, related => by
        have good : ∀ world outcome final, Eval primitive ⟨_, _, _, (Computation.bindValue first body).erase, native,
            values, needs⟩ world outcome final →
              Good primitive shape outcome (readComputation primitive (.bindValue first body) native env refs).1 := by
          intro world outcome final derivation
          have producer := (fundamental_computation firstFree native values needs env refs related).2
          cases derivation with
          | bindValueValue allocated forced bodyDerivation =>
              rename_i value
              have firstGood := forced_good primitive producer allocated forced
              intro store branch
              refine GoodFrom.bind primitive shape _ _ ⟨_, alloc_world store branch, ?_⟩
              rcases firstGood (store ++ [none]) branch with raised | ⟨result, member, agrees⟩
              · exact raised.elim
              obtain ⟨prior, priorMember, answer⟩ := cellAt_world _ _ store branch member
              refine GoodFrom.bind primitive shape _ _ ⟨prior, priorMember, ?_⟩
              rw [answer]
              revert agrees
              cases result.answer with
              | value semantic =>
                  intro agrees
                  exact (fundamental_computation bodyFree native
                    (Fin.cases (motive := fun _ => RuntimeValue Head Operation Effect m) value values) needs
                    (SemEnv.cons semantic env) refs (related.cons primitive agrees)).1 _ _ _ bodyDerivation _ _
              | stableFault _ => intro agrees; exact agrees.elim
              | retryableFault _ => intro agrees; exact agrees.elim
          | bindValueMismatch _ allocated forced notReturned =>
              rename_i answer
              have firstGood := forced_good primitive producer allocated forced
              rcases firstGood [] [] with raised | ⟨result, resultMember, agrees⟩
              · exact raised.elim
              exfalso
              clear resultMember
              revert agrees
              cases answer with
              | returned value => exact absurd rfl (notReturned value)
              | nativeFunction _ => intro agrees; cases result.answer <;> exact agrees
              | valueFunction _ => intro agrees; cases result.answer <;> exact agrees
          | bindValueFault _ allocated forced fault =>
              have firstGood := forced_good primitive producer allocated forced
              intro store branch
              refine GoodFrom.bind primitive shape _ _ ⟨_, alloc_world store branch, ?_⟩
              rcases firstGood (store ++ [none]) branch with raised | ⟨result, member, agrees⟩
              · exact GoodFrom.raised primitive shape raised
              obtain ⟨prior, priorMember, answer⟩ := cellAt_world _ _ store branch member
              refine GoodFrom.bind primitive shape _ _ ⟨prior, priorMember, ?_⟩
              rw [answer]
              revert agrees
              cases fault with
              | stableFault fault =>
                  cases result.answer with
                  | stableFault fault' => intro agrees; subst agrees; exact GoodFrom.failStable primitive shape fault
                  | value _ => intro agrees; exact agrees.elim
                  | retryableFault _ => intro agrees; exact agrees.elim
              | retryableFault reason =>
                  cases result.answer with
                  | retryableFault reason' =>
                      intro agrees; subst agrees; exact GoodFrom.failRetry primitive shape reason'
                  | value _ => intro agrees; exact agrees.elim
                  | stableFault _ => intro agrees; exact agrees.elim
          | bindValueAllocationFailure _ _ =>
              exact fun _ _ => GoodFrom.raised primitive shape (by
                simp [PolarizedNeedNaturalSemantics.allocationFailure, PolarizedNeedNaturalSemantics.retryResult,
                  MachineRaised])
        exact ⟨good, entry_only primitive (fun _ _ equal => by cases equal) good⟩
    | _, _, _, _, _, .sequenceSigma (first := first) (body := body) firstFree bodyFree, native, values, needs, env,
        refs, related => by
        have good : ∀ world outcome final, Eval primitive ⟨_, _, _, (Computation.sequenceSigma first body).erase,
            native, values, needs⟩ world outcome final →
              Good primitive (.returns .native) outcome
                (readComputation primitive (.sequenceSigma first body) native env refs).1 := by
          intro world outcome final derivation
          have producer := (fundamental_computation firstFree native values needs env refs related).2
          cases derivation with
          | sequenceSigmaValue allocated forced bodyDerivation =>
              rename_i value bodyOutcome
              have firstGood := forced_good primitive producer allocated forced
              have bodyGood := (fundamental_computation bodyFree _ values needs env refs related).1 _ _ _
                bodyDerivation
              intro store branch
              refine GoodFrom.bind primitive (.returns .native) _ _ ⟨_, alloc_world store branch, ?_⟩
              rcases firstGood (store ++ [none]) branch with raised | ⟨result, member, agrees⟩
              · exact raised.elim
              obtain ⟨prior, priorMember, answer⟩ := cellAt_world .native _ store branch member
              refine GoodFrom.bind primitive (.returns .native) _ _ ⟨prior, priorMember, ?_⟩
              rw [answer]
              revert agrees
              cases result.answer with
              | value semantic =>
                  intro agrees
                  simp only [RelValue] at agrees
                  injection agrees with agrees
                  subst agrees
                  rcases bodyGood prior.state prior.branch with raised | ⟨second, secondMember, secondAgrees⟩
                  · left
                    revert raised
                    cases bodyOutcome with
                    | value _ => exact False.elim
                    | stableFault _ => exact False.elim
                    | retryableFault _ => exact id
                  · right
                    obtain ⟨branch₂, answer₂, state₂, intents₂⟩ := second
                    refine ⟨WorldResult.prependIntents intents₂
                      ⟨branch₂, ScopedNeedNaturalSemantics.pairOutcome value answer₂, state₂, []⟩,
                      ScopedNeed.mem_bind secondMember (List.mem_singleton_self _), ?_⟩
                    · revert secondAgrees
                      cases bodyOutcome with
                      | value bodyAnswer =>
                          cases bodyAnswer with
                          | returned returned =>
                              cases answer₂ with
                              | value term =>
                                  intro secondAgrees
                                  simp only [RelValue] at secondAgrees
                                  subst secondAgrees
                                  rfl
                              | stableFault _ => exact False.elim
                              | retryableFault _ => exact False.elim
                          | nativeFunction _ => intro secondAgrees; cases answer₂ <;> exact secondAgrees.elim
                          | valueFunction _ => intro secondAgrees; cases answer₂ <;> exact secondAgrees.elim
                      | stableFault _ =>
                          cases answer₂ with
                          | stableFault _ => exact id
                          | value _ => exact False.elim
                          | retryableFault _ => exact False.elim
                      | retryableFault _ =>
                          cases answer₂ with
                          | retryableFault _ => exact id
                          | value _ => exact False.elim
                          | stableFault _ => exact False.elim
              | stableFault _ => intro agrees; exact agrees.elim
              | retryableFault _ => intro agrees; exact agrees.elim
          | sequenceSigmaMismatch _ allocated forced notNative =>
              rename_i answer
              have firstGood := forced_good primitive producer allocated forced
              rcases firstGood [] [] with raised | ⟨result, resultMember, agrees⟩
              · exact raised.elim
              exfalso
              clear resultMember
              revert agrees
              cases answer with
              | returned returned =>
                  cases result.answer with
                  | value semantic =>
                      intro agrees
                      simp only [RelValue] at agrees
                      exact notNative semantic (by rw [agrees])
                  | stableFault _ => intro agrees; exact agrees
                  | retryableFault _ => intro agrees; exact agrees
              | nativeFunction _ => intro agrees; cases result.answer <;> exact agrees
              | valueFunction _ => intro agrees; cases result.answer <;> exact agrees
          | sequenceSigmaFault _ allocated forced fault =>
              have firstGood := forced_good primitive producer allocated forced
              intro store branch
              refine GoodFrom.bind primitive (.returns .native) _ _ ⟨_, alloc_world store branch, ?_⟩
              rcases firstGood (store ++ [none]) branch with raised | ⟨result, member, agrees⟩
              · exact GoodFrom.raised primitive _ raised
              obtain ⟨prior, priorMember, answer⟩ := cellAt_world .native _ store branch member
              refine GoodFrom.bind primitive (.returns .native) _ _ ⟨prior, priorMember, ?_⟩
              rw [answer]
              revert agrees
              cases fault with
              | stableFault fault =>
                  cases result.answer with
                  | stableFault fault' => intro agrees; subst agrees; exact GoodFrom.failStable primitive _ fault
                  | value _ => intro agrees; exact agrees.elim
                  | retryableFault _ => intro agrees; exact agrees.elim
              | retryableFault reason =>
                  cases result.answer with
                  | retryableFault reason' =>
                      intro agrees; subst agrees; exact GoodFrom.failRetry primitive _ reason'
                  | value _ => intro agrees; exact agrees.elim
                  | stableFault _ => intro agrees; exact agrees.elim
          | sequenceSigmaAllocationFailure _ _ =>
              exact fun _ _ => GoodFrom.raised primitive _ (by
                simp [PolarizedNeedNaturalSemantics.allocationFailure, PolarizedNeedNaturalSemantics.retryResult,
                  MachineRaised])
        exact ⟨good, entry_only primitive (fun _ _ equal => by cases equal) good⟩
    | _, _, _, _, _, .nativeLambda (body := body) bodyFree, native, values, needs, env, refs, related => by
        have good : ∀ world outcome final, Eval primitive ⟨_, _, _, (Computation.nativeLambda body).erase, native,
            values, needs⟩ world outcome final →
              Good primitive _ outcome (readComputation primitive (.nativeLambda body) native env refs).1 := by
          intro world outcome final derivation
          cases derivation
          intro store branch argument world' outcome' final' bodyDerivation
          exact (fundamental_computation bodyFree (Fin.cases (motive := fun _ => Tm Head m) argument native) values
            needs env refs related).1 _ _ _ bodyDerivation store branch
        exact ⟨good, entry_only primitive (fun _ _ equal => by cases equal) good⟩
    | _, _, _, shape, _, .nativeApply (function := function) argument functionFree, native, values, needs, env, refs,
        related => by
        have good : ∀ world outcome final, Eval primitive ⟨_, _, _, (Computation.nativeApply function argument).erase,
            native, values, needs⟩ world outcome final →
              Good primitive shape outcome
                (readComputation primitive (.nativeApply function argument) native env refs).1 := by
          intro world outcome final derivation
          have functionGood := (fundamental_computation functionFree native values needs env refs related).1
          cases derivation with
          | nativeApply _ functionDerivation bodyDerivation =>
              intro store branch
              exact functionGood _ _ _ functionDerivation store branch (subst native argument) _ _ _ bodyDerivation
          | nativeApplyMismatch _ functionDerivation notFunction =>
              rename_i answer
              have atArgument := functionGood _ _ _ functionDerivation [] [] (subst native argument)
              exfalso
              revert atArgument
              cases answer with
              | nativeFunction body => exact absurd rfl (notFunction body)
              | returned _ => exact id
              | valueFunction _ => exact id
          | nativeApplyFault _ functionDerivation fault =>
              intro store branch
              have atArgument := functionGood _ _ _ functionDerivation store branch (subst native argument)
              cases fault <;> exact atArgument
        exact ⟨good, entry_only primitive (fun _ _ equal => by cases equal) good⟩
    | _, _, _, _, _, .valueLambda (body := body) bodyFree, native, values, needs, env, refs, related => by
        have good : ∀ world outcome final, Eval primitive ⟨_, _, _, (Computation.valueLambda body).erase, native,
            values, needs⟩ world outcome final →
              Good primitive _ outcome (readComputation primitive (.valueLambda body) native env refs).1 := by
          intro world outcome final derivation
          cases derivation
          intro store branch argument semantic relatedArgument world' outcome' final' bodyDerivation
          exact (fundamental_computation bodyFree native
            (Fin.cases (motive := fun _ => RuntimeValue Head Operation Effect m) argument values) needs
            (SemEnv.cons semantic env) refs (related.cons primitive relatedArgument)).1 _ _ _ bodyDerivation store branch
        exact ⟨good, entry_only primitive (fun _ _ equal => by cases equal) good⟩
    | _, _, _, shape, _, .valueApply (function := function) (argument := argument) functionFree argumentFree,
        native, values, needs, env, refs, related => by
        have good : ∀ world outcome final, Eval primitive ⟨_, _, _, (Computation.valueApply function argument).erase,
            native, values, needs⟩ world outcome final →
              Good primitive shape outcome
                (readComputation primitive (.valueApply function argument) native env refs).1 := by
          intro world outcome final derivation
          have functionGood := (fundamental_computation functionFree native values needs env refs related).1
          have argumentRelated := fundamental_value argumentFree native values needs env refs related
          cases derivation with
          | valueApply _ functionDerivation bodyDerivation =>
              intro store branch
              exact functionGood _ _ _ functionDerivation store branch _ _ argumentRelated _ _ _ bodyDerivation
          | valueApplyMismatch _ functionDerivation notFunction =>
              rename_i answer
              have atArgument := functionGood _ _ _ functionDerivation [] [] _ _ argumentRelated
              exfalso
              revert atArgument
              cases answer with
              | valueFunction body => exact absurd rfl (notFunction body)
              | returned _ => exact id
              | nativeFunction _ => exact id
          | valueApplyFault _ functionDerivation fault =>
              intro store branch
              have atArgument := functionGood _ _ _ functionDerivation store branch _ _ argumentRelated
              cases fault <;> exact atArgument
        exact ⟨good, entry_only primitive (fun _ _ equal => by cases equal) good⟩
    | _, _, _, shape, _, .forceThunk (value := value) valueFree, native, values, needs, env, refs, related => by
        have good : ∀ world outcome final, Eval primitive ⟨_, _, _, (Computation.forceThunk value).erase,
            native, values, needs⟩ world outcome final →
              Good primitive shape outcome (readComputation primitive (.forceThunk value) native env refs).1 := by
          intro world outcome final derivation
          obtain ⟨_, _, _, code, native', values', needs', captured, thunkGood⟩ :=
            fundamental_value valueFree native values needs env refs related
          cases derivation with
          | forceThunk _ captured' thunkDerivation =>
              rw [captured] at captured'
              cases captured'
              exact thunkGood _ _ _ thunkDerivation
          | forceThunkMismatch _ _ notThunk => exact absurd captured (notThunk _ _ _ _ _ _ _)
        exact ⟨good, entry_only primitive (fun _ _ equal => by cases equal) good⟩
    | _, _, _, shape, _, .unpackNative (value := value) (body := body) valueFree bodyFree, native, values, needs, env,
        refs, related => by
        have good : ∀ world outcome final, Eval primitive ⟨_, _, _, (Computation.unpackNative value body).erase,
            native, values, needs⟩ world outcome final →
              Good primitive shape outcome (readComputation primitive (.unpackNative value body) native env refs).1 := by
          intro world outcome final derivation
          obtain ⟨inner, captured, innerRelated⟩ := fundamental_value valueFree native values needs env refs related
          cases derivation with
          | unpackNative _ captured' bodyDerivation =>
              rw [captured] at captured'
              cases captured'
              exact (fundamental_computation bodyFree _ _ needs (SemEnv.cons (readValue primitive value native env refs).2 env)
                refs (related.cons primitive innerRelated)).1 _ _ _ bodyDerivation
          | unpackNativeMismatch _ _ _ notPackage => exact absurd captured (notPackage _ _)
        exact ⟨good, entry_only primitive (fun _ _ equal => by cases equal) good⟩
    | _, _, _, shape, _, .choose (left := left) (right := right) leftFree rightFree, native, values, needs, env, refs,
        related => by
        have leftGood := (fundamental_computation leftFree native values needs env refs related).1
        have rightGood := (fundamental_computation rightFree native values needs env refs related).1
        have selectedGood : ∀ position rule selected,
            Selection ⟨_, _, _, (Computation.choose left right).erase, native, values, needs⟩ position rule selected →
              ∀ world outcome final, Eval primitive selected world outcome final →
                Good primitive shape outcome (readComputation primitive (.choose left right) native env refs).2 := by
          intro position rule selected selection world outcome final derivation
          cases selection with
          | entry notChoice => exact absurd rfl (notChoice _ _)
          | left => exact Good.chooseLeft primitive (leftGood _ _ _ derivation)
          | right => exact Good.chooseRight primitive (rightGood _ _ _ derivation)
        refine ⟨?_, selectedGood⟩
        intro world outcome final derivation
        cases derivation with
        | choose _ _ allocated forced =>
            have producerGood := forced_good primitive selectedGood allocated forced
            intro store branch
            refine GoodFrom.bind primitive shape _ _ ⟨_, alloc_world store branch, ?_⟩
            cases shape with
            | returns answer =>
                rcases producerGood (store ++ [none]) branch with raised | ⟨result, member, agrees⟩
                · exact .inl raised
                obtain ⟨prior, priorMember, sameAnswer⟩ := cellAt_world answer _ store branch member
                exact .inr ⟨prior, priorMember, sameAnswer ▸ agrees⟩
            | nativePi shape => exact producerGood (store ++ [none]) branch
            | arrow domain shape => exact producerGood (store ++ [none]) branch
        | chooseAllocationFailure _ _ _ =>
            exact fun _ _ => GoodFrom.raised primitive shape (by
              simp [PolarizedNeedNaturalSemantics.allocationFailure, PolarizedNeedNaturalSemantics.retryResult,
                MachineRaised])
    | _, _, _, _, _, .call operation argument, native, values, needs, env, refs, _ => by
        have good : ∀ world outcome final, Eval primitive ⟨_, _, _, (Computation.call (Head := Head)
            (Effect := Effect) (k := _) (scope := _) operation argument).erase, native, values, needs⟩ world outcome
              final → Good primitive _ outcome (readComputation primitive (.call operation argument) native env refs).1 := by
          intro world outcome final derivation
          cases derivation
          intro store branch
          refine .inr ⟨_, List.mem_singleton_self _, ?_⟩
          generalize primitive operation (subst native argument) = produced
          cases produced with
          | value term => rfl
          | stableFault fault => rfl
          | retryableFault reason => cases reason <;> rfl
        exact ⟨good, entry_only primitive (fun _ _ equal => by cases equal) good⟩
    | _, _, _, shape, _, .emit effect (next := next) nextFree, native, values, needs, env, refs, related => by
        have good : ∀ world outcome final, Eval primitive ⟨_, _, _, (Computation.emit effect next).erase,
            native, values, needs⟩ world outcome final →
              Good primitive shape outcome (readComputation primitive (.emit effect next) native env refs).1 := by
          intro world outcome final derivation
          cases derivation with
          | emit _ nextDerivation =>
              intro store branch
              exact GoodFrom.bind primitive shape _ _ ⟨⟨branch, (), store, [effect]⟩, List.mem_singleton_self _,
                (fundamental_computation nextFree native values needs env refs related).1 _ _ _ nextDerivation
                  store branch⟩
        exact ⟨good, entry_only primitive (fun _ _ equal => by cases equal) good⟩
end

/-- **Without need cells, every natural outcome is an answer of the
reading**, other than a retry the machine raises itself: for a closed native
returner, from any world, with first-class thunks, value and native lambdas,
packages, sequencing and choice. -/
theorem needFree_sound {computation : Computation Head Operation Effect 0 [] 0 (.returns .native)}
    (needFree : computation.NeedFree) (native : Sub Head 0 m)
    {world final : PolarizedNeedMachine.NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m}
    (derivation : Eval primitive ⟨0, 0, 0, computation.erase, native, Fin.elim0, Fin.elim0⟩ world outcome final)
    (notRaised : ¬ MachineRaised outcome) :
    ∃ answer ∈ answers primitive computation native, outcome = PolarizedNeedEmbedding.outcome answer := by
  rcases (fundamental_computation primitive needFree native Fin.elim0 Fin.elim0 SemEnv.empty Fin.elim0
      (fun _ index => nomatch index)).1 world outcome final derivation [] [] with raised | ⟨result, member, agrees⟩
  · exact absurd raised notRaised
  refine ⟨result.answer, List.mem_map.mpr ⟨result, member, rfl⟩, ?_⟩
  revert agrees
  cases outcome with
  | value answer =>
      cases answer with
      | returned value =>
          cases result.answer with
          | value term => intro agrees; simp only [RelValue] at agrees; subst agrees; rfl
          | stableFault _ => intro agrees; exact agrees.elim
          | retryableFault _ => intro agrees; exact agrees.elim
      | nativeFunction _ => intro agrees; cases result.answer <;> exact agrees.elim
      | valueFunction _ => intro agrees; cases result.answer <;> exact agrees.elim
  | stableFault fault =>
      cases result.answer with
      | value _ => intro agrees; exact agrees.elim
      | stableFault _ => intro agrees; subst agrees; rfl
      | retryableFault _ => intro agrees; exact agrees.elim
  | retryableFault reason =>
      cases result.answer with
      | value _ => intro agrees; exact agrees.elim
      | stableFault _ => intro agrees; exact agrees.elim
      | retryableFault _ => intro agrees; subst agrees; rfl

#print axioms fundamental_computation
#print axioms needFree_sound

end NeedFree


/-! ## Examples -/

namespace Examples

open Shaped
open ScopedNeedNaturalSemantics.Examples (ExampleOperation)

abbrev examplePrimitive := ScopedNeedNaturalSemantics.Examples.primitive

/-- A choice between two heads. -/
def coin {n k : Nat} {scope : List VShape} : Computation Nat ExampleOperation Nat n scope k (.returns .native) :=
  .choose (.returnValue (.native (.head 1))) (.returnValue (.native (.head 2)))

/-- Force the thunk bound last twice and pair the answers. -/
def forceTwice {n k : Nat} {scope : List VShape} :
    Computation Nat ExampleOperation Nat n (.thunk (.returns .native) :: scope) k (.returns .native) :=
  .bindNative (.forceThunk (.var .zero))
    (.bindNative (.forceThunk (.var .zero)) (.returnValue (.native (.pair (.var 1) (.var 0)))))

/-- **A thunk runs again at every force**: a thunk of the choice, forced twice,
gives four pairs. -/
def thunkedCoin : Computation Nat ExampleOperation Nat 0 [] 0 (.returns .native) :=
  .bindValue (.returnValue (.thunk coin)) forceTwice

theorem thunkedCoin_answers :
    answers (Effect := Nat) examplePrimitive thunkedCoin ids =
      [.value (.pair (.head 1) (.head 1)), .value (.pair (.head 1) (.head 2)),
       .value (.pair (.head 2) (.head 1)), .value (.pair (.head 2) (.head 2))] := by
  decide

/-- **A need cell captured by a thunk is shared**: forcing the thunk twice
demands one cell, so the two answers agree. -/
def sharedInThunk : Computation Nat ExampleOperation Nat 0 [] 0 (.returns .native) :=
  .letNeed coin (.bindValue (.returnValue (.thunk (.forceNeed 0))) forceTwice)

theorem sharedInThunk_answers :
    answers (Effect := Nat) examplePrimitive sharedInThunk ids =
      [.value (.pair (.head 1) (.head 1)), .value (.pair (.head 2) (.head 2))] := by
  decide

/-- A value lambda that forces its thunked argument twice. -/
def twice {k : Nat} :
    Computation Nat ExampleOperation Nat 0 [] k (.arrow (.thunk (.returns .native)) (.returns .native)) :=
  .valueLambda forceTwice

/-- **Value lambdas pass thunks**: applied to a thunk of the choice, four
pairs; applied to a thunk that demands a need cell of it, two. -/
theorem twice_thunk_answers :
    answers (Effect := Nat) examplePrimitive (.valueApply twice (.thunk coin)) ids =
      [.value (.pair (.head 1) (.head 1)), .value (.pair (.head 1) (.head 2)),
       .value (.pair (.head 2) (.head 1)), .value (.pair (.head 2) (.head 2))] := by
  decide

theorem twice_need_answers :
    answers (Effect := Nat) examplePrimitive (.letNeed coin (.valueApply twice (.thunk (.forceNeed 0)))) ids =
      [.value (.pair (.head 1) (.head 1)), .value (.pair (.head 2) (.head 2))] := by
  decide

/-- **A package keeps its index with its payload**: a package of the index 7
and a thunk of the choice, unpacked and forced. -/
def packed : Computation Nat ExampleOperation Nat 0 [] 0 (.returns .native) :=
  .unpackNative (.pack (.head 7) (.thunk coin))
    (.bindNative (.forceThunk (.var .zero)) (.returnValue (.native (.pair (.var 1) (.var 0)))))

theorem packed_answers :
    answers (Effect := Nat) examplePrimitive packed ids =
      [.value (.pair (.head 7) (.head 1)), .value (.pair (.head 7) (.head 2))] := by
  decide

/-- The higher-order example of the raw syntax, applying a thunked function
to an argument, at its shapes; it lies outside the scoped-need image
(`PolarizedNeed.applyThunked_outside_old_image`). -/
def applyThunked {domain : VShape} {shape : CShape} :
    Computation Nat ExampleOperation Nat 0 [] 0 (.arrow (.thunk (.arrow domain shape)) (.arrow domain shape)) :=
  .valueLambda (.valueLambda (.valueApply (.forceThunk (.var (.succ .zero))) (.var .zero)))

theorem applyThunked_erase {domain : VShape} {shape : CShape} :
    (applyThunked (domain := domain) (shape := shape)).erase = PolarizedNeed.applyThunked := rfl

/-- It applied to a thunked function that forces its argument, and to a
thunked head. -/
def applied : Computation Nat ExampleOperation Nat 0 [] 0 (.returns .native) :=
  .valueApply (.valueApply applyThunked (.thunk (.valueLambda (.forceThunk (.var .zero)))))
    (.thunk (.returnValue (.native (.head 5))))

theorem applied_needFree : applied.NeedFree := by
  repeat' constructor

theorem applied_answers : answers (Effect := Nat) examplePrimitive applied ids = [.value (.head 5)] := by
  decide

/-- **So every natural derivation of its erasure returns the head**, from any
world, unless the machine raises a retry of its own. -/
theorem applied_natural {world final : PolarizedNeedMachine.NeedWorld Nat ExampleOperation Nat Nat Nat 0}
    {outcome : PolarizedNeedMachine.Outcome Nat ExampleOperation Nat Nat Nat 0}
    (derivation : PolarizedNeedNaturalSemantics.Eval examplePrimitive
      ⟨0, 0, 0, applied.erase, ids, Fin.elim0, Fin.elim0⟩ world outcome final)
    (notRaised : ¬ MachineRaised outcome) :
    outcome = .value (.returned (.native (.head 5))) := by
  obtain ⟨answer, member, equal⟩ := needFree_sound examplePrimitive applied_needFree ids derivation notRaised
  rw [applied_answers, List.mem_singleton] at member
  subst member
  exact equal

theorem thunkedCoin_needFree : thunkedCoin.NeedFree := by
  repeat' constructor

/-- **A thunk of a choice, forced twice, in the natural semantics**: every
derivation of its erasure answers one of the four pairs, unless the machine
raises a retry of its own. -/
theorem thunkedCoin_natural {world final : PolarizedNeedMachine.NeedWorld Nat ExampleOperation Nat Nat Nat 0}
    {outcome : PolarizedNeedMachine.Outcome Nat ExampleOperation Nat Nat Nat 0}
    (derivation : PolarizedNeedNaturalSemantics.Eval examplePrimitive
      ⟨0, 0, 0, thunkedCoin.erase, ids, Fin.elim0, Fin.elim0⟩ world outcome final)
    (notRaised : ¬ MachineRaised outcome) :
    outcome ∈ ([.value (.pair (.head 1) (.head 1)), .value (.pair (.head 1) (.head 2)),
      .value (.pair (.head 2) (.head 1)), .value (.pair (.head 2) (.head 2))] :
        List (ScopedNeedMachine.Outcome Nat Nat Nat 0)).map PolarizedNeedEmbedding.outcome := by
  obtain ⟨answer, member, equal⟩ := needFree_sound examplePrimitive thunkedCoin_needFree ids derivation notRaised
  rw [thunkedCoin_answers] at member
  exact List.mem_map.mpr ⟨answer, member, equal.symm⟩

/-! ### The side condition is necessary -/

/-- A world whose next allocation collides with a cell it already holds. -/
def collidingWorld : PolarizedNeedMachine.NeedWorld Nat ExampleOperation Nat Nat Nat 0 :=
  { lineage := 0, path := [], receipts := .empty, nextCell := 0, nextEvaluator := 0,
    heap := { current := Function.update (fun _ => none) ⟨0, [], 0, 0⟩
                (some ⟨⟨0, 0, 0, .returnValue (.native (.head 1)), ids, Fin.elim0, Fin.elim0⟩, .suspended⟩),
              spine := [] } }

/-- A native sequencing, which allocates a cell. -/
def sequenced : Computation Nat ExampleOperation Nat 0 [] 0 (.returns .native) :=
  .bindNative (.returnValue (.native (.head 1))) (.returnValue (.native (.var 0)))

theorem sequenced_needFree : sequenced.NeedFree := by
  repeat' constructor

theorem sequenced_answers : answers (Effect := Nat) examplePrimitive sequenced ids = [.value (.head 1)] := by
  decide

/-- **Without the side condition the conclusion fails**: from a heap whose
next allocation collides, the natural semantics derives a retry the machine
raises itself, which no answer of the reading is. -/
theorem raised_necessary :
    ∃ (outcome : PolarizedNeedMachine.Outcome Nat ExampleOperation Nat Nat Nat 0)
      (final : PolarizedNeedMachine.NeedWorld Nat ExampleOperation Nat Nat Nat 0),
      Nonempty (PolarizedNeedNaturalSemantics.Eval examplePrimitive
        ⟨0, 0, 0, sequenced.erase, ids, Fin.elim0, Fin.elim0⟩ collidingWorld outcome final) ∧
      MachineRaised outcome ∧
      ¬ ∃ answer ∈ answers (Effect := Nat) examplePrimitive sequenced ids,
        outcome = PolarizedNeedEmbedding.outcome answer := by
  refine ⟨_, _, ⟨PolarizedNeedNaturalSemantics.Eval.bindNativeAllocationFailure _ ?_⟩, ?_, ?_⟩
  · simp [collidingWorld, World.allocate?, Heap.allocate?, Heap.lookup, World.freshCell]
  · simp [MachineRaised, PolarizedNeedNaturalSemantics.allocationFailure, PolarizedNeedNaturalSemantics.retryResult]
  · rw [sequenced_answers]
    simp [PolarizedNeedEmbedding.outcome, PolarizedNeedNaturalSemantics.allocationFailure,
      PolarizedNeedNaturalSemantics.retryResult]

end Examples

end Mettapedia.TypeTheory.ContextualCBPV.PolarizedValues
