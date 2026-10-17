import Mathlib.Computability.TuringMachine.Computable

/-!
# Extra finite registers for stack-machine subroutines

An original statement acts on its own state component while retaining a
caller's separate registers. Label renaming embeds the original subroutine
in a larger control graph; every statement keeps its original stack effects.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.StackMachineRegisters

open Turing

universe u v w x y z
variable {Key : Type u} {Label : Type v} {Label' : Type w}
  {State : Type x} {Extra : Type y} {Alphabet : Key → Type z}

/-- Embed a statement using its physical stack, label and register maps.
The operation needs no packaged machine or enumeration of finite states.
The supplied halt statement is the caller's explicit continuation. -/
def embedStatement {TargetKey : Type u} {TargetState : Type x}
    {TargetAlphabet : TargetKey → Type z}
    (keys : Key → TargetKey) (labels : Label → Label')
    (pull : TargetState → State) (put : TargetState → State → TargetState)
    (cells : ∀ key, Alphabet key = TargetAlphabet (keys key))
    (onHalt : TM2.Stmt TargetAlphabet Label' TargetState) :
    TM2.Stmt Alphabet Label State → TM2.Stmt TargetAlphabet Label' TargetState
  | .push key value rest => .push (keys key)
      (fun state => (cells key).mp (value (pull state)))
      (embedStatement keys labels pull put cells onHalt rest)
  | .peek key update rest => .peek (keys key)
      (fun state value => put state
        (update (pull state) ((congrArg Option (cells key).symm).mp value)))
      (embedStatement keys labels pull put cells onHalt rest)
  | .pop key update rest => .pop (keys key)
      (fun state value => put state
        (update (pull state) ((congrArg Option (cells key).symm).mp value)))
      (embedStatement keys labels pull put cells onHalt rest)
  | .load update rest => .load (fun state => put state (update (pull state)))
      (embedStatement keys labels pull put cells onHalt rest)
  | .branch condition yes no => .branch (fun state => condition (pull state))
      (embedStatement keys labels pull put cells onHalt yes)
      (embedStatement keys labels pull put cells onHalt no)
  | .goto label => .goto (fun state => labels (label (pull state)))
  | .halt => onHalt

/-- An embedded subroutine returns to a fixed caller label at its original
halt boundary. Stack and register maps are supplied by the caller. -/
def embeddedReturningConfig {TargetKey : Type u} {TargetState : Type x}
    {TargetAlphabet : TargetKey → Type z}
    (labels : Label → Label') (resume : Label') (registers : State → TargetState)
    (storage : (∀ key, List (Alphabet key)) → ∀ key, List (TargetAlphabet key))
    (source : TM2.Cfg Alphabet Label State) : TM2.Cfg TargetAlphabet Label' TargetState where
  l := some (source.l.elim resume labels)
  var := registers source.var
  stk := storage source.stk

private theorem cast_head {First Second : Type z} (same : First = Second) (word : List First) :
    (congrArg Option same.symm).mp ((word.map same.mp).head?) = word.head? := by
  cases same
  change (word.map id).head? = word.head?
  simp

/-- An original halted configuration executes the caller's finite continuation in the same physical step. -/
def embeddedContinuationConfig {TargetKey : Type u} [DecidableEq TargetKey] {TargetState : Type x}
    {TargetAlphabet : TargetKey → Type z}
    (labels : Label → Label') (registers : State → TargetState)
    (storage : (∀ key, List (Alphabet key)) → ∀ key, List (TargetAlphabet key))
    (onHalt : TM2.Stmt TargetAlphabet Label' TargetState)
    (source : TM2.Cfg Alphabet Label State) : TM2.Cfg TargetAlphabet Label' TargetState :=
  match source.l with
  | none => TM2.stepAux onHalt (registers source.var) (storage source.stk)
  | some label => ⟨some (labels label),registers source.var,storage source.stk⟩

theorem stepAux_embedContinuation [DecidableEq Key]
    {TargetKey : Type u} [DecidableEq TargetKey] {TargetState : Type x}
    {TargetAlphabet : TargetKey → Type z}
    (keys : Key → TargetKey) (labels : Label → Label')
    (onHalt : TM2.Stmt TargetAlphabet Label' TargetState)
    (pull : TargetState → State) (put : TargetState → State → TargetState)
    (cells : ∀ key, Alphabet key = TargetAlphabet (keys key))
    (registers : State → TargetState)
    (storage : (∀ key, List (Alphabet key)) → ∀ key, List (TargetAlphabet key))
    (readRegisters : ∀ state, pull (registers state) = state)
    (writeRegisters : ∀ state value, put (registers state) value = registers value)
    (readStack : ∀ contents key,
      storage contents (keys key) = (contents key).map (cells key).mp)
    (writeStack : ∀ contents key value,
      storage (Function.update contents key value) =
        Function.update (storage contents) (keys key) (value.map (cells key).mp))
    (statement : TM2.Stmt Alphabet Label State) (state : State)
    (contents : ∀ key, List (Alphabet key)) :
    TM2.stepAux (embedStatement keys labels pull put cells onHalt statement)
        (registers state) (storage contents) =
      embeddedContinuationConfig labels registers storage onHalt (TM2.stepAux statement state contents) := by
  induction statement generalizing state contents with
  | push key value rest ih =>
      simp only [embedStatement, TM2.stepAux, readRegisters]
      rw [readStack, ← List.map_cons, ← writeStack]
      exact ih state _
  | peek key update rest ih =>
      simp only [embedStatement, TM2.stepAux, readRegisters, readStack, cast_head, writeRegisters]
      exact ih _ contents
  | pop key update rest ih =>
      simp only [embedStatement, TM2.stepAux, readRegisters, readStack, cast_head, writeRegisters]
      rw [← List.map_tail, ← writeStack]
      exact ih _ _
  | load update rest ih =>
      simpa only [embedStatement, TM2.stepAux, readRegisters, writeRegisters] using ih _ contents
  | branch condition yes no yesIH noIH =>
      cases h : condition state <;>
        simp [embedStatement, TM2.stepAux, readRegisters, h, yesIH, noIH]
  | goto label => simp only [embedStatement, TM2.stepAux, readRegisters, embeddedContinuationConfig]
  | halt => rfl


/-- Every original statement has exactly the same physical stack effects
under a caller's stack and register embeddings. The read and update laws
record where the original storage live, including retained caller storage. -/
theorem stepAux_embedStatement [DecidableEq Key]
    {TargetKey : Type u} [DecidableEq TargetKey] {TargetState : Type x}
    {TargetAlphabet : TargetKey → Type z}
    (keys : Key → TargetKey) (labels : Label → Label') (resume : Label')
    (pull : TargetState → State) (put : TargetState → State → TargetState)
    (cells : ∀ key, Alphabet key = TargetAlphabet (keys key))
    (registers : State → TargetState)
    (storage : (∀ key, List (Alphabet key)) → ∀ key, List (TargetAlphabet key))
    (readRegisters : ∀ state, pull (registers state) = state)
    (writeRegisters : ∀ state value, put (registers state) value = registers value)
    (readStack : ∀ contents key,
      storage contents (keys key) = (contents key).map (cells key).mp)
    (writeStack : ∀ contents key value,
      storage (Function.update contents key value) =
        Function.update (storage contents) (keys key) (value.map (cells key).mp))
    (statement : TM2.Stmt Alphabet Label State) (state : State)
    (contents : ∀ key, List (Alphabet key)) :
    TM2.stepAux (embedStatement keys labels pull put cells (.goto (fun _ => resume)) statement)
        (registers state) (storage contents) =
      embeddedReturningConfig labels resume registers storage (TM2.stepAux statement state contents) := by
  have same := stepAux_embedContinuation keys labels (.goto (fun _ => resume)) pull put cells
    registers storage readRegisters writeRegisters readStack writeStack statement state contents
  have finalConfig : ∀ original : TM2.Cfg Alphabet Label State,
      embeddedContinuationConfig labels registers storage (.goto (fun _ => resume)) original =
        embeddedReturningConfig labels resume registers storage original := by
    intro original
    cases original with
    | mk label register stored => cases label <;> rfl
  exact same.trans (finalConfig _)

/-- A successful subroutine transition is one caller transition, including
its jump to the explicit return label. -/
theorem step_embedStatement [DecidableEq Key]
    {TargetKey : Type u} [DecidableEq TargetKey] {TargetState : Type x}
    {TargetAlphabet : TargetKey → Type z}
    (keys : Key → TargetKey) (labels : Label → Label') (resume : Label')
    (pull : TargetState → State) (put : TargetState → State → TargetState)
    (cells : ∀ key, Alphabet key = TargetAlphabet (keys key))
    (registers : State → TargetState)
    (storage : (∀ key, List (Alphabet key)) → ∀ key, List (TargetAlphabet key))
    (readRegisters : ∀ state, pull (registers state) = state)
    (writeRegisters : ∀ state value, put (registers state) value = registers value)
    (readStack : ∀ contents key,
      storage contents (keys key) = (contents key).map (cells key).mp)
    (writeStack : ∀ contents key value,
      storage (Function.update contents key value) =
        Function.update (storage contents) (keys key) (value.map (cells key).mp))
    (source : Label → TM2.Stmt Alphabet Label State)
    (target : Label' → TM2.Stmt TargetAlphabet Label' TargetState)
    (before after : TM2.Cfg Alphabet Label State)
    (body : ∀ label, before.l = some label → target (labels label) =
      embedStatement keys labels pull put cells (.goto (fun _ => resume)) (source label))
    (executed : TM2.step source before = some after) :
    TM2.step target (embeddedReturningConfig labels resume registers storage before) =
      some (embeddedReturningConfig labels resume registers storage after) := by
  cases before with
  | mk label register contents =>
      cases label with
      | none => simp [TM2.step] at executed
      | some label =>
          simp only [TM2.step] at executed
          have identified := Option.some.inj executed
          subst after
          simp only [embeddedReturningConfig, Option.elim_some, TM2.step]
          rw [body label rfl]
          exact congrArg some (stepAux_embedStatement keys labels resume pull put cells registers storage
            readRegisters writeRegisters readStack writeStack (source label) register contents)

theorem step_embedContinuation [DecidableEq Key]
    {TargetKey : Type u} [DecidableEq TargetKey] {TargetState : Type x}
    {TargetAlphabet : TargetKey → Type z}
    (keys : Key → TargetKey) (labels : Label → Label')
    (onHalt : TM2.Stmt TargetAlphabet Label' TargetState)
    (pull : TargetState → State) (put : TargetState → State → TargetState)
    (cells : ∀ key, Alphabet key = TargetAlphabet (keys key))
    (registers : State → TargetState)
    (storage : (∀ key, List (Alphabet key)) → ∀ key, List (TargetAlphabet key))
    (readRegisters : ∀ state, pull (registers state) = state)
    (writeRegisters : ∀ state value, put (registers state) value = registers value)
    (readStack : ∀ contents key,
      storage contents (keys key) = (contents key).map (cells key).mp)
    (writeStack : ∀ contents key value,
      storage (Function.update contents key value) =
        Function.update (storage contents) (keys key) (value.map (cells key).mp))
    (source : Label → TM2.Stmt Alphabet Label State)
    (target : Label' → TM2.Stmt TargetAlphabet Label' TargetState)
    (before after : TM2.Cfg Alphabet Label State)
    (body : ∀ label, before.l = some label → target (labels label) =
      embedStatement keys labels pull put cells onHalt (source label))
    (executed : TM2.step source before = some after) :
    TM2.step target (embeddedContinuationConfig labels registers storage onHalt before) =
      some (embeddedContinuationConfig labels registers storage onHalt after) := by
  cases before with
  | mk label register contents =>
      cases label with
      | none => simp [TM2.step] at executed
      | some label =>
          simp only [TM2.step] at executed
          have identified := Option.some.inj executed
          subst after
          simp only [embeddedContinuationConfig, TM2.step]
          rw [body label rfl]
          exact congrArg some (stepAux_embedContinuation keys labels onHalt pull put cells registers storage
            readRegisters writeRegisters readStack writeStack (source label) register contents)

/-- Add separate caller registers without changing a subroutine's operations. -/
def extend (labels : Label → Label') :
    TM2.Stmt Alphabet Label State → TM2.Stmt Alphabet Label' (State × Extra)
  | .push key value rest => .push key (fun state => value state.1) (extend labels rest)
  | .peek key update rest => .peek key (fun state value => (update state.1 value, state.2)) (extend labels rest)
  | .pop key update rest => .pop key (fun state value => (update state.1 value, state.2)) (extend labels rest)
  | .load update rest => .load (fun state => (update state.1, state.2)) (extend labels rest)
  | .branch condition yes no => .branch (fun state => condition state.1) (extend labels yes) (extend labels no)
  | .goto label => .goto (fun state => labels (label state.1))
  | .halt => .halt

/-- A configuration embeds its label and keeps every original stack. -/
def config (labels : Label → Label') (extra : Extra) (source : TM2.Cfg Alphabet Label State) :
    TM2.Cfg Alphabet Label' (State × Extra) where
  l := source.l.map labels
  var := (source.var, extra)
  stk := source.stk

variable [DecidableEq Key]

theorem stepAux_extend (labels : Label → Label') (extra : Extra)
    (statement : TM2.Stmt Alphabet Label State) (state : State)
    (contents : ∀ key, List (Alphabet key)) :
    TM2.stepAux (extend labels statement) (state, extra) contents =
      config labels extra (TM2.stepAux statement state contents) := by
  induction statement generalizing state contents with
  | push key value rest ih => simpa [extend, TM2.stepAux, config] using ih state _
  | peek key update rest ih => simpa [extend, TM2.stepAux, config] using ih _ contents
  | pop key update rest ih => simpa [extend, TM2.stepAux, config] using ih _ _
  | load update rest ih => simpa [extend, TM2.stepAux, config] using ih _ contents
  | branch condition yes no yesIH noIH =>
      cases h : condition state <;> simp [extend, TM2.stepAux, h, config, yesIH, noIH]
  | goto label => rfl
  | halt => rfl

/-- One source transition remains one transition when its label's body is the
embedded original statement. No execution-time clock is supplied separately. -/
theorem step_extend (labels : Label → Label') (extra : Extra)
    (source : Label → TM2.Stmt Alphabet Label State)
    (target : Label' → TM2.Stmt Alphabet Label' (State × Extra))
    (state : TM2.Cfg Alphabet Label State)
    (body : ∀ label, state.l = some label → target (labels label) = extend labels (source label)) :
    TM2.step target (config labels extra state) =
      (TM2.step source state).map (config labels extra) := by
  cases state with
  | mk label register contents =>
      cases label with
      | none => rfl
      | some label =>
          simp only [TM2.step, config, Option.map_some]
          rw [body label rfl]
          exact congrArg some (stepAux_extend labels extra (source label) register contents)

/-- Embed an original subroutine while returning to the caller at its halt
boundary. Caller registers and the physical stacks retain their contents. -/
def returning (labels : Label → Label') (resume : Extra → Label') :
    TM2.Stmt Alphabet Label State → TM2.Stmt Alphabet Label' (State × Extra)
  | .push key value rest => .push key (fun state => value state.1) (returning labels resume rest)
  | .peek key update rest => .peek key (fun state value => (update state.1 value, state.2)) (returning labels resume rest)
  | .pop key update rest => .pop key (fun state value => (update state.1 value, state.2)) (returning labels resume rest)
  | .load update rest => .load (fun state => (update state.1, state.2)) (returning labels resume rest)
  | .branch condition yes no => .branch (fun state => condition state.1)
      (returning labels resume yes) (returning labels resume no)
  | .goto label => .goto (fun state => labels (label state.1))
  | .halt => .goto (fun state => resume state.2)

/-- A halted original configuration denotes the caller's continuation. -/
def returningConfig (labels : Label → Label') (resume : Extra → Label')
    (extra : Extra) (source : TM2.Cfg Alphabet Label State) :
    TM2.Cfg Alphabet Label' (State × Extra) where
  l := some (source.l.elim (resume extra) labels)
  var := (source.var, extra)
  stk := source.stk

theorem stepAux_returning (labels : Label → Label') (resume : Extra → Label')
    (extra : Extra) (statement : TM2.Stmt Alphabet Label State) (state : State)
    (contents : ∀ key, List (Alphabet key)) :
    TM2.stepAux (returning labels resume statement) (state, extra) contents =
      returningConfig labels resume extra (TM2.stepAux statement state contents) := by
  induction statement generalizing state contents with
  | push key value rest ih => simpa [returning, TM2.stepAux, returningConfig] using ih state _
  | peek key update rest ih => simpa [returning, TM2.stepAux, returningConfig] using ih _ contents
  | pop key update rest ih => simpa [returning, TM2.stepAux, returningConfig] using ih _ _
  | load update rest ih => simpa [returning, TM2.stepAux] using ih _ contents
  | branch condition yes no yesIH noIH =>
      cases h : condition state <;> simp [returning, TM2.stepAux, h, yesIH, noIH]
  | goto label => rfl
  | halt => rfl

/-- Each successful original transition is the same physical transition in
its caller, including the final jump to the caller's continuation. -/
theorem step_returning (labels : Label → Label') (resume : Extra → Label')
    (extra : Extra) (source : Label → TM2.Stmt Alphabet Label State)
    (target : Label' → TM2.Stmt Alphabet Label' (State × Extra))
    (before after : TM2.Cfg Alphabet Label State)
    (body : ∀ label, before.l = some label →
      target (labels label) = returning labels resume (source label))
    (executed : TM2.step source before = some after) :
    TM2.step target (returningConfig labels resume extra before) =
      some (returningConfig labels resume extra after) := by
  cases before with
  | mk label register contents =>
      cases label with
      | none => simp [TM2.step] at executed
      | some label =>
          simp only [TM2.step] at executed
          have identified := Option.some.inj executed
          subst after
          simp only [returningConfig, Option.elim_some, TM2.step]
          rw [body label rfl]
          exact congrArg some (stepAux_returning labels resume extra (source label) register contents)

variable {Cell : Type z}

/-- Add a caller-owned stack beside the original dependent alphabet family. -/
abbrev withStackAlphabet (Alphabet : Key → Type z) (Cell : Type z) : Option Key → Type z
  | none => Cell
  | some key => Alphabet key

def withStackContents (contents : ∀ key, List (Alphabet key)) (extra : List Cell) :
    ∀ key, List (withStackAlphabet Alphabet Cell key)
  | none => extra
  | some key => contents key

/-- Every original operation addresses its embedded stack; caller storage is
preserved, including arbitrary nonempty contents. -/
def withStack (labels : Label → Label') : TM2.Stmt Alphabet Label State →
    TM2.Stmt (withStackAlphabet Alphabet Cell) Label' State
  | .push key value rest => .push (some key) value (withStack labels rest)
  | .peek key update rest => .peek (some key) update (withStack labels rest)
  | .pop key update rest => .pop (some key) update (withStack labels rest)
  | .load update rest => .load update (withStack labels rest)
  | .branch condition yes no => .branch condition (withStack labels yes) (withStack labels no)
  | .goto label => .goto (fun state => labels (label state))
  | .halt => .halt

def withStackConfig (labels : Label → Label') (extra : List Cell) (source : TM2.Cfg Alphabet Label State) :
    TM2.Cfg (withStackAlphabet Alphabet Cell) Label' State where
  l := source.l.map labels
  var := source.var
  stk := withStackContents source.stk extra

theorem withStackContents_update (contents : ∀ key, List (Alphabet key))
    (extra : List Cell) (key : Key) (value : List (Alphabet key)) :
    withStackContents (Function.update contents key value) extra =
      Function.update (withStackContents contents extra) (some key) value := by
  funext index
  cases index with
  | none => simp [withStackContents, Function.update]
  | some index =>
      by_cases same : index = key
      · subst index; simp [withStackContents, Function.update]
      · simp [withStackContents, Function.update, same]

theorem stepAux_withStack (labels : Label → Label') (extra : List Cell) (statement : TM2.Stmt Alphabet Label State)
    (state : State) (contents : ∀ key, List (Alphabet key)) :
    TM2.stepAux (withStack labels statement) state (withStackContents contents extra) =
      withStackConfig labels extra (TM2.stepAux statement state contents) := by
  induction statement generalizing state contents with
  | push key value rest ih =>
      simp only [withStack, TM2.stepAux, withStackContents]
      have result := ih state (Function.update contents key (value state :: contents key))
      rw [withStackContents_update] at result
      exact result
  | peek key update rest ih => simpa only [withStack, TM2.stepAux, withStackContents] using ih _ contents
  | pop key update rest ih =>
      simp only [withStack, TM2.stepAux, withStackContents]
      have result := ih (update state (contents key).head?) (Function.update contents key (contents key).tail)
      rw [withStackContents_update] at result
      exact result
  | load update rest ih => simpa only [withStack, TM2.stepAux] using ih _ contents
  | branch condition yes no yesIH noIH =>
      cases h : condition state <;> simp [withStack, TM2.stepAux, h, yesIH, noIH]
  | goto label => rfl
  | halt => rfl

theorem step_withStack (labels : Label → Label') (extra : List Cell)
    (source : Label → TM2.Stmt Alphabet Label State)
    (target : Label' → TM2.Stmt (withStackAlphabet Alphabet Cell) Label' State)
    (state : TM2.Cfg Alphabet Label State)
    (body : ∀ label, state.l = some label → target (labels label) = withStack labels (source label)) :
    TM2.step target (withStackConfig labels extra state) =
      (TM2.step source state).map (withStackConfig labels extra) := by
  cases state with
  | mk label register contents =>
      cases label with
      | none => rfl
      | some label =>
          simp only [TM2.step, withStackConfig, Option.map_some]
          rw [body label rfl]
          exact congrArg some (stepAux_withStack labels extra (source label) register contents)


/-- A guarded subroutine retains exactly its physical transition count. The
source invariant restricts the supplied step equation to states that can occur
along this run; invariant closure is proved independently of its result. -/
def evalsInto {Source Target : Type} (sourceStep : Source → Option Source)
    (targetStep : Target → Option Target) (embed : Source → Target)
    (invariant : Source → Prop)
    (preserves : ∀ before after, invariant before → sourceStep before = some after → invariant after)
    (steps : ∀ state, invariant state → targetStep (embed state) = (sourceStep state).map embed)
    {input : Source} {output : Option Source} {bound : Nat}
    (initial : invariant input) (run : StateTransition.EvalsToInTime sourceStep input output bound) :
    StateTransition.EvalsToInTime targetStep (embed input) (output.map embed) bound := by
  have commutes : ∀ (n : Nat) (state : Option Source),
      (∀ source, state = some source → invariant source) →
      (flip Option.bind targetStep)^[n] (state.map embed) =
        ((flip Option.bind sourceStep)^[n] state).map embed := by
    intro n
    induction n with
    | zero => intro state _valid; rfl
    | succ n ih =>
      intro state valid
      cases state with
      | none =>
        simpa only [Function.iterate_succ_apply, Option.map_none, flip, Option.bind_none]
          using ih none (by intro source impossible; cases impossible)
      | some source =>
        have sourceValid := valid source rfl
        have nextValid : ∀ next, sourceStep source = some next → invariant next :=
          fun next computed => preserves source next sourceValid computed
        have next := ih (sourceStep source) nextValid
        simpa only [Function.iterate_succ_apply, Option.map_some, flip, Option.bind_some,
          steps source sourceValid] using next
  refine ⟨⟨run.steps, ?_⟩, run.steps_le_m⟩
  calc
    (flip Option.bind targetStep)^[run.steps] (some (embed input)) =
        ((flip Option.bind sourceStep)^[run.steps] (some input)).map embed :=
      commutes run.steps (some input) (by intro source equality; cases equality; exact initial)
    _ = output.map embed := congrArg (Option.map embed) run.evals_in_steps

end Mettapedia.Computability.StackMachineRegisters

namespace Mettapedia.Computability.StackMachineRegisters.WordFrame

open Turing StateTransition
open Turing.TM2.Stmt

set_option backward.isDefEq.respectTransparency false

inductive Key where
  | local | frames
  deriving DecidableEq, Fintype

inductive Phase where
  | push | save | restore
  deriving DecidableEq, Fintype

variable {A : Type} [Inhabited A]

abbrev Cells : Key → Type
  | .local => A
  | .frames => Option A

instance [Fintype A] (key : Key) : Fintype (Cells (A := A) key) := by
  cases key <;> dsimp only [Cells] <;> infer_instance

abbrev Control := Option A × Option (Option A) × Bool

def initial : Control (A := A) := (none,none,false)

/-- Every frame has its own delimiter, including an empty word. Saving and
restoring move physical symbols rather than storing a word in the control. -/
def program : Phase → TM2.Stmt (Cells (A := A)) Phase (Control (A := A))
  | .push => push .frames (fun _ => none) (goto (fun _ => .save))
  | .save => pop .local (fun state value => (value,state.2))
      (branch (fun state => state.1.isSome)
        (push .frames (fun state => some (state.1.getD default)) (goto (fun _ => .save)))
        (load (fun _ => (none,none,true)) halt))
  | .restore => pop .frames (fun state value => (state.1,value,state.2.2))
      (branch (fun state => state.2.1.isSome)
        (branch (fun state => state.2.1.join.isSome)
          (push .local (fun state => state.2.1.join.getD default) (goto (fun _ => .restore)))
          (load (fun _ => (none,none,true)) halt))
        (load (fun _ => initial) halt))

def machine [Fintype A] (entry : Phase) : FinTM2 where
  K := Key
  k₀ := .local
  k₁ := .local
  Γ := Cells (A := A)
  Λ := Phase
  main := entry
  σ := Control (A := A)
  initialState := initial (A := A)
  m := program (A := A)

abbrev Cfg := TM2.Cfg (Cells (A := A)) Phase (Control (A := A))

def step : Cfg (A := A) → Option (Cfg (A := A)) := TM2.step program

theorem machine_step [Fintype A] (entry : Phase) : (machine (A := A) entry).step = step := rfl

def config (phase : Option Phase) (state : Control (A := A))
    (localWord : List A) (frames : List (Option A)) : Cfg (A := A) where
  l := phase
  var := state
  stk key := match key with | .local => localWord | .frames => frames

local macro "frame_step" : tactic => `(tactic| (
  simp [step,program,config,initial,TM2.step,TM2.stepAux]
  all_goals funext key
  all_goals cases key <;> simp [Function.update]))

theorem push_step (state : Control (A := A)) (word : List A) (frames : List (Option A)) :
    step (config (some .push) state word frames) =
      some (config (some .save) state word (none::frames)) := by frame_step

theorem save_cons (state : Control (A := A)) (head : A) (word : List A) (frames : List (Option A)) :
    step (config (some .save) state (head::word) frames) =
      some (config (some .save) (some head,state.2) word (some head::frames)) := by frame_step

theorem save_nil (state : Control (A := A)) (frames : List (Option A)) :
    step (config (some .save) state [] frames) =
      some (config none (none,none,true) [] frames) := by frame_step

theorem restore_cons (state : Control (A := A)) (head : A) (frames : List (Option A)) (word : List A) :
    step (config (some .restore) state word (some head::frames)) =
      some (config (some .restore) (state.1,some (some head),state.2.2) (head::word) frames) := by frame_step

theorem restore_delimiter (state : Control (A := A)) (frames : List (Option A)) (word : List A) :
    step (config (some .restore) state word (none::frames)) =
      some (config none (none,none,true) word frames) := by frame_step

theorem restore_missing (state : Control (A := A)) (word : List A) :
    step (config (some .restore) state word []) =
      some (config none initial word []) := by frame_step

/-- Saving charges every moved symbol and the end-of-word transition. -/
def saveLoop (word : List A) (frames : List (Option A)) (state : Control (A := A)) :
    EvalsToInTime step (config (some .save) state word frames)
      (some (config none (none,none,true) [] (word.reverse.map some++frames)))
      (word.length+1) := by
  induction word generalizing frames state with
  | nil =>
      exact ⟨⟨1, by simpa [flip,Option.bind] using save_nil state frames⟩, le_rfl⟩
  | cons head word ih =>
      have first : EvalsToInTime step (config (some .save) state (head::word) frames)
          (some (config (some .save) (some head,state.2) word (some head::frames))) 1 :=
        ⟨⟨1, by simpa [flip,Option.bind] using save_cons state head word frames⟩, le_rfl⟩
      have rest := ih (some head::frames) (some head,state.2)
      simpa only [List.reverse_cons,List.map_append,List.map_singleton,List.append_assoc,
        List.singleton_append,List.length_cons,Nat.add_assoc] using
        EvalsToInTime.trans _ _ _ _ _ _ first rest

/-- The frame delimiter is written even when the caller's word is empty. -/
def saveRun (word : List A) (frames : List (Option A)) (state : Control (A := A)) :
    EvalsToInTime step (config (some .push) state word frames)
      (some (config none (none,none,true) [] (word.reverse.map some++none::frames)))
      (word.length+2) := by
  have first : EvalsToInTime step (config (some .push) state word frames)
      (some (config (some .save) state word (none::frames))) 1 :=
    ⟨⟨1, by simpa [flip,Option.bind] using push_step state word frames⟩,le_rfl⟩
  have rest := saveLoop word (none::frames) state
  simpa only [Nat.add_assoc] using EvalsToInTime.trans _ _ _ _ _ _ first rest

/-- Popping stops at the owned delimiter and leaves every outer frame intact. -/
def restoreLoop (stored : List A) (outer : List (Option A)) (word : List A)
    (state : Control (A := A)) :
    EvalsToInTime step (config (some .restore) state word (stored.map some++none::outer))
      (some (config none (none,none,true) (stored.reverse++word) outer))
      (stored.length+1) := by
  induction stored generalizing word state with
  | nil =>
      exact ⟨⟨1,by simpa [flip,Option.bind] using restore_delimiter state outer word⟩,le_rfl⟩
  | cons head stored ih =>
      have first : EvalsToInTime step
          (config (some .restore) state word (some head::(stored.map some++none::outer)))
          (some (config (some .restore) (state.1,some (some head),state.2.2) (head::word)
            (stored.map some++none::outer))) 1 :=
        ⟨⟨1,by simpa [flip,Option.bind] using
          (restore_cons state head (stored.map some++none::outer) word)⟩,le_rfl⟩
      have rest := ih (head::word) (state.1,some (some head),state.2.2)
      simpa only [List.map_cons,List.cons_append,List.reverse_cons,List.append_assoc,
        List.singleton_append,List.nil_append,List.length_cons,Nat.add_assoc] using
        EvalsToInTime.trans _ _ _ _ _ _ first rest

def restoreRun (saved : List A) (outer : List (Option A)) (word : List A)
    (state : Control (A := A)) :
    EvalsToInTime step (config (some .restore) state word (saved.reverse.map some++none::outer))
      (some (config none (none,none,true) (saved++word) outer))
      (saved.length+1) := by
  simpa only [List.reverse_reverse,List.length_reverse] using restoreLoop saved.reverse outer word state

end Mettapedia.Computability.StackMachineRegisters.WordFrame

namespace Mettapedia.Computability.StackMachineRegisters.Frame
universe u z
variable {Key TargetKey : Type u} {Alphabet : Key → Type z} {TargetAlphabet : TargetKey → Type z}
variable [DecidableEq Key] [DecidableEq TargetKey]

/-- Place the original stacks at the caller's selected physical keys, keeping every other stack. -/
def overlay (keys : Key → TargetKey) (select : TargetKey → Option Key)
    (sound : ∀ target key, select target = some key → keys key = target)
    (cells : ∀ key, Alphabet key = TargetAlphabet (keys key))
    (base : ∀ key, List (TargetAlphabet key))
    (contents : ∀ key, List (Alphabet key)) : ∀ key, List (TargetAlphabet key) :=
  fun target => match selected : select target with
    | none => base target
    | some key => (contents key).map ((cells key).trans (congrArg TargetAlphabet (sound target key selected))).mp

omit [DecidableEq Key] [DecidableEq TargetKey] in
theorem read (keys : Key → TargetKey) (select : TargetKey → Option Key)
    (sound : ∀ target key, select target = some key → keys key = target)
    (complete : ∀ key, select (keys key) = some key)
    (cells : ∀ key, Alphabet key = TargetAlphabet (keys key))
    (base : ∀ key, List (TargetAlphabet key))
    (contents : ∀ key, List (Alphabet key)) (key : Key) :
    overlay keys select sound cells base contents (keys key) = (contents key).map (cells key).mp := by
  unfold overlay
  split
  · rename_i absent
    simp only [complete key] at absent
    contradiction
  · rename_i chosen chosen_eq
    have same : chosen = key := Option.some.inj (chosen_eq.symm.trans (complete key))
    subst chosen
    rfl

theorem write (keys : Key → TargetKey) (select : TargetKey → Option Key)
    (sound : ∀ target key, select target = some key → keys key = target)
    (complete : ∀ key, select (keys key) = some key)
    (cells : ∀ key, Alphabet key = TargetAlphabet (keys key))
    (base : ∀ key, List (TargetAlphabet key))
    (contents : ∀ key, List (Alphabet key)) (key : Key) (value : List (Alphabet key)) :
    overlay keys select sound cells base (Function.update contents key value) =
      Function.update (overlay keys select sound cells base contents) (keys key) (value.map (cells key).mp) := by
  funext target
  by_cases matched : keys key = target
  · subst target
    rw [read keys select sound complete cells base _ key]
    simp [Function.update]
  · cases selected : select target with
    | none =>
        unfold overlay
        split <;> rename_i matching
        · simp only [Function.update_of_ne (Ne.symm matched)]
          split
          · rfl
          · rename_i found contradictory
            simp only [selected] at contradictory
            contradiction
        · simp only [selected] at matching
          contradiction
    | some chosen =>
        have different : key ≠ chosen := by
          intro same
          subst chosen
          exact matched (sound target key selected)
        unfold overlay
        split <;> rename_i matching
        · simp only [selected] at matching
          contradiction
        · rename_i found
          have same : found = chosen := Option.some.inj (matching.symm.trans selected)
          subst found
          simp only [Function.update_of_ne (Ne.symm matched), Function.update_of_ne (Ne.symm different)]
          split
          · rename_i contradictory
            simp only [selected] at contradictory
            contradiction
          · rename_i found matchedAgain
            have sameAgain : found = chosen := Option.some.inj (matchedAgain.symm.trans selected)
            subst found
            rfl
end Mettapedia.Computability.StackMachineRegisters.Frame


namespace Mettapedia.Computability.StackMachineRegisters.StackSnapshot
universe u v

/-- A finite physical snapshot retains each addressed stack word separately.
Reading any listed address returns its complete original contents. -/
def snapshot {K : Type u} (Γ : K → Type v) (contents : ∀ key, List (Γ key)) (word : List K) :
 List (Sigma fun key => List (Γ key)) := word.map (fun key => ⟨key,contents key⟩)

def lookup {K : Type u} [DecidableEq K] (Γ : K → Type v) :
 List (Sigma fun key => List (Γ key)) → (key : K) → List (Γ key)
 | [], _ => []
 | ⟨stored, value⟩ :: rest, key => if same : stored = key then same ▸ value else lookup Γ rest key

theorem lookup_snapshot {K : Type u} [DecidableEq K] (Γ : K → Type v)
 (contents : ∀ key, List (Γ key)) (word : List K) (key : K) (member : key ∈ word) :
 lookup Γ (snapshot Γ contents word) key = contents key := by
 induction word with
 | nil => cases member
 | cons head tail ih =>
   by_cases same : head = key
   · subst head; simp [snapshot,lookup]
   · have included : key ∈ tail := by
      rcases List.mem_cons.mp member with equal | included
      · exact False.elim (same equal.symm)
      · exact included
     simpa only [snapshot,List.map_cons,lookup,dif_neg same] using ih included


end Mettapedia.Computability.StackMachineRegisters.StackSnapshot
