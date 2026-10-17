import Mettapedia.GSLT.LanguageDef.CertificateDataTraversal

/-!
# Structural traversal of the original pattern token stream

Finite grammar tasks describe the original `PatternTokens` syntax. The visitor
retains the token fields and emits finite boundary events: dynamic names stay
in the original fields, and numeric values are carried by bit events. Scope
admission and rendering consume this traversal without introducing another
pattern carrier or a second source grammar.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.PatternSpanExecution
open Turing StateTransition
open Turing.TM2.Stmt
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.Computability
open CertificateDataTraversal

inductive NumberRole where
  | boundIndex | binderArity
  deriving DecidableEq, Fintype
inductive NameRole where
  | constructor | free | binder | capture
  deriving DecidableEq, Fintype
inductive OptionRole where
  | lambdaBinder | collectionCapture
  deriving DecidableEq, Fintype
inductive Node where
  | bound | free | application | lambda | multiLambda | substitution | collection
  deriving DecidableEq, Fintype
inductive Event where
  | begin (node : Node) | finish
  | name (role : NameRole)
  | numberStart (role : NumberRole)
  | bit (role : NumberRole) (value : Bool)
  | numberEnd (role : NumberRole)
  | enterOne | enterMany | leave
  | metadataPresent (role : OptionRole) | namedBinder | freeVariable
  | vector | bag | set
  | argumentsStart | argumentsEnd
  deriving DecidableEq, Fintype
inductive Task where
  | pattern | patterns
  | natural (role : NumberRole)
  | name (role : NameRole)
  | optional (role : OptionRole)
  | names | collectionKind
  | emit (event : Event)
  deriving DecidableEq, Fintype

def optionName : OptionRole → NameRole
  | .lambdaBinder => .binder | .collectionCapture => .capture

/-- Only the finite lexical classification influences grammar control. A
name field is accepted independently of its spelling, including tag words. -/
def plan : Task → Option (Fin 14) → Option (List Task)
  | .pattern, some 7 => some [.emit (.begin .bound), .emit (.numberStart .boundIndex),
      .natural .boundIndex, .emit .finish]
  | .pattern, some 8 => some [.emit (.begin .free), .emit .freeVariable,
      .name .free, .emit .finish]
  | .pattern, some 0 => some [.emit (.begin .application), .name .constructor,
      .emit .argumentsStart, .patterns, .emit .argumentsEnd, .emit .finish]
  | .pattern, some 3 => some [.emit (.begin .lambda), .optional .lambdaBinder,
      .emit .enterOne, .pattern, .emit .leave, .emit .finish]
  | .pattern, some 4 => some [.emit (.begin .multiLambda), .emit (.numberStart .binderArity),
      .natural .binderArity, .names, .emit .enterMany, .pattern, .emit .leave, .emit .finish]
  | .pattern, some 5 => some [.emit (.begin .substitution), .emit .enterOne, .pattern,
      .emit .leave, .pattern, .emit .finish]
  | .pattern, some 6 => some [.emit (.begin .collection), .collectionKind,
      .optional .collectionCapture, .emit .argumentsStart, .patterns,
      .emit .argumentsEnd, .emit .finish]
  | .patterns, some 2 => some []
  | .patterns, some 1 => some [.pattern, .patterns]
  | .natural role, some 11 => some [.emit (.bit role false), .natural role]
  | .natural role, some 12 => some [.emit (.bit role true), .natural role]
  | .natural role, some 13 => some [.emit (.numberEnd role)]
  | .name role, _ => some [.emit (.name role)]
  | .optional _, some 9 => some []
  | .optional role, some 10 => some [.emit (.metadataPresent role), .name (optionName role)]
  | .names, some 2 => some []
  | .names, some 1 => some [.emit .namedBinder, .name .binder, .names]
  | .collectionKind, some 8 => some [.emit .vector]
  | .collectionKind, some 7 => some [.emit .bag]
  | .collectionKind, some 5 => some [.emit .set]
  | _, _ => none

abbrev tokenTag := PatternTokenField.result

/-- A finite-task traversal witness records exactly which original token
fields were consumed and which finite events were emitted. -/
inductive Visits : List Task → List String → List String → List Event → Prop
  | done (tail : List String) : Visits [] tail tail []
  | emit {event : Event} {tasks : List Task} {input tail : List String} {events : List Event} :
      Visits tasks input tail events →
      Visits (.emit event :: tasks) input tail (event :: events)
  | token {task : Task} {tasks next : List Task} {token : String}
      {input tail : List String} {events : List Event} :
      plan task (tokenTag token) = some next →
      Visits (next ++ tasks) input tail events →
      Visits (task :: tasks) (token :: input) tail events

theorem Visits.append {first second : List Task} {input middle tail : List String}
    {before after : List Event} (left : Visits first input middle before)
    (right : Visits second middle tail after) :
    Visits (first ++ second) input tail (before ++ after) := by
  induction left with
  | done => exact right
  | emit _ ih => exact .emit (ih right)
  | @token task tasks next token input middle events accepted _ ih =>
      exact Visits.token (task := task) (tasks := tasks ++ second) (next := next)
        accepted (by simpa only [List.append_assoc] using ih right)

theorem Visits.event (event : Event) (input : List String) :
    Visits [.emit event] input input [event] := .emit (.done input)

theorem Visits.events (events : List Event) (input : List String) :
    Visits (events.map Task.emit) input input events := by
  induction events with
  | nil => exact .done input
  | cons event events ih => exact .emit ih

def numberEvents (role : NumberRole) (value : Nat) : List Event :=
  (Nat.digits 2 value).map (fun digit => .bit role (digit != 0)) ++ [.numberEnd role]

def optionEvents (role : OptionRole) : Option String → List Event
  | none => [] | some _ => [.metadataPresent role, .name (optionName role)]

def nameEvents : List String → List Event
  | [] => [] | _ :: tail => .namedBinder :: .name .binder :: nameEvents tail

def kindEvent : CollType → Event
  | .vec => .vector | .hashBag => .bag | .hashSet => .set

mutual
  def events : Pattern → List Event
    | .bvar index => [.begin .bound, .numberStart .boundIndex] ++
        numberEvents .boundIndex index ++ [.finish]
    | .fvar _ => [.begin .free, .freeVariable, .name .free, .finish]
    | .apply _ arguments => [.begin .application, .name .constructor, .argumentsStart] ++
        listEvents arguments ++ [.argumentsEnd, .finish]
    | .lambda name body => [.begin .lambda] ++ optionEvents .lambdaBinder name ++
        [.enterOne] ++ events body ++ [.leave, .finish]
    | .multiLambda arity names body => [.begin .multiLambda, .numberStart .binderArity] ++
        numberEvents .binderArity arity ++ nameEvents names ++ [.enterMany] ++
        events body ++ [.leave, .finish]
    | .subst body replacement => [.begin .substitution, .enterOne] ++ events body ++
        [.leave] ++ events replacement ++ [.finish]
    | .collection kind elements rest => [.begin .collection, kindEvent kind] ++
        optionEvents .collectionCapture rest ++ [.argumentsStart] ++ listEvents elements ++
        [.argumentsEnd, .finish]
  def listEvents : List Pattern → List Event
    | [] => [] | value :: values => events value ++ listEvents values
end

theorem plan_name (role : NameRole) (tag : Option (Fin 14)) :
    plan (.name role) tag = some [.emit (.name role)] := by
  cases tag with
  | none => rfl
  | some tag => fin_cases tag <;> rfl

theorem tokenTag_authored (index : Fin 14) :
    tokenTag (PatternTokenField.tags index) = some index := by
  fin_cases index <;> decide

theorem visits_name (role : NameRole) (name : String) (tail : List String) :
    Visits [.name role] (name :: tail) tail [.name role] :=
  .token (plan_name role _) (.emit (.done tail))

theorem visits_number (role : NumberRole) (value : Nat) (tail : List String) :
    Visits [.natural role] (Mettapedia.OSLF.MeTTaIL.PatternTokens.bits value ++ "e" :: tail)
      tail (numberEvents role value) := by
  have bits : ∀ (digits : List Nat), (∀ digit ∈ digits, digit < 2) →
      Visits [.natural role]
        (digits.map (fun digit => if digit = 0 then "0" else "1") ++ "e" :: tail)
        tail (digits.map (fun digit => Event.bit role (digit != 0)) ++ [.numberEnd role]) := by
    intro digits
    induction digits with
    | nil =>
        intro _
        apply Visits.token
        · rw [show tokenTag "e" = some 13 from tokenTag_authored 13]; rfl
        · exact .emit (.done tail)
    | cons digit digits ih =>
        intro bound
        have rest := ih (fun d member => bound d (by simp [member]))
        have small := bound digit (by simp)
        by_cases zero : digit = 0
        · simp only [List.map_cons, zero, ↓reduceIte, List.cons_append, bne_self_eq_false]
          apply Visits.token
          · rw [show tokenTag "0" = some 11 from tokenTag_authored 11]; rfl
          · exact .emit rest
        · have one : digit = 1 := by omega
          subst digit
          simp only [List.map_cons, Nat.one_ne_zero, ↓reduceIte, List.cons_append]
          apply Visits.token
          · rw [show tokenTag "1" = some 12 from tokenTag_authored 12]; rfl
          · exact .emit rest
  exact bits (Nat.digits 2 value) (fun _ member => Nat.digits_lt_base (by decide) member)

theorem visits_option (role : OptionRole) (name : Option String) (tail : List String) :
    Visits [.optional role] (Mettapedia.OSLF.MeTTaIL.PatternTokens.option name tail)
      tail (optionEvents role name) := by
  cases name with
  | none =>
      apply Visits.token
      · rw [show tokenTag "n" = some 9 from tokenTag_authored 9]; rfl
      · exact .done tail
  | some name =>
      apply Visits.token
      · rw [show tokenTag "o" = some 10 from tokenTag_authored 10]; rfl
      · exact .emit (visits_name (optionName role) name tail)

theorem visits_names (names tail : List String) :
    Visits [.names] (Mettapedia.OSLF.MeTTaIL.PatternTokens.names names tail)
      tail (nameEvents names) := by
  induction names with
  | nil =>
      apply Visits.token
      · rw [show tokenTag "z" = some 2 from tokenTag_authored 2]; rfl
      · exact .done tail
  | cons name names ih =>
      apply Visits.token
      · rw [show tokenTag "h" = some 1 from tokenTag_authored 1]; rfl
      · exact .emit ((visits_name .binder name _).append ih)

theorem visits_kind (kind : CollType) (tail : List String) :
    Visits [.collectionKind] (Mettapedia.OSLF.MeTTaIL.PatternTokens.collection kind :: tail)
      tail [kindEvent kind] := by
  cases kind with
  | vec =>
      apply Visits.token (next := [.emit .vector])
      · change plan .collectionKind (tokenTag "v") = _
        rw [show tokenTag "v" = some 8 from tokenTag_authored 8]; rfl
      · exact .emit (.done tail)
  | hashBag =>
      apply Visits.token (next := [.emit .bag])
      · change plan .collectionKind (tokenTag "b") = _
        rw [show tokenTag "b" = some 7 from tokenTag_authored 7]; rfl
      · exact .emit (.done tail)
  | hashSet =>
      apply Visits.token (next := [.emit .set])
      · change plan .collectionKind (tokenTag "s") = _
        rw [show tokenTag "s" = some 5 from tokenTag_authored 5]; rfl
      · exact .emit (.done tail)

theorem Visits.surround {tasks : List Task} {input tail : List String} {middle : List Event}
    (visit : Visits tasks input tail middle) (before after : List Event) :
    Visits (before.map Task.emit ++ tasks ++ after.map Task.emit) input tail
      (before ++ middle ++ after) :=
  ((Visits.events before input).append visit).append (Visits.events after tail)

mutual
  theorem visits_write (value : Pattern) (tail : List String) :
      Visits [.pattern] (Mettapedia.OSLF.MeTTaIL.PatternTokens.write value tail)
        tail (events value) := by
    cases value with
    | bvar index =>
        apply Visits.token
        · rw [show tokenTag "b" = some 7 from tokenTag_authored 7]; rfl
        · simpa [events, List.append_assoc] using
            (visits_number .boundIndex index tail).surround
              [.begin .bound, .numberStart .boundIndex] [.finish]
    | fvar name =>
        apply Visits.token
        · rw [show tokenTag "v" = some 8 from tokenTag_authored 8]; rfl
        · simpa [events] using (visits_name .free name tail).surround
            [.begin .free, .freeVariable] [.finish]
    | apply name arguments =>
        apply Visits.token
        · rw [show tokenTag "a" = some 0 from tokenTag_authored 0]; rfl
        · have children := visits_writeList arguments tail
          have start := (Visits.event .argumentsStart _).append children
          have named := (visits_name .constructor name _).append start
          simpa [events, List.append_assoc] using named.surround
            [.begin .application] [.argumentsEnd, .finish]
    | lambda name body =>
        apply Visits.token
        · rw [show tokenTag "l" = some 3 from tokenTag_authored 3]; rfl
        · have child := visits_write body tail
          have entering := (Visits.event .enterOne _).append child
          have named := (visits_option .lambdaBinder name _).append entering
          simpa [events, List.append_assoc] using named.surround
            [.begin .lambda] [.leave, .finish]
    | multiLambda arity names body =>
        apply Visits.token
        · rw [show tokenTag "m" = some 4 from tokenTag_authored 4]; rfl
        · have child := visits_write body tail
          have entering := (Visits.event .enterMany _).append child
          have named := (visits_names names _).append entering
          have number := (visits_number .binderArity arity _).append named
          simpa [events, List.append_assoc] using number.surround
            [.begin .multiLambda, .numberStart .binderArity] [.leave, .finish]
    | subst body replacement =>
        apply Visits.token
        · rw [show tokenTag "s" = some 5 from tokenTag_authored 5]; rfl
        · have right := visits_write replacement tail
          have leaving := (Visits.event .leave _).append right
          have left := (visits_write body _).append leaving
          simpa [events, List.append_assoc] using left.surround
            [.begin .substitution, .enterOne] [.finish]
    | collection kind elements capture =>
        apply Visits.token
        · rw [show tokenTag "c" = some 6 from tokenTag_authored 6]; rfl
        · have children := visits_writeList elements tail
          have entering := (Visits.event .argumentsStart _).append children
          have capture := (visits_option .collectionCapture capture _).append entering
          have kind := (visits_kind kind _).append capture
          simpa [events, List.append_assoc] using kind.surround
            [.begin .collection] [.argumentsEnd, .finish]
    termination_by sizeOf value
    decreasing_by all_goals sizeOf_pattern_dec

  theorem visits_writeList (values : List Pattern) (tail : List String) :
      Visits [.patterns] (Mettapedia.OSLF.MeTTaIL.PatternTokens.writeList values tail)
        tail (listEvents values) := by
    cases values with
    | nil =>
        apply Visits.token
        · rw [show tokenTag "z" = some 2 from tokenTag_authored 2]; rfl
        · exact .done tail
    | cons value values =>
        apply Visits.token
        · rw [show tokenTag "h" = some 1 from tokenTag_authored 1]; rfl
        · simpa [listEvents] using (visits_write value _).append (visits_writeList values tail)
    termination_by sizeOf values
    decreasing_by all_goals sizeOf_pattern_dec
end

namespace Execution

inductive Stack where
  | input | frames | scratch | span | tasks | events | result
  deriving DecidableEq, Fintype
abbrev StackAlphabet : Stack → Type
  | .tasks => Task
  | .events => Event
  | _ => Alphabet

structure Control where
  symbol : Option Alphabet
  current : Option Task
  cursors : FiniteWordClassifier.Residuals PatternTokenField.words
  event : Option Event
  deriving Fintype

def initial : Control := ⟨none, none, FiniteWordClassifier.initial PatternTokenField.words, none⟩

inductive Phase where
  | start | next | listCell
  | field (phase : CertificateDataTraversal.Phase)
  | clearScratch
  | dispatch (task : Task) (tag : Option (Fin 14))
  | finishSpan | restoreSpan
  | rejectInput | rejectFrames | rejectScratch | rejectSpan | rejectTasks | rejectEvents
  deriving DecidableEq, Fintype

def pushTasks : List Task → TM2.Stmt StackAlphabet Phase Control → TM2.Stmt StackAlphabet Phase Control
  | [], rest => rest
  | task :: tasks, rest => pushTasks tasks (push .tasks (fun _ => task) rest)

def parserKey : Option CertificateDataTraversal.Stack → Stack
  | none => .span
  | some .input => .input | some .frames => .frames | some .output => .scratch

abbrev ParserAlphabet := StackMachineRegisters.withStackAlphabet
  (fun _ : CertificateDataTraversal.Stack => Alphabet) Alphabet

def parserAlphabet (key : Option CertificateDataTraversal.Stack) :
    ParserAlphabet key ≃ StackAlphabet (parserKey key) := by
  cases key with
  | none => exact Equiv.refl Alphabet
  | some key => cases key <;> exact Equiv.refl Alphabet

/-- Reuse every original walker operation. Captured-byte writes also advance
finite dictionary cursors; no dynamic field is kept in a control register. -/
abbrev ParserStmt := TM2.Stmt ParserAlphabet
  CertificateDataTraversal.Phase (Option Alphabet)
abbrev ParserCfg := TM2.Cfg ParserAlphabet
  CertificateDataTraversal.Phase (Option Alphabet)

def parserProgram (phase : CertificateDataTraversal.Phase) : ParserStmt := PrefixField.machine.m phase

theorem parser_machine_step : PrefixField.machine.step = TM2.step parserProgram := by
  rfl

def observe : ParserStmt → TM2.Stmt StackAlphabet Phase Control
  | .push none value rest => push .span (fun state => value state.symbol)
      (load (fun state => {state with cursors :=
        FiniteWordClassifier.advanceAll PatternTokenField.words state.cursors (value state.symbol)})
        (observe rest))
  | .push (some key) value rest => push (parserKey (some key))
      (fun state => parserAlphabet (some key) (value state.symbol)) (observe rest)
  | .peek key update rest => peek (parserKey key)
      (fun state value => {state with symbol := update state.symbol (value.map (parserAlphabet key).symm)}) (observe rest)
  | .pop key update rest => pop (parserKey key)
      (fun state value => {state with symbol := update state.symbol (value.map (parserAlphabet key).symm)}) (observe rest)
  | .load update rest => load (fun state => {state with symbol := update state.symbol}) (observe rest)
  | .branch condition yes no => branch (fun state => condition state.symbol) (observe yes) (observe no)
  | .goto label => goto (fun state => .field (label state.symbol))
  | .halt => halt

def fieldProgram (phase : CertificateDataTraversal.Phase) : TM2.Stmt StackAlphabet Phase Control :=
  observe (parserProgram phase)

/-- The executable program body avoids enumerating its finite cursor-product
state space. Every read updates finite residuals and the physical span stack. -/
def program : Phase → TM2.Stmt StackAlphabet Phase Control
  | .start => push .tasks (fun _ => .pattern) (goto fun _ => .next)
  | .next => pop .tasks (fun state value => {state with current := value})
      (branch (fun state => state.current.isNone)
        (load (fun _ => initial) (goto fun _ => .finishSpan))
        (branch (fun state => match state.current with | some (.emit _) => true | _ => false)
          (push .events (fun state => match state.current with | some (.emit event) => event | _ => .finish)
            (load (fun _ => initial) (goto fun _ => .next)))
          (load (fun state => {initial with current := state.current}) (goto fun _ => .listCell))))
  | .listCell => pop .input (fun state value => {state with symbol := value})
      (branch (fun state => state.symbol == some 4)
        (push .span (fun _ => 4) (load (fun state => {state with symbol := none})
          (goto fun _ => .field .header)))
        (goto fun _ => .rejectInput))
  | .field .checkTail => goto fun _ => .clearScratch
  | .field .rejectInput => goto fun _ => .rejectInput
  | .field .rejectFrames => goto fun _ => .rejectInput
  | .field .rejectOutput => goto fun _ => .rejectInput
  | .field phase => fieldProgram phase
  | .clearScratch => pop .scratch (fun state value => {state with symbol := value})
      (branch (fun state => state.symbol.isSome) (goto fun _ => .clearScratch)
        (goto fun state => .dispatch (state.current.getD .pattern)
          (FiniteWordClassifier.finish PatternTokenField.words state.cursors)))
  | .dispatch task tag => match plan task tag with
      | none => goto fun _ => .rejectInput
      | some tasks => pushTasks tasks (load (fun _ => initial) (goto fun _ => .next))
  | .finishSpan => push .result (fun _ => 2)
      (push .result (fun _ => 3) (goto fun _ => .restoreSpan))
  | .restoreSpan => pop .span (fun state value => {state with symbol := value})
      (branch (fun state => state.symbol.isSome)
        (push .result (fun state => state.symbol.getD 2) (goto fun _ => .restoreSpan))
        (load (fun _ => initial) halt))
  | .rejectInput => pop .input (fun state value => {state with symbol := value})
      (branch (fun state => state.symbol.isSome) (goto fun _ => .rejectInput)
        (goto fun _ => .rejectFrames))
  | .rejectFrames => pop .frames (fun state value => {state with symbol := value})
      (branch (fun state => state.symbol.isSome) (goto fun _ => .rejectFrames)
        (goto fun _ => .rejectScratch))
  | .rejectScratch => pop .scratch (fun state value => {state with symbol := value})
      (branch (fun state => state.symbol.isSome) (goto fun _ => .rejectScratch)
        (goto fun _ => .rejectSpan))
  | .rejectSpan => pop .span (fun state value => {state with symbol := value})
      (branch (fun state => state.symbol.isSome) (goto fun _ => .rejectSpan)
        (goto fun _ => .rejectTasks))
  | .rejectTasks => pop .tasks (fun state value => {state with current := value})
      (branch (fun state => state.current.isSome) (goto fun _ => .rejectTasks)
        (goto fun _ => .rejectEvents))
  | .rejectEvents => pop .events (fun state value => {state with event := value})
      (branch (fun state => state.event.isSome) (goto fun _ => .rejectEvents)
        (push .result (fun _ => 0) (load (fun _ => initial) halt)))

def machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .result
  Γ := StackAlphabet
  Γk₀Fin := by change Fintype Alphabet; infer_instance
  Λ := Phase
  main := .start
  σ := Control
  initialState := initial
  m := program

abbrev Cfg := TM2.Cfg StackAlphabet Phase Control

def step : Cfg → Option Cfg := TM2.step program

theorem machine_step : machine.step = step := rfl

def config (phase : Option Phase) (state : Control)
    (input frames scratch span : List Alphabet) (tasks : List Task) (events : List Event)
    (result : List Alphabet) : Cfg where
  l := phase
  var := state
  stk key := match (show Stack from key) with
    | .input => input | .frames => frames | .scratch => scratch | .span => span
    | .tasks => tasks | .events => events | .result => result

def ready (input span : List Alphabet) (tasks : List Task) (events : List Event) : Cfg :=
  config (some .next) initial input [] [] span tasks events []

theorem cursor_append (first second : List Alphabet)
    (state : FiniteWordClassifier.Residuals PatternTokenField.words) :
    FiniteWordClassifier.walkState PatternTokenField.words (first ++ second) state =
      FiniteWordClassifier.walkState PatternTokenField.words second
        (FiniteWordClassifier.walkState PatternTokenField.words first state) := by
  induction first generalizing state with
  | nil => rfl
  | cons head tail ih =>
      simpa only [List.cons_append, FiniteWordClassifier.walkState] using
        ih (FiniteWordClassifier.advanceAll PatternTokenField.words state head)

theorem cursor_cons (head : Alphabet) (memo : List Alphabet) :
    FiniteWordClassifier.walkState PatternTokenField.words (head :: memo).reverse
        (FiniteWordClassifier.initial PatternTokenField.words) =
      FiniteWordClassifier.advanceAll PatternTokenField.words
        (FiniteWordClassifier.walkState PatternTokenField.words memo.reverse
          (FiniteWordClassifier.initial PatternTokenField.words)) head := by
  simp only [List.reverse_cons, cursor_append, FiniteWordClassifier.walkState]

def embedField (task : Task) (tasks : List Task) (events : List Event)
    (span : List Alphabet) (source : ParserCfg) : Cfg :=
  let memo : List Alphabet := source.stk none
  config (source.l.map Phase.field)
    ⟨source.var, some task, FiniteWordClassifier.walkState PatternTokenField.words
      memo.reverse (FiniteWordClassifier.initial PatternTokenField.words), none⟩
    (source.stk (some CertificateDataTraversal.Stack.input))
    (source.stk (some CertificateDataTraversal.Stack.frames))
    (source.stk (some CertificateDataTraversal.Stack.output))
    (memo ++ span) tasks events []

theorem embedField_config (task : Task) (tasks : List Task) (events : List Event)
    (span : List Alphabet) (phase : Option CertificateDataTraversal.Phase)
    (state : Option Alphabet) (input frames output memo : List Alphabet) :
    embedField task tasks events span (PrefixField.config phase state input frames output memo) =
      config (phase.map Phase.field)
        ⟨state, some task, FiniteWordClassifier.walkState PatternTokenField.words memo.reverse
          (FiniteWordClassifier.initial PatternTokenField.words), none⟩
        input frames output (memo ++ span) tasks events [] := rfl

theorem header_mapped (task : Task) (tasks : List Task) (events : List Event)
    (span : List Alphabet) (state : Option Alphabet) (input frames output memo : List Alphabet) :
    machine.step (embedField task tasks events span
      (PrefixField.config (some .header) state input frames output memo)) =
      (TM2.step parserProgram (PrefixField.config (some .header) state input frames output memo)).map
        (embedField task tasks events span) := by
  rw [machine_step]
  cases input with
  | nil =>
      with_unfolding_all simp [step, program, fieldProgram, observe, parserProgram, parserAlphabet,
        PrefixField.machine_header, embedField, config, PrefixField.config,
        TM2.step, TM2.stepAux, parserKey]
  | cons head tail =>
      fin_cases head <;>
        with_unfolding_all simp [step, program, fieldProgram, observe, parserProgram, parserAlphabet,
          PrefixField.machine_header, embedField, config, PrefixField.config,
          TM2.step, TM2.stepAux, parserKey, cursor_append, FiniteWordClassifier.walkState, Bool.cond_eq_ite, Function.update]
      all_goals funext key
      all_goals cases key <;> simp [Function.update]

theorem number_mapped (task : Task) (tasks : List Task) (events : List Event)
    (span : List Alphabet) (state : Option Alphabet) (input frames output memo : List Alphabet) :
    machine.step (embedField task tasks events span
      (PrefixField.config (some .number) state input frames output memo)) =
      (TM2.step parserProgram (PrefixField.config (some .number) state input frames output memo)).map
        (embedField task tasks events span) := by
  rw [machine_step]
  cases input with
  | nil =>
      with_unfolding_all simp [step, program, fieldProgram, observe, parserProgram, parserAlphabet,
        PrefixField.machine_number, embedField, config, PrefixField.config,
        TM2.step, TM2.stepAux, parserKey, SharedReferenceExecution.isBit]
  | cons head tail =>
      fin_cases head <;>
        with_unfolding_all simp [step, program, fieldProgram, observe, parserProgram, parserAlphabet,
          PrefixField.machine_number, embedField, config, PrefixField.config,
          TM2.step, TM2.stepAux, parserKey, cursor_append, FiniteWordClassifier.walkState, Bool.cond_eq_ite, Function.update, SharedReferenceExecution.isBit]
      all_goals funext key
      all_goals cases key <;> simp [Function.update]


theorem complete_mapped (task : Task) (tasks : List Task) (events : List Event)
    (span : List Alphabet) (state : Option Alphabet) (input frames output memo : List Alphabet)
    (second : Bool) :
    machine.step (embedField task tasks events span
      (PrefixField.config (some .complete) state input
        ((if second then 1 else 0) :: frames) output memo)) =
      (TM2.step parserProgram (PrefixField.config (some .complete) state input
        ((if second then 1 else 0) :: frames) output memo)).map
        (embedField task tasks events span) := by
  rw [machine_step]
  cases second <;>
    with_unfolding_all simp [step, program, fieldProgram, observe, parserProgram, parserAlphabet,
      PrefixField.machine_complete, CertificateDataTraversal.machine,
      embedField, config, PrefixField.config, StackMachineRegisters.withStack,
      TM2.step, TM2.stepAux, parserKey,
      Bool.cond_eq_ite, Function.update]
  all_goals funext key
  all_goals cases key <;> simp [Function.update]

theorem field_steps (task : Task) (tasks : List Task) (events : List Event)
    (span : List Alphabet) (source : PrefixField.machine.Cfg) (allowed : PrefixField.scanning source) :
    step (embedField task tasks events span source) =
      (PrefixField.machine.step source).map (embedField task tasks events span) := by
  rw [parser_machine_step]
  rcases allowed with header | number | ⟨complete, first | second⟩
  · have same := PrefixField.config_eta source
    rw [header] at same
    rw [same]
    simpa only [machine_step] using header_mapped task tasks events span source.var
      (source.stk (some CertificateDataTraversal.Stack.input))
      (source.stk (some CertificateDataTraversal.Stack.frames))
      (source.stk (some CertificateDataTraversal.Stack.output)) (source.stk none)
  · have same := PrefixField.config_eta source
    rw [number] at same
    rw [same]
    simpa only [machine_step] using number_mapped task tasks events span source.var
      (source.stk (some CertificateDataTraversal.Stack.input))
      (source.stk (some CertificateDataTraversal.Stack.frames))
      (source.stk (some CertificateDataTraversal.Stack.output)) (source.stk none)
  · have frames := List.head?_eq_some_iff.mp first
    obtain ⟨tail, frameEq⟩ := frames
    have same := PrefixField.config_eta source
    rw [complete, frameEq] at same
    rw [same]
    simpa only [machine_step, Bool.false_eq_true, ↓reduceIte] using
      complete_mapped task tasks events span source.var
        (source.stk (some CertificateDataTraversal.Stack.input)) tail
        (source.stk (some CertificateDataTraversal.Stack.output)) (source.stk none) false
  · have frames := List.head?_eq_some_iff.mp second
    obtain ⟨tail, frameEq⟩ := frames
    have same := PrefixField.config_eta source
    rw [complete, frameEq] at same
    rw [same]
    simpa only [machine_step, ↓reduceIte] using
      complete_mapped task tasks events span source.var
        (source.stk (some CertificateDataTraversal.Stack.input)) tail
        (source.stk (some CertificateDataTraversal.Stack.output)) (source.stk none) true

/-- The original byte walker realizes a classified field inside the visitor.
Its unread input, structural continuations, original bytes and transition
count survive the embedding. -/
noncomputable def fieldRun (task : Task) (tasks : List Task) (events : List Event)
    (span : List Alphabet) (value : Data) (input frames output memo : List Alphabet)
    (state : Option Alphabet) :=
  PrefixField.walkInto step (embedField task tasks events span)
    (steps := field_steps task tasks events span)
    value input frames output memo state

def fields (tokens : List String) : List Alphabet :=
  tokens.flatMap fun token => 4 :: encodeWith Codec.string token

def tokenWire (tokens : List String) : List Alphabet :=
  encodeWith (Codec.list Codec.string) tokens

theorem tokenWire_eq (tokens : List String) : tokenWire tokens = fields tokens ++ [3, 2] := by
  have law := encodeWith_list Codec.string tokens
  have zero : encodeData (.atom 0) = ([3, 2] : List Alphabet) := rfl
  rw [zero] at law
  exact law

theorem tokenWire_cons (token : String) (tokens : List String) :
    tokenWire (token :: tokens) = 4 :: encodeWith Codec.string token ++ tokenWire tokens := by
  simp only [tokenWire_eq, fields, List.flatMap_cons, List.append_assoc]

theorem next_emit (event : Event) (input span : List Alphabet) (tasks : List Task) (events : List Event) :
    step (ready input span (.emit event :: tasks) events) =
      some (ready input span tasks (event :: events)) := by
  simp [step, program, config, ready, initial, TM2.step, TM2.stepAux]
  funext key
  cases key <;> simp [Function.update]

theorem next_token (task : Task) (notEmit : ∀ event, task ≠ .emit event)
    (input span : List Alphabet) (tasks : List Task) (events : List Event) :
    step (ready input span (task :: tasks) events) =
      some (config (some .listCell) {initial with current := some task}
        input [] [] span tasks events []) := by
  cases task <;>
    simp [step, program, config, ready, initial, TM2.step, TM2.stepAux] at notEmit ⊢
  all_goals funext key
  all_goals cases key <;> simp [Function.update]

theorem cell_cons (task : Task) (input span : List Alphabet) (tasks : List Task) (events : List Event) :
    step (config (some .listCell) {initial with current := some task}
      (4 :: input) [] [] span tasks events []) =
      some (embedField task tasks events (4 :: span)
        (PrefixField.config (some .header) none input [] [] [])) := by
  simp [step, program, config, embedField, PrefixField.config, initial,
    FiniteWordClassifier.walkState, TM2.step, TM2.stepAux]
  funext key
  cases key <;> simp [Function.update]

theorem field_empty (task : Task) (tasks : List Task) (events : List Event)
    (span input scratch : List Alphabet) (state : Option Alphabet)
    (cursors : FiniteWordClassifier.Residuals PatternTokenField.words) :
    step (config (some (.field .complete)) ⟨state, some task, cursors, none⟩
      input [] scratch span tasks events []) =
      some (config (some (.field .checkTail)) ⟨none, some task, cursors, none⟩
        input [] scratch span tasks events []) := by
  simp [step, program, fieldProgram, parserProgram, observe,
    PrefixField.machine_complete, CertificateDataTraversal.machine, StackMachineRegisters.withStack,
    config, parserAlphabet, parserKey, TM2.step, TM2.stepAux, Equiv.refl_symm, Equiv.refl_apply]

theorem field_return (state : Control) (input scratch span : List Alphabet)
    (tasks : List Task) (events : List Event) :
    step (config (some (.field .checkTail)) state input [] scratch span tasks events []) =
      some (config (some .clearScratch) state input [] scratch span tasks events []) := rfl

theorem clear_cons (state : Control) (head : Alphabet) (input scratch span : List Alphabet)
    (tasks : List Task) (events : List Event) :
    step (config (some .clearScratch) state input [] (head :: scratch) span tasks events []) =
      some (config (some .clearScratch) {state with symbol := some head}
        input [] scratch span tasks events []) := by
  simp [step, program, config, TM2.step, TM2.stepAux]
  funext key
  cases key <;> simp [Function.update]

theorem clear_nil (state : Control) (input span : List Alphabet)
    (tasks : List Task) (events : List Event) :
    step (config (some .clearScratch) state input [] [] span tasks events []) =
      some (config (some (.dispatch (state.current.getD .pattern)
        (FiniteWordClassifier.finish PatternTokenField.words state.cursors)))
        {state with symbol := none} input [] [] span tasks events []) := by
  simp [step, program, config, TM2.step, TM2.stepAux]

noncomputable def clearRun (state : Control) (input scratch span : List Alphabet)
    (tasks : List Task) (events : List Event) :
    EvalsToInTime step (config (some .clearScratch) state input [] scratch span tasks events [])
      (some (config (some (.dispatch (state.current.getD .pattern)
        (FiniteWordClassifier.finish PatternTokenField.words state.cursors)))
        {state with symbol := none} input [] [] span tasks events [])) (scratch.length + 1) := by
  induction scratch generalizing state with
  | nil => simpa using StackMachineComposition.oneStep (clear_nil state input span tasks events)
  | cons head scratch ih =>
      have first := StackMachineComposition.oneStep (clear_cons state head input scratch span tasks events)
      have rest := ih {state with symbol := some head}
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EvalsToInTime.trans _ _ _ _ _ _ first rest

theorem pushTasks_apply (next : List Task) (statement : TM2.Stmt StackAlphabet Phase Control)
    (state : Control) (input span : List Alphabet) (tasks : List Task) (events : List Event) :
    TM2.stepAux (pushTasks next statement) state
      (config none state input [] [] span tasks events []).stk =
      TM2.stepAux statement state (config none state input [] [] span (next ++ tasks) events []).stk := by
  induction next generalizing statement tasks with
  | nil => rfl
  | cons head tail ih =>
      simp only [pushTasks]
      rw [ih]
      simp only [TM2.stepAux]
      congr 1
      funext key
      cases key <;> simp [config, Function.update]

theorem dispatch_accepted (task : Task) (tag : Option (Fin 14)) (next : List Task)
    (accepted : plan task tag = some next) (state : Control) (input span : List Alphabet)
    (tasks : List Task) (events : List Event) :
    step (config (some (.dispatch task tag)) state input [] [] span tasks events []) =
      some (ready input span (next ++ tasks) events) := by
  simp only [step, TM2.step, config, program, accepted]
  change some (TM2.stepAux (pushTasks next (load (fun _ => initial) (goto fun _ => .next)))
    state (config none state input [] [] span tasks events []).stk) = _
  rw [pushTasks_apply]
  rfl


theorem accepted_not_emit (task : Task) (tag : Option (Fin 14)) (next : List Task)
    (accepted : plan task tag = some next) : ∀ event, task ≠ .emit event := by
  intro event same
  subst task
  cases tag with
  | none => cases accepted
  | some tag => fin_cases tag <;> cases accepted

theorem classified_field (token : String) :
    FiniteWordClassifier.finish PatternTokenField.words
      (FiniteWordClassifier.walkState PatternTokenField.words (encodeWith Codec.string token)
        (FiniteWordClassifier.initial PatternTokenField.words)) = tokenTag token := by
  rw [FiniteWordClassifier.finish_walk]
  exact Dictionary.classify_original Codec.string PatternTokenField.tags token

set_option maxRecDepth 4096 in
/-- One original String field is physically scanned, classified and retained.
The walker scratch is reclaimed before the next grammar task is dispatched. -/
noncomputable def tokenRun (task : Task) (tasks next : List Task) (token : String)
    (accepted : plan task (tokenTag token) = some next)
    (tail : List String) (span : List Alphabet) (events : List Event) :
    EvalsToInTime step (ready (tokenWire (token :: tail)) span (task :: tasks) events)
      (some (ready (tokenWire tail) ((4 :: encodeWith Codec.string token).reverse ++ span)
        (next ++ tasks) events))
      (scanCost (Codec.string.put token) + (postorderWire (Codec.string.put token)).length + 6) := by
  let value := Codec.string.put token
  let bytes := encodeWith Codec.string token
  let cursors := FiniteWordClassifier.walkState PatternTokenField.words bytes
    (FiniteWordClassifier.initial PatternTokenField.words)
  let captured := (4 :: bytes).reverse ++ span
  let state : Control := ⟨none, some task, cursors, none⟩
  have first := StackMachineComposition.oneStep
    (next_token task (accepted_not_emit task _ next accepted)
      (tokenWire (token :: tail)) span tasks events)
  rw [tokenWire_cons] at first
  have cell := StackMachineComposition.oneStep
    (cell_cons task (bytes ++ tokenWire tail) span tasks events)
  have walk := fieldRun task tasks events (4 :: span) value (tokenWire tail) [] [] [] none
  have walked : EvalsToInTime step
      (embedField task tasks events (4 :: span)
        (PrefixField.config (some .header) none (bytes ++ tokenWire tail) [] [] []))
      (some (config (some (.field .complete))
        ⟨finalState value, some task, cursors, none⟩
        (tokenWire tail) [] (postorderWire value).reverse captured tasks events []))
      (scanCost value) := by
    change EvalsToInTime step
      (embedField task tasks events (4 :: span)
        (PrefixField.config (some .header) none (writeData value (tokenWire tail)) [] [] []))
      (some (embedField task tasks events (4 :: span)
        (PrefixField.config (some .complete) (finalState value) (tokenWire tail) []
          ((postorderWire value).reverse ++ []) ((encodeData value).reverse ++ []))))
      (scanCost value) at walk
    rw [writeData_append, show writeData value [] = bytes from rfl,
      show encodeData value = bytes from rfl] at walk
    simpa only [embedField_config, Option.map_some, List.append_nil,
      List.reverse_reverse, List.reverse_cons, captured, List.append_assoc, List.singleton_append] using walk
  have empty := StackMachineComposition.oneStep
    (field_empty task tasks events captured (tokenWire tail)
      (postorderWire value).reverse (finalState value) cursors)
  have returned := StackMachineComposition.oneStep
    (field_return state (tokenWire tail) (postorderWire value).reverse captured tasks events)
  have cleared := clearRun state (tokenWire tail) (postorderWire value).reverse captured tasks events
  have classify : FiniteWordClassifier.finish PatternTokenField.words cursors = tokenTag token :=
    classified_field token
  have dispatched := StackMachineComposition.oneStep
    (dispatch_accepted task (tokenTag token) next accepted state
      (tokenWire tail) captured tasks events)
  have clearTarget : EvalsToInTime step
      (config (some .clearScratch) state (tokenWire tail) []
        (postorderWire value).reverse captured tasks events [])
      (some (config (some (.dispatch task (tokenTag token))) state
        (tokenWire tail) [] [] captured tasks events []))
      ((postorderWire value).length + 1) := by
    simpa only [state, Option.getD_some, classify, List.length_reverse] using cleared
  have joined := EvalsToInTime.trans _ _ _ _ _ _ first cell
  have joined := EvalsToInTime.trans _ _ _ _ _ _ joined walked
  have joined := EvalsToInTime.trans _ _ _ _ _ _ joined empty
  have joined := EvalsToInTime.trans _ _ _ _ _ _ joined returned
  have joined := EvalsToInTime.trans _ _ _ _ _ _ joined clearTarget
  have joined := EvalsToInTime.trans _ _ _ _ _ _ joined dispatched
  convert joined using 1
  · simp only [tokenWire_cons]
  · dsimp only [value]
    omega

theorem token_cost_le (token : String) :
    scanCost (Codec.string.put token) + (postorderWire (Codec.string.put token)).length + 6 ≤
      6 * (4 :: encodeWith Codec.string token).length := by
  have cost := scanCost_add_one_le (Codec.string.put token)
  have bytes : (encodeWith Codec.string token).length = dataWeight (Codec.string.put token) := by
    simp [encodeWith, encodeData, writeData_length]
  rw [postorderWire_length, List.length_cons, bytes]
  omega


/-- Every finite-task visit runs on the original byte stream. Pending caller
work, unread tokens and physical event order are retained. -/
theorem visits_execution {tasks : List Task} {input tail : List String} {emitted : List Event}
    (visited : Visits tasks input tail emitted) (pending : List Task)
    (span : List Alphabet) (before : List Event) :
    ∃ consumed : List String, input = consumed ++ tail ∧
      Nonempty (EvalsToInTime step (ready (tokenWire input) span (tasks ++ pending) before)
        (some (ready (tokenWire tail) ((fields consumed).reverse ++ span)
          pending (emitted.reverse ++ before)))
        (6 * (fields consumed).length + emitted.length)) := by
  induction visited generalizing pending span before with
  | done tail =>
      refine ⟨[], rfl, ?_⟩
      simpa only [fields, List.flatMap_nil, List.reverse_nil, List.nil_append,
        List.length_nil, Nat.mul_zero, Nat.add_zero] using
        (show Nonempty (EvalsToInTime step (ready (tokenWire tail) span pending before)
          (some (ready (tokenWire tail) span pending before)) 0) from
          ⟨EvalsToInTime.refl _ _⟩)
  | @emit event tasks input tail emitted _ ih =>
      obtain ⟨consumed, same, ⟨rest⟩⟩ := ih pending span (event :: before)
      have first := StackMachineComposition.oneStep
        (next_emit event (tokenWire input) span (tasks ++ pending) before)
      have joined := EvalsToInTime.trans _ _ _ _ _ _ first rest
      refine ⟨consumed, same, ?_⟩
      simpa only [List.cons_append, List.reverse_cons, List.singleton_append, List.append_assoc, List.nil_append,
        List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (show Nonempty _ from ⟨joined⟩)
  | @token task tasks next token input tail emitted accepted _ ih =>
      obtain ⟨consumed, same, ⟨rest⟩⟩ := ih pending
        ((4 :: encodeWith Codec.string token).reverse ++ span) before
      have first := tokenRun task (tasks ++ pending) next token accepted input span before
      have aligned : EvalsToInTime step
          (ready (tokenWire input) ((4 :: encodeWith Codec.string token).reverse ++ span)
            (next ++ (tasks ++ pending)) before)
          (some (ready (tokenWire tail)
            ((fields consumed).reverse ++ (4 :: encodeWith Codec.string token).reverse ++ span)
            pending (emitted.reverse ++ before)))
          (6 * (fields consumed).length + emitted.length) := by
        simpa only [List.append_assoc] using rest
      have joined := EvalsToInTime.trans _ _ _ _ _ _ first aligned
      have cost := token_cost_le token
      have enlarged :
          (6 * (fields consumed).length + emitted.length) +
            (scanCost (Codec.string.put token) + (postorderWire (Codec.string.put token)).length + 6) ≤
          6 * (fields (token :: consumed)).length + emitted.length := by
        simp only [fields, List.flatMap_cons, List.length_append] at cost ⊢
        omega
      refine ⟨token :: consumed, by simp only [List.cons_append, same], ?_⟩
      have bounded := (show EvalsToInTime step _ _
        (6 * (fields (token :: consumed)).length + emitted.length) from
        ⟨joined.toEvalsTo, joined.steps_le_m.trans enlarged⟩)
      simpa only [fields, List.flatMap_cons, List.reverse_append, List.reverse_cons, List.append_assoc,
        List.cons_append, List.singleton_append, List.nil_append] using (show Nonempty _ from ⟨bounded⟩)


theorem next_done (input span : List Alphabet) (emitted : List Event) :
    step (ready input span [] emitted) =
      some (config (some .finishSpan) initial input [] [] span [] emitted []) := by
  simp [step, program, config, ready, initial, TM2.step, TM2.stepAux]

theorem finish_span (input span : List Alphabet) (emitted : List Event) :
    step (config (some .finishSpan) initial input [] [] span [] emitted []) =
      some (config (some .restoreSpan) initial input [] [] span [] emitted [3, 2]) := by
  simp [step, program, config, TM2.step, TM2.stepAux]
  funext key
  cases key <;> simp [Function.update]

theorem restore_cons (state : Control) (head : Alphabet) (input span result : List Alphabet)
    (emitted : List Event) :
    step (config (some .restoreSpan) state input [] [] (head :: span) [] emitted result) =
      some (config (some .restoreSpan) {state with symbol := some head}
        input [] [] span [] emitted (head :: result)) := by
  simp [step, program, config, TM2.step, TM2.stepAux]
  funext key
  cases key <;> simp [Function.update]

theorem restore_nil (state : Control) (input result : List Alphabet) (emitted : List Event) :
    step (config (some .restoreSpan) state input [] [] [] [] emitted result) =
      some (config none initial input [] [] [] [] emitted result) := by
  simp [step, program, config, TM2.step, TM2.stepAux]

noncomputable def restoreRun (state : Control) (input span result : List Alphabet)
    (emitted : List Event) :
    EvalsToInTime step (config (some .restoreSpan) state input [] [] span [] emitted result)
      (some (config none initial input [] [] [] [] emitted (span.reverse ++ result)))
      (span.length + 1) := by
  induction span generalizing state result with
  | nil => simpa using StackMachineComposition.oneStep (restore_nil state input result emitted)
  | cons head span ih =>
      have first := StackMachineComposition.oneStep (restore_cons state head input span result emitted)
      have rest := ih {state with symbol := some head} (head :: result)
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
        List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EvalsToInTime.trans _ _ _ _ _ _ first rest

noncomputable def finishRun (input span : List Alphabet) (emitted : List Event) :
    EvalsToInTime step (ready input span [] emitted)
      (some (config none initial input [] [] [] [] emitted (span.reverse ++ [3, 2])))
      (span.length + 3) := by
  have first := StackMachineComposition.oneStep (next_done input span emitted)
  have middle := StackMachineComposition.oneStep (finish_span input span emitted)
  have last := restoreRun initial input span [3, 2] emitted
  have joined := EvalsToInTime.trans _ _ _ _ _ _ first middle
  have joined := EvalsToInTime.trans _ _ _ _ _ _ joined last
  convert joined using 1

/-- Return an original complete token-list span and leave the caller's unread
suffix untouched. Finite events remain in reverse chronological stack order. -/
theorem visits_complete {tasks : List Task} {input tail : List String} {emitted : List Event}
    (visited : Visits tasks input tail emitted) :
    ∃ consumed : List String, input = consumed ++ tail ∧
      Nonempty (EvalsToInTime step (ready (tokenWire input) [] tasks [])
        (some (config none initial (tokenWire tail) [] [] [] [] emitted.reverse
          (tokenWire consumed)))
        (7 * (fields consumed).length + emitted.length + 3)) := by
  obtain ⟨consumed, same, ⟨run⟩⟩ := visits_execution visited [] [] []
  have final := finishRun (tokenWire tail) (fields consumed).reverse emitted.reverse
  have aligned : EvalsToInTime step (ready (tokenWire input) [] tasks [])
      (some (ready (tokenWire tail) (fields consumed).reverse [] emitted.reverse))
      (6 * (fields consumed).length + emitted.length) := by
    simpa only [List.append_nil] using run
  have joined := EvalsToInTime.trans _ _ _ _ _ _ aligned final
  refine ⟨consumed, same, ?_⟩
  have output : (fields consumed).reverse.reverse ++ [3, 2] = tokenWire consumed := by
    rw [List.reverse_reverse, tokenWire_eq]
  rw [output] at joined
  have clock :
      ((fields consumed).reverse.length + 3) + (6 * (fields consumed).length + emitted.length) =
      7 * (fields consumed).length + emitted.length + 3 := by
    rw [List.length_reverse]
    omega
  rw [clock] at joined
  exact ⟨joined⟩


theorem plan_length_le (task : Task) (tag : Option (Fin 14)) (next : List Task)
    (accepted : plan task tag = some next) : next.length ≤ 10 := by
  cases task <;> cases tag with
  | none => simp [plan] at accepted <;> subst next <;> simp
  | some tag => fin_cases tag <;> simp [plan] at accepted <;> subst next <;> simp

theorem Visits.tail_length_le {tasks : List Task} {input tail : List String} {emitted : List Event}
    (visited : Visits tasks input tail emitted) : tail.length ≤ input.length := by
  induction visited with
  | done => exact le_rfl
  | emit _ ih => exact ih
  | token _ _ ih => simp only [List.length_cons]; omega

theorem Visits.events_length_le {tasks : List Task} {input tail : List String} {emitted : List Event}
    (visited : Visits tasks input tail emitted) :
    emitted.length ≤ tasks.length + 10 * (input.length - tail.length) := by
  induction visited with
  | done => simp
  | emit _ ih => simp only [List.length_cons]; omega
  | @token task tasks next token input tail emitted accepted visit ih =>
      have suffix := Visits.tail_length_le visit
      have count := plan_length_le task (tokenTag token) next accepted
      simp only [List.length_append, List.length_cons] at ih ⊢
      omega

theorem fields_count_le (tokens : List String) : tokens.length ≤ (fields tokens).length := by
  induction tokens with
  | nil => rfl
  | cons token tokens ih =>
      simp only [fields, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
      omega

theorem pattern_events_length_le (value : Pattern) :
    (events value).length ≤ 1 + 10 * (fields (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode value)).length := by
  have length := Visits.events_length_le (visits_write value [])
  have fields := fields_count_le (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode value)
  simp only [List.length_singleton, List.length_nil, Nat.sub_zero] at length
  change (events value).length ≤ 1 + 10 *
    (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode value).length at length
  omega

def startConfig (tokens : List String) : Cfg :=
  config (some .start) initial (tokenWire tokens) [] [] [] [] [] []

theorem start_step (tokens : List String) :
    step (startConfig tokens) = some (ready (tokenWire tokens) [] [.pattern] []) := by
  simp [step, startConfig, ready, program, config, TM2.step, TM2.stepAux]
  funext key
  cases key <;> simp [Function.update]

/-- The actual finite stack program traverses every original encoded pattern,
including opaque binders and metadata, without interpreting them as HOL terms. -/
theorem pattern_execution (value : Pattern) (tail : List String) :
    Nonempty (EvalsToInTime step
      (startConfig (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode value ++ tail))
      (some (config none initial (tokenWire tail) [] [] [] [] (events value).reverse
        (tokenWire (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode value))))
      (7 * (fields (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode value)).length +
        (events value).length + 4)) := by
  obtain ⟨consumed, same, ⟨walk⟩⟩ := visits_complete (visits_write value tail)
  have writeEq : Mettapedia.OSLF.MeTTaIL.PatternTokens.write value tail =
      Mettapedia.OSLF.MeTTaIL.PatternTokens.encode value ++ tail := by
    simpa only [List.nil_append, Mettapedia.OSLF.MeTTaIL.PatternTokens.encode] using
      Mettapedia.OSLF.MeTTaIL.PatternTokens.write_append value [] tail
  have captured : consumed = Mettapedia.OSLF.MeTTaIL.PatternTokens.encode value := by
    apply List.append_cancel_right
    exact same.symm.trans writeEq
  rw [captured, writeEq] at walk
  have first := StackMachineComposition.oneStep
    (start_step (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode value ++ tail))
  have joined := EvalsToInTime.trans _ _ _ _ _ _ first walk
  have clock :
      (7 * (fields (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode value)).length + (events value).length + 3) + 1 =
      7 * (fields (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode value)).length + (events value).length + 4 := by omega
  rw [clock] at joined
  exact ⟨joined⟩

theorem pattern_clock_le (value : Pattern) :
    7 * (fields (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode value)).length + (events value).length + 4 ≤
      17 * (tokenWire (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode value)).length + 5 := by
  have events := pattern_events_length_le value
  simp only [tokenWire_eq, List.length_append, List.length_cons, List.length_nil] at ⊢
  omega

/-- The original certificate pattern codec is the exact input domain of the
visitor; this law only exposes its existing token-list representation. -/
theorem original_pattern_wire (value : Pattern) :
    encodeWith CertificateDataEncoding.patternCodec value =
      tokenWire (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode value) := rfl

/-- A linear bound on the actual traversal's transitions includes all original
UTF-8 name payloads and binary numeric fields. -/
theorem pattern_execution_linear (value : Pattern) (tail : List String) :
    Nonempty (EvalsToInTime step
      (startConfig (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode value ++ tail))
      (some (config none initial (tokenWire tail) [] [] [] [] (events value).reverse
        (tokenWire (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode value))))
      (17 * (encodeWith CertificateDataEncoding.patternCodec value).length + 5)) := by
  obtain ⟨run⟩ := pattern_execution value tail
  rw [original_pattern_wire]
  exact ⟨⟨run.toEvalsTo, run.steps_le_m.trans (pattern_clock_le value)⟩⟩

end Execution

namespace Hooks

/-- Dynamic field bytes remain on stacks, interleaved with finite grammar
boundaries. The enclosing source-list marker is not part of a String field. -/
inductive Symbol where
  | fieldStart (task : Task) | byte (value : Alphabet) | fieldEnd | event (value : Event)
  deriving DecidableEq, Fintype

def field (task : Task) (token : String) : List Symbol :=
  .fieldStart task :: (encodeWith Codec.string token).map Symbol.byte ++ [.fieldEnd]

def erase : List Symbol → List Event :=
  List.filterMap fun symbol => match symbol with | .event event => some event | _ => none

/-- This is a trace refinement of the existing finite-task visitor. The
original `plan` is the sole grammar; fields retain their original codec. -/
inductive Trace : List Task → List String → List String → List Symbol → Prop
  | done (tail : List String) : Trace [] tail tail []
  | emit {event : Event} {tasks : List Task} {input tail : List String} {hooks : List Symbol} :
      Trace tasks input tail hooks → Trace (.emit event :: tasks) input tail (.event event :: hooks)
  | token {task : Task} {tasks next : List Task} {token : String}
      {input tail : List String} {hooks : List Symbol} :
      plan task (tokenTag token) = some next → Trace (next ++ tasks) input tail hooks →
      Trace (task :: tasks) (token :: input) tail (field task token ++ hooks)

theorem erase_field (task : Task) (token : String) : erase (field task token) = [] := by
  simp [erase, field, List.filterMap_map]

theorem erase_event (event : Event) (hooks : List Symbol) :
    erase (.event event :: hooks) = event :: erase hooks := rfl

theorem erase_append (left right : List Symbol) : erase (left ++ right) = erase left ++ erase right := by
  exact List.filterMap_append

theorem Trace.forget {tasks : List Task} {input tail : List String} {hooks : List Symbol}
    (trace : Trace tasks input tail hooks) : Visits tasks input tail (erase hooks) := by
  induction trace with
  | done => exact .done _
  | emit _ ih => exact .emit ih
  | @token task tasks next token input tail hooks accepted _ ih =>
      simpa only [erase_append, erase_field, List.nil_append] using
        Visits.token accepted ih

theorem Visits.with_trace {tasks : List Task} {input tail : List String} {emitted : List Event}
    (visited : Visits tasks input tail emitted) :
    ∃ hooks, Trace tasks input tail hooks ∧ erase hooks = emitted := by
  induction visited with
  | done tail => exact ⟨[], .done tail, rfl⟩
  | @emit event tasks input tail emitted _ ih =>
      obtain ⟨hooks, trace, same⟩ := ih
      exact ⟨.event event :: hooks, .emit trace, by simpa [erase] using congrArg (List.cons event) same⟩
  | @token task tasks next token input tail emitted accepted _ ih =>
      obtain ⟨hooks, trace, same⟩ := ih
      exact ⟨field task token ++ hooks, .token accepted trace,
        by simpa only [erase_append, erase_field, List.nil_append] using same⟩


/-- A finite static projection recovers the original source-list fields.
It copies dynamic bytes; it does not decode or reconstruct their values. -/
def sourceImage : Symbol → List Alphabet
  | .fieldStart _ => [4]
  | .byte value => [value]
  | .fieldEnd | .event _ => []

def sourceBytes (hooks : List Symbol) : List Alphabet := hooks.flatMap sourceImage

theorem sourceBytes_append (left right : List Symbol) :
    sourceBytes (left ++ right) = sourceBytes left ++ sourceBytes right := by
  exact List.flatMap_append

theorem sourceBytes_field (task : Task) (token : String) :
    sourceBytes (field task token) = 4 :: encodeWith Codec.string token := by
  simp [sourceBytes, field, sourceImage, List.flatMap_map]

theorem sourceBytes_event (event : Event) (hooks : List Symbol) :
    sourceBytes (.event event :: hooks) = sourceBytes hooks := rfl

theorem Trace.sourceBytes {tasks : List Task} {input tail : List String} {hooks : List Symbol}
    (trace : Trace tasks input tail hooks) :
    ∃ consumed, input = consumed ++ tail ∧
      sourceBytes hooks = PatternSpanExecution.Execution.fields consumed := by
  induction trace with
  | done tail => exact ⟨[],rfl,rfl⟩
  | @emit event tasks input tail hooks _ ih =>
      obtain ⟨consumed, same, bytes⟩ := ih
      exact ⟨consumed, same, bytes⟩
  | @token task tasks next token input tail hooks accepted _ ih =>
      obtain ⟨consumed, same, bytes⟩ := ih
      refine ⟨token :: consumed, by simp only [List.cons_append, same], ?_⟩
      simp only [sourceBytes_append, sourceBytes_field, bytes,
        PatternSpanExecution.Execution.fields, List.flatMap_cons]

theorem Trace.pattern_sourceBytes (value : Pattern) (hooks : List Symbol)
    (trace : Trace [.pattern] (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode value) [] hooks) :
    Hooks.sourceBytes hooks ++ [3,2] = encodeWith CertificateDataEncoding.patternCodec value := by
  obtain ⟨consumed, same, bytes⟩ := trace.sourceBytes
  simp only [List.append_nil] at same
  rw [bytes, ← same]
  rw [PatternSpanExecution.Execution.original_pattern_wire,
    PatternSpanExecution.Execution.tokenWire_eq]

theorem Trace.append_tail {tasks : List Task} {input tail : List String} {hooks : List Symbol}
    (trace : Trace tasks input tail hooks) (suffix : List String) :
    Trace tasks (input ++ suffix) (tail ++ suffix) hooks := by
  induction trace with
  | done tail => exact .done (tail ++ suffix)
  | emit _ ih => exact .emit ih
  | token accepted _ ih => simpa only [List.cons_append] using Trace.token accepted ih

theorem Trace.hooks_length_le {tasks : List Task} {input tail : List String} {hooks : List Symbol}
    (trace : Trace tasks input tail hooks) :
    hooks.length ≤ (PatternSpanExecution.Execution.fields input).length + input.length + (erase hooks).length := by
  induction trace with
  | done => simp
  | emit _ ih => simp [erase] at ih ⊢; omega
  | @token task tasks next token input tail hooks accepted _ ih =>
      have erased : erase (field task token ++ hooks) = erase hooks := by
        rw [erase_append, erase_field, List.nil_append]
      have fieldLength : (field task token).length =
          (encodeWith Codec.string token).length + 2 := by simp [field]
      rw [List.length_append, fieldLength, erased]
      simp only [PatternSpanExecution.Execution.fields, List.flatMap_cons, List.length_append,
        List.length_cons] at ih ⊢
      omega


theorem Trace.unique {tasks : List Task} {input firstTail secondTail : List String}
    {firstHooks secondHooks : List Symbol}
    (first : Trace tasks input firstTail firstHooks)
    (second : Trace tasks input secondTail secondHooks) :
    firstTail = secondTail ∧ firstHooks = secondHooks := by
  induction first generalizing secondTail secondHooks with
  | done tail =>
      cases second
      exact ⟨rfl,rfl⟩
  | emit previous ih =>
      cases second with
      | emit following =>
          obtain ⟨rfl,rfl⟩ := ih following
          exact ⟨rfl,rfl⟩
      | token accepted _ => simp [plan] at accepted
  | @token task tasks next token input tail hooks accepted previous ih =>
      cases second with
      | emit _ => simp [plan] at accepted
      | @token _ _ otherNext _ _ _ _ otherAccepted following =>
          have same : next = otherNext := Option.some.inj (accepted.symm.trans otherAccepted)
          subst otherNext
          obtain ⟨rfl,rfl⟩ := ih following
          exact ⟨rfl,rfl⟩

theorem Trace.append {first second : List Task} {input middle tail : List String}
    {before after : List Symbol} (left : Trace first input middle before)
    (right : Trace second middle tail after) :
    Trace (first ++ second) input tail (before ++ after) := by
  induction left with
  | done => exact right
  | emit _ ih => exact .emit (ih right)
  | @token task tasks next token input middle hooks accepted _ ih =>
      simpa only [List.cons_append,List.append_assoc] using
        Trace.token (task:=task) (tasks:=tasks++second) (next:=next)
          accepted (by simpa only [List.append_assoc] using ih right)

theorem Trace.event (event : Event) (input : List String) :
    Trace [.emit event] input input [.event event] := .emit (.done input)

theorem Trace.events (events : List Event) (input : List String) :
    Trace (events.map Task.emit) input input (events.map Symbol.event) := by
  induction events with
  | nil => exact .done input
  | cons event events ih => exact .emit ih

theorem Trace.surround {tasks : List Task} {input tail : List String}
    {middle : List Symbol} (trace : Trace tasks input tail middle)
    (before after : List Event) :
    Trace (before.map Task.emit ++ tasks ++ after.map Task.emit) input tail
      (before.map Symbol.event ++ middle ++ after.map Symbol.event) :=
  ((Trace.events before input).append trace).append (Trace.events after tail)


namespace Execution

abbrev Cells := StackMachineRegisters.withStackAlphabet
  (StackMachineRegisters.withStackAlphabet PatternSpanExecution.Execution.StackAlphabet Symbol) Symbol
instance (key : Option (Option PatternSpanExecution.Execution.Stack)) : Fintype (Cells key) := by
  cases key with
  | none => change Fintype Symbol; infer_instance
  | some key => cases key with
    | none => change Fintype Symbol; infer_instance
    | some key => cases key <;> infer_instance

inductive Phase where
  | visit (phase : PatternSpanExecution.Execution.Phase)
  | reverseHooks | rejectHooks
  deriving DecidableEq, Fintype
abbrev Control := PatternSpanExecution.Execution.Control × Option Symbol

def initial : Control := (PatternSpanExecution.Execution.initial, none)

def key (source : PatternSpanExecution.Execution.Stack) : Option (Option PatternSpanExecution.Execution.Stack) :=
  some (some source)

/-- Instrument the original statements. Only writes of original field bytes
and boundary events add hook symbols; source operations are retained exactly. -/
def lift (capture : Bool) : TM2.Stmt PatternSpanExecution.Execution.StackAlphabet
    PatternSpanExecution.Execution.Phase PatternSpanExecution.Execution.Control → TM2.Stmt Cells Phase Control
  | .push .span value rest =>
      push (key .span) (fun state => value state.1)
        (if capture then push (some none) (fun state => .byte (value state.1)) (lift capture rest)
          else lift capture rest)
  | .push .events value rest => push (key .events) (fun state => value state.1)
      (push (some none) (fun state => .event (value state.1)) (lift capture rest))
  | .push source value rest => push (key source) (fun state => value state.1) (lift capture rest)
  | .peek source update rest => peek (key source)
      (fun state value => (update state.1 value, state.2)) (lift capture rest)
  | .pop source update rest => pop (key source)
      (fun state value => (update state.1 value, state.2)) (lift capture rest)
  | .load update rest => load (fun state => (update state.1, state.2)) (lift capture rest)
  | .branch condition yes no => branch (fun state => condition state.1) (lift capture yes) (lift capture no)
  | .goto label => goto (fun state => .visit (label state.1))
  | .halt => goto fun _ => .reverseHooks

/-- Original field reading, lexical dispatch and finite tasks are reused.
The only additional loop restores hook-stream order at the final boundary. -/
def program : Phase → TM2.Stmt Cells Phase Control
  | .visit .listCell => push (some none) (fun state => .fieldStart (state.1.current.getD .pattern))
      (lift false (PatternSpanExecution.Execution.program .listCell))
  | .visit .clearScratch => pop (key .scratch) (fun state value => ({state.1 with symbol := value}, state.2))
      (branch (fun state => state.1.symbol.isSome) (goto fun _ => .visit .clearScratch)
        (push (some none) (fun _ => .fieldEnd)
          (goto fun state => .visit (.dispatch (state.1.current.getD .pattern)
            (FiniteWordClassifier.finish PatternTokenField.words state.1.cursors)))))
  | .visit (.field phase) => lift true (PatternSpanExecution.Execution.program (.field phase))
  | .visit .rejectEvents => pop (key .events) (fun state value => ({state.1 with event := value}, state.2))
      (branch (fun state => state.1.event.isSome) (goto fun _ => .visit .rejectEvents)
        (push (key .result) (fun _ => (0 : Alphabet)) (load (fun _ => initial) (goto fun _ => .rejectHooks))))
  | .visit phase => lift false (PatternSpanExecution.Execution.program phase)
  | .reverseHooks => pop (some none) (fun state value => (state.1, value))
      (branch (fun state => state.2.isSome)
        (push none (fun state => state.2.getD .fieldEnd) (goto fun _ => .reverseHooks))
        (load (fun _ => initial) halt))
  | .rejectHooks => pop (some none) (fun state value => (state.1, value))
      (branch (fun state => state.2.isSome) (goto fun _ => .rejectHooks)
        (load (fun _ => initial) halt))

abbrev Cfg := TM2.Cfg Cells Phase Control

def step : Cfg → Option Cfg := TM2.step program

def machine : FinTM2 where
  K := Option (Option PatternSpanExecution.Execution.Stack)
  k₀ := key .input
  k₁ := none
  Γ := Cells
  Λ := Phase
  main := .visit .start
  σ := Control
  initialState := initial
  m := program

theorem machine_step : machine.step = step := rfl

def config (phase : Option Phase) (state : Control)
    (input frames scratch span : List Alphabet) (tasks : List Task) (events : List Event)
    (receipt : List Alphabet) (hooks output : List Symbol) : Cfg where
  l := phase
  var := state
  stk index := match index with
    | none => output
    | some none => hooks
    | some (some .input) => input | some (some .frames) => frames
    | some (some .scratch) => scratch | some (some .span) => span
    | some (some .tasks) => tasks | some (some .events) => events
    | some (some .result) => receipt

def ready (input span : List Alphabet) (tasks : List Task) (events : List Event)
    (hooks : List Symbol) : Cfg := config (some (.visit .next)) initial input [] [] span tasks events [] hooks []

def startConfig (input : List String) : Cfg :=
  config (some (.visit .start)) initial (PatternSpanExecution.Execution.tokenWire input) [] [] [] [] [] [] [] []

/-- The hook copy of a scanned field is a sequence of original bytes. The
source cursor and stored span are the unchanged visitor's configuration. -/
def embedField (task : Task) (tasks : List Task) (events : List Event)
    (span : List Alphabet) (hooks : List Symbol) (source : PatternSpanExecution.Execution.ParserCfg) : Cfg :=
  let old := PatternSpanExecution.Execution.embedField task tasks events span source
  config (old.l.map Phase.visit) (old.var, none)
    (old.stk .input) (old.stk .frames) (old.stk .scratch) (old.stk .span)
    tasks events [] ((source.stk none).map Symbol.byte ++ hooks) []

theorem embedField_config (task : Task) (tasks : List Task) (events : List Event)
    (span : List Alphabet) (hooks : List Symbol) (phase : Option CertificateDataTraversal.Phase)
    (state : Option Alphabet) (input frames output memo : List Alphabet) :
    embedField task tasks events span hooks (PrefixField.config phase state input frames output memo) =
      config ((phase.map PatternSpanExecution.Execution.Phase.field).map Phase.visit)
        (⟨state, some task, FiniteWordClassifier.walkState PatternTokenField.words memo.reverse
          (FiniteWordClassifier.initial PatternTokenField.words), none⟩, none)
        input frames output (memo ++ span) tasks events [] (memo.map Symbol.byte ++ hooks) [] := rfl

theorem header_mapped (task : Task) (tasks : List Task) (events : List Event)
    (span : List Alphabet) (hooks : List Symbol) (state : Option Alphabet) (input frames output memo : List Alphabet) :
    step (embedField task tasks events span hooks
      (PrefixField.config (some .header) state input frames output memo)) =
      (TM2.step PatternSpanExecution.Execution.parserProgram (PrefixField.config (some .header) state input frames output memo)).map
        (embedField task tasks events span hooks) := by
  cases input with
  | nil =>
      with_unfolding_all simp [step, program, lift, PatternSpanExecution.Execution.program,
        PatternSpanExecution.Execution.embedField, PatternSpanExecution.Execution.config,
        PatternSpanExecution.Execution.fieldProgram, PatternSpanExecution.Execution.observe,
        PatternSpanExecution.Execution.parserAlphabet, PatternSpanExecution.Execution.parserKey,
        key, PatternSpanExecution.Execution.parserProgram,
        PrefixField.machine_header, embedField, config, PrefixField.config,
        TM2.step, TM2.stepAux]
  | cons head tail =>
      fin_cases head <;>
        with_unfolding_all simp [step, program, lift, PatternSpanExecution.Execution.program,
        PatternSpanExecution.Execution.embedField, PatternSpanExecution.Execution.config,
        PatternSpanExecution.Execution.fieldProgram, PatternSpanExecution.Execution.observe,
        PatternSpanExecution.Execution.parserAlphabet, PatternSpanExecution.Execution.parserKey,
        PatternSpanExecution.Execution.cursor_append, FiniteWordClassifier.walkState, key, List.map_cons, PatternSpanExecution.Execution.parserProgram,
          PrefixField.machine_header, embedField, config, PrefixField.config,
          TM2.step, TM2.stepAux, Bool.cond_eq_ite, Function.update]
      all_goals funext index
      all_goals cases index with
        | none => simp [Function.update]
        | some index => cases index with
          | none => simp [Function.update]
          | some index => cases index <;> simp [Function.update]

theorem number_mapped (task : Task) (tasks : List Task) (events : List Event)
    (span : List Alphabet) (hooks : List Symbol) (state : Option Alphabet) (input frames output memo : List Alphabet) :
    step (embedField task tasks events span hooks
      (PrefixField.config (some .number) state input frames output memo)) =
      (TM2.step PatternSpanExecution.Execution.parserProgram (PrefixField.config (some .number) state input frames output memo)).map
        (embedField task tasks events span hooks) := by
  cases input with
  | nil =>
      with_unfolding_all simp [step, program, lift, PatternSpanExecution.Execution.program,
        PatternSpanExecution.Execution.embedField, PatternSpanExecution.Execution.config,
        PatternSpanExecution.Execution.fieldProgram, PatternSpanExecution.Execution.observe,
        PatternSpanExecution.Execution.parserAlphabet, PatternSpanExecution.Execution.parserKey,
        key, PatternSpanExecution.Execution.parserProgram,
        PrefixField.machine_number, embedField, config, PrefixField.config,
        TM2.step, TM2.stepAux, SharedReferenceExecution.isBit]
  | cons head tail =>
      fin_cases head <;>
        with_unfolding_all simp [step, program, lift, PatternSpanExecution.Execution.program,
        PatternSpanExecution.Execution.embedField, PatternSpanExecution.Execution.config,
        PatternSpanExecution.Execution.fieldProgram, PatternSpanExecution.Execution.observe,
        PatternSpanExecution.Execution.parserAlphabet, PatternSpanExecution.Execution.parserKey,
        PatternSpanExecution.Execution.cursor_append, FiniteWordClassifier.walkState, key, List.map_cons, PatternSpanExecution.Execution.parserProgram,
          PrefixField.machine_number, embedField, config, PrefixField.config,
          TM2.step, TM2.stepAux, Bool.cond_eq_ite, Function.update, SharedReferenceExecution.isBit]
      all_goals funext index
      all_goals cases index with
        | none => simp [Function.update]
        | some index => cases index with
          | none => simp [Function.update]
          | some index => cases index <;> simp [Function.update]


theorem complete_mapped (task : Task) (tasks : List Task) (events : List Event)
    (span : List Alphabet) (hooks : List Symbol) (state : Option Alphabet) (input frames output memo : List Alphabet)
    (second : Bool) :
    step (embedField task tasks events span hooks
      (PrefixField.config (some .complete) state input
        ((if second then 1 else 0) :: frames) output memo)) =
      (TM2.step PatternSpanExecution.Execution.parserProgram (PrefixField.config (some .complete) state input
        ((if second then 1 else 0) :: frames) output memo)).map
        (embedField task tasks events span hooks) := by
  cases second <;>
    with_unfolding_all simp [step, program, lift, PatternSpanExecution.Execution.program,
        PatternSpanExecution.Execution.embedField, PatternSpanExecution.Execution.config,
        PatternSpanExecution.Execution.fieldProgram, PatternSpanExecution.Execution.observe,
        PatternSpanExecution.Execution.parserAlphabet, PatternSpanExecution.Execution.parserKey,
        key, PatternSpanExecution.Execution.parserProgram,
      PrefixField.machine_complete, CertificateDataTraversal.machine,
      embedField, config, PrefixField.config, StackMachineRegisters.withStack,
      TM2.step, TM2.stepAux,
      Bool.cond_eq_ite, Function.update]
  all_goals funext index
  all_goals cases index with
    | none => simp [Function.update]
    | some index => cases index with
      | none => simp [Function.update]
      | some index => cases index <;> simp [Function.update]

theorem field_steps (task : Task) (tasks : List Task) (events : List Event)
    (span : List Alphabet) (hooks : List Symbol) (source : PrefixField.machine.Cfg) (allowed : PrefixField.scanning source) :
    step (embedField task tasks events span hooks source) =
      (PrefixField.machine.step source).map (embedField task tasks events span hooks) := by
  rw [PatternSpanExecution.Execution.parser_machine_step]
  rcases allowed with header | number | ⟨complete, first | second⟩
  · have same := PrefixField.config_eta source
    rw [header] at same
    rw [same]
    simpa only [] using header_mapped task tasks events span hooks source.var
      (source.stk (some CertificateDataTraversal.Stack.input))
      (source.stk (some CertificateDataTraversal.Stack.frames))
      (source.stk (some CertificateDataTraversal.Stack.output)) (source.stk none)
  · have same := PrefixField.config_eta source
    rw [number] at same
    rw [same]
    simpa only [] using number_mapped task tasks events span hooks source.var
      (source.stk (some CertificateDataTraversal.Stack.input))
      (source.stk (some CertificateDataTraversal.Stack.frames))
      (source.stk (some CertificateDataTraversal.Stack.output)) (source.stk none)
  · have frames := List.head?_eq_some_iff.mp first
    obtain ⟨tail, frameEq⟩ := frames
    have same := PrefixField.config_eta source
    rw [complete, frameEq] at same
    rw [same]
    simpa only [Bool.false_eq_true, ↓reduceIte] using
      complete_mapped task tasks events span hooks source.var
        (source.stk (some CertificateDataTraversal.Stack.input)) tail
        (source.stk (some CertificateDataTraversal.Stack.output)) (source.stk none) false
  · have frames := List.head?_eq_some_iff.mp second
    obtain ⟨tail, frameEq⟩ := frames
    have same := PrefixField.config_eta source
    rw [complete, frameEq] at same
    rw [same]
    simpa only [machine_step, ↓reduceIte] using
      complete_mapped task tasks events span hooks source.var
        (source.stk (some CertificateDataTraversal.Stack.input)) tail
        (source.stk (some CertificateDataTraversal.Stack.output)) (source.stk none) true

/-- The original byte walker records complete original field words in the
hook stack while retaining the same source field span and unread input. -/
noncomputable def fieldRun (task : Task) (tasks : List Task) (events : List Event)
    (span : List Alphabet) (hooks : List Symbol) (value : Data)
    (input frames output memo : List Alphabet) (state : Option Alphabet) :=
  PrefixField.walkInto step (embedField task tasks events span hooks)
    (steps := field_steps task tasks events span hooks)
    value input frames output memo state


local macro "hook_step" : tactic => `(tactic| (
  simp [step, program, lift, key, config, ready, initial,
    PatternSpanExecution.Execution.program, PatternSpanExecution.Execution.initial,
    TM2.step, TM2.stepAux]
  all_goals funext index
  all_goals cases index with
    | none => simp [Function.update]
    | some index => cases index with
      | none => simp [Function.update]
      | some index => cases index <;> simp [Function.update]))

theorem next_emit (event : Event) (input span : List Alphabet) (tasks : List Task)
    (events : List Event) (hooks : List Symbol) :
    step (ready input span (.emit event :: tasks) events hooks) =
      some (ready input span tasks (event :: events) (.event event :: hooks)) := by hook_step

theorem next_token (task : Task) (notEmit : ∀ event, task ≠ .emit event)
    (input span : List Alphabet) (tasks : List Task) (events : List Event) (hooks : List Symbol) :
    step (ready input span (task :: tasks) events hooks) =
      some (config (some (.visit .listCell)) ({PatternSpanExecution.Execution.initial with current := some task}, none)
        input [] [] span tasks events [] hooks []) := by
  cases task <;>
    simp [step, program, lift, key, config, ready, initial,
      PatternSpanExecution.Execution.program, PatternSpanExecution.Execution.initial,
      TM2.step, TM2.stepAux] at notEmit ⊢
  all_goals funext index
  all_goals cases index with
    | none => simp [Function.update]
    | some index => cases index with
      | none => simp [Function.update]
      | some index => cases index <;> simp [Function.update]

theorem cell_cons (task : Task) (input span : List Alphabet) (tasks : List Task)
    (events : List Event) (hooks : List Symbol) :
    step (config (some (.visit .listCell)) ({PatternSpanExecution.Execution.initial with current := some task}, none)
      (4 :: input) [] [] span tasks events [] hooks []) =
      some (embedField task tasks events (4 :: span) (.fieldStart task :: hooks)
        (PrefixField.config (some .header) none input [] [] [])) := by
  simp [step, program, lift, key, config, embedField, PrefixField.config,
    PatternSpanExecution.Execution.program, PatternSpanExecution.Execution.embedField,
    PatternSpanExecution.Execution.config, PatternSpanExecution.Execution.initial,
    FiniteWordClassifier.walkState, TM2.step, TM2.stepAux]
  funext index
  cases index with
  | none => simp [Function.update]
  | some index => cases index with
    | none => simp [Function.update]
    | some index => cases index <;> simp [Function.update]

theorem field_empty (task : Task) (tasks : List Task) (events : List Event)
    (span input scratch : List Alphabet) (state : Option Alphabet)
    (cursors : FiniteWordClassifier.Residuals PatternTokenField.words) (hooks : List Symbol) :
    step (config (some (.visit (.field .complete))) (⟨state, some task, cursors, none⟩, none)
      input [] scratch span tasks events [] hooks []) =
      some (config (some (.visit (.field .checkTail))) (⟨none, some task, cursors, none⟩, none)
        input [] scratch span tasks events [] hooks []) := by
  simp [step, program, lift, key, PatternSpanExecution.Execution.program,
    PatternSpanExecution.Execution.fieldProgram, PatternSpanExecution.Execution.parserProgram,
    PatternSpanExecution.Execution.observe, PrefixField.machine_complete,
    CertificateDataTraversal.machine, StackMachineRegisters.withStack,
    config, PatternSpanExecution.Execution.parserAlphabet,
    PatternSpanExecution.Execution.parserKey, TM2.step, TM2.stepAux]

theorem field_return (state : PatternSpanExecution.Execution.Control) (input scratch span : List Alphabet)
    (tasks : List Task) (events : List Event) (hooks : List Symbol) :
    step (config (some (.visit (.field .checkTail))) (state, none) input [] scratch span tasks events [] hooks []) =
      some (config (some (.visit .clearScratch)) (state, none) input [] scratch span tasks events [] hooks []) := rfl

theorem clear_cons (state : PatternSpanExecution.Execution.Control) (head : Alphabet)
    (input scratch span : List Alphabet) (tasks : List Task) (events : List Event) (hooks : List Symbol) :
    step (config (some (.visit .clearScratch)) (state, none) input [] (head :: scratch) span tasks events [] hooks []) =
      some (config (some (.visit .clearScratch)) ({state with symbol := some head}, none)
        input [] scratch span tasks events [] hooks []) := by hook_step

theorem clear_nil (state : PatternSpanExecution.Execution.Control) (input span : List Alphabet)
    (tasks : List Task) (events : List Event) (hooks : List Symbol) :
    step (config (some (.visit .clearScratch)) (state, none) input [] [] span tasks events [] hooks []) =
      some (config (some (.visit (.dispatch (state.current.getD .pattern)
        (FiniteWordClassifier.finish PatternTokenField.words state.cursors))))
        ({state with symbol := none}, none) input [] [] span tasks events [] (.fieldEnd :: hooks) []) := by
  hook_step

noncomputable def clearRun (state : PatternSpanExecution.Execution.Control) (input scratch span : List Alphabet)
    (tasks : List Task) (events : List Event) (hooks : List Symbol) :
    EvalsToInTime step (config (some (.visit .clearScratch)) (state, none) input [] scratch span tasks events [] hooks [])
      (some (config (some (.visit (.dispatch (state.current.getD .pattern)
        (FiniteWordClassifier.finish PatternTokenField.words state.cursors))))
        ({state with symbol := none}, none) input [] [] span tasks events [] (.fieldEnd :: hooks) []))
      (scratch.length + 1) := by
  induction scratch generalizing state with
  | nil => simpa using StackMachineComposition.oneStep (clear_nil state input span tasks events hooks)
  | cons head scratch ih =>
      have first := StackMachineComposition.oneStep (clear_cons state head input scratch span tasks events hooks)
      have rest := ih {state with symbol := some head}
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EvalsToInTime.trans _ _ _ _ _ _ first rest

theorem pushTasks_apply (next : List Task)
    (statement : TM2.Stmt PatternSpanExecution.Execution.StackAlphabet
      PatternSpanExecution.Execution.Phase PatternSpanExecution.Execution.Control)
    (state : PatternSpanExecution.Execution.Control) (input span : List Alphabet)
    (tasks : List Task) (events : List Event) (hooks : List Symbol) :
    TM2.stepAux (lift false (PatternSpanExecution.Execution.pushTasks next statement)) (state, none)
      (config none (state, none) input [] [] span tasks events [] hooks []).stk =
      TM2.stepAux (lift false statement) (state, none)
        (config none (state, none) input [] [] span (next ++ tasks) events [] hooks []).stk := by
  induction next generalizing statement tasks with
  | nil => rfl
  | cons head tail ih =>
      simp only [PatternSpanExecution.Execution.pushTasks]
      rw [ih]
      simp only [lift, TM2.stepAux]
      congr 1
      funext index
      cases index with
      | none => simp [config, key, Function.update]
      | some index => cases index with
        | none => simp [config, key, Function.update]
        | some index => cases index <;> simp [config, key, Function.update]

theorem dispatch_accepted (task : Task) (tag : Option (Fin 14)) (next : List Task)
    (accepted : plan task tag = some next) (state : PatternSpanExecution.Execution.Control)
    (input span : List Alphabet) (tasks : List Task) (events : List Event) (hooks : List Symbol) :
    step (config (some (.visit (.dispatch task tag))) (state, none) input [] [] span tasks events [] hooks []) =
      some (ready input span (next ++ tasks) events hooks) := by
  simp only [step, TM2.step, config, program, PatternSpanExecution.Execution.program, accepted]
  change some (TM2.stepAux (lift false (PatternSpanExecution.Execution.pushTasks next
      (load (fun _ => PatternSpanExecution.Execution.initial) (goto fun _ => .next))))
    (state, none) (config none (state, none) input [] [] span tasks events [] hooks []).stk) = _
  rw [pushTasks_apply]
  rfl


set_option maxRecDepth 4096 in
/-- A field hook records its finite task, exact original String bytes and end
boundary, while the original visitor retains source span and unread input. -/
noncomputable def tokenRun (task : Task) (tasks next : List Task) (token : String)
    (accepted : plan task (tokenTag token) = some next)
    (tail : List String) (span : List Alphabet) (events : List Event) (hooks : List Symbol) :
    EvalsToInTime step (ready (PatternSpanExecution.Execution.tokenWire (token :: tail)) span (task :: tasks) events hooks)
      (some (ready (PatternSpanExecution.Execution.tokenWire tail)
        ((4 :: encodeWith Codec.string token).reverse ++ span) (next ++ tasks) events
        ((field task token).reverse ++ hooks)))
      (scanCost (Codec.string.put token) + (postorderWire (Codec.string.put token)).length + 6) := by
  let value := Codec.string.put token
  let bytes := encodeWith Codec.string token
  let cursors := FiniteWordClassifier.walkState PatternTokenField.words bytes
    (FiniteWordClassifier.initial PatternTokenField.words)
  let captured := (4 :: bytes).reverse ++ span
  let capturedHooks := bytes.reverse.map Symbol.byte ++ .fieldStart task :: hooks
  let state : PatternSpanExecution.Execution.Control := ⟨none, some task, cursors, none⟩
  have first := StackMachineComposition.oneStep
    (next_token task (PatternSpanExecution.Execution.accepted_not_emit task _ next accepted)
      (PatternSpanExecution.Execution.tokenWire (token :: tail)) span tasks events hooks)
  rw [PatternSpanExecution.Execution.tokenWire_cons] at first
  have cell := StackMachineComposition.oneStep
    (cell_cons task (bytes ++ PatternSpanExecution.Execution.tokenWire tail) span tasks events hooks)
  have walk := fieldRun task tasks events (4 :: span) (.fieldStart task :: hooks)
    value (PatternSpanExecution.Execution.tokenWire tail) [] [] [] none
  have walked : EvalsToInTime step
      (embedField task tasks events (4 :: span) (.fieldStart task :: hooks)
        (PrefixField.config (some .header) none (bytes ++ PatternSpanExecution.Execution.tokenWire tail) [] [] []))
      (some (config (some (.visit (.field .complete)))
        (⟨finalState value, some task, cursors, none⟩, none)
        (PatternSpanExecution.Execution.tokenWire tail) [] (postorderWire value).reverse captured
        tasks events [] capturedHooks []))
      (scanCost value) := by
    change EvalsToInTime step
      (embedField task tasks events (4 :: span) (.fieldStart task :: hooks)
        (PrefixField.config (some .header) none (writeData value (PatternSpanExecution.Execution.tokenWire tail)) [] [] []))
      (some (embedField task tasks events (4 :: span) (.fieldStart task :: hooks)
        (PrefixField.config (some .complete) (finalState value) (PatternSpanExecution.Execution.tokenWire tail) []
          ((postorderWire value).reverse ++ []) ((encodeData value).reverse ++ []))))
      (scanCost value) at walk
    rw [writeData_append, show writeData value [] = bytes from rfl,
      show encodeData value = bytes from rfl] at walk
    simpa only [embedField_config, Option.map_some, List.append_nil, List.map_append,
      List.reverse_reverse, List.reverse_cons, captured, capturedHooks,
      List.append_assoc, List.singleton_append] using walk
  have empty := StackMachineComposition.oneStep
    (field_empty task tasks events captured (PatternSpanExecution.Execution.tokenWire tail)
      (postorderWire value).reverse (finalState value) cursors capturedHooks)
  have returned := StackMachineComposition.oneStep
    (field_return state (PatternSpanExecution.Execution.tokenWire tail) (postorderWire value).reverse
      captured tasks events capturedHooks)
  have cleared := clearRun state (PatternSpanExecution.Execution.tokenWire tail)
    (postorderWire value).reverse captured tasks events capturedHooks
  have classify : FiniteWordClassifier.finish PatternTokenField.words cursors = tokenTag token :=
    PatternSpanExecution.Execution.classified_field token
  have dispatched := StackMachineComposition.oneStep
    (dispatch_accepted task (tokenTag token) next accepted state
      (PatternSpanExecution.Execution.tokenWire tail) captured tasks events (.fieldEnd :: capturedHooks))
  have clearTarget : EvalsToInTime step
      (config (some (.visit .clearScratch)) (state, none) (PatternSpanExecution.Execution.tokenWire tail)
        [] (postorderWire value).reverse captured tasks events [] capturedHooks [])
      (some (config (some (.visit (.dispatch task (tokenTag token)))) (state, none)
        (PatternSpanExecution.Execution.tokenWire tail) [] [] captured tasks events [] (.fieldEnd :: capturedHooks) []))
      ((postorderWire value).length + 1) := by
    simpa only [state, Option.getD_some, classify, List.length_reverse] using cleared
  have joined := EvalsToInTime.trans _ _ _ _ _ _ first cell
  have joined := EvalsToInTime.trans _ _ _ _ _ _ joined walked
  have joined := EvalsToInTime.trans _ _ _ _ _ _ joined empty
  have joined := EvalsToInTime.trans _ _ _ _ _ _ joined returned
  have joined := EvalsToInTime.trans _ _ _ _ _ _ joined clearTarget
  have joined := EvalsToInTime.trans _ _ _ _ _ _ joined dispatched
  have fieldEq : .fieldEnd :: capturedHooks = (field task token).reverse ++ hooks := by
    simp [field, capturedHooks, bytes, List.append_assoc]
  rw [fieldEq] at joined
  convert joined using 1
  · simp only [PatternSpanExecution.Execution.tokenWire_cons]
  · dsimp only [value]; omega


/-- Each annotated trace executes through the unchanged task discipline.
Caller work, source bytes, original events and hook order all survive. -/
theorem trace_execution {tasks : List Task} {input tail : List String} {emitted : List Symbol}
    (visited : Trace tasks input tail emitted) (pending : List Task)
    (span : List Alphabet) (before : List Event) (beforeHooks : List Symbol) :
    ∃ consumed : List String, input = consumed ++ tail ∧
      Nonempty (EvalsToInTime step
        (ready (PatternSpanExecution.Execution.tokenWire input) span (tasks ++ pending) before beforeHooks)
        (some (ready (PatternSpanExecution.Execution.tokenWire tail)
          ((PatternSpanExecution.Execution.fields consumed).reverse ++ span) pending
          ((erase emitted).reverse ++ before) (emitted.reverse ++ beforeHooks)))
        (6 * (PatternSpanExecution.Execution.fields consumed).length + (erase emitted).length)) := by
  induction visited generalizing pending span before beforeHooks with
  | done tail =>
      refine ⟨[], rfl, ?_⟩
      simpa only [PatternSpanExecution.Execution.fields, List.flatMap_nil,
        erase, List.filterMap_nil, List.reverse_nil, List.nil_append,
        List.length_nil, Nat.mul_zero, Nat.add_zero] using
        (show Nonempty (EvalsToInTime step
          (ready (PatternSpanExecution.Execution.tokenWire tail) span pending before beforeHooks)
          (some (ready (PatternSpanExecution.Execution.tokenWire tail) span pending before beforeHooks)) 0)
          from ⟨EvalsToInTime.refl _ _⟩)
  | @emit event tasks input tail emitted _ ih =>
      obtain ⟨consumed, same, ⟨rest⟩⟩ := ih pending span (event :: before) (.event event :: beforeHooks)
      have first := StackMachineComposition.oneStep
        (next_emit event (PatternSpanExecution.Execution.tokenWire input) span
          (tasks ++ pending) before beforeHooks)
      have joined := EvalsToInTime.trans _ _ _ _ _ _ first rest
      refine ⟨consumed, same, ?_⟩
      simpa only [erase_event, List.cons_append,
        List.reverse_cons, List.singleton_append, List.append_assoc, List.nil_append,
        List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (show Nonempty _ from ⟨joined⟩)
  | @token task tasks next token input tail emitted accepted _ ih =>
      obtain ⟨consumed, same, ⟨rest⟩⟩ := ih pending
        ((4 :: encodeWith Codec.string token).reverse ++ span) before
        ((field task token).reverse ++ beforeHooks)
      have first := tokenRun task (tasks ++ pending) next token accepted input span before beforeHooks
      have aligned : EvalsToInTime step
          (ready (PatternSpanExecution.Execution.tokenWire input)
            ((4 :: encodeWith Codec.string token).reverse ++ span) (next ++ (tasks ++ pending))
            before ((field task token).reverse ++ beforeHooks))
          (some (ready (PatternSpanExecution.Execution.tokenWire tail)
            ((PatternSpanExecution.Execution.fields consumed).reverse ++
              (4 :: encodeWith Codec.string token).reverse ++ span) pending
            ((erase emitted).reverse ++ before) (emitted.reverse ++ (field task token).reverse ++ beforeHooks)))
          (6 * (PatternSpanExecution.Execution.fields consumed).length + (erase emitted).length) := by
        simpa only [List.append_assoc] using rest
      have joined := EvalsToInTime.trans _ _ _ _ _ _ first aligned
      have cost := PatternSpanExecution.Execution.token_cost_le token
      have enlarged :
          (6 * (PatternSpanExecution.Execution.fields consumed).length + (erase emitted).length) +
            (scanCost (Codec.string.put token) + (postorderWire (Codec.string.put token)).length + 6) ≤
          6 * (PatternSpanExecution.Execution.fields (token :: consumed)).length + (erase emitted).length := by
        simp only [PatternSpanExecution.Execution.fields, List.flatMap_cons, List.length_append] at cost ⊢
        omega
      refine ⟨token :: consumed, by simp only [List.cons_append, same], ?_⟩
      have bounded := (show EvalsToInTime step _ _ _ from ⟨joined.toEvalsTo, joined.steps_le_m.trans enlarged⟩)
      simpa only [PatternSpanExecution.Execution.fields, List.flatMap_cons, List.reverse_append,
        erase_append, erase_field, List.nil_append, List.append_assoc, List.cons_append, List.reverse_cons] using
        (show Nonempty _ from ⟨bounded⟩)

theorem next_done (input span : List Alphabet) (events : List Event) (hooks : List Symbol) :
    step (ready input span [] events hooks) =
      some (config (some (.visit .finishSpan)) initial input [] [] span [] events [] hooks []) := by hook_step

theorem finish_span (input span : List Alphabet) (events : List Event) (hooks : List Symbol) :
    step (config (some (.visit .finishSpan)) initial input [] [] span [] events [] hooks []) =
      some (config (some (.visit .restoreSpan)) initial input [] [] span [] events [3, 2] hooks []) := by hook_step

theorem restore_cons (state : PatternSpanExecution.Execution.Control) (head : Alphabet)
    (input span receipt : List Alphabet) (events : List Event) (hooks : List Symbol) :
    step (config (some (.visit .restoreSpan)) (state, none) input [] [] (head :: span) [] events receipt hooks []) =
      some (config (some (.visit .restoreSpan)) ({state with symbol := some head}, none)
        input [] [] span [] events (head :: receipt) hooks []) := by hook_step

theorem restore_nil (state : PatternSpanExecution.Execution.Control) (input receipt : List Alphabet)
    (events : List Event) (hooks : List Symbol) :
    step (config (some (.visit .restoreSpan)) (state, none) input [] [] [] [] events receipt hooks []) =
      some (config (some .reverseHooks) initial input [] [] [] [] events receipt hooks []) := by hook_step

noncomputable def restoreRun (state : PatternSpanExecution.Execution.Control) (input span receipt : List Alphabet)
    (events : List Event) (hooks : List Symbol) :
    EvalsToInTime step
      (config (some (.visit .restoreSpan)) (state, none) input [] [] span [] events receipt hooks [])
      (some (config (some .reverseHooks) initial input [] [] [] [] events (span.reverse ++ receipt) hooks []))
      (span.length + 1) := by
  induction span generalizing state receipt with
  | nil => simpa using StackMachineComposition.oneStep (restore_nil state input receipt events hooks)
  | cons head span ih =>
      have first := StackMachineComposition.oneStep (restore_cons state head input span receipt events hooks)
      have rest := ih {state with symbol := some head} (head :: receipt)
      simpa [List.reverse_cons, List.append_assoc] using EvalsToInTime.trans _ _ _ _ _ _ first rest

theorem reverse_cons (state : Control) (head : Symbol) (hooks output : List Symbol)
    (input receipt : List Alphabet) (events : List Event) :
    step (config (some .reverseHooks) state input [] [] [] [] events receipt (head :: hooks) output) =
      some (config (some .reverseHooks) (state.1, some head) input [] [] [] [] events receipt hooks (head :: output)) := by
  hook_step

theorem reverse_nil (state : Control) (output : List Symbol) (input receipt : List Alphabet) (events : List Event) :
    step (config (some .reverseHooks) state input [] [] [] [] events receipt [] output) =
      some (config none initial input [] [] [] [] events receipt [] output) := by hook_step

noncomputable def reverseRun (state : Control) (hooks output : List Symbol)
    (input receipt : List Alphabet) (events : List Event) :
    EvalsToInTime step (config (some .reverseHooks) state input [] [] [] [] events receipt hooks output)
      (some (config none initial input [] [] [] [] events receipt [] (hooks.reverse ++ output)))
      (hooks.length + 1) := by
  induction hooks generalizing state output with
  | nil => simpa using StackMachineComposition.oneStep (reverse_nil state output input receipt events)
  | cons head hooks ih =>
      have first := StackMachineComposition.oneStep (reverse_cons state head hooks output input receipt events)
      have rest := ih (state.1, some head) (head :: output)
      simpa [List.reverse_cons, List.append_assoc] using EvalsToInTime.trans _ _ _ _ _ _ first rest

noncomputable def finishRun (input span : List Alphabet) (events : List Event) (hooks : List Symbol) :
    EvalsToInTime step (ready input span [] events hooks)
      (some (config none initial input [] [] [] [] events (span.reverse ++ [3, 2]) [] hooks.reverse))
      (span.length + hooks.length + 4) := by
  have first := StackMachineComposition.oneStep (next_done input span events hooks)
  have middle := StackMachineComposition.oneStep (finish_span input span events hooks)
  have restored := restoreRun PatternSpanExecution.Execution.initial input span [3, 2] events hooks
  have reversed := reverseRun initial hooks [] input (span.reverse ++ [3, 2]) events
  have joined := EvalsToInTime.trans _ _ _ _ _ _ first middle
  have joined := EvalsToInTime.trans _ _ _ _ _ _ joined restored
  have joined := EvalsToInTime.trans _ _ _ _ _ _ joined reversed
  simp only [List.append_nil] at joined
  exact ⟨joined.toEvalsTo, joined.steps_le_m.trans (by omega)⟩

theorem trace_complete {tasks : List Task} {input tail : List String} {hooks : List Symbol}
    (visited : Trace tasks input tail hooks) :
    ∃ consumed : List String, input = consumed ++ tail ∧
      Nonempty (EvalsToInTime step (ready (PatternSpanExecution.Execution.tokenWire input) [] tasks [] [])
        (some (config none initial (PatternSpanExecution.Execution.tokenWire tail)
          [] [] [] [] (erase hooks).reverse (PatternSpanExecution.Execution.tokenWire consumed) [] hooks))
        (7 * (PatternSpanExecution.Execution.fields consumed).length + (erase hooks).length + hooks.length + 4)) := by
  obtain ⟨consumed, same, ⟨run⟩⟩ := trace_execution visited [] [] [] []
  have final := finishRun (PatternSpanExecution.Execution.tokenWire tail)
    (PatternSpanExecution.Execution.fields consumed).reverse (erase hooks).reverse hooks.reverse
  simp only [List.append_nil] at run
  have joined := EvalsToInTime.trans _ _ _ _ _ _ run final
  have output : (PatternSpanExecution.Execution.fields consumed).reverse.reverse ++ [3, 2] =
      PatternSpanExecution.Execution.tokenWire consumed := by
    rw [List.reverse_reverse, PatternSpanExecution.Execution.tokenWire_eq]
  rw [output] at joined
  simp only [List.reverse_reverse, List.length_reverse] at joined
  refine ⟨consumed, same, ?_⟩
  exact ⟨⟨joined.toEvalsTo, joined.steps_le_m.trans (by omega)⟩⟩


theorem start_step (input : List String) :
    step (startConfig input) =
      some (ready (PatternSpanExecution.Execution.tokenWire input) [] [.pattern] [] []) := by
  unfold startConfig
  hook_step

/-- Every original pattern produces its exact annotated field trace. Original
scope events and source bytes remain independently visible and unchanged. -/
theorem pattern_execution (value : Pattern) (tail : List String) :
    ∃ hooks, Trace [.pattern] (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode value) [] hooks ∧
      erase hooks = events value ∧
      Nonempty (EvalsToInTime step
        (startConfig (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode value ++ tail))
        (some (config none initial (PatternSpanExecution.Execution.tokenWire tail)
          [] [] [] [] (events value).reverse
          (PatternSpanExecution.Execution.tokenWire (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode value)) [] hooks))
        (7 * (PatternSpanExecution.Execution.fields (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode value)).length +
          (events value).length + hooks.length + 5)) := by
  obtain ⟨hooks, traced, erased⟩ := Visits.with_trace (visits_write value [])
  have inputEq : Mettapedia.OSLF.MeTTaIL.PatternTokens.write value [] =
      Mettapedia.OSLF.MeTTaIL.PatternTokens.encode value := rfl
  rw [inputEq] at traced
  have extended := traced.append_tail tail
  simp only [List.nil_append] at extended
  obtain ⟨consumed, same, ⟨walk⟩⟩ := trace_complete extended
  have captured : consumed = Mettapedia.OSLF.MeTTaIL.PatternTokens.encode value := by
    apply List.append_cancel_right
    exact same.symm
  rw [captured, erased] at walk
  have first := StackMachineComposition.oneStep
    (start_step (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode value ++ tail))
  have joined := EvalsToInTime.trans _ _ _ _ _ _ first walk
  refine ⟨hooks, traced, erased, ?_⟩
  exact ⟨⟨joined.toEvalsTo, joined.steps_le_m.trans (by omega)⟩⟩

/-- The full hook traversal has a linear actual clock in the original byte
packet. Dynamic UTF-8 and binary fields are charged in that packet. -/
theorem pattern_execution_linear (value : Pattern) (tail : List String) :
    ∃ hooks, Trace [.pattern] (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode value) [] hooks ∧
      erase hooks = events value ∧
      Nonempty (EvalsToInTime step
        (startConfig (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode value ++ tail))
        (some (config none initial (PatternSpanExecution.Execution.tokenWire tail)
          [] [] [] [] (events value).reverse
          (PatternSpanExecution.Execution.tokenWire (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode value)) [] hooks))
        (29 * (encodeWith CertificateDataEncoding.patternCodec value).length + 7)) := by
  obtain ⟨hooks, trace, erased, ⟨run⟩⟩ := pattern_execution value tail
  have hookLength := trace.hooks_length_le
  rw [erased] at hookLength
  have eventLength := PatternSpanExecution.Execution.pattern_events_length_le value
  have tokenLength := PatternSpanExecution.Execution.fields_count_le
    (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode value)
  have fieldLength : (PatternSpanExecution.Execution.fields (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode value)).length ≤
      (encodeWith CertificateDataEncoding.patternCodec value).length := by
    rw [PatternSpanExecution.Execution.original_pattern_wire, PatternSpanExecution.Execution.tokenWire_eq,
      List.length_append]
    exact Nat.le_add_right _ _
  refine ⟨hooks, trace, erased, ?_⟩
  exact ⟨⟨run.toEvalsTo, run.steps_le_m.trans (by omega)⟩⟩

end Execution
end Hooks

end Mettapedia.GSLT.LanguageDef.PatternSpanExecution

namespace Mettapedia.GSLT.LanguageDef.PatternSpanExecution.Nesting

open Mettapedia.GSLT.LanguageDef.PatternSpanExecution
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- This is balanced event nesting, independent of the source grammar.
Fields and ordinary events remain neutral; metadata is retained as bytes. -/
inductive Closed : List Hooks.Symbol → Prop
  | nil : Closed []
  | neutral {head : Hooks.Symbol} {tail : List Hooks.Symbol}
      (notBegin : ∀ node, head ≠ .event (.begin node))
      (notFinish : head ≠ .event .finish) : Closed tail → Closed (head :: tail)
  | nested (node : Node) {body tail : List Hooks.Symbol} :
      Closed body → Closed tail → Closed (.event (.begin node) :: body ++ .event .finish :: tail)

theorem Closed.append {left right : List Hooks.Symbol} (first : Closed left)
    (second : Closed right) : Closed (left ++ right) := by
  induction first with
  | nil => exact second
  | neutral notBegin notFinish _ ih => exact .neutral notBegin notFinish ih
  | @nested node body tail bodyProof tailProof bodyIH tailIH =>
      simpa only [List.append_assoc,List.cons_append] using Closed.nested node bodyProof tailIH

theorem Closed.eventless {hooks : List Hooks.Symbol} (empty : Hooks.erase hooks = []) : Closed hooks := by
  induction hooks with
  | nil => exact .nil
  | cons head tail ih =>
      cases head with
      | fieldStart task => exact .neutral (by simp) (by simp) (ih empty)
      | byte value => exact .neutral (by simp) (by simp) (ih empty)
      | fieldEnd => exact .neutral (by simp) (by simp) (ih empty)
      | event event => simp [Hooks.erase] at empty

inductive EventClosed : List Event → Prop
  | nil : EventClosed []
  | neutral {head : Event} {tail : List Event}
      (notBegin : ∀ node, head ≠ .begin node) (notFinish : head ≠ .finish) :
      EventClosed tail → EventClosed (head::tail)
  | nested (node : Node) {body tail : List Event} :
      EventClosed body → EventClosed tail → EventClosed (.begin node :: body ++ .finish :: tail)

def boundary : Event → Bool
  | .begin _ | .finish => true
  | _ => false

theorem EventClosed.append {left right : List Event} (first : EventClosed left)
    (second : EventClosed right) : EventClosed (left ++ right) := by
  induction first with
  | nil => exact second
  | neutral notBegin notFinish _ ih => exact .neutral notBegin notFinish ih
  | @nested node body tail bodyProof tailProof bodyIH tailIH =>
      simpa only [List.append_assoc,List.cons_append] using EventClosed.nested node bodyProof tailIH

theorem EventClosed.neutrals (events : List Event)
    (ordinary : ∀ event ∈ events, boundary event = false) : EventClosed events := by
  induction events with
  | nil => exact .nil
  | cons head tail ih =>
      apply EventClosed.neutral
      · intro node equal
        have forbidden := ordinary head (by simp)
        simp [equal,boundary] at forbidden
      · intro equal
        have forbidden := ordinary head (by simp)
        simp [equal,boundary] at forbidden
      · exact ih (by intro event member; exact ordinary event (by simp [member]))

theorem EventClosed.surround (node : Node) (before after : List Event)
    {middle : List Event} (balanced : EventClosed middle)
    (beforeOrdinary : ∀ event ∈ before, boundary event = false)
    (afterOrdinary : ∀ event ∈ after, boundary event = false) :
    EventClosed (.begin node :: before ++ middle ++ after ++ [.finish]) := by
  have inside := ((EventClosed.neutrals before beforeOrdinary).append balanced).append
    (EventClosed.neutrals after afterOrdinary)
  simpa only [List.append_assoc,List.cons_append,List.append_nil] using EventClosed.nested node inside .nil

theorem numberEvents_closed (role : NumberRole) (value : Nat) :
    EventClosed (numberEvents role value) := by
  apply EventClosed.neutrals
  intro event member
  simp only [numberEvents,List.mem_append,List.mem_map,List.mem_singleton] at member
  rcases member with ⟨digit,_,rfl⟩ | rfl <;> rfl

theorem optionEvents_closed (role : OptionRole) (value : Option String) :
    EventClosed (optionEvents role value) := by
  apply EventClosed.neutrals
  intro event member
  cases value <;> simp [optionEvents] at member
  rcases member with rfl | rfl <;> rfl

theorem nameEvents_closed (names : List String) : EventClosed (nameEvents names) := by
  induction names with
  | nil => exact .nil
  | cons head tail ih =>
      exact .neutral (by decide) (by decide) (.neutral (by decide) (by decide) ih)

mutual
  theorem pattern_events_closed (pattern : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
      EventClosed (events pattern) := by
    cases pattern with
    | bvar index =>
        simpa only [events,List.append_assoc,List.cons_append,List.nil_append] using
          (numberEvents_closed .boundIndex index).surround .bound [.numberStart .boundIndex] []
            (by simp [boundary]) (by simp)
    | fvar name =>
        simpa only [events,List.append_assoc,List.cons_append,List.nil_append] using
          EventClosed.nil.surround .free [.freeVariable,.name .free] []
            (by simp [boundary]) (by simp)
    | apply name arguments =>
        simpa only [events,List.append_assoc,List.cons_append,List.nil_append] using
          (patterns_events_closed arguments).surround .application
            [.name .constructor,.argumentsStart] [.argumentsEnd]
            (by simp [boundary]) (by simp [boundary])
    | lambda name body =>
        have entering := (EventClosed.neutrals [.enterOne] (by simp [boundary])).append
          (pattern_events_closed body)
        have inside := (optionEvents_closed .lambdaBinder name).append entering
        simpa only [events,List.append_assoc,List.cons_append,List.nil_append] using
          inside.surround .lambda [] [.leave] (by simp) (by simp [boundary])
    | multiLambda arity names body =>
        have entering := (EventClosed.neutrals [.enterMany] (by simp [boundary])).append
          (pattern_events_closed body)
        have named := (nameEvents_closed names).append entering
        have inside := (numberEvents_closed .binderArity arity).append named
        simpa only [events,List.append_assoc,List.cons_append,List.nil_append] using
          inside.surround .multiLambda [.numberStart .binderArity] [.leave]
            (by simp [boundary]) (by simp [boundary])
    | subst body replacement =>
        have second := (EventClosed.neutrals [.leave] (by simp [boundary])).append
          (pattern_events_closed replacement)
        have inside := (pattern_events_closed body).append second
        simpa only [events,List.append_assoc,List.cons_append,List.nil_append] using
          inside.surround .substitution [.enterOne] [] (by simp [boundary]) (by simp)
    | collection kind elements capture =>
        have entering := (EventClosed.neutrals [.argumentsStart] (by simp [boundary])).append
          (patterns_events_closed elements)
        have inside := (optionEvents_closed .collectionCapture capture).append entering
        simpa only [events,List.append_assoc,List.cons_append,List.nil_append] using
          inside.surround .collection [kindEvent kind] [.argumentsEnd]
            (by cases kind <;> simp [kindEvent,boundary]) (by simp [boundary])
    termination_by sizeOf pattern
    decreasing_by all_goals sizeOf_pattern_dec

  theorem patterns_events_closed (patterns : List Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
      EventClosed (listEvents patterns) := by
    cases patterns with
    | nil => exact .nil
    | cons pattern patterns => exact (pattern_events_closed pattern).append (patterns_events_closed patterns)
    termination_by sizeOf patterns
    decreasing_by all_goals sizeOf_pattern_dec
end

/-- Adding original field bytes around an event trace preserves its nesting. -/
theorem Closed.of_events {events : List Event} (closed : EventClosed events)
    (hooks : List Hooks.Symbol) (same : Hooks.erase hooks = events) : Closed hooks := by
  induction closed generalizing hooks with
  | nil => exact Closed.eventless same
  | @neutral head tail notBegin notFinish _ ih =>
      obtain ⟨before,symbol,after,split,noEvents,selected,remaining⟩ :=
        List.filterMap_eq_cons_iff.mp same
      have beforeEmpty : Hooks.erase before = [] := List.filterMap_eq_nil_iff.mpr noEvents
      have selectedEq : symbol = .event head := by
        cases symbol <;> simp_all
      subst symbol
      rw [split]
      exact (Closed.eventless beforeEmpty).append
        (.neutral (by intro node; simpa using notBegin node) (by simpa using notFinish) (ih after remaining))
  | @nested node body tail _ _ bodyIH tailIH =>
      simp only [List.cons_append] at same
      obtain ⟨before,opening,after,split,noEvents,selected,remaining⟩ :=
        List.filterMap_eq_cons_iff.mp same
      have beforeEmpty : Hooks.erase before = [] := List.filterMap_eq_nil_iff.mpr noEvents
      have openingEq : opening = .event (.begin node) := by cases opening <;> simp_all
      subst opening
      obtain ⟨inside,closingPart,splitAfter,insideEvents,closingEvents⟩ :=
        List.filterMap_eq_append_iff.mp remaining
      obtain ⟨beforeClose,closing,rest,splitClose,noCloseEvents,selectedClose,restEvents⟩ :=
        List.filterMap_eq_cons_iff.mp closingEvents
      have beforeCloseEmpty : Hooks.erase beforeClose = [] := List.filterMap_eq_nil_iff.mpr noCloseEvents
      have closingEq : closing = .event .finish := by cases closing <;> simp_all
      subst closing
      rw [split,splitAfter,splitClose]
      have insideClosed := (bodyIH inside insideEvents).append (Closed.eventless beforeCloseEmpty)
      have grouped := Closed.nested node insideClosed (tailIH rest restEvents)
      simpa only [List.append_assoc,List.cons_append] using (Closed.eventless beforeEmpty).append grouped

/-- The original source visitor's complete pattern traces are balanced;
this statement also covers opaque binder and collection metadata. -/
theorem pattern_span_closed (pattern : Pattern) (hooks : List Hooks.Symbol)
    (observed : Hooks.erase hooks = events pattern) : Closed hooks :=
  Closed.of_events (pattern_events_closed pattern) hooks observed


end Mettapedia.GSLT.LanguageDef.PatternSpanExecution.Nesting
