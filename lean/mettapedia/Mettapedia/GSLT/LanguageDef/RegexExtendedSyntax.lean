import Mettapedia.GSLT.LanguageDef.RegexTextIngress
import Mettapedia.GSLT.LanguageDef.RegexClassLexing

/-!
# Extended-mode regex lexical preparation

Flag directives are recognized lexically, before the authored regex grammar.
Their trivia is interpreted under the mode active before the directive; the
new mode takes effect only after its closing delimiter. Ordinary groups save
and restore that mode. Escape pairs and bracket contents retain their input.

Located scalar units carry original source indices throughout preparation.
Byte provenance is consequently measured in the original Unicode input, not
in a reconstructed string with trivia removed. The source rules and reference
driver below are distinct; native C conformance remains a separate claim.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexExtendedSyntax

abbrev Unit := Char × Nat

/-- Unicode 16 White_Space, the declared RegexWhitespace lexical dependency. -/
def whitespace (unit : Unit) : Bool :=
  [9,10,11,12,13,32,133,160,5760,8192,8193,8194,8195,8196,8197,8198,8199,
    8200,8201,8202,8232,8233,8239,8287,12288].contains unit.1.toNat

def otherFlag (unit : Unit) : Bool := ['i','m','s','u','U'].contains unit.1

inductive DirectiveState where
  | question
  | flags (enable any value : Bool)
  | comment (previous : DirectiveState)
  deriving DecidableEq, Repr

def DirectiveState.normal : DirectiveState → Bool
  | .comment _ => false
  | _ => true

inductive DirectiveMove where
  | more (state : DirectiveState) (retain : Bool)
  | finish (grouped value : Bool)
  deriving DecidableEq, Repr

/-- One lexical source action while recognizing a directive. A comment has
its own mode, so neither flags nor delimiters inside it can change meaning. -/
inductive DirectiveOne (current : Bool) : DirectiveState → Unit → DirectiveMove → Prop where
  | commentBody {before unit} (notEnd : unit.1 ≠ '\n') :
      DirectiveOne current (.comment before) unit (.more (.comment before) false)
  | commentEnd {before unit} (line : unit.1 = '\n') :
      DirectiveOne current (.comment before) unit (.more before false)
  | trivia {state unit} (normal : state.normal = true) (enabled : current = true)
      (space : whitespace unit = true) :
      DirectiveOne current state unit (.more state false)
  | commentStart {state unit} (normal : state.normal = true) (enabled : current = true)
      (hash : unit.1 = '#') :
      DirectiveOne current state unit (.more (.comment state) false)
  | question {unit} (mark : unit.1 = '?') :
      DirectiveOne current .question unit (.more (.flags true false current) true)
  | minus {enable any value unit} (mark : unit.1 = '-') :
      DirectiveOne current (.flags enable any value) unit (.more (.flags false true value) true)
  | extended {enable any value unit} (mark : unit.1 = 'x') :
      DirectiveOne current (.flags enable any value) unit (.more (.flags enable true enable) true)
  | other {enable any value unit} (flag : otherFlag unit = true) :
      DirectiveOne current (.flags enable any value) unit (.more (.flags enable true value) true)
  | localDirective {enable any value unit} (delimiter : unit.1 = ':') :
      DirectiveOne current (.flags enable any value) unit (.finish true value)
  | global {enable value unit} (delimiter : unit.1 = ')') :
      DirectiveOne current (.flags enable true value) unit (.finish false value)

def directiveMove (current : Bool) (state : DirectiveState) (unit : Unit) : Option DirectiveMove :=
  match state with
  | .comment before =>
      some (.more (if unit.1 = '\n' then before else .comment before) false)
  | state =>
      if current && whitespace unit then some (.more state false)
      else if current && unit.1 == '#' then some (.more (.comment state) false)
      else match state with
      | .question =>
          if unit.1 = '?' then some (.more (.flags true false current) true) else none
      | .flags enable any value =>
          if unit.1 = '-' then some (.more (.flags false true value) true)
          else if unit.1 = 'x' then some (.more (.flags enable true enable) true)
          else if otherFlag unit then some (.more (.flags enable true value) true)
          else if unit.1 = ':' then some (.finish true value)
          else if unit.1 = ')' && any then some (.finish false value)
          else none
      | .comment _ => none

theorem directiveMove_sound {current : Bool} {state : DirectiveState} {unit : Unit}
    {move : DirectiveMove} (computed : directiveMove current state unit = some move) :
    DirectiveOne current state unit move := by
  cases state with
  | comment before =>
      by_cases line : unit.1 = '\n'
      · simp [directiveMove, line] at computed
        subst move
        exact .commentEnd line
      · simp [directiveMove, line] at computed
        subst move
        exact .commentBody line
  | question =>
      unfold directiveMove at computed
      split_ifs at computed <;> simp_all only [Option.some.injEq, Bool.and_eq_true,
        beq_iff_eq]
      all_goals aesop (add safe constructors DirectiveOne)
  | flags enable any value =>
      unfold directiveMove at computed
      split_ifs at computed <;> simp_all only [Option.some.injEq, Bool.and_eq_true,
        beq_iff_eq]
      all_goals aesop (add safe constructors DirectiveOne)

theorem directiveMove_complete {current : Bool} {state : DirectiveState} {unit : Unit}
    {move : DirectiveMove} (step : DirectiveOne current state unit move) :
    directiveMove current state unit = some move := by
  cases step with
  | commentBody notEnd => simp [directiveMove, notEnd]
  | commentEnd line => simp [directiveMove, line]
  | trivia normal enabled space =>
      subst current
      cases state <;> simp_all [directiveMove, DirectiveState.normal]
  | commentStart normal enabled hash =>
      subst current
      cases unit with
      | mk char position =>
          change char = '#' at hash
          subst char
          cases state <;> simp_all [directiveMove, DirectiveState.normal, whitespace]
  | other flag =>
      cases unit with
      | mk char position =>
          simp only [otherFlag, List.contains_cons, List.contains_nil, Bool.or_false,
            Bool.or_eq_true, beq_iff_eq] at flag
          rcases flag with first | first | first | first | first <;>
            subst char <;> simp [directiveMove, whitespace, otherFlag]
  | question mark => cases unit; simp_all [directiveMove, whitespace]
  | minus mark => cases unit; simp_all [directiveMove, whitespace]
  | extended mark => cases unit; simp_all [directiveMove, whitespace]
  | localDirective delimiter => cases unit; simp_all [directiveMove, whitespace, otherFlag]
  | global delimiter => cases unit; simp_all [directiveMove, whitespace, otherFlag]

structure DirectiveResult where
  retained : List Unit
  remaining : List Unit
  grouped : Bool
  extended : Bool
  deriving DecidableEq, Repr

def prepend (keep : Bool) (unit : Unit) (result : DirectiveResult) : DirectiveResult :=
  { result with retained := if keep then unit :: result.retained else result.retained }

def readDirective (current : Bool) (state : DirectiveState) : List Unit → Option DirectiveResult
  | [] => none
  | unit :: rest => do
      match ← directiveMove current state unit with
      | .finish grouped value => some ⟨[unit], rest, grouped, value⟩
      | .more next keep => (prepend keep unit) <$> readDirective current next rest

/-- A finite directive source derivation records the original consumed
prefix, every retained scalar, and exactly the delimiter that ends it. -/
inductive ReadsDirective (current : Bool) :
    DirectiveState → List Unit → DirectiveResult → Prop where
  | finish {state unit rest grouped value}
      (step : DirectiveOne current state unit (.finish grouped value)) :
      ReadsDirective current state (unit :: rest) ⟨[unit], rest, grouped, value⟩
  | more {state unit rest next keep result}
      (step : DirectiveOne current state unit (.more next keep))
      (tail : ReadsDirective current next rest result) :
      ReadsDirective current state (unit :: rest) (prepend keep unit result)

theorem readDirective_sound (current : Bool) (input : List Unit) :
    ∀ state result, readDirective current state input = some result →
      ReadsDirective current state input result := by
  induction input with
  | nil => simp [readDirective]
  | cons unit rest ih =>
      intro state result computed
      simp only [readDirective] at computed
      cases moved : directiveMove current state unit with
      | none => simp [moved] at computed
      | some move =>
          cases move with
          | finish grouped value =>
              simp [moved] at computed
              subst result
              exact .finish (directiveMove_sound moved)
          | more next keep =>
              simp only [moved] at computed
              cases tail : readDirective current next rest with
              | none => simp [tail] at computed
              | some answer =>
                  simp [tail] at computed
                  subst result
                  exact .more (directiveMove_sound moved) (ih next answer tail)

theorem readDirective_complete {current : Bool} {state : DirectiveState}
    {input : List Unit} {result : DirectiveResult}
    (derived : ReadsDirective current state input result) :
    readDirective current state input = some result := by
  induction derived with
  | finish step => simp [readDirective, directiveMove_complete step]
  | more step tail ih => simp [readDirective, directiveMove_complete step, ih]

theorem readDirective_iff (current : Bool) (state : DirectiveState)
    (input : List Unit) (result : DirectiveResult) :
    readDirective current state input = some result ↔ ReadsDirective current state input result :=
  ⟨readDirective_sound current input state result, readDirective_complete⟩

theorem ReadsDirective.remaining_lt {current : Bool} {state : DirectiveState}
    {input : List Unit} {result : DirectiveResult}
    (derived : ReadsDirective current state input result) :
    result.remaining.length < input.length := by
  induction derived with
  | finish => simp
  | more _ _ ih => simp only [prepend]; simp only [List.length_cons]; omega

theorem ReadsDirective.provenance {current : Bool} {state : DirectiveState}
    {input : List Unit} {result : DirectiveResult}
    (derived : ReadsDirective current state input result) :
    (result.retained ++ result.remaining).Sublist input := by
  induction derived with
  | finish => exact List.Sublist.refl _
  | @more state unit rest next keep result step tail ih =>
      cases keep <;> simp only [prepend, Bool.false_eq_true, ↓reduceIte,
        List.cons_append] <;> first | exact ih.cons _ | exact ih.cons_cons _

structure State where
  extended : Bool := false
  scopes : List Bool := []
  deriving DecidableEq, Repr

def closeGroup (state : State) : State :=
  match state.scopes with
  | [] => state
  | value :: rest => { state with extended := value, scopes := rest }

def enterDirective (state : State) (result : DirectiveResult) : State :=
  { state with
    extended := result.extended
    scopes := if result.grouped then state.extended :: state.scopes else state.scopes }

def skipLine : List Unit → List Unit
  | [] => []
  | unit :: rest => if unit.1 = '\n' then unit :: rest else skipLine rest

inductive LineTail : List Unit → List Unit → Prop where
  | empty : LineTail [] []
  | endLine {unit rest} (newline : unit.1 = '\n') : LineTail (unit :: rest) (unit :: rest)
  | text {unit rest remaining} (notEnd : unit.1 ≠ '\n') (tail : LineTail rest remaining) :
      LineTail (unit :: rest) remaining

theorem skipLine_sound (input : List Unit) : LineTail input (skipLine input) := by
  induction input with
  | nil => exact .empty
  | cons unit rest ih =>
      by_cases newline : unit.1 = '\n'
      · simpa [skipLine, newline] using LineTail.endLine (rest := rest) newline
      · simpa [skipLine, newline] using LineTail.text newline ih

theorem skipLine_complete {input remaining : List Unit} (source : LineTail input remaining) :
    skipLine input = remaining := by
  induction source with
  | empty => rfl
  | endLine newline => simp [skipLine, newline]
  | text notEnd _ ih => simp [skipLine, notEnd, ih]

theorem LineTail.provenance {input remaining : List Unit} (source : LineTail input remaining) :
    remaining.Sublist input := by
  induction source with
  | empty => exact .refl _
  | endLine => exact .refl _
  | text _ _ ih => exact ih.cons _

structure Result where
  state : State
  retained : List Unit
  remaining : List Unit
  deriving DecidableEq, Repr

/-- Source lexical rules specify scope changes and what must be retained.
An ordinary opening parenthesis requires failure of the independent directive
grammar, not failure of an unspecified parser supplied by a caller. -/
inductive Step : State → List Unit → Result → Prop where
  | escaped {state unit next rest} (slash : unit.1 = '\\') :
      Step state (unit :: next :: rest) ⟨state, [unit,next], rest⟩
  | trailingEscape {state unit} (slash : unit.1 = '\\') :
      Step state [unit] ⟨state, [unit], []⟩
  | trivia {state unit rest} (enabled : state.extended = true)
      (space : whitespace unit = true) : Step state (unit :: rest) ⟨state, [], rest⟩
  | comment {state unit rest remaining}
      (enabled : state.extended = true) (hash : unit.1 = '#') (body : LineTail rest remaining) :
      Step state (unit :: rest) ⟨state, [], remaining⟩
  | openClass {state unit rest retained remaining} (bracket : unit.1 = '[')
      (region : RegexClassLexing.Region rest retained remaining) :
      Step state (unit :: rest) ⟨state, unit :: retained, remaining⟩
  | directive {state unit rest answer}
      (opening : unit.1 = '(') (source : ReadsDirective state.extended .question rest answer) :
      Step state (unit :: rest)
        ⟨enterDirective state answer, unit :: answer.retained, answer.remaining⟩
  | openGroup {state unit rest} (opening : unit.1 = '(')
      (notDirective : ¬ ∃ answer, ReadsDirective state.extended .question rest answer) :
      Step state (unit :: rest)
        ⟨{ state with scopes := state.extended :: state.scopes }, [unit], rest⟩
  | closeGroup {state unit rest} (closing : unit.1 = ')') :
      Step state (unit :: rest) ⟨closeGroup state, [unit], rest⟩
  | plain {state unit rest}
      (ordinary : unit.1 ∉ ['\\','[','(',')'])
      (notSpace : state.extended = false ∨ whitespace unit = false)
      (notComment : state.extended = false ∨ unit.1 ≠ '#') :
      Step state (unit :: rest) ⟨state, [unit], rest⟩

def next (state : State) : List Unit → Option Result
  | [] => none
  | unit :: rest =>
      if unit.1 = '\\' then
        match rest with
        | [] => some ⟨state, [unit], []⟩
        | following :: after => some ⟨state, [unit,following], after⟩
      else if state.extended && whitespace unit then some ⟨state, [], rest⟩
      else if state.extended && unit.1 == '#' then some ⟨state, [], skipLine rest⟩
      else if unit.1 = '[' then
        let region := RegexClassLexing.readRegion rest
        some ⟨state, unit :: region.1, region.2⟩
      else if unit.1 = '(' then
        match readDirective state.extended .question rest with
        | some answer => some ⟨enterDirective state answer, unit :: answer.retained, answer.remaining⟩
        | none => some ⟨{ state with scopes := state.extended :: state.scopes }, [unit], rest⟩
      else if unit.1 = ')' then some ⟨closeGroup state, [unit], rest⟩
      else some ⟨state, [unit], rest⟩

theorem next_sound (state : State) (input : List Unit) (result : Result)
    (computed : next state input = some result) : Step state input result := by
  cases input with
  | nil => simp [next] at computed
  | cons unit rest =>
      unfold next at computed
      by_cases slash : unit.1 = '\\'
      · simp only [slash, ↓reduceIte] at computed
        cases rest with
        | nil => simp at computed; subst result; exact .trailingEscape slash
        | cons following after => simp at computed; subst result; exact .escaped slash
      · simp only [slash, ↓reduceIte] at computed
        by_cases space : (state.extended && whitespace unit) = true
        · simp [space] at computed
          subst result
          apply Step.trivia <;> simp_all
        · simp only [space] at computed
          by_cases hash : (state.extended && (unit.1 == '#')) = true
          · simp [hash] at computed
            subst result
            exact .comment (Bool.and_eq_true_iff.mp hash).1
              (by simpa using (Bool.and_eq_true_iff.mp hash).2) (skipLine_sound rest)
          · simp only [hash] at computed
            by_cases bracket : unit.1 = '['
            · simp [bracket] at computed
              subst result
              exact .openClass bracket ((RegexClassLexing.readRegion_iff _ _ _).1 Prod.mk.eta.symm)
            · simp only [bracket, ↓reduceIte] at computed
              by_cases opening : unit.1 = '('
              · simp only [opening, ↓reduceIte] at computed
                cases directive : readDirective state.extended .question rest with
                | some answer =>
                    simp [directive] at computed
                    subst result
                    exact .directive opening (readDirective_sound _ _ _ _ directive)
                | none =>
                    simp [directive] at computed
                    subst result
                    have notDirective : ¬ ∃ answer, ReadsDirective state.extended .question rest answer := by
                      rintro ⟨answer, source⟩
                      have present := readDirective_complete source
                      rw [directive] at present
                      cases present
                    exact Step.openGroup opening notDirective
              · simp only [opening, ↓reduceIte] at computed
                by_cases closing : unit.1 = ')'
                · simp [closing] at computed
                  subst result
                  exact .closeGroup closing
                · simp [closing] at computed
                  subst result
                  apply Step.plain (by simp_all)
                  · cases extended : state.extended <;> simp_all
                  · cases extended : state.extended <;> simp_all

theorem Step.remaining_lt {state : State} {input : List Unit} {result : Result}
    (source : Step state input result) : result.remaining.length < input.length := by
  cases source with
  | comment _ _ body =>
      have bound := body.provenance.length_le
      simp only [List.length_cons]
      omega
  | directive _ body =>
      have bound := body.remaining_lt
      simp only [List.length_cons]
      omega
  | openClass _ region =>
      have bound := congrArg List.length region.partition
      simp only [List.length_append, List.length_cons] at *
      omega
  | _ => simp

theorem Step.provenance {state : State} {input : List Unit} {result : Result}
    (source : Step state input result) :
    (result.retained ++ result.remaining).Sublist input := by
  cases source with
  | escaped => exact .refl _
  | trailingEscape => exact .refl _
  | trivia => exact (List.Sublist.refl _).cons _
  | comment _ _ body => exact body.provenance.cons _
  | openClass _ region => simp [region.partition]
  | directive _ body => exact body.provenance.cons_cons _
  | openGroup => exact .refl _
  | closeGroup => exact .refl _
  | plain => exact .refl _

theorem whitespace_not_syntax {unit : Unit} (space : whitespace unit = true) :
    unit.1 ∉ ['\\','#','[','(',')'] := by
  rcases unit with ⟨char, position⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at *
  rintro (rfl | rfl | rfl | rfl | rfl) <;> simp [whitespace] at space

theorem next_complete {state : State} {input : List Unit} {result : Result}
    (source : Step state input result) : next state input = some result := by
  cases source with
  | escaped slash => simp [next, slash]
  | trailingEscape slash => simp [next, slash]
  | trivia enabled space =>
      have ordinary := whitespace_not_syntax space
      simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at ordinary
      simp [next, ordinary.1, enabled, space]
  | @comment unit rest remaining enabled hash body =>
      rcases unit with ⟨char, position⟩
      change char = '#' at hash
      subst char
      simp [next, enabled, whitespace, skipLine_complete body]
  | openClass bracket region =>
      simp [next, bracket, whitespace, (RegexClassLexing.readRegion_iff _ _ _).2 region]
  | directive opening source =>
      simp [next, opening, whitespace, readDirective_complete source]
  | @openGroup unit rest opening notDirective =>
      have absent : readDirective state.extended .question rest = none := by
        cases result : readDirective state.extended .question rest with
        | none => rfl
        | some answer =>
            exact False.elim (notDirective ⟨answer, readDirective_sound _ _ _ _ result⟩)
      simp [next, opening, whitespace, absent]
  | closeGroup closing => simp [next, closing, whitespace]
  | plain ordinary notSpace notComment =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at ordinary
      cases enabled : state.extended <;>
        simp_all [next]

theorem next_iff (state : State) (input : List Unit) (result : Result) :
    next state input = some result ↔ Step state input result :=
  ⟨next_sound state input result, next_complete⟩

theorem next_exists (state : State) (unit : Unit) (rest : List Unit) :
    (next state (unit :: rest)).isSome = true := by
  by_cases slash : unit.1 = '\\'
  · cases rest <;> simp [next, slash]
  · simp only [next, slash, ↓reduceIte]
    split_ifs <;> first | rfl |
      (cases readDirective state.extended .question rest <;> rfl)

structure Prepared where
  state : State
  retained : List Unit
  deriving DecidableEq, Repr

def drive : Nat → State → List Unit → Option Prepared
  | 0, _, _ => none
  | _ + 1, state, [] => some ⟨state, []⟩
  | fuel + 1, state, input@(_ :: _) => do
      let result ← next state input
      let tail ← drive fuel result.state result.remaining
      some ⟨tail.state, result.retained ++ tail.retained⟩

/-- Source execution is a chain of independently specified lexical actions.
No source constructor invokes `drive` or `next`. -/
inductive Prepares : State → List Unit → Prepared → Prop where
  | empty {state} : Prepares state [] ⟨state, []⟩
  | step {state input result answer}
      (head : Step state input result)
      (tail : Prepares result.state result.remaining answer) :
      Prepares state input ⟨answer.state, result.retained ++ answer.retained⟩

theorem drive_sound (fuel : Nat) : ∀ state input answer,
    drive fuel state input = some answer → Prepares state input answer := by
  induction fuel with
  | zero => simp [drive]
  | succ fuel ih =>
      intro state input answer computed
      cases input with
      | nil => simp [drive] at computed; subst answer; exact .empty
      | cons unit rest =>
          simp only [drive] at computed
          cases moved : next state (unit :: rest) with
          | none => simp [moved] at computed
          | some result =>
              simp only [moved] at computed
              cases completed : drive fuel result.state result.remaining with
              | none => simp [completed] at computed
              | some tail =>
                  simp [completed] at computed
                  subst answer
                  exact .step (next_sound _ _ _ moved) (ih _ _ _ completed)

theorem drive_complete {state : State} {input : List Unit} {answer : Prepared}
    (source : Prepares state input answer) :
    ∀ fuel, input.length < fuel → drive fuel state input = some answer := by
  induction source with
  | empty =>
      intro fuel enough
      cases fuel with
      | zero => simp at enough
      | succ fuel => rfl
  | @step state input result answer head tail ih =>
      intro fuel enough
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
          have smaller := head.remaining_lt
          have completed := ih fuel (by omega)
          cases input with
          | nil => cases head
          | cons unit rest => simp [drive, next_complete head, completed]

theorem Prepares.provenance {state : State} {input : List Unit} {answer : Prepared}
    (source : Prepares state input answer) : answer.retained.Sublist input := by
  induction source with
  | empty => exact .refl _
  | step head _ ih => exact ((List.Sublist.refl _).append ih).trans head.provenance

theorem preparation_exists (input : List Unit) (state : State) :
    ∃ answer, Prepares state input answer := by
  induction input using WellFounded.induction (measure List.length).wf generalizing state with
  | h input ih =>
      cases input with
      | nil => exact ⟨⟨state, []⟩, .empty⟩
      | cons unit rest =>
          cases moved : next state (unit :: rest) with
          | none =>
              have accepted := next_exists state unit rest
              simp [moved] at accepted
          | some result =>
              have source := next_sound state _ result moved
              obtain ⟨answer, tail⟩ := ih result.remaining source.remaining_lt result.state
              exact ⟨_, .step source tail⟩

theorem drive_total (input : List Unit) (state : State) :
    (drive (input.length + 1) state input).isSome = true := by
  obtain ⟨answer, source⟩ := preparation_exists input state
  rw [drive_complete source (input.length + 1) (by omega)]
  rfl

/-- The internal recursion bound is earned by strict source consumption.
There is no caller-visible cap or unfinished default preparation. -/
def prepare (state : State) (input : List Unit) : Prepared :=
  (drive (input.length + 1) state input).get (drive_total input state)

theorem prepare_exact (state : State) (input : List Unit) :
    drive (input.length + 1) state input = some (prepare state input) :=
  (Option.some_get (drive_total input state)).symm

theorem prepare_source (state : State) (input : List Unit) :
    Prepares state input (prepare state input) :=
  drive_sound _ _ _ _ (prepare_exact state input)

theorem prepare_iff (state : State) (input : List Unit) (answer : Prepared) :
    prepare state input = answer ↔ Prepares state input answer := by
  constructor
  · intro same
    rw [← same]
    exact prepare_source state input
  · intro source
    exact Option.some.inj ((prepare_exact state input).symm.trans
      (drive_complete source (input.length + 1) (by omega)))

def cleaned (answer : Prepared) : List Char := answer.retained.map Prod.fst

/-- Original positions, not cleaned-string positions, determine byte edges. -/
noncomputable def originalByteSpan (original : List Char) (unit : Unit) : Nat × Nat :=
  ((original.take unit.2).utf8Encode.size,
    (original.take (unit.2 + 1)).utf8Encode.size)

theorem retained_original_lookup (original : List Char) (state : State)
    {unit : Unit} (retained : unit ∈ (prepare state original.zipIdx).retained) :
    original[unit.2]? = some unit.1 := by
  have member := (prepare_source state original.zipIdx).provenance.subset retained
  obtain ⟨lower, upper, value⟩ := List.mem_zipIdx member
  simp only [Nat.zero_add, Nat.sub_zero] at upper value
  exact List.getElem?_eq_some_iff.mpr ⟨upper, value.symm⟩

structure BytePreparation where
  original : List Char
  prepared : Prepared
  deriving DecidableEq, Repr

def prepareBytes (bytes : ByteArray) : Except Nat BytePreparation :=
  (Mettapedia.Data.String.Utf8.decode bytes).map fun chars =>
    ⟨chars.toList, prepare {} chars.toList.zipIdx⟩

def Parsed (bytes : ByteArray) (tree : Mettapedia.GSLT.Parsing.PresentationExprSemantics.CST) : Prop :=
  ∃ prepared, prepareBytes bytes = .ok prepared ∧
    RegexTextIngress.Parsed (cleaned prepared.prepared).utf8Encode tree

/-- Independent extended-mode source meaning: exact original encoding,
source lexical execution, then the original-row regex grammar on its retained
scalars. Neither the decoder nor executable lexical driver defines this side. -/
def Source (bytes : ByteArray) (tree : Mettapedia.GSLT.Parsing.PresentationExprSemantics.CST) : Prop :=
  ∃ original : List Char, original.utf8Encode = bytes ∧
    ∃ answer, Prepares {} original.zipIdx answer ∧
      Nonempty (RegexScalarSyntax.RootDerives ((cleaned answer).map Char.toNat) tree)

theorem encoded_parsed_iff (chars : List Char)
    (tree : Mettapedia.GSLT.Parsing.PresentationExprSemantics.CST) :
    RegexTextIngress.Parsed chars.utf8Encode tree ↔
      Nonempty (RegexScalarSyntax.RootDerives (chars.map Char.toNat) tree) := by
  constructor
  · rintro ⟨input, decoded, parsed⟩
    rw [RegexTextIngress.decodeScalars_encoded] at decoded
    cases decoded
    exact RegexScalarSyntax.packed_iff_source.mp parsed
  · intro source
    exact ⟨chars.map Char.toNat, RegexTextIngress.decodeScalars_encoded chars,
      RegexScalarSyntax.packed_iff_source.mpr source⟩

/-- Full preparation/grammar preservation and reflection. A parser still
retains its cleaned-coordinate forest together with the original provenance. -/
theorem parsed_iff_source (bytes : ByteArray)
    (tree : Mettapedia.GSLT.Parsing.PresentationExprSemantics.CST) :
    Parsed bytes tree ↔ Source bytes tree := by
  constructor
  · rintro ⟨prepared, computed, parsed⟩
    unfold prepareBytes at computed
    cases decoded : Mettapedia.Data.String.Utf8.decode bytes with
    | error offset => simp [decoded, Except.map] at computed
    | ok chars =>
        simp only [decoded, Except.map, Except.ok.injEq] at computed
        subst prepared
        exact ⟨chars.toList, Mettapedia.Data.String.Utf8.encode_decoded decoded,
          prepare {} chars.toList.zipIdx, prepare_source _ _,
          (encoded_parsed_iff _ _).mp parsed⟩
  · rintro ⟨original, encoded, answer, lexed, parsed⟩
    subst bytes
    have selected := (prepare_iff {} original.zipIdx answer).mpr lexed
    refine ⟨⟨original, answer⟩, ?_, (encoded_parsed_iff _ _).mpr parsed⟩
    simp [prepareBytes, Mettapedia.Data.String.Utf8.decode_encoded, Except.map, selected]

theorem invalid_bytes_retain_their_fault {bytes : ByteArray} {offset : Nat}
    (invalid : Mettapedia.Data.String.Utf8.decode bytes = .error offset) :
    prepareBytes bytes = .error offset := by
  simp [prepareBytes, invalid, Except.map]

/-- Retain an explicit tree policy and attributed lowering after extended
lexical preparation. The resulting pattern feeds the existing authored
compiler/Pike observation theorem; no second compiler is introduced. -/
theorem selected_projection_iff
    (bytes : ByteArray) (policy : Mettapedia.GSLT.Parsing.PresentationExprSemantics.CST → Prop)
    (view : RegexSourceProjection.Flags → CettaWire.Term → Option RegexSourceProjection.Form)
    (state : RegexSourceProjection.State) (answer : RegexSourceProjection.Output) :
    (∃ tree, Parsed bytes tree ∧ policy tree ∧
      ∃ fuel, RegexSourceProjection.project view fuel state (RegexScalarSyntax.wire tree) = some answer) ↔
    ∃ tree, Source bytes tree ∧ policy tree ∧
      RegexSourceProjection.Projects view state (RegexScalarSyntax.wire tree) answer := by
  constructor
  · rintro ⟨tree, parsed, retained, computed⟩
    exact ⟨tree, (parsed_iff_source bytes tree).mp parsed, retained,
      (RegexSourceProjection.project_iff view state (RegexScalarSyntax.wire tree) answer).mp computed⟩
  · rintro ⟨tree, source, retained, projected⟩
    exact ⟨tree, (parsed_iff_source bytes tree).mpr source, retained,
      (RegexSourceProjection.project_iff view state (RegexScalarSyntax.wire tree) answer).mpr projected⟩

namespace Controls

def text (source : String) : String :=
  String.ofList (cleaned (prepare {} source.toList.zipIdx))

theorem scoped_mode_restores_the_parent :
    text "(?x:a b) c" = "(?x:ab) c" := by decide +kernel

theorem escape_pairs_and_bracket_contents_are_not_trivia :
    text "(?x)\\#\\ [ #] a # comment\nb" = "(?x)\\#\\ [ #]ab" := by decide +kernel

theorem nested_class_trivia_survives_until_the_outer_close :
    text "(?x)[[a] # ] # comment\nb" = "(?x)[[a] # ]b" := by decide +kernel

theorem literal_and_nested_empty_brackets_have_distinct_regions :
    text "(?x)[[] # comment\na" = "(?x)[[]a" ∧
    text "(?x)[[]] # comment\na" = "(?x)[[]]a" := by decide +kernel

theorem ambiguous_bracket_prefix_uses_the_longest_lexical_region :
    text "(?x)[[] # ] # comment\na" = "(?x)[[] # ]a" := by decide +kernel

theorem unclosed_class_does_not_lose_comment_shaped_text :
    text "(?x)[a # unfinished" = "(?x)[a # unfinished" := by decide +kernel

theorem unicode_trivia_is_removed_outside_literals :
    text "(?x)a\u2003b\u00a0c" = "(?x)abc" := by decide +kernel

theorem disabling_directive_uses_the_old_mode_until_its_delimiter :
    text "(?x)( ? - x : a b ) c" = "(?x)(?-x: a b )c" := by decide +kernel

theorem whitespace_is_retained_without_extended_mode :
    text "a b#c" = "a b#c" := by decide +kernel

theorem comment_text_cannot_install_flags :
    text "(?x)a#(?-x)\n b" = "(?x)ab" := by decide +kernel

theorem scoped_mode_does_not_erase_the_following_parent_space :
    text "(?x:a b) c" ≠ "(?x:ab)c" := by decide +kernel

theorem escape_does_not_install_a_directive :
    text "\\(?x)a b" = "\\(?x)a b" := by decide +kernel

end Controls

#print axioms prepare_iff
#print axioms parsed_iff_source
#print axioms retained_original_lookup
#print axioms selected_projection_iff

end Mettapedia.GSLT.LanguageDef.RegexExtendedSyntax
