import Mettapedia.GSLT.LanguageDef.RegexRepetitionLowering
import Mettapedia.GSLT.LanguageDef.CettaWireTerm
import Mettapedia.GSLT.LanguageDef.ModuleFormat.RegexSyntaxAuthoring
import Mettapedia.GSLT.Parsing.ParserProfileSemantics
import Mathlib.Tactic

/-!
# Attributed projection of physical regex CSTs

The input is the shared CeTTa wire carrier, with the actual `CstRuleV1`
label/span/children layout and `cp` natural payloads. The projection retains
preorder capture allocation independently of executable repetition expansion.
Flags flow left-to-right and are restored on leaving a group. The independent
attributed judgment below describes the same projection without invoking its
recursive evaluator.

This boundary begins with an explicitly selected CST. It is not a lexer,
packed-forest disambiguator, or proof that native C implements this function.
An unrecognized interpretation returns `none` without classifying its source
as malformed mathematics. Source spans remain in the caller's CST.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexSourceProjection

open RegexSelection
open CettaWire (Term)
open Mettapedia.GSLT.Parsing.ParserProfileSemantics (isUnicodeScalar)

structure Flags where
  dotall : Bool := false
  multiline : Bool := false
  reverse : Bool := false
  insensitive : Bool := false
  unicode : Bool := true
  extended : Bool := false
  deriving DecidableEq, Repr

structure State where
  flags : Flags := {}
  nextGroup : Nat := 1
  names : List (Nat × String) := []
  deriving DecidableEq, Repr

structure Output where
  pattern : Pattern
  state : State
  deriving DecidableEq, Repr

/-- The renderer preserves the exact native protocol wrapper. -/
def cst (name : String) (children : List Term := []) (start stop : Nat := 0) : Term :=
  .application "CstRuleV1" (.string name :: .natural start :: .natural stop :: children)

def fields? : Term → Option (String × List Term)
  | .application "CstRuleV1" (.string name :: .natural _ :: .natural _ :: children) => some (name, children)
  | _ => none

@[simp] theorem fields_cst (name : String) (children : List Term) (start stop : Nat) :
    fields? (cst name children start stop) = some (name, children) := rfl

def cp (value : Nat) : Term := .application "cp" [.natural value]

def scalar? (tree : Term) : Option Nat :=
  let value := match tree with
    | .application "cp" [.natural value] => some value
    | _ => do
        let (_, children) ← fields? tree
        let .application "cp" [.natural value] ← children.head? | none
        some value
  value.filter isUnicodeScalar

def escaped? (value : Nat) : Option Pattern :=
  match value with
  | 110 => some (.literal 10)
  | 114 => some (.literal 13)
  | 116 => some (.literal 9)
  | 97 => some (.literal 7)
  | 102 => some (.literal 12)
  | 118 => some (.literal 11)
  | 65 => some (.assertion "text-start")
  | 122 => some (.assertion "text-end")
  | other =>
      if (48 ≤ other ∧ other ≤ 57) ∨ (65 ≤ other ∧ other ≤ 90) ∨ (97 ≤ other ∧ other ≤ 122)
      then none else some (.literal other)

/-- Unicode decimal digits are interpreted by value. The maximal digit run
may freely combine blocks; no script-homogeneity condition is imposed. -/
def decimalDigit? (value : Nat) : Option Nat :=
  (ModuleFormat.RegexSyntaxAuthoring.decimalStarts.find?
    (fun first => decide (first ≤ value ∧ value < first + 10))).map (value - ·)

def digitsAux? : Nat → Term → Nat → Option Nat
  | 0, _, _ => none
  | fuel + 1, tree, before => do
      let (name, children) ← fields? tree
      match name, children with
      | "re-src:digits-one", [digit] => do
          let digit ← scalar? digit
          let value ← decimalDigit? digit
          some (before * 10 + value)
      | "re-src:digits-more", [digit, rest] => do
          let digit ← scalar? digit
          let value ← decimalDigit? digit
          digitsAux? fuel rest (before * 10 + value)
      | _, _ => none

def digits? (fuel : Nat) (tree : Term) : Option Nat := digitsAux? fuel tree 0

def name? : Nat → Term → Option String
  | 0, _ => none
  | fuel + 1, tree => do
      let (name, children) ← fields? tree
      match name, children with
      | "re-src:name-one", [scalar] => do
          let value ← scalar? scalar
          some (String.singleton (Char.ofNat value))
      | "re-src:name-more", [scalar, rest] => do
          let value ← scalar? scalar
          let after ← name? fuel rest
          some (String.singleton (Char.ofNat value) ++ after)
      | _, _ => none

def flag? (enable : Bool) (flags : Flags) (name : String) : Option (Bool × Flags) :=
  match name with
  | "re-src:flag-minus" => some (false, flags)
  | "re-src:flag-s" => some (enable, { flags with dotall := enable })
  | "re-src:flag-m" => some (enable, { flags with multiline := enable })
  | "re-src:flag-U" => some (enable, { flags with reverse := enable })
  | "re-src:flag-i" => some (enable, { flags with insensitive := enable })
  | "re-src:flag-u" => some (enable, { flags with unicode := enable })
  | "re-src:flag-x" => some (enable, { flags with extended := enable })
  | _ => none

def flags? : Nat → Term → Flags → Bool → Option Flags
  | 0, _, _, _ => none
  | fuel + 1, tree, flags, enable => do
      let (name, children) ← fields? tree
      match name, children with
      | "re-src:flags-one", [flag] => do
          let (name, _) ← fields? flag
          (flag? enable flags name).map Prod.snd
      | "re-src:flags-more", [flag, rest] => do
          let (name, _) ← fields? flag
          let (enable, flags) ← flag? enable flags name
          flags? fuel rest flags enable
      | _, _ => none

def splitRange (low high : Nat) : List ScalarRange :=
  if low ≤ 55295 ∧ 57344 ≤ high then [(low, 55295), (57344, high)] else [(low, high)]

/-- Recognize the exact adjacent unescaped class syntax whose set-operation
interpretation is deliberately not supplied by the interval-only profile. -/
def setOperation? (first rest : Term) : Bool := (do
  let (firstName, [firstScalar]) ← fields? first | none
  let ("re-src:class-tail", [second, _]) ← fields? rest | none
  let ("re-src:class-char", [secondScalar]) ← fields? second | none
  let a ← scalar? firstScalar
  let b ← scalar? secondScalar
  some ((firstName == "re-src:first-char" || firstName == "re-src:class-char") &&
    a == b && (a == 38 || a == 126))).getD false

def classes? : Nat → Term → Option (List ScalarRange)
  | 0, _ => none
  | fuel + 1, tree => do
      let (name, children) ← fields? tree
      match name, children with
      | "re-src:class-empty", [] | "re-src:class-tail-empty", [] => some []
      | "re-src:class-tail-dash", [] => some [(45, 45)]
      | "re-src:class-initial-dash", [rest] => ((45, 45) :: ·) <$> classes? fuel rest
      | "re-src:class-first", [first, rest] | "re-src:class-tail", [first, rest] => do
          if setOperation? first rest then none else do
          let before ← classes? fuel first
          let after ← classes? fuel rest
          some (before ++ after)
      | "re-src:first-char", [scalar] | "re-src:class-char", [scalar] => do
          let value ← scalar? scalar
          some [(value, value)]
      | "re-src:first-range", [low, high] | "re-src:class-range", [low, high] => do
          let low ← scalar? low
          let high ← scalar? high
          if low ≤ high then some (splitRange low high) else none
      | "re-src:first-escape", [scalar] | "re-src:class-escape", [scalar] => do
          let value ← scalar? scalar
          let .literal value ← escaped? value | none
          some [(value, value)]
      | _, _ => none

/-- Subtract one inclusive interval without enumerating its points. -/
def subtractRange (source cut : ScalarRange) : List ScalarRange :=
  if source.1 ≤ source.2 then
    if cut.2 < source.1 ∨ source.2 < cut.1 ∨ cut.2 < cut.1 then [source]
    else (if source.1 < cut.1 then [(source.1, cut.1 - 1)] else []) ++
      (if cut.2 < source.2 then [(cut.2 + 1, source.2)] else [])
  else []

def complementRanges (cuts : List ScalarRange) : List ScalarRange :=
  cuts.foldl (fun remaining cut => remaining.flatMap (subtractRange · cut))
    [(0, 55295), (57344, 1114111)]

def InRanges (point : Nat) (ranges : List ScalarRange) : Prop :=
  ∃ range ∈ ranges, range.1 ≤ point ∧ point ≤ range.2

theorem in_subtractRange_iff (source cut : ScalarRange) (point : Nat) :
    InRanges point (subtractRange source cut) ↔
      source.1 ≤ point ∧ point ≤ source.2 ∧ ¬ (cut.1 ≤ point ∧ point ≤ cut.2) := by
  unfold subtractRange
  split_ifs <;> simp_all [InRanges] <;> omega

theorem in_flatMap_subtract_iff (remaining : List ScalarRange) (cut : ScalarRange) (point : Nat) :
    InRanges point (remaining.flatMap (subtractRange · cut)) ↔
      InRanges point remaining ∧ ¬ (cut.1 ≤ point ∧ point ≤ cut.2) := by
  simp only [InRanges, List.mem_flatMap]
  constructor
  · rintro ⟨range, ⟨source, sourceMember, rangeMember⟩, low, high⟩
    have source := (in_subtractRange_iff source cut point).mp ⟨range, rangeMember, low, high⟩
    exact ⟨⟨_, sourceMember, source.1, source.2.1⟩, source.2.2⟩
  · rintro ⟨⟨source, sourceMember, low, high⟩, outside⟩
    obtain ⟨range, rangeMember, low, high⟩ := (in_subtractRange_iff source cut point).mpr ⟨low, high, outside⟩
    exact ⟨range, ⟨source, sourceMember, rangeMember⟩, low, high⟩

theorem in_fold_subtract_iff (cuts remaining : List ScalarRange) (point : Nat) :
    InRanges point (cuts.foldl (fun rest cut => rest.flatMap (subtractRange · cut)) remaining) ↔
      InRanges point remaining ∧ ¬ InRanges point cuts := by
  induction cuts generalizing remaining with
  | nil => simp [InRanges]
  | cons cut cuts ih =>
      rw [List.foldl_cons, ih, in_flatMap_subtract_iff]
      simp only [InRanges, List.mem_cons]
      constructor
      · rintro ⟨⟨inside, outside⟩, later⟩
        refine ⟨inside, ?_⟩
        rintro ⟨range, same | member, low, high⟩
        · subst range; exact outside ⟨low, high⟩
        · exact later ⟨range, member, low, high⟩
      · rintro ⟨inside, outside⟩
        refine ⟨⟨inside, ?_⟩, ?_⟩
        · rintro ⟨low, high⟩
          exact outside ⟨cut, Or.inl rfl, low, high⟩
        · rintro ⟨range, member, low, high⟩
          exact outside ⟨range, Or.inr member, low, high⟩

/-- Complement is in the Unicode-scalar universe, not all machine integers.
No enumeration of Unicode points appears in this interval algorithm. -/
theorem complementRanges_correct (cuts : List ScalarRange) (point : Nat) :
    InRanges point (complementRanges cuts) ↔
      isUnicodeScalar point = true ∧ ¬ InRanges point cuts := by
  rw [complementRanges, in_fold_subtract_iff]
  have scalarCarrier : InRanges point [(0, 55295), (57344, 1114111)] ↔ isUnicodeScalar point = true := by
    simp [InRanges, isUnicodeScalar]
    omega
  exact and_congr_left fun _ => scalarCarrier

theorem mem_rangeLetters_iff (range : ScalarRange) (point : Nat) :
    point ∈ rangeLetters range ↔ range.1 ≤ point ∧ point ≤ range.2 := by
  simp only [rangeLetters, List.mem_range'_1]
  omega

theorem mem_classLetters_iff (ranges : List ScalarRange) (point : Nat) :
    point ∈ classLetters ranges ↔ InRanges point ranges := by
  simp only [classLetters, List.mem_flatMap, mem_rangeLetters_iff, InRanges]

theorem complemented_class_meaning (ranges : List ScalarRange) (point : Nat) :
    point ∈ classLetters (complementRanges ranges) ↔
      isUnicodeScalar point = true ∧ point ∉ classLetters ranges := by
  simp only [mem_classLetters_iff, complementRanges_correct]

inductive Repeat where
  | optional | star | plus
  | exact (count : Nat)
  | atLeast (count : Nat)
  | bounded (low extra : Nat)
  deriving DecidableEq, Repr

def Repeat.apply (kind : Repeat) (body : Pattern) (greedy : Bool) : Pattern :=
  match kind with
  | .optional => .optional body greedy
  | .star => .star body greedy
  | .plus => .plus body greedy
  | .exact count => RepetitionLowering.exact body count
  | .atLeast count => RepetitionLowering.atLeast body count greedy
  | .bounded low extra => RepetitionLowering.bounded body low extra greedy

inductive Form where
  | leaf (pattern : Pattern)
  | pass (child : Term)
  | binary (alternate : Bool) (first second : Term)
  | group (name : Option String) (child : Term)
  | scoped (flags : Flags) (child : Term)
  | setFlags (flags : Flags)
  | repeat (kind : Repeat) (lazy : Bool) (child : Term)
  deriving Repr

def view? (fuel : Nat) (flags : Flags) (tree : Term) : Option Form := do
  let (name, children) ← fields? tree
  match name, children with
  | "re-src:empty", [] => some (.leaf .epsilon)
  | "re-src:literal", [scalar] => (fun value => Form.leaf (.literal value)) <$> scalar? scalar
  | "re-src:escape", [scalar] => do return .leaf (← escaped? (← scalar? scalar))
  | "re-src:dot", [] => some (.leaf (if flags.dotall then .any else
      .class_ [(0, 9), (11, 55295), (57344, 1114111)]))
  | "re-src:start", [] => some (.leaf (.assertion (if flags.multiline then "line-start" else "text-start")))
  | "re-src:end", [] => some (.leaf (.assertion (if flags.multiline then "line-end" else "text-end")))
  | "re-src:pattern", [child] | "re-src:atom", [child] => some (.pass child)
  | "re-src:sequence", [first, second] => some (.binary false first second)
  | "re-src:alt", [first, second] => some (.binary true first second)
  | "re-src:group", [child] => some (.group none child)
  | "re-src:capture", [child] => some (.group (some "") child)
  | "re-src:named", [name, child] | "re-src:named-python", [name, child] => do
      return .group (some (← name? fuel name)) child
  | "re-src:flags", [source] => (Form.setFlags ·) <$> flags? fuel source flags true
  | "re-src:scoped-flags", [source, child] => do return .scoped (← flags? fuel source flags true) child
  | "re-src:star", [child] => some (.repeat .star false child)
  | "re-src:star-lazy", [child] => some (.repeat .star true child)
  | "re-src:plus", [child] => some (.repeat .plus false child)
  | "re-src:plus-lazy", [child] => some (.repeat .plus true child)
  | "re-src:optional", [child] => some (.repeat .optional false child)
  | "re-src:optional-lazy", [child] => some (.repeat .optional true child)
  | "re-src:exact", [child, count] | "re-src:exact-lazy", [child, count] => do
      return .repeat (.exact (← digits? fuel count)) false child
  | "re-src:at-least", [child, count] => do return .repeat (.atLeast (← digits? fuel count)) false child
  | "re-src:at-least-lazy", [child, count] => do return .repeat (.atLeast (← digits? fuel count)) true child
  | "re-src:bounded", [child, low, high] | "re-src:bounded-lazy", [child, low, high] => do
      let low ← digits? fuel low
      let high ← digits? fuel high
      if low ≤ high then some (.repeat (.bounded low (high - low)) (name == "re-src:bounded-lazy") child)
      else none
  | "re-src:class", [source] => (fun ranges => Form.leaf (.class_ ranges)) <$> classes? fuel source
  | "re-src:class-not", [source] => do return .leaf (.class_ (complementRanges (← classes? fuel source)))
  | _, _ => none

def enterGroup (state : State) (name : Option String) : State :=
  match name with
  | none => state
  | some name => { state with nextGroup := state.nextGroup + 1, names := (state.nextGroup, name) :: state.names }

def closeGroup (before : State) (name : Option String) (child : Output) : Output :=
  ⟨match name with | none => child.pattern | some _ => .capture before.nextGroup child.pattern,
    { child.state with flags := before.flags }⟩

/-- This evaluator interprets CST forms; it does not invoke graph compilation
or use a graph execution result as the meaning of a source constructor. -/
def project (view : Flags → Term → Option Form) : Nat → State → Term → Option Output
  | 0, _, _ => none
  | fuel + 1, state, tree => do
      let form ← view state.flags tree
      match form with
      | .leaf pattern => some ⟨pattern, state⟩
      | .pass child => project view fuel state child
      | .binary alternate first second => do
          let left ← project view fuel state first
          let right ← project view fuel left.state second
          some ⟨if alternate then .alt left.pattern right.pattern else .seq left.pattern right.pattern, right.state⟩
      | .group name child => (closeGroup state name ·) <$> project view fuel (enterGroup state name) child
      | .scoped flags child => do
          let answer ← project view fuel { state with flags := flags } child
          some ⟨answer.pattern, { answer.state with flags := state.flags }⟩
      | .setFlags flags => some ⟨.epsilon, { state with flags := flags }⟩
      | .repeat kind lazy child => do
          let answer ← project view fuel state child
          some ⟨kind.apply answer.pattern (lazy == answer.state.flags.reverse), answer.state⟩

/-- An attributed source judgment. Recursive premises describe source child
meanings and state flow; they do not mention `project`. The syntactic view
retains the separately checked payload/flag/class interpretation boundary. -/
inductive Projects (view : Flags → Term → Option Form) : State → Term → Output → Prop
  | leaf {state tree pattern} : view state.flags tree = some (.leaf pattern) → Projects view state tree ⟨pattern, state⟩
  | pass {state tree child answer} : view state.flags tree = some (.pass child) →
      Projects view state child answer → Projects view state tree answer
  | binary {state tree alternate first second left right} :
      view state.flags tree = some (.binary alternate first second) →
      Projects view state first left → Projects view left.state second right →
      Projects view state tree ⟨if alternate then .alt left.pattern right.pattern else .seq left.pattern right.pattern, right.state⟩
  | group {state tree name child answer} : view state.flags tree = some (.group name child) →
      Projects view (enterGroup state name) child answer → Projects view state tree (closeGroup state name answer)
  | scoped {state tree flags child answer} : view state.flags tree = some (.scoped flags child) →
      Projects view { state with flags := flags } child answer →
      Projects view state tree ⟨answer.pattern, { answer.state with flags := state.flags }⟩
  | setFlags {state tree flags} : view state.flags tree = some (.setFlags flags) →
      Projects view state tree ⟨.epsilon, { state with flags := flags }⟩
  | repeat {state tree kind lazy child answer} : view state.flags tree = some (.repeat kind lazy child) →
      Projects view state child answer →
      Projects view state tree ⟨kind.apply answer.pattern (lazy == answer.state.flags.reverse), answer.state⟩

theorem project_sound (view : Flags → Term → Option Form) (fuel : Nat) :
    ∀ state tree answer, project view fuel state tree = some answer → Projects view state tree answer := by
  induction fuel with
  | zero => simp [project]
  | succ fuel ih =>
      intro state tree answer computed
      cases classified : view state.flags tree with
      | none => simp [project, classified] at computed
      | some form =>
          cases form with
          | leaf pattern =>
              simp [project, classified] at computed
              subst answer
              exact .leaf classified
          | setFlags flags =>
              simp [project, classified] at computed
              subst answer
              exact .setFlags classified
          | pass child =>
              simp only [project, classified] at computed
              exact .pass classified (ih state child answer computed)
          | binary alternate first second =>
              cases left : project view fuel state first with
              | none => simp [project, classified, left] at computed
              | some leftAnswer =>
                  cases right : project view fuel leftAnswer.state second with
                  | none => simp [project, classified, left, right] at computed
                  | some rightAnswer =>
                      simp [project, classified, left, right] at computed
                      subst answer
                      exact .binary classified (ih _ _ _ left) (ih _ _ _ right)
          | group name child =>
              cases inner : project view fuel (enterGroup state name) child with
              | none => simp [project, classified, inner] at computed
              | some childAnswer =>
                  simp [project, classified, inner] at computed
                  subst answer
                  exact .group classified (ih _ _ _ inner)
          | «scoped» flags child =>
              cases inner : project view fuel { state with flags := flags } child with
              | none => simp [project, classified, inner] at computed
              | some childAnswer =>
                  simp [project, classified, inner] at computed
                  subst answer
                  exact .scoped classified (ih _ _ _ inner)
          | «repeat» kind lazy child =>
              cases inner : project view fuel state child with
              | none => simp [project, classified, inner] at computed
              | some childAnswer =>
                  simp [project, classified, inner] at computed
                  subst answer
                  exact .repeat classified (ih _ _ _ inner)

/-- A finite source derivation supplies its own sufficient traversal depth.
This is not a fixed API ceiling or an assumption that projection succeeds. -/
theorem Projects.complete {view : Flags → Term → Option Form} {state : State} {tree : Term} {answer : Output}
    (derived : Projects view state tree answer) :
    ∃ bound, ∀ fuel, bound ≤ fuel → project view fuel state tree = some answer := by
  induction derived with
  | leaf classified =>
      refine ⟨1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => simp [project, classified]
  | setFlags classified =>
      refine ⟨1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => simp [project, classified]
  | pass classified _ ih =>
      obtain ⟨bound, complete⟩ := ih
      refine ⟨bound + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => simp [project, classified, complete fuel (by omega)]
  | binary classified _ _ ihLeft ihRight =>
      obtain ⟨leftBound, leftComplete⟩ := ihLeft
      obtain ⟨rightBound, rightComplete⟩ := ihRight
      refine ⟨max leftBound rightBound + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => simp [project, classified, leftComplete fuel (by omega), rightComplete fuel (by omega)]
  | group classified _ ih =>
      obtain ⟨bound, complete⟩ := ih
      refine ⟨bound + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => simp [project, classified, complete fuel (by omega)]
  | «scoped» classified _ ih =>
      obtain ⟨bound, complete⟩ := ih
      refine ⟨bound + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => simp [project, classified, complete fuel (by omega)]
  | «repeat» classified _ ih =>
      obtain ⟨bound, complete⟩ := ih
      refine ⟨bound + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => simp [project, classified, complete fuel (by omega)]

/-- Preservation and reflection for the recursive CST evaluator. The
inductive judgment authorizes source constructors and attributed state flow. -/
theorem project_iff (view : Flags → Term → Option Form) (state : State) (tree : Term) (answer : Output) :
    (∃ fuel, project view fuel state tree = some answer) ↔ Projects view state tree answer := by
  constructor
  · rintro ⟨fuel, computed⟩
    exact project_sound view fuel state tree answer computed
  · intro derived
    obtain ⟨bound, complete⟩ := derived.complete
    exact ⟨bound, complete bound le_rfl⟩

/-- Every allocated group advances the counter once, even if its execution
instructions are subsequently erased by zero repetition. -/
theorem Projects.group_accounting {view : Flags → Term → Option Form}
    {state : State} {tree : Term} {answer : Output} (derived : Projects view state tree answer) :
    state.nextGroup ≤ answer.state.nextGroup ∧
      answer.state.nextGroup + state.names.length = state.nextGroup + answer.state.names.length := by
  induction derived with
  | leaf _ => exact ⟨le_rfl, rfl⟩
  | setFlags _ => exact ⟨le_rfl, rfl⟩
  | pass _ _ ih => exact ih
  | binary _ _ _ ihLeft ihRight =>
      constructor <;> dsimp at * <;> omega
  | @group state tree name child answer _ _ ih =>
      cases name <;> simp [enterGroup, closeGroup] at ih ⊢ <;> omega
  | «scoped» _ _ ih => exact ih
  | «repeat» _ _ ih => exact ih

/-- Layout extension never discards the caller's earlier declarations. -/
theorem Projects.names_extend {view : Flags → Term → Option Form}
    {state : State} {tree : Term} {answer : Output} (derived : Projects view state tree answer) :
    ∃ added, answer.state.names = added ++ state.names := by
  induction derived with
  | leaf _ => exact ⟨[], rfl⟩
  | setFlags _ => exact ⟨[], rfl⟩
  | pass _ _ ih => exact ih
  | binary _ _ _ ihLeft ihRight =>
      obtain ⟨left, leftEqual⟩ := ihLeft
      obtain ⟨right, rightEqual⟩ := ihRight
      exact ⟨right ++ left, by simp [rightEqual, leftEqual, List.append_assoc]⟩
  | @group state tree name child answer _ _ ih =>
      obtain ⟨added, equal⟩ := ih
      cases name with
      | none => exact ⟨added, equal⟩
      | some name =>
          exact ⟨added ++ [(state.nextGroup, name)], by simpa [closeGroup, enterGroup, List.append_assoc] using equal⟩
  | «scoped» _ _ ih => exact ih
  | «repeat» _ _ ih => exact ih

namespace Controls

private def literal (value : Nat) : Term := cst "re-src:literal" [cst "re-src:lex-scalar" [cp value]]
private def flag (name : String) : Term := cst "re-src:flags-one" [cst name]
private def capture (body : Term) : Term := cst "re-src:capture" [body]
private def sequence (first second : Term) : Term := cst "re-src:sequence" [first, second]

theorem captures_are_allocated_in_preorder :
    project (view? 20) 20 {} (capture (sequence (literal 97) (capture (literal 98)))) =
      some ⟨.capture 1 (.seq (.literal 97) (.capture 2 (.literal 98))),
        ⟨{}, 3, [(2, ""), (1, "")]⟩⟩ := by decide

theorem scoped_flags_restore_but_global_flags_flow_rightward :
    project (view? 20) 20 {} (sequence
      (cst "re-src:scoped-flags" [flag "re-src:flag-s", cst "re-src:dot"])
      (cst "re-src:dot")) =
      some ⟨.seq .any (.class_ [(0, 9), (11, 55295), (57344, 1114111)]), {}⟩ ∧
    project (view? 20) 20 {} (sequence
      (cst "re-src:flags" [flag "re-src:flag-s"]) (cst "re-src:dot")) =
      some ⟨.seq .epsilon .any, ⟨{ dotall := true }, 1, []⟩⟩ := by decide

theorem zero_repeat_retains_declared_group_layout :
    project (view? 20) 20 {} (cst "re-src:exact" [capture (literal 97),
      cst "re-src:digits-one" [cst "re-src:lex-digit" [cp 48]]]) =
      some ⟨.epsilon, ⟨{}, 2, [(1, "")]⟩⟩ := by decide

theorem class_range_excludes_surrogate_interval :
    project (view? 20) 20 {} (cst "re-src:class" [cst "re-src:first-range"
      [cst "re-src:lex-class-first" [cp 55295], cst "re-src:lex-class" [cp 57344]]]) =
      some ⟨.class_ [(55295, 55295), (57344, 57344)], {}⟩ := by decide

theorem unknown_escape_and_non_scalar_are_not_invented_literals :
    project (view? 20) 20 {} (cst "re-src:escape" [cst "re-src:lex-escaped" [cp 100]]) = none ∧
      project (view? 20) 20 {} (literal 55296) = none := by decide

private def digit (value : Nat) : Term := cst "re-src:lex-digit" [cp value]

theorem mixed_unicode_decimal_counts :
    digits? 8 (cst "re-src:digits-more" [digit 1633,
      cst "re-src:digits-one" [digit 65299]]) = some 13 ∧
    digits? 8 (cst "re-src:digits-more" [digit 48,
      cst "re-src:digits-one" [digit 1635]]) = some 3 := by decide

theorem superscript_is_not_a_decimal_count :
    digits? 8 (cst "re-src:digits-one" [digit 179]) = none := by decide

theorem unicode_case_and_extended_flags_are_explicit :
    flag? true {} "re-src:flag-i" = some (true, { insensitive := true }) ∧
    flag? false {} "re-src:flag-u" = some (false, { unicode := false }) ∧
    flag? true {} "re-src:flag-x" = some (true, { extended := true }) := by decide

end Controls

end Mettapedia.GSLT.LanguageDef.RegexSourceProjection
