import Mettapedia.GSLT.LanguageDef.RegexUnicodeProjection
import Mettapedia.GSLT.LanguageDef.RegexExtendedCompilerSemantics

/-!
# Attributed projection of context-dependent regex syntax

The physical CST view extends the existing Unicode payload interpretation.
Capture identities are allocated in written preorder before an execution
direction is chosen. Named references remain identities until the complete
declaration layout is available, so forward declarations are not lost.

The source judgment has independent recursive premises; it does not invoke
the traversal. Resolution is a subsequent boundary, not parsing or native
execution. A reverse-body interpretation is explicit and does not assert
JavaScript compatibility.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexDependentProjection

open CettaWire (Term)
open RegexSourceProjection (Flags State Repeat fields? digits? name? enterGroup cst cp)
open RegexClassMaterialization (Catalog)
open RegexDependentObservation (Comparison LookKind)

abbrev Executable := RegexExtendedCompilerSemantics.Pattern

inductive Reference where
  | number (group : Nat)
  | name (spelling : String)
  deriving DecidableEq, Repr

inductive LookbehindPolicy where
  | writtenForward | reverseConsumption
  deriving DecidableEq, Repr

def comparison (flags : Flags) : Comparison :=
  if flags.insensitive then (if flags.unicode then .unicodeFold else .asciiFold) else .exact

def behindKind (policy : LookbehindPolicy) (negative : Bool) : LookKind :=
  match policy, negative with
  | .writtenForward, false => .behind
  | .writtenForward, true => .notBehind
  | .reverseConsumption, false => .reverseBehind
  | .reverseConsumption, true => .reverseNotBehind

inductive SourcePattern where
  | regular (pattern : RegexSelection.Pattern)
  | binary (alternate : Bool) (first second : SourcePattern)
  | capture (group : Nat) (body : SourcePattern)
  | repeat (kind : Repeat) (body : SourcePattern) (greedy : Bool)
  | reference (identity : Reference) (comparison : Comparison)
  | look (kind : LookKind) (body : SourcePattern)
  deriving DecidableEq, Repr

structure Output where
  pattern : SourcePattern
  state : State
  deriving DecidableEq, Repr

inductive Form where
  | regular (pattern : RegexSelection.Pattern)
  | pass (child : Term)
  | binary (alternate : Bool) (first second : Term)
  | group (name : Option String) (child : Term)
  | scoped (flags : Flags) (child : Term)
  | setFlags (flags : Flags)
  | repeat (kind : Repeat) (lazy : Bool) (child : Term)
  | reference (identity : Reference) (comparison : Comparison)
  | look (kind : LookKind) (child : Term)
  deriving Repr

def liftForm : RegexSourceProjection.Form → Form
  | .leaf pattern => .regular pattern
  | .pass child => .pass child
  | .binary alternate first second => .binary alternate first second
  | .group name child => .group name child
  | .scoped flags child => .scoped flags child
  | .setFlags flags => .setFlags flags
  | .repeat kind lazy child => .repeat kind lazy child

def view? (catalog : Catalog) (payloadDepth : Nat) (policy : LookbehindPolicy)
    (flags : Flags) (tree : Term) : Option Form := do
  let (label, children) ← fields? tree
  match label, children with
  | "re-src:backref", [identity] =>
      return .reference (.number (← digits? payloadDepth identity)) (comparison flags)
  | "re-src:backref-name", [identity] | "re-src:backref-python", [identity] =>
      return .reference (.name (← name? payloadDepth identity)) (comparison flags)
  | "re-src:lookahead", [body] => some (.look .ahead body)
  | "re-src:not-lookahead", [body] => some (.look .notAhead body)
  | "re-src:lookbehind", [body] => some (.look (behindKind policy false) body)
  | "re-src:not-lookbehind", [body] => some (.look (behindKind policy true) body)
  | _, _ => liftForm <$> RegexUnicodeProjection.view? catalog payloadDepth flags tree

def closeGroup (before : State) (name : Option String) (answer : Output) : Output :=
  ⟨match name with
    | none => answer.pattern
    | some _ => .capture before.nextGroup answer.pattern,
    { answer.state with flags := before.flags }⟩

def closeLook (before : State) (kind : LookKind) (answer : Output) : Output :=
  ⟨.look kind answer.pattern, { answer.state with flags := before.flags }⟩

def project (view : Flags → Term → Option Form) : Nat → State → Term → Option Output
  | 0, _, _ => none
  | fuel + 1, state, tree => do
      let form ← view state.flags tree
      match form with
      | .regular pattern => some ⟨.regular pattern, state⟩
      | .reference identity mode => some ⟨.reference identity mode, state⟩
      | .pass child => project view fuel state child
      | .binary alternate first second => do
          let left ← project view fuel state first
          let right ← project view fuel left.state second
          some ⟨.binary alternate left.pattern right.pattern, right.state⟩
      | .group name child => closeGroup state name <$> project view fuel (enterGroup state name) child
      | .look kind child => closeLook state kind <$> project view fuel state child
      | .scoped flags child => do
          let answer ← project view fuel { state with flags := flags } child
          some ⟨answer.pattern, { answer.state with flags := state.flags }⟩
      | .setFlags flags => some ⟨.regular .epsilon, { state with flags := flags }⟩
      | .repeat kind lazy child => do
          let answer ← project view fuel state child
          some ⟨.repeat kind answer.pattern (lazy == answer.state.flags.reverse), answer.state⟩

inductive Projects (view : Flags → Term → Option Form) : State → Term → Output → Prop
  | regular {state tree pattern} : view state.flags tree = some (.regular pattern) →
      Projects view state tree ⟨.regular pattern, state⟩
  | reference {state tree identity mode} : view state.flags tree = some (.reference identity mode) →
      Projects view state tree ⟨.reference identity mode, state⟩
  | pass {state tree child answer} : view state.flags tree = some (.pass child) →
      Projects view state child answer → Projects view state tree answer
  | binary {state tree alternate first second left right} :
      view state.flags tree = some (.binary alternate first second) →
      Projects view state first left → Projects view left.state second right →
      Projects view state tree ⟨.binary alternate left.pattern right.pattern, right.state⟩
  | group {state tree name child answer} : view state.flags tree = some (.group name child) →
      Projects view (enterGroup state name) child answer → Projects view state tree (closeGroup state name answer)
  | look {state tree kind child answer} : view state.flags tree = some (.look kind child) →
      Projects view state child answer → Projects view state tree (closeLook state kind answer)
  | scoped {state tree flags child answer} : view state.flags tree = some (.scoped flags child) →
      Projects view { state with flags := flags } child answer →
      Projects view state tree ⟨answer.pattern, { answer.state with flags := state.flags }⟩
  | setFlags {state tree flags} : view state.flags tree = some (.setFlags flags) →
      Projects view state tree ⟨.regular .epsilon, { state with flags := flags }⟩
  | repeat {state tree kind lazy child answer} : view state.flags tree = some (.repeat kind lazy child) →
      Projects view state child answer →
      Projects view state tree ⟨.repeat kind answer.pattern (lazy == answer.state.flags.reverse), answer.state⟩

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
          | regular pattern =>
              simp [project, classified] at computed
              subst answer
              exact .regular classified
          | reference identity mode =>
              simp [project, classified] at computed
              subst answer
              exact .reference classified
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
          | look kind child =>
              cases inner : project view fuel state child with
              | none => simp [project, classified, inner] at computed
              | some childAnswer =>
                  simp [project, classified, inner] at computed
                  subst answer
                  exact .look classified (ih _ _ _ inner)
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

theorem Projects.complete {view : Flags → Term → Option Form} {state : State} {tree : Term} {answer : Output}
    (derived : Projects view state tree answer) :
    ∃ bound, ∀ fuel, bound ≤ fuel → project view fuel state tree = some answer := by
  induction derived with
  | regular classified | reference classified | setFlags classified =>
      refine ⟨1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => simp [project, classified]
  | pass classified _ ih | group classified _ ih | look classified _ ih | «scoped» classified _ ih | «repeat» classified _ ih =>
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

theorem project_iff (view : Flags → Term → Option Form) (state : State) (tree : Term) (answer : Output) :
    (∃ fuel, project view fuel state tree = some answer) ↔ Projects view state tree answer := by
  constructor
  · rintro ⟨fuel, computed⟩
    exact project_sound view fuel state tree answer computed
  · intro derived
    obtain ⟨bound, complete⟩ := derived.complete
    exact ⟨bound, complete bound le_rfl⟩

theorem Projects.group_accounting {view : Flags → Term → Option Form}
    {state : State} {tree : Term} {answer : Output} (derived : Projects view state tree answer) :
    state.nextGroup ≤ answer.state.nextGroup ∧
      answer.state.nextGroup + state.names.length = state.nextGroup + answer.state.names.length := by
  induction derived with
  | regular _ | reference _ | setFlags _ => exact ⟨le_rfl, rfl⟩
  | pass _ _ ih | look _ _ ih | «scoped» _ _ ih | «repeat» _ _ ih => exact ih
  | binary _ _ _ ihLeft ihRight => constructor <;> dsimp at * <;> omega
  | @group state tree name child answer _ _ ih =>
      cases name <;> simp [enterGroup, closeGroup] at ih ⊢ <;> omega

theorem Projects.names_extend {view : Flags → Term → Option Form}
    {state : State} {tree : Term} {answer : Output} (derived : Projects view state tree answer) :
    ∃ added, answer.state.names = added ++ state.names := by
  induction derived with
  | regular _ | reference _ | setFlags _ => exact ⟨[], rfl⟩
  | pass _ _ ih | look _ _ ih | «scoped» _ _ ih | «repeat» _ _ ih => exact ih
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

theorem Projects.look_restores_flags {view : Flags → Term → Option Form}
    {state : State} {tree child : Term} {answer : Output} {kind : LookKind}
    (derived : Projects view state tree answer)
    (classified : view state.flags tree = some (.look kind child)) :
    answer.state.flags = state.flags := by
  cases derived <;> simp_all [closeLook]

def embedRegular : RegexSelection.Pattern → Executable
  | .zero => .zero | .epsilon => .epsilon | .any => .any
  | .literal scalar => .literal scalar
  | .class_ ranges => .class_ ranges
  | .assertion name => .assertion name
  | .seq first second => .seq (embedRegular first) (embedRegular second)
  | .alt first second => .alt (embedRegular first) (embedRegular second)
  | .optional body greedy => .optional (embedRegular body) greedy
  | .star body greedy => .star (embedRegular body) greedy
  | .plus body greedy => .plus (embedRegular body) greedy
  | .capture group body => .capture group (embedRegular body)

def copies (body : Executable) : Nat → Executable → Executable
  | 0, tail => tail
  | count + 1, tail => .seq body (copies body count tail)

def options (body : Executable) : Nat → Bool → Executable
  | 0, _ => .epsilon
  | count + 1, greedy => .optional (.seq body (options body count greedy)) greedy

def applyRepeat (kind : Repeat) (body : Executable) (greedy : Bool) : Executable :=
  match kind with
  | .optional => .optional body greedy
  | .star => .star body greedy
  | .plus => .plus body greedy
  | .exact count => copies body count .epsilon
  | .atLeast 0 => .star body greedy
  | .atLeast (count + 1) => copies body count (.plus body greedy)
  | .bounded lower extra => copies body lower (options body extra greedy)

def reference? (layout : State) : Reference → Option Nat
  | .number group => if 0 < group ∧ group < layout.nextGroup then some group else none
  | .name spelling => do
      let [(group, _)] := layout.names.filter (fun declaration => declaration.2 == spelling) | none
      if 0 < group ∧ group < layout.nextGroup then some group else none

def prepareLook (kind : LookKind) (body : Executable) : Executable :=
  .look kind (match kind with
    | .reverseBehind | .reverseNotBehind => body.reverse
    | _ => body)

def resolve (layout : State) : SourcePattern → Option Executable
  | .regular pattern => some (embedRegular pattern)
  | .binary alternate first second => do
      let first ← resolve layout first
      let second ← resolve layout second
      some (if alternate then .alt first second else .seq first second)
  | .capture group body => .capture group <$> resolve layout body
  | .repeat kind body greedy => (applyRepeat kind · greedy) <$> resolve layout body
  | .reference identity mode => (.backref · mode) <$> reference? layout identity
  | .look kind body => prepareLook kind <$> resolve layout body

inductive Resolves (layout : State) : SourcePattern → Executable → Prop
  | regular (pattern) : Resolves layout (.regular pattern) (embedRegular pattern)
  | binary {alternate first second left right} : Resolves layout first left → Resolves layout second right →
      Resolves layout (.binary alternate first second) (if alternate then .alt left right else .seq left right)
  | capture {group body result} : Resolves layout body result →
      Resolves layout (.capture group body) (.capture group result)
  | repeat {kind body greedy result} : Resolves layout body result →
      Resolves layout (.repeat kind body greedy) (applyRepeat kind result greedy)
  | reference {identity mode group} : reference? layout identity = some group →
      Resolves layout (.reference identity mode) (.backref group mode)
  | look {kind body result} : Resolves layout body result →
      Resolves layout (.look kind body) (prepareLook kind result)

theorem resolve_sound (layout : State) (pattern : SourcePattern) (result : Executable)
    (computed : resolve layout pattern = some result) : Resolves layout pattern result := by
  induction pattern generalizing result with
  | regular pattern =>
      simp [resolve] at computed
      subst result
      exact .regular pattern
  | reference identity mode =>
      cases chosen : reference? layout identity with
      | none => simp [resolve, chosen] at computed
      | some group =>
          simp [resolve, chosen] at computed
          subst result
          exact .reference chosen
  | binary alternate first second ihFirst ihSecond =>
      cases left : resolve layout first with
      | none => simp [resolve, left] at computed
      | some leftAnswer =>
          cases right : resolve layout second with
          | none => simp [resolve, left, right] at computed
          | some rightAnswer =>
              simp [resolve, left, right] at computed
              subst result
              exact .binary (ihFirst _ left) (ihSecond _ right)
  | capture group body ih | «repeat» kind body greedy ih | look kind body ih =>
      cases inner : resolve layout body with
      | none => simp [resolve, inner] at computed
      | some answer =>
          simp [resolve, inner] at computed
          subst result
          first | exact .capture (ih _ inner) | exact .repeat (ih _ inner) | exact .look (ih _ inner)

theorem Resolves.complete {layout : State} {pattern : SourcePattern} {result : Executable}
    (derived : Resolves layout pattern result) : resolve layout pattern = some result := by
  induction derived <;> simp_all [resolve]

theorem resolve_iff (layout : State) (pattern : SourcePattern) (result : Executable) :
    resolve layout pattern = some result ↔ Resolves layout pattern result :=
  ⟨resolve_sound layout pattern result, Resolves.complete⟩

/-- Empty spellings denote ordinary unnamed captures, not duplicate names. -/
def LayoutNamesUnique (layout : State) : Prop :=
  ((layout.names.filter fun declaration => declaration.2 != "").map Prod.snd).Nodup

instance (layout : State) : Decidable (LayoutNamesUnique layout) := by
  unfold LayoutNamesUnique
  infer_instance

def prepare (answer : Output) : Option Executable :=
  if LayoutNamesUnique answer.state then resolve answer.state answer.pattern else none

theorem prepare_iff (answer : Output) (result : Executable) :
    prepare answer = some result ↔
      LayoutNamesUnique answer.state ∧ Resolves answer.state answer.pattern result := by
  unfold prepare
  split_ifs with unique
  · simp [unique, resolve_iff]
  · simp [unique]

theorem reference_number_declared {layout : State} {group resolved : Nat}
    (computed : reference? layout (.number group) = some resolved) :
    resolved = group ∧ 0 < group ∧ group < layout.nextGroup := by
  simp only [reference?] at computed
  split_ifs at computed with valid
  · simp only [Option.some.injEq] at computed
    exact ⟨computed.symm, valid⟩

theorem selected_resolved_iff (catalog : Catalog) (payloadDepth : Nat) (policy : LookbehindPolicy)
    (state : State) (tree : Term) (answer : Output) (result : Executable) :
    ((∃ fuel, project (view? catalog payloadDepth policy) fuel state tree = some answer) ∧
      resolve answer.state answer.pattern = some result) ↔
      (Projects (view? catalog payloadDepth policy) state tree answer ∧
        Resolves answer.state answer.pattern result) := by
  rw [project_iff, resolve_iff]

/-- Structural occurrence in the physical carrier, independent of projection
or declaration lookup. Lexical selection applies before source coordinates
are transported back through extended-mode preparation. -/
inductive Occurs : Term → Term → Prop
  | root (tree) : Occurs tree tree
  | child {wanted head children child} : child ∈ children → Occurs wanted child →
      Occurs wanted (.application head children)

def EndsDecimalRun (input : List Nat) (stop : Nat) : Prop :=
  ∀ scalar, input[stop]? = some scalar → RegexSourceProjection.decimalDigit? scalar = none

/-- This lexical policy is independent of which capture slots exist. A run
cannot be shortened merely to turn an unresolved reference into a known one. -/
def NumericReferencesMaximal (input : List Nat) (tree : Term) : Prop :=
  ∀ start stop children, Occurs (cst "re-src:backref" children start stop) tree →
    EndsDecimalRun input stop

theorem maximal_reference_cannot_split_before_digit {input : List Nat} {tree : Term}
    {start stop scalar value : Nat} {children : List Term}
    (maximal : NumericReferencesMaximal input tree)
    (occurs : Occurs (cst "re-src:backref" children start stop) tree)
    (next : input[stop]? = some scalar)
    (digit : RegexSourceProjection.decimalDigit? scalar = some value) : False := by
  have absent := maximal start stop children occurs scalar next
  rw [digit] at absent
  contradiction

namespace Controls

private def catalog : Catalog := ⟨"fixture", fun _ => none, []⟩
private def literal (value : Nat) : Term := cst "re-src:literal" [cst "re-src:lex-scalar" [cp value]]
private def name (value : Nat) : Term := cst "re-src:name-one" [cst "re-src:lex-name" [cp value]]
private def numeric (value : Nat) : Term := cst "re-src:digits-one" [cst "re-src:lex-digit" [cp value]]
private def selected := view? catalog 20 .writtenForward

theorem look_allocates_without_leaking_flags :
    project selected 20 {} (cst "re-src:lookahead" [cst "re-src:capture" [literal 97]]) =
      some ⟨.look .ahead (.capture 1 (.regular (.literal 97))), ⟨{}, 2, [(1, "")]⟩⟩ := by decide

theorem forward_named_identity_is_retained_until_layout_resolution :
    project selected 20 {} (cst "re-src:sequence"
      [cst "re-src:backref-name" [name 120], cst "re-src:named" [name 120, literal 97]]) =
      some ⟨.binary false (.reference (.name "x") .exact) (.capture 1 (.regular (.literal 97))),
        ⟨{}, 2, [(1, "x")]⟩⟩ ∧
    resolve ⟨{}, 2, [(1, "x")]⟩
      (.binary false (.reference (.name "x") .exact) (.capture 1 (.regular (.literal 97)))) =
      some (.seq (.backref 1 .exact) (.capture 1 (.literal 97))) := by decide

theorem unicode_numeric_identity_and_comparison :
    project selected 20 ⟨{ insensitive := true }, 3, []⟩ (cst "re-src:backref" [numeric 1634]) =
      some ⟨.reference (.number 2) .unicodeFold, ⟨{ insensitive := true }, 3, []⟩⟩ ∧
    reference? ⟨{}, 3, []⟩ (.number 2) = some 2 := by decide

theorem undeclared_and_ambiguous_references_remain_unresolved :
    reference? {} (.number 1) = none ∧
    reference? ⟨{}, 2, [(1, "x")]⟩ (.name "absent") = none ∧
    reference? ⟨{}, 3, [(1, "x"), (2, "x")]⟩ (.name "x") = none := by decide

theorem reverse_policy_changes_order_not_capture_identity :
    prepareLook .reverseBehind (.seq (.capture 1 (.literal 97)) (.capture 2 (.literal 98))) =
      .look .reverseBehind (.seq (.capture 2 (.literal 98)) (.capture 1 (.literal 97))) ∧
    behindKind .writtenForward false = .behind := by decide

theorem look_scopes_flags_but_keeps_written_group_order :
    project selected 20 {} (cst "re-src:sequence"
      [cst "re-src:lookbehind" [cst "re-src:sequence"
        [cst "re-src:flags" [cst "re-src:flags-one" [cst "re-src:flag-i"]],
         cst "re-src:capture" [cst "re-src:backref" [numeric 49]]]],
       cst "re-src:backref" [numeric 49]]) =
      some ⟨.binary false
        (.look .behind (.binary false (.regular .epsilon) (.capture 1 (.reference (.number 1) .unicodeFold))))
        (.reference (.number 1) .exact), ⟨{}, 2, [(1, "")]⟩⟩ := by decide

theorem duplicate_nonempty_names_cannot_be_prepared :
    prepare ⟨.regular .epsilon, ⟨{}, 3, [(1, "x"), (2, "x")]⟩⟩ = none ∧
    prepare ⟨.regular .epsilon, ⟨{}, 3, [(1, ""), (2, "")]⟩⟩ = some .epsilon := by decide

theorem zero_count_preserves_layout_and_positive_minimum_uses_plus :
    resolve ⟨{}, 2, [(1, "x")]⟩ (.repeat (.exact 0) (.capture 1 (.regular (.literal 97))) true) =
      some .epsilon ∧
    applyRepeat (.atLeast 1) (.capture 1 (.literal 97)) true = .plus (.capture 1 (.literal 97)) true := by decide

theorem maximal_decimal_identity_has_no_declared_prefix_fallback :
    digits? 8 (cst "re-src:digits-more" [cst "re-src:lex-digit" [cp 49],
      cst "re-src:digits-one" [cst "re-src:lex-digit" [cp 1634]]]) = some 12 ∧
    reference? ⟨{}, 2, [(1, "a")]⟩ (.number 12) = none ∧
    reference? ⟨{}, 2, [(1, "a")]⟩ (.number 1) = some 1 := by decide

theorem lexical_reference_end_distinguishes_nd_from_superscript :
    ¬ EndsDecimalRun [92,49,1634] 2 ∧
    EndsDecimalRun [92,49,179] 2 ∧ EndsDecimalRun [92,49] 2 := by
  simp [EndsDecimalRun, RegexSourceProjection.decimalDigit?,
    ModuleFormat.RegexSyntaxAuthoring.decimalStarts]

end Controls

end Mettapedia.GSLT.LanguageDef.RegexDependentProjection
