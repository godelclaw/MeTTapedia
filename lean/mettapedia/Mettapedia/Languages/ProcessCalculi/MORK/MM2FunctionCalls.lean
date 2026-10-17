import Mettapedia.Languages.ProcessCalculi.MORK.MM2Expressiveness
import Mettapedia.OSLF.MeTTaIL.Match

/-!
# Function calls through sinks and factors

A **call provider** maps an argument to a finite list of results, a bag.  Its semantic
identity is a MeTTaIL language: the results of a function on an argument are the normal
forms the language's rewrite rules reach from the encoded call (`languageResults`,
`languageResults_spec`).  A native implementation generated from the same language
realizes the provider; the calculus sees only its results.

The extension adds two forms to mainline MM2:

* the **call sink** `(call F A $r S₁ … Sₖ)` in an `O` output.  For every row and every
  result `b` of `F` on the row's instance of `A`, the continuation sinks run with `$r`
  bound to `b`.  They are finalized at the call sink's position, inside the caller's
  firing: the results return before any other executable is selected;
* the **call factor** `(call F A $r)` in an `I` input.  Every row is extended by every
  result, so every sink of the firing sees the result.  A product of call factors is the
  Kleisli composition of the bag monad (`callFactors_bind`).

A function name that the provider table does not register is looked up among the
equations `(= (F A) b)` of the read copy, which is the construct of the call theorems of
`MM2Expressiveness`.

Results:

* `fireCalling_base`: directives without call forms fire exactly as in mainline MM2.
* `window_closes` and `window_closes_native`: a caller and a watcher at the least
  location report `(out 7)`: the call returns within the caller's firing, whether the
  function is an equation of the space or a native provider.
* `callFactors_bind`, `bind_support` and `bind_occurrences`: two call factors compose as
  multiset bind; staged answers are its support, and occurrence-indexed providers keep
  every occurrence apart.
* `native_definition_hidden` and `equation_definition_visible`: the same call results,
  with a definition that a reflective reader cannot see (a provider) and one it can (an
  equation).  Abstraction holds exactly where definitions are not atoms.
* `forged_window_agrees`, `forged_window_caught`, `forged_reflection_agrees`: in the kernel
  model, translations inside the class `CallElimination` reproduce the reports of both call
  witnesses once their callers have a valid input, by computing the report symbols with
  `pure`.  Their syntactic conditions do not prevent forged reports; a context without the
  watcher exposes the window forger.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.FunctionCalls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Mainline
open Mettapedia.Languages.ProcessCalculi.MORK.Expressiveness

/-! ## Providers -/

/-- A call provider: the results of the function on an argument, with repeats. -/
structure CallProvider where
  results : Atom → List Atom

/-- Providers registered by function name. -/
abbrev ProviderTable := String → Option CallProvider

/-- No registered providers. -/
def emptyTable : ProviderTable := fun _ => none

/-- The results of `(F A)` among the equations of a space. -/
def equationResults (read : List Atom) (function argument : Atom) : List Atom :=
  read.filterMap fun atom =>
    match atom with
    | .expression [.symbol "=", .expression [f, a], b] =>
        if f = function ∧ a = argument then some b else none
    | _ => none

/-- Resolve a call: a registered provider, otherwise the equations of the read copy. -/
def resolveCall (table : ProviderTable) (read : List Atom) (function argument : Atom) :
    List Atom :=
  match function with
  | .symbol name =>
      match table name with
      | some provider => provider.results argument
      | none => equationResults read function argument
  | _ => equationResults read function argument

/-! ### Providers defined by MeTTaIL languages -/

/-- MeTTaIL terms. -/
abbrev ILTerm := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern

/-- MeTTaIL language definitions. -/
abbrev ILLanguage := Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef

/-- Normal forms that top-level rewriting reaches within `fuel` steps. -/
def normalForms (language : ILLanguage) : ℕ → ILTerm → List ILTerm
  | 0, _ => []
  | fuel + 1, term =>
      match Mettapedia.OSLF.MeTTaIL.Match.rewriteStep language term with
      | [] => [term]
      | next => next.flatMap (normalForms language fuel)

/-- One rewrite step of a language. -/
def RewritesTo (language : ILLanguage) (source target : ILTerm) : Prop :=
  target ∈ Mettapedia.OSLF.MeTTaIL.Match.rewriteStep language source

/-- **Every result is a reachable normal form.** -/
theorem normalForms_spec (language : ILLanguage) :
    ∀ (fuel : ℕ) (term result : ILTerm), result ∈ normalForms language fuel term →
      Mettapedia.OSLF.MeTTaIL.Match.rewriteStep language result = [] ∧
        Relation.ReflTransGen (RewritesTo language) term result
  | 0, _, _, member => by simp [normalForms] at member
  | fuel + 1, term, result, member => by
      unfold normalForms at member
      cases next : Mettapedia.OSLF.MeTTaIL.Match.rewriteStep language term with
      | nil =>
          rw [next] at member
          simp only [List.mem_singleton] at member
          subst member
          exact ⟨next, .refl⟩
      | cons first rest =>
          rw [next] at member
          obtain ⟨middle, middleMember, nested⟩ := List.mem_flatMap.mp member
          obtain ⟨normal, reach⟩ := normalForms_spec language fuel middle result nested
          refine ⟨normal, Relation.ReflTransGen.head ?_ reach⟩
          show middle ∈ Mettapedia.OSLF.MeTTaIL.Match.rewriteStep language term
          rw [next]
          exact middleMember

/-- A function defined by a MeTTaIL language, with the codec between atoms and terms that
its generated implementation uses. -/
structure LanguageFunction where
  language : ILLanguage
  encode : Atom → Option ILTerm
  decode : ILTerm → Option Atom
  fuel : ℕ

/-- The provider a language function defines. -/
def LanguageFunction.provider (function : LanguageFunction) : CallProvider where
  results argument :=
    match function.encode argument with
    | none => []
    | some term => (normalForms function.language function.fuel term).filterMap function.decode

/-- **The provider's results are decoded reachable normal forms of the encoded call.** -/
theorem languageResults_spec (function : LanguageFunction) (argument result : Atom)
    (member : result ∈ function.provider.results argument) :
    ∃ term normal, function.encode argument = some term ∧ function.decode normal = some result ∧
      Mettapedia.OSLF.MeTTaIL.Match.rewriteStep function.language normal = [] ∧
      Relation.ReflTransGen (RewritesTo function.language) term normal := by
  unfold LanguageFunction.provider at member
  simp only at member
  cases encoded : function.encode argument with
  | none => rw [encoded] at member; simp at member
  | some term =>
      rw [encoded] at member
      obtain ⟨normal, normalMember, decoded⟩ := List.mem_filterMap.mp member
      obtain ⟨irreducible, reach⟩ := normalForms_spec function.language function.fuel term normal
        normalMember
      exact ⟨term, normal, rfl, decoded, irreducible, reach⟩

/-- Every native realization that agrees with the provider's results up to order is the
same provider for the calculus: the bag of results is the observable. -/
structure ProviderRealization (provider : CallProvider) where
  run : Atom → List Atom
  realizes : ∀ argument, (run argument).Perm (provider.results argument)

/-! ## Call sinks and call factors -/

/-- A sink of the extended output: a mainline sink or a call. -/
inductive CallingSink where
  | base (sink : MainlineSink)
  /-- `(call F A $r S₁ … Sₖ)`. -/
  | call (function argument : Atom) (result : String) (continuation : List MainlineSink)
  deriving Repr, DecidableEq

/-- A factor of the extended input: a mainline factor or a call. -/
inductive CallingSource where
  | base (source : MainlineSource)
  /-- `(call F A $r)`. -/
  | call (function argument : Atom) (result : String)
  deriving Repr, DecidableEq

/-- Decode a sink of the extended language. -/
def decodeCallingSink (profile : BuildProfile) : Atom → Except MainlineFault CallingSink
  | .expression (.symbol "call" :: function :: argument :: .var result :: continuation) => do
      let sinks ← decodeAll (decodeSink profile) continuation
      pure (.call function argument result sinks)
  | form => (decodeSink profile form).map .base

/-- Decode a factor of the extended language. -/
def decodeCallingSource (profile : BuildProfile) : Atom → Except MainlineFault CallingSource
  | .expression [.symbol "call", function, argument, .var result] =>
      .ok (.call function argument result)
  | form => (decodeSource profile form).map .base

/-- The input of an extended directive. -/
inductive CallingInput where
  | compat (patterns : List Atom)
  | explicit (sources : List CallingSource)
  deriving Repr, DecidableEq

/-- The output of an extended directive. -/
inductive CallingOutput where
  | compat (templates : List Atom)
  | sinks (sinks : List CallingSink)
  deriving Repr, DecidableEq

/-- A decoded directive of the extended language. -/
structure CallingDirective where
  atom : Atom
  input : CallingInput
  output : CallingOutput
  deriving Repr, DecidableEq

def decodeCallingInput (profile : BuildProfile) :
    Atom → Option (Except MainlineFault CallingInput)
  | .expression (.symbol "," :: patterns) => some (.ok (.compat patterns))
  | .expression (.symbol "I" :: factors) =>
      some ((decodeAll (decodeCallingSource profile) factors).map .explicit)
  | _ => none

def decodeCallingOutput (profile : BuildProfile) :
    Atom → Option (Except MainlineFault CallingOutput)
  | .expression (.symbol "," :: templates) => some (.ok (.compat templates))
  | .expression (.symbol "O" :: forms) =>
      some ((decodeAll (decodeCallingSink profile) forms).map .sinks)
  | _ => none

/-- Decode a selected shell, as `decodeDirective` does. -/
def decodeCallingDirective (profile : BuildProfile) (raw : RawExecFact) :
    Except MainlineFault (Option CallingDirective) :=
  match decodeCallingInput profile raw.inputExpr,
      decodeCallingOutput profile (kernelOutput raw.loc raw.inputExpr raw.templateExpr) with
  | some input, some output => do
      let output ← output
      let input ← input
      pure (some ⟨raw.atom, input, output⟩)
  | _, _ => .ok none

/-! ### Rows -/

/-- Rows of one extended factor: a base factor's rows, or the call's results, each
unified with the result variable under the substitution of the factors before it. -/
def callingSourceRows (prims : Primitives) (table : ProviderTable) (external : ExternalState)
    (tag : ℕ → String) (index : ℕ) (θ : Subst) (read : List Atom) : CallingSource → List Subst
  | .base source => sourceRows prims external tag index θ read source
  | .call function argument result =>
      (resolveCall table read (applySubst θ function) (applySubst θ argument)).filterMap
        fun value => unifyOption θ [(.var result, value)]

/-- The product of extended factors. -/
def callingProductRows (prims : Primitives) (table : ProviderTable) (external : ExternalState)
    (tag : ℕ → String) (read : List Atom) : ℕ → Subst → List CallingSource → List Subst
  | _, θ, [] => [θ]
  | index, θ, source :: rest =>
      (callingSourceRows prims table external tag index θ read source).flatMap fun next =>
        callingProductRows prims table external tag read (index + 1) next rest

/-- A resource a base factor opens, if it is missing. -/
def callingMissingResource (external : ExternalState) : CallingSource → Option MainlineFault
  | .base source => missingResource external source
  | .call .. => none

/-- The rows of an extended input. -/
def callingRows (prims : Primitives) (table : ProviderTable) (external : ExternalState)
    (tag : ℕ → String) (read : List Atom) : CallingInput → Except MainlineFault (List Subst)
  | .compat patterns => .ok (conjunctionRows tag read 0 [] patterns)
  | .explicit sources =>
      match sources.findSome? (callingMissingResource external) with
      | some fault => .error fault
      | none => .ok (callingProductRows prims table external tag read 0 [] sources)

/-- The coverage view of an extended input: a call factor contributes the variables of
its function and argument; its result variable is introduced by the call. -/
def CallingInput.coverage : CallingInput → InputSpec
  | .compat patterns => .compat ⟨patterns⟩
  | .explicit sources => .explicit (sources.map fun source =>
      match source with
      | .base source => source.coverageFactor
      | .call function argument result =>
          .btm (.expression [function, argument, .var result]))

/-- The rows a call sink runs its continuation on. -/
def callRows (table : ProviderTable) (read : List Atom) (rows : List Subst)
    (function argument : Atom) (result : String) : List Subst :=
  rows.flatMap fun σ =>
    (resolveCall table read (applySubst σ function) (applySubst σ argument)).map
      fun value => (result, value) :: σ

/-! ### Firing -/

/-- The writes of the eager sinks of an extended output. -/
def callingEager (prims : Primitives) (input : InputSpec) (rows : List Subst)
    (space : List Atom) (sinks : List CallingSink) : List Atom :=
  sinks.foldl (fun current sink =>
    match sink with
    | .base sink => morkUnionSupport current (eagerOutputs prims input rows sink)
    | .call .. => current) space

/-- Finalize one extended sink.  A call sink finalizes its continuation, eager writes
first, on the rows the call returns. -/
def finalizeCallingSink (prims : Primitives) (table : ProviderTable) (read : List Atom)
    (input : InputSpec) (rows : List Subst) (state : List Atom × ExternalState) :
    CallingSink → Except MainlineFault (List Atom × ExternalState)
  | .base sink => finalizeMainlineSink prims input rows state sink
  | .call function argument result continuation =>
      applyMainlineSinks prims input (callRows table read rows function argument result)
        state.1 state.2 continuation

/-- Apply an extended output. -/
def applyCallingSinks (prims : Primitives) (table : ProviderTable) (read : List Atom)
    (input : InputSpec) (rows : List Subst) (space : List Atom) (external : ExternalState)
    (sinks : List CallingSink) : Except MainlineFault (List Atom × ExternalState) :=
  sinks.foldlM (finalizeCallingSink prims table read input rows)
    (callingEager prims input rows space sinks, external)

/-- **One firing of the extended language.** -/
def fireCalling (prims : Primitives) (table : ProviderTable) (external : ExternalState)
    (space : List Atom) (directive : CallingDirective) :
    Except MainlineFault (List Atom × ExternalState) := do
  let live := morkEraseSupport space directive.atom
  let read := morkInsertSupport live directive.atom
  let solved ← callingRows prims table external (factorTag directive.atom) read directive.input
  let input := directive.input.coverage
  let rows := solved.map (inputRow (inputSpecVariables input))
  match directive.output with
  | .compat templates =>
      pure (templates.foldl (fun current template =>
        morkUnionSupport current (staged input rows template)) live, external)
  | .sinks sinks => applyCallingSinks prims table read input rows live external sinks

/-- One step of the extended language. -/
def callingStep (profile : BuildProfile) (prims : Primitives) (table : ProviderTable)
    (external : ExternalState) (space : List Atom) : StepOutcome :=
  match selectNextScheduled (WQComputable.cRawExecFacts space) with
  | none => .quiescent
  | some raw =>
      match decodeCallingDirective profile raw with
      | .error fault => .aborted fault
      | .ok none => .next (morkEraseSupport space raw.atom) external
      | .ok (some directive) =>
          match fireCalling prims table external space directive with
          | .error fault => .aborted fault
          | .ok (next, after) => .next next after

/-- Runs of the extended language with exact fuel. -/
def callingRun (profile : BuildProfile) (prims : Primitives) (table : ProviderTable) :
    ℕ → ExternalState → List Atom → List Atom × ExternalState × Option MainlineFault
  | 0, external, space => (space, external, none)
  | fuel + 1, external, space =>
      match callingStep profile prims table external space with
      | .quiescent => (space, external, none)
      | .aborted fault => (space, external, some fault)
      | .next next after => callingRun profile prims table fuel after next


/-! ## Conservativity -/

/-- A mainline input as an extended input. -/
def liftInput : MainlineInput → CallingInput
  | .compat patterns => .compat patterns
  | .explicit sources => .explicit (sources.map .base)

/-- A mainline output as an extended output. -/
def liftOutput : MainlineOutput → CallingOutput
  | .compat templates => .compat templates
  | .sinks sinks => .sinks (sinks.map .base)

/-- A mainline directive as an extended directive. -/
def liftDirective (directive : MainlineDirective) : CallingDirective :=
  ⟨directive.atom, liftInput directive.input, liftOutput directive.output⟩

theorem callingProductRows_base (prims : Primitives) (table : ProviderTable)
    (external : ExternalState) (tag : ℕ → String) (read : List Atom) :
    ∀ (sources : List MainlineSource) (index : ℕ) (θ : Subst),
      callingProductRows prims table external tag read index θ (sources.map .base) =
        productRows prims external tag read index θ sources
  | [], _, _ => rfl
  | source :: rest, index, θ => by
      simp only [List.map_cons, callingProductRows, productRows, callingSourceRows]
      congr 1
      funext next
      exact callingProductRows_base prims table external tag read rest (index + 1) next

theorem findSome_base (external : ExternalState) (sources : List MainlineSource) :
    (sources.map CallingSource.base).findSome? (callingMissingResource external) =
      sources.findSome? (missingResource external) := by
  induction sources with
  | nil => rfl
  | cons source rest ih =>
      simp only [List.map_cons, List.findSome?_cons, callingMissingResource]
      cases missingResource external source with
      | none => exact ih
      | some fault => rfl

theorem callingRows_base (prims : Primitives) (table : ProviderTable) (external : ExternalState)
    (tag : ℕ → String) (read : List Atom) (input : MainlineInput) :
    callingRows prims table external tag read (liftInput input) =
      mainlineRows prims external tag read input := by
  cases input with
  | compat patterns => rfl
  | explicit sources =>
      simp only [liftInput, callingRows, mainlineRows, findSome_base]
      cases sources.findSome? (missingResource external) with
      | some fault => rfl
      | none => simp [callingProductRows_base]

theorem coverage_base (input : MainlineInput) : (liftInput input).coverage = input.coverage := by
  cases input with
  | compat patterns => rfl
  | explicit sources =>
      simp only [liftInput, CallingInput.coverage, MainlineInput.coverage,
        List.map_map]
      rfl

theorem callingEager_base (prims : Primitives) (input : InputSpec) (rows : List Subst) :
    ∀ (sinks : List MainlineSink) (space : List Atom),
      callingEager prims input rows space (sinks.map .base) =
        sinks.foldl (fun current sink => morkUnionSupport current (eagerOutputs prims input rows sink))
          space
  | [], _ => rfl
  | sink :: rest, space => by
      simp only [List.map_cons, callingEager, List.foldl_cons]
      exact callingEager_base prims input rows rest _

theorem finalizeCalling_base (prims : Primitives) (table : ProviderTable) (read : List Atom)
    (input : InputSpec) (rows : List Subst) :
    ∀ (sinks : List MainlineSink) (state : List Atom × ExternalState),
      (sinks.map CallingSink.base).foldlM (finalizeCallingSink prims table read input rows) state =
        sinks.foldlM (finalizeMainlineSink prims input rows) state
  | [], _ => rfl
  | sink :: rest, state => by
      simp only [List.map_cons, List.foldlM_cons, finalizeCallingSink]
      cases finalizeMainlineSink prims input rows state sink with
      | error fault => rfl
      | ok next =>
          simp only [bind, Except.bind]
          exact finalizeCalling_base prims table read input rows rest next

/-- **Conservativity.**  A directive without call forms fires exactly as in mainline
MM2, whatever providers are registered. -/
theorem fireCalling_base (prims : Primitives) (table : ProviderTable) (external : ExternalState)
    (space : List Atom) (directive : MainlineDirective) :
    fireCalling prims table external space (liftDirective directive) =
      fireDirective prims external space directive := by
  obtain ⟨atom, input, output⟩ := directive
  simp only [fireCalling, fireDirective, liftDirective, callingRows_base]
  cases mainlineRows prims external (factorTag atom) (morkInsertSupport (morkEraseSupport space atom) atom)
      input with
  | error fault => rfl
  | ok rows =>
      simp only [bind, Except.bind]
      cases output with
      | compat templates =>
          simp only [liftOutput, coverage_base]
      | sinks sinks =>
          simp only [liftOutput, coverage_base, applyCallingSinks,
            applyMainlineSinks, callingEager_base, finalizeCalling_base]

theorem decodeCallingSink_of_decodeSink {profile : BuildProfile} {form : Atom}
    {sink : MainlineSink} (decoded : decodeSink profile form = .ok sink) :
    decodeCallingSink profile form = .ok (.base sink) := by
  unfold decodeCallingSink
  split
  · rename_i function argument result continuation
    exfalso
    cases continuation with
    | nil =>
        simp [decodeSink, recognizeSink, aggregateOfHead?, bind, Except.bind] at decoded
    | cons first rest =>
        simp [decodeSink, recognizeSink, bind, Except.bind] at decoded
  · simp [decoded, Except.map]

theorem decodeCallingSource_of_decodeSource {profile : BuildProfile} {form : Atom}
    {source : MainlineSource} (decoded : decodeSource profile form = .ok source) :
    decodeCallingSource profile form = .ok (.base source) := by
  unfold decodeCallingSource
  split
  · simp [decodeSource, recognizeSource, bind, Except.bind] at decoded
  · simp [decoded, Except.map]

theorem decodeAll_lift {α β : Type} {decode : Atom → Except MainlineFault α}
    {lift : Atom → Except MainlineFault β} {embed : α → β}
    (agree : ∀ form value, decode form = .ok value → lift form = .ok (embed value)) :
    ∀ (forms : List Atom) (values : List α), decodeAll decode forms = .ok values →
      decodeAll lift forms = .ok (values.map embed)
  | [], values, decoded => by
      simp only [decodeAll, Except.ok.injEq] at decoded
      subst decoded
      rfl
  | form :: rest, values, decoded => by
      simp only [decodeAll, bind, Except.bind] at decoded
      cases first : decode form with
      | error fault => rw [first] at decoded; cases decoded
      | ok value =>
          rw [first] at decoded
          cases others : decodeAll decode rest with
          | error fault => rw [others] at decoded; cases decoded
          | ok tail =>
              rw [others] at decoded
              simp only [pure, Except.pure, Except.ok.injEq] at decoded
              subst decoded
              simp [decodeAll, agree form value first,
                decodeAll_lift agree rest tail others, bind, Except.bind, pure, Except.pure]

theorem decodeCallingInput_lift (profile : BuildProfile) (form : Atom) (input : MainlineInput)
    (decoded : decodeInput profile form = some (.ok input)) :
    decodeCallingInput profile form = some (.ok (liftInput input)) := by
  unfold decodeInput at decoded
  split at decoded
  · simp only [Option.some.injEq, Except.ok.injEq] at decoded
    subst decoded
    rfl
  · rename_i factors
    simp only [Option.some.injEq] at decoded
    cases sources : decodeAll (decodeSource profile) factors with
    | error fault => simp [sources, Except.map] at decoded
    | ok values =>
        simp only [sources, Except.map, Except.ok.injEq] at decoded
        subst decoded
        simp [decodeCallingInput, decodeAll_lift (fun form value decoded =>
          decodeCallingSource_of_decodeSource decoded) factors values sources, Except.map, liftInput]
  · cases decoded

theorem decodeCallingOutput_lift (profile : BuildProfile) (form : Atom) (output : MainlineOutput)
    (decoded : decodeOutput profile form = some (.ok output)) :
    decodeCallingOutput profile form = some (.ok (liftOutput output)) := by
  unfold decodeOutput at decoded
  split at decoded
  · simp only [Option.some.injEq, Except.ok.injEq] at decoded
    subst decoded
    rfl
  · rename_i forms
    simp only [Option.some.injEq] at decoded
    cases sinks : decodeAll (decodeSink profile) forms with
    | error fault => simp [sinks, Except.map] at decoded
    | ok values =>
        simp only [sinks, Except.map, Except.ok.injEq] at decoded
        subst decoded
        simp [decodeCallingOutput, decodeAll_lift (fun form value decoded =>
          decodeCallingSink_of_decodeSink decoded) forms values sinks, Except.map, liftOutput]
  · cases decoded

/-- A shell that decodes in mainline MM2 decodes in the extension to the same directive. -/
theorem decodeCallingDirective_of_decodeDirective {profile : BuildProfile} {raw : RawExecFact}
    {directive : MainlineDirective} (decoded : decodeDirective profile raw = .ok (some directive)) :
    decodeCallingDirective profile raw = .ok (some (liftDirective directive)) := by
  unfold decodeDirective at decoded
  unfold decodeCallingDirective
  cases inputDecoded : decodeInput profile raw.inputExpr with
  | none => simp [inputDecoded] at decoded
  | some inputResult =>
      cases outputDecoded : decodeOutput profile (kernelOutput raw.loc raw.inputExpr raw.templateExpr) with
      | none => simp [inputDecoded, outputDecoded] at decoded
      | some outputResult =>
          simp only [inputDecoded, outputDecoded, bind, Except.bind] at decoded
          cases outputResult with
          | error fault => cases decoded
          | ok output =>
              cases inputResult with
              | error fault => cases decoded
              | ok input =>
                  simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at decoded
                  subst decoded
                  simp [decodeCallingInput_lift profile _ input inputDecoded,
                    decodeCallingOutput_lift profile _ output outputDecoded, bind, Except.bind,
                    pure, Except.pure, liftDirective]

/-- **Step-level conservativity.**  When the selected directive decodes in mainline MM2,
the extended language takes the same step. -/
theorem callingStep_eq_mainline (profile : BuildProfile) (prims : Primitives)
    (table : ProviderTable) (external : ExternalState) (space : List Atom) (raw : RawExecFact)
    (directive : MainlineDirective)
    (selected : selectNextScheduled (WQComputable.cRawExecFacts space) = some raw)
    (decoded : decodeDirective profile raw = .ok (some directive)) :
    (callingStep profile prims table external space).space? =
      (mainlineStep profile prims external space).space? := by
  simp only [callingStep, mainlineStep, selected, decoded,
    decodeCallingDirective_of_decodeDirective decoded, fireCalling_base]
  cases fireDirective prims external space directive with
  | error fault => rfl
  | ok result => rfl


/-! ## Witness programs -/

/-- The value `7`. -/
def seven : Atom := .symbol "7"

/-- `(exec () (,) (O (call f a $r (+ (g $r)))))`: the window caller with the empty
conjunction, which the kernel fires (unlike the empty expression `()`). -/
def commaCaller : Atom :=
  .expression [.symbol "exec", .expression [], .expression [.symbol ","],
    .expression [.symbol "O", callAtom]]

/-- `(exec (z) (,) (O (call f a $r (+ (g $r)))))`: the reflection caller with the empty
conjunction. -/
def commaCallerZ : Atom :=
  .expression [.symbol "exec", locZ, .expression [.symbol ","], .expression [.symbol "O", callAtom]]

/-- The report atoms `(out X)` of a space. -/
def reports (space : List Atom) : List Atom :=
  space.filter fun atom =>
    match atom with
    | .expression [.symbol "out", _] => true
    | _ => false

/-- `f` as a native provider with `f a = 7`. -/
def nativeF : ProviderTable := fun name =>
  if name = "f" then
    some ⟨fun argument => if argument = .symbol "a" then [seven] else []⟩
  else none

/-- A sketch of the `pure` registry functions used below: a symbol evaluates to itself,
`tuple` builds an expression from its evaluated arguments, and `reverse_symbol` reverses
a symbol. -/
def sketchEval : Atom → Option Atom
  | .symbol name => some (.symbol name)
  | .expression (.symbol "tuple" :: arguments) => (sketchEvalList arguments).map .expression
  | .expression (.symbol "reverse_symbol" :: arguments) =>
      match sketchEvalList arguments with
      | some [.symbol name] => some (.symbol (String.ofList name.toList.reverse))
      | _ => none
  | _ => none
where
  sketchEvalList : List Atom → Option (List Atom)
    | [] => some []
    | first :: rest =>
        match sketchEval first, sketchEvalList rest with
        | some value, some values => some (value :: values)
        | _, _ => none

/-- Primitives whose registry is `sketchEval`. -/
def sketchPrimitives : Primitives := { inertPrimitives with eval := sketchEval }

/-- `(exec (zz) (, (= (f a) $v)) (O (pure $o $o (tuple (reverse_symbol tuo) $v))))`: look
the call up after the watcher and write `(out VALUE)`, computing the symbol `out`. -/
def forgedLookup : Atom :=
  .expression [.symbol "exec", .expression [.symbol "zz"],
    .expression [.symbol ",", .expression [.symbol "=",
      .expression [.symbol "f", .symbol "a"], .var "v"]],
    .expression [.symbol "O", .expression [.symbol "pure", .var "o", .var "o",
      .expression [.symbol "tuple", .expression [.symbol "reverse_symbol", .symbol "tuo"],
        .var "v"]]]]

/-- `(+ forgedLookup)`. -/
def forgedWindowSink : Atom := .expression [.symbol "+", forgedLookup]

/-- `(pure $o $o (tuple (reverse_symbol tuo) (reverse_symbol llac)))`: write `(out call)`,
computing both symbols. -/
def forgedReport : Atom :=
  .expression [.symbol "pure", .var "o", .var "o",
    .expression [.symbol "tuple", .expression [.symbol "reverse_symbol", .symbol "tuo"],
      .expression [.symbol "reverse_symbol", .symbol "llac"]]]

/-- `(exec () (, (= (f $x) $y)) (O (+ (saw $x $y))))`: read the definition of `f`. -/
def equationReader : Atom :=
  .expression [.symbol "exec", .expression [],
    .expression [.symbol ",", .expression [.symbol "=",
      .expression [.symbol "f", .var "x"], .var "y"]],
    .expression [.symbol "O", .expression [.symbol "+",
      .expression [.symbol "saw", .var "x", .var "y"]]]]


/-! ## Calls return within the firing -/

/-- **The caller's own firing writes the call's result**: after one step the watcher is
next and `(g 7)` is already present; no auxiliary executable was scheduled. -/
theorem call_returns_within_firing :
    (callingStep defaultProfile inertPrimitives emptyTable ExternalState.empty
        [commaCaller, watcherExec, equationOf seven]).space? =
      some [watcherExec, equationOf seven, .expression [.symbol "g", seven]] := by
  decide +kernel

/-- **The window closes**: a call to an equation of the space reports `(out 7)`. -/
theorem window_closes :
    reports (callingRun defaultProfile inertPrimitives emptyTable 4 ExternalState.empty
      [commaCaller, watcherExec, equationOf seven]).1 = [outOf seven] := by
  decide +kernel

/-- The same with `f` a native provider and no equation in the space. -/
theorem window_closes_native :
    reports (callingRun defaultProfile inertPrimitives nativeF 4 ExternalState.empty
      [commaCaller, watcherExec]).1 = [outOf seven] := by
  decide +kernel

/-! ## Reflection is gated by where a definition lives -/

/-- **An equation is visible**: the reader sees the definition of `f`. -/
theorem equation_definition_visible :
    (callingRun defaultProfile inertPrimitives emptyTable 6 ExternalState.empty
        [equationReader, commaCaller, watcherExec, equationOf seven]).1 =
      [equationOf seven, .expression [.symbol "g", seven], outOf seven,
        .expression [.symbol "saw", .symbol "a", seven]] := by
  decide +kernel

/-- **A provider is hidden**: the same call results, and the reader sees nothing. -/
theorem native_definition_hidden :
    (callingRun defaultProfile inertPrimitives nativeF 6 ExternalState.empty
        [equationReader, commaCaller, watcherExec]).1 =
      [.expression [.symbol "g", seven], outOf seven] := by
  decide +kernel

/-! ## Answers compose as the bag monad -/

theorem applySubst_symbol (σ : Subst) (name : String) : applySubst σ (.symbol name) = .symbol name := rfl

theorem applySubst_bound_var (name : String) (value : Atom) :
    applySubst [(name, value)] (.var name) = value := by
  simp [applySubst, Subst.lookup]

/-- A `filterMap` whose function returns `some` on every member is a `map`. -/
theorem filterMap_eq_map_of_some {α β : Type} (f : α → Option β) (g : α → β) :
    ∀ (items : List α), (∀ item ∈ items, f item = some (g item)) → items.filterMap f = items.map g
  | [], _ => rfl
  | item :: rest, always => by
      rw [List.filterMap_cons, always item (by simp)]
      simp only [List.map_cons]
      exact congrArg _ (filterMap_eq_map_of_some f g rest fun other member =>
        always other (List.mem_cons_of_mem _ member))

/-- **Two call factors compose as bind.**  When the argument and every result are ground,
the rows of `(I (call f A $r) (call g $r $s))` are the results of `g` on each result of
`f`, in order, repeats included. -/
theorem callFactors_bind (prims : Primitives) (table : ProviderTable) (external : ExternalState)
    (tag : ℕ → String) (read : List Atom) (first second : String) (argument : Atom)
    (groundArgument : isGroundAtom argument = true) (result answer : String) (distinct : answer ≠ result)
    (groundFirst : ∀ value ∈ resolveCall table read (.symbol first) argument, isGroundAtom value = true)
    (groundSecond : ∀ value ∈ resolveCall table read (.symbol first) argument,
      ∀ next ∈ resolveCall table read (.symbol second) value, isGroundAtom next = true) :
    callingProductRows prims table external tag read 0 []
        [.call (.symbol first) argument result, .call (.symbol second) (.var result) answer] =
      (resolveCall table read (.symbol first) argument).flatMap fun value =>
        (resolveCall table read (.symbol second) value).map fun next =>
          [(answer, next), (result, value)] := by
  simp only [callingProductRows, callingSourceRows, applySubst_symbol,
    applySubst_of_ground [] argument groundArgument]
  rw [filterMap_eq_map_of_some _ (fun value => [(result, value)])
    (resolveCall table read (.symbol first) argument)
    (fun value member => by
      rw [unifyOption_var_ground [] result value (by simp [Subst.lookup]) (groundFirst value member)]
      simp [bindSolved])]
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro value member
  have looked : applySubst [(result, value)] (.var result) = value := applySubst_bound_var result value
  rw [looked, List.flatMap_singleton']
  rw [filterMap_eq_map_of_some _ (fun next => [(answer, next), (result, value)])
    (resolveCall table read (.symbol second) value)
    (fun next nextMember => by
      rw [unifyOption_var_ground [(result, value)] answer next
        (by simp [Subst.lookup, Ne.symm distinct]) (groundSecond value member next nextMember)]
      simp [bindSolved, applySubst_of_ground _ value (groundFirst value member)])]

/-- **The answer bag is MeTTa Zero's bind**: reading the answer variable off the rows
gives `Multiset.bind` of the two providers' bags. -/
theorem callFactors_answers (prims : Primitives) (table : ProviderTable) (external : ExternalState)
    (tag : ℕ → String) (read : List Atom) (first second : String) (argument : Atom)
    (groundArgument : isGroundAtom argument = true) (result answer : String) (distinct : answer ≠ result)
    (groundFirst : ∀ value ∈ resolveCall table read (.symbol first) argument, isGroundAtom value = true)
    (groundSecond : ∀ value ∈ resolveCall table read (.symbol first) argument,
      ∀ next ∈ resolveCall table read (.symbol second) value, isGroundAtom next = true) :
    ((callingProductRows prims table external tag read 0 []
        [.call (.symbol first) argument result, .call (.symbol second) (.var result) answer]).filterMap
          (fun row => Subst.lookup row answer) : Multiset Atom) =
      (resolveCall table read (.symbol first) argument : Multiset Atom).bind fun value =>
        (resolveCall table read (.symbol second) value : Multiset Atom) := by
  rw [callFactors_bind prims table external tag read first second argument groundArgument result
    answer distinct groundFirst groundSecond]
  rw [Multiset.coe_bind]
  congr 1
  induction (resolveCall table read (.symbol first) argument) with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.flatMap_cons, List.filterMap_append, ih]
      congr 1
      induction (resolveCall table read (.symbol second) head) with
      | nil => rfl
      | cons next rest restIh => simp [Subst.lookup]

/-- `(exec 0 (I (call f a $r) (call g $r $s)) (O (+ (ans $s))))`. -/
def bindExec : Atom :=
  .expression [.symbol "exec", .grounded (.int 0),
    .expression [.symbol "I",
      .expression [.symbol "call", .symbol "f", .symbol "a", .var "r"],
      .expression [.symbol "call", .symbol "g", .var "r", .var "s"]],
    .expression [.symbol "O", .expression [.symbol "+", .expression [.symbol "ans", .var "s"]]]]

/-- `f a = {x, x}` and `g` the identity. -/
def repeatTable : ProviderTable := fun name =>
  if name = "f" then some ⟨fun _ => [.symbol "x", .symbol "x"]⟩
  else if name = "g" then some ⟨fun value => [value]⟩ else none

/-- `f a = {(1 x), (2 x)}`: the same payload under two occurrence indices. -/
def indexedTable : ProviderTable := fun name =>
  if name = "f" then
    some ⟨fun _ => [.expression [.symbol "1", .symbol "x"], .expression [.symbol "2", .symbol "x"]]⟩
  else if name = "g" then some ⟨fun value => [value]⟩ else none

/-- **The staged store keeps the support of the bag, and occurrence indices keep the bag.**
Two occurrences of the answer `x` are written once; the same answers under distinct indices
are written twice. -/
theorem answers_support_and_occurrences :
    (callingStep defaultProfile inertPrimitives repeatTable ExternalState.empty [bindExec]).space? =
        some [.expression [.symbol "ans", .symbol "x"]] ∧
      (callingStep defaultProfile inertPrimitives indexedTable ExternalState.empty [bindExec]).space? =
        some [.expression [.symbol "ans", .expression [.symbol "1", .symbol "x"]],
          .expression [.symbol "ans", .expression [.symbol "2", .symbol "x"]]] := by
  decide +kernel

/-! ## The call witnesses in the kernel model

Every translation below lies in the class `CallElimination`: it keeps every atom without
`call`, replaces the single call sink of a caller by an expansion that mentions neither
`call` nor `out`, and is a union homomorphism.  With the callers' input made valid, both
witnesses report the same in the extension and in the kernel model: the expansion
computes the report symbols with `pure`. -/

/-- Replace the single call sink of a caller by `expansion`. -/
def forgeAtom (expansion : Atom) (a : Atom) : Atom :=
  match a with
  | .expression [.symbol "exec", loc, input, .expression [.symbol "O", call]] =>
      if occursB (.symbol "call") call = true ∧ occursB (.symbol "call") loc = false ∧
          occursB (.symbol "call") input = false then
        .expression [.symbol "exec", loc, input, .expression [.symbol "O", expansion]]
      else .expression [.symbol "exec", loc, input, .expression [.symbol "O", call]]
  | other => other

/-- **Every expansion that avoids `call` and `out` syntactically is a member of
`CallElimination`.** -/
def forgeCalls (expansion : Atom) (plain : ¬ Occurs (.symbol "call") expansion)
    (quiet : ¬ Occurs (.symbol "out") expansion) : CallElimination where
  map space := space.image (forgeAtom expansion)
  expand _ := [expansion]
  map_union first second := Finset.image_union first second
  map_plain a free := by
    rw [Finset.image_singleton]
    congr 1
    unfold forgeAtom
    split
    · rename_i loc input call
      rw [if_neg]
      rintro ⟨inCall, -, -⟩
      exact free (occurs_exec_sink ((occursB_iff _ _).mp inCall))
    · rfl
  map_exec loc input call inCall freeLoc freeInput := by
    rw [Finset.image_singleton]
    congr 1
    simp only [forgeAtom]
    rw [if_pos ⟨(occursB_iff _ _).mpr inCall, occursB_false freeLoc, occursB_false freeInput⟩]
  expand_plain _ _ sink member := by
    simp only [List.mem_singleton] at member
    subst member
    exact plain
  expand_quiet _ _ sink member outIn := by
    simp only [List.mem_singleton] at member
    subst member
    exact absurd outIn quiet

/-- The window expansion: write the lookup executable `forgedLookup`. -/
def forgeWindow : CallElimination :=
  forgeCalls forgedWindowSink (not_occurs_of_occursB (by decide)) (not_occurs_of_occursB (by decide))

/-- The reflection expansion: write `(out call)` directly. -/
def forgeReflection : CallElimination :=
  forgeCalls forgedReport (not_occurs_of_occursB (by decide)) (not_occurs_of_occursB (by decide))

/-- The translated window caller. -/
def forgedCaller : Atom :=
  .expression [.symbol "exec", .expression [], .expression [.symbol ","],
    .expression [.symbol "O", forgedWindowSink]]

/-- The translated reflection caller. -/
def forgedCallerZ : Atom :=
  .expression [.symbol "exec", locZ, .expression [.symbol ","], .expression [.symbol "O", forgedReport]]

theorem watcher_callFree : ¬ Occurs (.symbol "call") watcherExec := not_occurs_of_occursB (by decide)

theorem equation_callFree : ¬ Occurs (.symbol "call") (equationOf seven) :=
  not_occurs_of_occursB (by decide)

theorem comma_callFree : ¬ Occurs (.symbol "call") (.expression [.symbol ","]) :=
  not_occurs_of_occursB (by decide)

theorem forgeWindow_window :
    forgeWindow.map ({commaCaller} ∪ {watcherExec} ∪ {equationOf seven}) =
      {forgedCaller} ∪ {watcherExec} ∪ {equationOf seven} := by
  rw [forgeWindow.map_union, forgeWindow.map_union, forgeWindow.map_plain _ watcher_callFree,
    forgeWindow.map_plain _ equation_callFree]
  congr 2

theorem forgeReflection_program :
    forgeReflection.map ({readerExec} ∪ {commaCallerZ}) = {readerExec} ∪ {forgedCallerZ} := by
  rw [forgeReflection.map_union, forgeReflection.map_plain _ callFree_readerExec]
  congr 1

/-- **The window witness does not separate in the kernel model.**  The extension reports
`(out 7)` alone; so does the kernel on the translated program, whose lookup runs after the
watcher and computes the report. -/
theorem forged_window_agrees :
    reports (callingRun defaultProfile inertPrimitives emptyTable 4 ExternalState.empty
        [commaCaller, watcherExec, equationOf seven]).1 = [outOf seven] ∧
      reports (mainlineRun defaultProfile sketchPrimitives 5 ExternalState.empty
        [forgedCaller, watcherExec, equationOf seven]).1 = [outOf seven] := by
  decide +kernel

/-- **A context without the watcher exposes the forger.** -/
theorem forged_window_caught :
    reports (callingRun defaultProfile inertPrimitives emptyTable 4 ExternalState.empty
        [commaCaller, equationOf seven]).1 = [] ∧
      reports (mainlineRun defaultProfile sketchPrimitives 5 ExternalState.empty
        [forgedCaller, equationOf seven]).1 = [outOf seven] := by
  decide +kernel

/-- **The reflection witness does not separate in the kernel model**, and a context without
the reader exposes the forger. -/
theorem forged_reflection_agrees :
    (callingRun defaultProfile inertPrimitives emptyTable 4 ExternalState.empty
        [readerExec, commaCallerZ]).1 = [outOf (.symbol "call")] ∧
      (mainlineRun defaultProfile sketchPrimitives 4 ExternalState.empty
        [readerExec, forgedCallerZ]).1 = [outOf (.symbol "call")] ∧
      (callingRun defaultProfile inertPrimitives emptyTable 4 ExternalState.empty
        [commaCallerZ]).1 = [] ∧
      (mainlineRun defaultProfile sketchPrimitives 4 ExternalState.empty
        [forgedCallerZ]).1 = [outOf (.symbol "call")] := by
  decide +kernel


/-! ## The driver route: calls on the unmodified kernel

A firing requests a call by writing `(call-request F A $r CONT)`.  After every kernel
step, the driver adds `CONT[$r := b]` for every result `b` of `F` on `A` and removes the
request, before the scheduler selects anything.  No executable observes a pending
request, so the call returns before the next selection. -/

/-- `(call-request F A $r CONT)`. -/
def requestAtom (function argument : Atom) (result : String) (continuation : Atom) : Atom :=
  .expression [.symbol "call-request", function, argument, .var result, continuation]

/-- Whether an atom is a call request. -/
def isRequest : Atom → Bool
  | .expression [.symbol "call-request", _, _, .var _, _] => true
  | _ => false

/-- The continuation instances one request contributes, given the space. -/
def requestAdditions (table : ProviderTable) (space : List Atom) : Atom → List Atom
  | .expression [.symbol "call-request", function, argument, .var result, continuation] =>
      (resolveCall table space function argument).map fun value =>
        applySubst [(result, value)] continuation
  | _ => []

/-- Resolve every pending request of a space. -/
def resolveRequests (table : ProviderTable) (space : List Atom) : List Atom :=
  morkUnionSupport (space.filter fun atom => !isRequest atom)
    ((space.filter isRequest).flatMap (requestAdditions table space))

/-- One driver step: a kernel step, then request resolution. -/
def driverStep (profile : BuildProfile) (prims : Primitives) (table : ProviderTable)
    (external : ExternalState) (space : List Atom) : StepOutcome :=
  match mainlineStep profile prims external space with
  | .next next after => .next (resolveRequests table next) after
  | other => other

/-- Driver runs with exact fuel. -/
def driverRun (profile : BuildProfile) (prims : Primitives) (table : ProviderTable) :
    ℕ → ExternalState → List Atom → List Atom × ExternalState × Option MainlineFault
  | 0, external, space => (space, external, none)
  | fuel + 1, external, space =>
      match driverStep profile prims table external space with
      | .quiescent => (space, external, none)
      | .aborted fault => (space, external, some fault)
      | .next next after => driverRun profile prims table fuel after next

/-- `(exec () (,) (O (+ (call-request f a $r (g $r)))))`: the window caller for the driver. -/
def requestCaller : Atom :=
  .expression [.symbol "exec", .expression [], .expression [.symbol ","],
    .expression [.symbol "O", .expression [.symbol "+",
      requestAtom (.symbol "f") (.symbol "a") "r" (.expression [.symbol "g", .var "r"])]]]

/-- **The driver closes the window on the unmodified kernel**, with `f` an equation of
the space or a native provider; without the driver the request stays pending and nothing
is reported.  The driver forges nothing: without the watcher no report appears. -/
theorem driver_window_closes :
    reports (driverRun defaultProfile inertPrimitives emptyTable 4 ExternalState.empty
        [requestCaller, watcherExec, equationOf seven]).1 = [outOf seven] ∧
      reports (driverRun defaultProfile inertPrimitives nativeF 4 ExternalState.empty
        [requestCaller, watcherExec]).1 = [outOf seven] ∧
      reports (mainlineRun defaultProfile inertPrimitives 4 ExternalState.empty
        [requestCaller, watcherExec, equationOf seven]).1 = [] ∧
      reports (driverRun defaultProfile inertPrimitives emptyTable 4 ExternalState.empty
        [requestCaller, equationOf seven]).1 = [] := by
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.MORK.FunctionCalls
