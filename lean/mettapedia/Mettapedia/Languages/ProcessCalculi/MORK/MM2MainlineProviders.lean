import Mettapedia.Languages.ProcessCalculi.MORK.MM2RuleScopedExecution
import Mettapedia.Languages.ProcessCalculi.MORK.ComputablePatternMonotonicity

/-!
# Mainline MM2: the complete provider inventory and the kernel's order of effects

At the pinned MORK kernel revision an `O` output dispatches each template to one of eighteen
sink forms, an `I` input dispatches each factor to one of five source forms, and a comma
output writes its templates verbatim.  `MainlineSink` and `MainlineSource` list them all;
this module gives each one a meaning on the computable list carrier of the rule-scoped
executor, with the kernel's actual order of effects.

* **Adds are eager.**  An `(+ x)` sink writes each instance while the matches are being
  enumerated; its finalizer does nothing.  Every other sink stages its instances and is
  finalized from left to right.  Hence `(O (- x) (+ x))` leaves `x` absent, while the
  left-to-right batch `cApplyRuleScopedSinkBatch`, shared by the support work queue and
  the programmable-space source profile, leaves it present
  (`remove_then_add_separates`).  The two agree whenever every add precedes every other
  sink (`mainline_eq_ruleScoped_of_addsFirst`); with ground stored atoms the whole firing
  agrees (`MM2SupportKernelBridge.fireDirective_eq_ruleScoped_ground`).
* **Equality and inequality factors range over stored atoms.**  `(== P W)` enumerates a
  stored atom matching `P` and matches `W` against the same atom; `(!= P W)` enumerates a
  stored atom matching `P` and a different stored atom matching `W`.  The core factor
  semantics instead erases the instantiated `P` whether or not it is stored, so the two
  disagree when nothing stored matches `P` (`neq_requires_stored_left`).
* **Patterns are unified with stored atoms.**  A stored atom's variables are renamed apart
  for each use (`renameApart`, `factorTag`); a pattern constant meets a stored variable,
  repeated variables corefer and the occurs check applies (`unifyOption`), so a join can
  go through stored variables (`unification_separates`).  `(!= P W)` reads the second
  atom's repeated variables at the first atom's levels when the first has variables
  (`neqReading`), as the kernel does.
* **Foreign computation is a parameter.**  The `pure` registry, unification and
  anti-unification of a batch, the aggregate values, the solver's models and wasm
  programs are supplied by `Primitives`; files and solver instances persist in
  `ExternalState`.  The module fixes what the kernel does with their results: what is
  staged, when it is written, and which batches abort.

Model limits.  Where the kernel's behaviour depends on the order in which its trie
enumerates rows (a duplicate instance reaching a full `head`/`tail` buffer) or on
byte-level write keys (aggregate guards whose template context does not begin with a
variable), the model reports a fault instead of choosing.

The kernel's numbering of output variables is modelled, including its defect for an
`(I …)` input with an `(O …)` output (`kernelOutput`): after a sink that introduces a
variable, a later sink's variables are numbered from the input's count again.  With the
input `(I (BTM (q $z)))`, `(O (count (cnt $k) $k $z) (+ (t $w $w)))` writes `(t $a $b)`,
and `(O (+ (t $w $w)) (count (cnt $k) $k $z))` makes the count variable fresh, which takes
the byte-keyed aggregate arm.  A variable in an executable's location is not modelled.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.Mainline

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK

/-! ## The kernel's order of effects for the core sinks -/

/-- A core sink writes while the matches are enumerated exactly when it is an add. -/
def writesEagerly : Sink → Bool
  | .add _ => true
  | _ => false

/-- Every sink staged and finalized in turn, as the rule-scoped executor does. -/
abbrev ruleScopedBatch (input : InputSpec) (rows : List Subst) (space : List Atom)
    (sinks : List Sink) : List Atom :=
  cApplyRuleScopedSinkBatch input rows space sinks

/-- The writes of the eager sinks, in template order. -/
def eagerWrites (input : InputSpec) (rows : List Subst) (space : List Atom)
    (sinks : List Sink) : List Atom :=
  sinks.foldl (fun current sink =>
    if writesEagerly sink then
      finalizeRuleScopedSink sink (rows.foldl (stageRuleScopedSink input sink) []) current
    else current) space

/-- **The kernel's order.**  Eager writes first, then every other sink finalized from left
to right.  An add's own finalizer is inert, so it is dropped from the finalized list. -/
def mainlineBatch (input : InputSpec) (rows : List Subst) (space : List Atom)
    (sinks : List Sink) : List Atom :=
  ruleScopedBatch input rows (eagerWrites input rows space sinks)
    (sinks.filter fun sink => !writesEagerly sink)

theorem eagerWrites_append (input : InputSpec) (rows : List Subst) (space : List Atom)
    (first second : List Sink) :
    eagerWrites input rows space (first ++ second) =
      eagerWrites input rows (eagerWrites input rows space first) second := by
  simp [eagerWrites, List.foldl_append]

theorem eagerWrites_of_none_eager (input : InputSpec) (rows : List Subst) :
    ∀ (sinks : List Sink) (space : List Atom),
      (∀ sink ∈ sinks, writesEagerly sink = false) → eagerWrites input rows space sinks = space
  | [], _, _ => rfl
  | sink :: rest, space, noEager => by
      have head : writesEagerly sink = false := noEager sink (by simp)
      simp only [eagerWrites, List.foldl_cons, head] at *
      exact eagerWrites_of_none_eager input rows rest space
        (fun other member => noEager other (by simp [member]))

theorem eagerWrites_of_all_eager (input : InputSpec) (rows : List Subst) :
    ∀ (sinks : List Sink) (space : List Atom),
      (∀ sink ∈ sinks, writesEagerly sink = true) →
        eagerWrites input rows space sinks = ruleScopedBatch input rows space sinks
  | [], _, _ => rfl
  | sink :: rest, space, all => by
      have head : writesEagerly sink = true := all sink (by simp)
      simp only [eagerWrites, List.foldl_cons, head, if_true]
      show eagerWrites input rows _ rest = _
      rw [eagerWrites_of_all_eager input rows rest _ (fun other member => all other (by simp [member]))]
      rfl

/-- **Agreement.**  When every add precedes every other sink, the kernel's order is the
left-to-right batch. -/
theorem mainline_eq_ruleScoped_of_addsFirst (input : InputSpec) (rows : List Subst)
    (space : List Atom) (adds rest : List Sink)
    (eager : ∀ sink ∈ adds, writesEagerly sink = true)
    (lazy : ∀ sink ∈ rest, writesEagerly sink = false) :
    mainlineBatch input rows space (adds ++ rest) =
      ruleScopedBatch input rows space (adds ++ rest) := by
  unfold mainlineBatch ruleScopedBatch
  rw [eagerWrites_append, eagerWrites_of_none_eager input rows rest _ lazy,
    eagerWrites_of_all_eager input rows adds space eager, cApplyRuleScopedSinkBatch_append]
  have dropAdds : adds.filter (fun sink => !writesEagerly sink) = [] :=
    List.filter_eq_nil_iff.mpr fun sink member => by simp [eager sink member]
  have keepRest : rest.filter (fun sink => !writesEagerly sink) = rest :=
    List.filter_eq_self.mpr fun sink member => by simp [lazy sink member]
  rw [List.filter_append, dropAdds, keepRest, List.nil_append]

/-! ### Separating examples -/

/-- The atom `(x)`. -/
def xAtom : Atom := .expression [.symbol "x"]

/-- The empty conjunction. -/
def emptyInput : InputSpec := .compat ⟨[]⟩

/-- **`(O (- (x)) (+ (x)))` from the empty space.**  The left-to-right batch removes, then
adds, and keeps `(x)`; the kernel writes `(x)` while enumerating, then removes it. -/
theorem remove_then_add_separates :
    ruleScopedBatch emptyInput [[]] [] [.remove xAtom, .add xAtom] = [xAtom] ∧
      mainlineBatch emptyInput [[]] [] [.remove xAtom, .add xAtom] = [] := by
  decide +kernel

/-- The same with `(x)` already stored: the batch keeps it, the kernel drops it. -/
theorem remove_then_add_separates_present :
    ruleScopedBatch emptyInput [[]] [xAtom] [.remove xAtom, .add xAtom] = [xAtom] ∧
      mainlineBatch emptyInput [[]] [xAtom] [.remove xAtom, .add xAtom] = [] := by
  decide +kernel

/-- `(edge a b)`. -/
def edgeAtom (first second : String) : Atom :=
  .expression [.symbol "edge", .symbol first, .symbol second]

/-- The conjunction `(, (edge $x $y))`. -/
def edgeInput : InputSpec := .compat ⟨[.expression [.symbol "edge", .var "x", .var "y"]]⟩

/-- The two rows of `(edge $x $y)` over `(edge a b)` and `(edge b c)`. -/
def edgeRows : List Subst :=
  [[("y", .symbol "b"), ("x", .symbol "a")], [("y", .symbol "c"), ("x", .symbol "b")]]

/-- **Both orders of the programmable-space example.**  `(O (+ $x) (- $y))` and
`(O (- $y) (+ $x))` over the two edges: the kernel leaves `a` in both orders; the
left-to-right batch leaves `a` for the first and `a`, `b` for the second. -/
theorem edge_example_orders :
    mainlineBatch edgeInput edgeRows [edgeAtom "a" "b", edgeAtom "b" "c"]
        [.add (.var "x"), .remove (.var "y")] =
      [edgeAtom "a" "b", edgeAtom "b" "c", .symbol "a"] ∧
    mainlineBatch edgeInput edgeRows [edgeAtom "a" "b", edgeAtom "b" "c"]
        [.remove (.var "y"), .add (.var "x")] =
      [edgeAtom "a" "b", edgeAtom "b" "c", .symbol "a"] ∧
    ruleScopedBatch edgeInput edgeRows [edgeAtom "a" "b", edgeAtom "b" "c"]
        [.remove (.var "y"), .add (.var "x")] =
      [edgeAtom "a" "b", edgeAtom "b" "c", .symbol "a", .symbol "b"] := by
  decide +kernel


/-! ## The inventory -/

/-- The eight aggregate sinks.  Each groups its staged instances by their context. -/
inductive AggregateKind where
  | count
  | hash
  | sum
  | bitAnd
  | fsum
  | fmin
  | fmax
  | fprod
  deriving Repr, DecidableEq

/-- The head symbol of an aggregate sink. -/
def AggregateKind.spelling : AggregateKind → String
  | .count => "count"
  | .hash => "hash"
  | .sum => "sum"
  | .bitAnd => "and"
  | .fsum => "fsum"
  | .fmin => "fmin"
  | .fmax => "fmax"
  | .fprod => "fprod"

/-- Every sink form of an `O` output.  `core` carries the four forms the support model
already owns: `(+ x)`, `(- x)`, `(head n x)` and `(tail n x)`. -/
inductive MainlineSink where
  | core (sink : Sink)
  /-- `(U x)`: the most general unifier of every staged instance. -/
  | unify (body : Atom)
  /-- `(AU x)`: the least general generalization of every staged instance. -/
  | antiUnify (body : Atom)
  /-- `(count C N P)`, `(hash C N P)`, `(sum C N P)`, `(and C N P)`, `(fsum C N P)`,
  `(fmin C N P)`, `(fmax C N P)`, `(fprod C N P)`. -/
  | aggregate (kind : AggregateKind) (context count payload : Atom)
  /-- `(ACT name x)`: replace the named file by the staged instances. -/
  | act (file : String) (body : Atom)
  /-- `(pure T $r C)`: write `T` with `$r` bound to the value of the call `C`. -/
  | pure (template result call : Atom)
  /-- `(z3 name s)`: send the staged statements to the named solver. -/
  | z3 (solver : String) (statement : Atom)
  /-- `(wasm program x)`: write the program's output for each instance. -/
  | wasm (program body : Atom)
  deriving Repr, DecidableEq

/-- Every factor form of an `I` input.  `core` carries `(BTM p)`, `(== P W)` and
`(!= P W)`; their mainline meaning is `sourceRows`, not `matchSourceFactor`. -/
inductive MainlineSource where
  | core (factor : SourceFactor)
  /-- `(ACT name p)`: match against the atoms of the named file. -/
  | act (file : String) (pattern : Atom)
  /-- `(z3 name p)`: match against the model the named solver reports. -/
  | z3 (solver : String) (pattern : Atom)
  deriving Repr, DecidableEq

/-- Compile-time features of the kernel. -/
inductive Feature where
  | grounding
  | wasm
  | z3
  | leapfrog
  | specializeIO
  deriving Repr, DecidableEq

/-- A choice of compile-time features. -/
structure BuildProfile where
  features : List Feature
  deriving Repr, DecidableEq

/-- The default feature set of the kernel crate. -/
def defaultProfile : BuildProfile := ⟨[.grounding, .specializeIO]⟩

/-- The feature a sink form needs, if any. -/
def MainlineSink.feature? : MainlineSink → Option Feature
  | .pure .. => some .grounding
  | .wasm .. => some .wasm
  | .z3 .. => some .z3
  | _ => none

/-- The feature a source form needs, if any. -/
def MainlineSource.feature? : MainlineSource → Option Feature
  | .z3 .. => some .z3
  | _ => none

/-- Why a firing aborts the kernel process.  Every case is a panic in the kernel, which
ends the whole run, not only the directive. -/
inductive MainlineFault where
  | unrecognizedSink (form : Atom)
  | unrecognizedSource (form : Atom)
  | missingFeature (feature : Feature) (form : Atom)
  | malformed (form : Atom)
  /-- A `pure` result position that is neither a template variable nor a fresh variable. -/
  | unimplementedPureShape (form : Atom)
  /-- A `head`/`tail` batch with repeated instances: the kernel's buffer assertion fails
  for some enumeration orders. -/
  | extremaDuplicate (form : Atom)
  /-- An `AU` sink reached by exactly one row: the kernel slices its buffer with a length
  that only a second instance sets, and panics. -/
  | antiUnifySingleRow (form : Atom)
  /-- An aggregate payload the kernel cannot read as a number. -/
  | aggregateValue (form : Atom)
  /-- An aggregate guard whose template context does not begin with a variable: the
  kernel writes it under a doubled key. -/
  | misKeyedAggregate (form : Atom)
  /-- A `z3` factor naming a solver no `z3` sink has created. -/
  | missingSolver (solver : String)
  /-- An `ACT` factor naming a file that does not exist. -/
  | missingFile (file : String)
  deriving Repr, DecidableEq

/-- Require a feature of the build. -/
def requireFeature (profile : BuildProfile) (form : Atom) :
    Option Feature → Except MainlineFault Unit
  | none => .ok ()
  | some feature =>
      if profile.features.contains feature then .ok () else .error (.missingFeature feature form)

/-- The aggregate sink a head symbol names, if any. -/
def aggregateOfHead? : String → Option AggregateKind
  | "count" => some .count
  | "hash" => some .hash
  | "sum" => some .sum
  | "and" => some .bitAnd
  | "fsum" => some .fsum
  | "fmin" => some .fmin
  | "fmax" => some .fmax
  | "fprod" => some .fprod
  | _ => none

/-- Recognize a sink form, dispatching on its head symbol and arity exactly as the kernel
does.  Anything else is the kernel's `unrecognized sink` panic. -/
def recognizeSink (form : Atom) : Except MainlineFault MainlineSink :=
  match form with
  | .expression [.symbol "-", body] => .ok (.core (.remove body))
  | .expression [.symbol "+", body] => .ok (.core (.add body))
  | .expression [.symbol "U", body] => .ok (.unify body)
  | .expression [.symbol "AU", body] => .ok (.antiUnify body)
  | .expression [.symbol "head", count, body] =>
      match parseExtremaSink true count body with
      | some sink => .ok (.core sink)
      | none => .error (.malformed form)
  | .expression [.symbol "tail", count, body] =>
      match parseExtremaSink false count body with
      | some sink => .ok (.core sink)
      | none => .error (.malformed form)
  | .expression [.symbol "ACT", .symbol file, body] => .ok (.act file body)
  | .expression [.symbol "ACT", _, _] => .error (.malformed form)
  | .expression [.symbol "wasm", program, body] => .ok (.wasm program body)
  | .expression [.symbol "z3", .symbol solver, statement] => .ok (.z3 solver statement)
  | .expression [.symbol "z3", _, _] => .error (.malformed form)
  | .expression [.symbol "pure", template, result, call] => .ok (.pure template result call)
  | .expression [.symbol head, context, count, payload] =>
      match aggregateOfHead? head with
      | some kind => .ok (.aggregate kind context count payload)
      | none => .error (.unrecognizedSink form)
  | _ => .error (.unrecognizedSink form)

/-- Decode a sink under a build profile: a recognized form whose feature is missing is
the kernel's missing-feature panic. -/
def decodeSink (profile : BuildProfile) (form : Atom) : Except MainlineFault MainlineSink := do
  let sink ← recognizeSink form
  requireFeature profile form sink.feature?
  pure sink

/-- Recognize a source factor as the kernel does.  An unknown factor is the kernel's
`unreachable` panic. -/
def recognizeSource (form : Atom) : Except MainlineFault MainlineSource :=
  match form with
  | .expression [.symbol "BTM", pattern] => .ok (.core (.btm pattern))
  | .expression [.symbol "ACT", .symbol _, .var _] => .error (.malformed form)
  | .expression [.symbol "ACT", .symbol file, pattern] => .ok (.act file pattern)
  | .expression [.symbol "ACT", _, _] => .error (.malformed form)
  | .expression [.symbol "z3", .symbol solver, pattern] => .ok (.z3 solver pattern)
  | .expression [.symbol "z3", _, _] => .error (.malformed form)
  | .expression [.symbol "==", pattern, witness] => .ok (.core (.eqConstraint pattern witness))
  | .expression [.symbol "!=", pattern, witness] => .ok (.core (.neqConstraint pattern witness))
  | _ => .error (.unrecognizedSource form)

/-- Decode a source factor under a build profile. -/
def decodeSource (profile : BuildProfile) (form : Atom) : Except MainlineFault MainlineSource := do
  let source ← recognizeSource form
  requireFeature profile form source.feature?
  pure source

/-- The input of a directive. -/
inductive MainlineInput where
  /-- `(, p₁ … pₙ)`: a conjunction over the read copy. -/
  | compat (patterns : List Atom)
  /-- `(I f₁ … fₙ)`: a product of source factors. -/
  | explicit (sources : List MainlineSource)
  deriving Repr, DecidableEq

/-- The output of a directive. -/
inductive MainlineOutput where
  /-- `(, t₁ … tₙ)`: every template instance is written verbatim. -/
  | compat (templates : List Atom)
  /-- `(O s₁ … sₙ)`: sinks. -/
  | sinks (sinks : List MainlineSink)
  deriving Repr, DecidableEq

/-- A decoded directive, retaining its stored atom. -/
structure MainlineDirective where
  atom : Atom
  input : MainlineInput
  output : MainlineOutput
  deriving Repr, DecidableEq

/-- Decode every element, stopping at the first fault. -/
def decodeAll {α : Type} (decode : Atom → Except MainlineFault α) :
    List Atom → Except MainlineFault (List α)
  | [] => .ok []
  | form :: rest => do
      let first ← decode form
      let others ← decodeAll decode rest
      pure (first :: others)

/-- Decode an input expression; `none` when it is not an input. -/
def decodeInput (profile : BuildProfile) : Atom → Option (Except MainlineFault MainlineInput)
  | .expression (.symbol "," :: patterns) => some (.ok (.compat patterns))
  | .expression (.symbol "I" :: factors) =>
      some ((decodeAll (decodeSource profile) factors).map .explicit)
  | _ => none

/-- Decode an output expression; `none` when it is not an output. -/
def decodeOutput (profile : BuildProfile) : Atom → Option (Except MainlineFault MainlineOutput)
  | .expression (.symbol "," :: templates) => some (.ok (.compat templates))
  | .expression (.symbol "O" :: forms) => some ((decodeAll (decodeSink profile) forms).map .sinks)
  | _ => none

/-! ### The kernel's numbering of output variables

Every variable of an `(exec L I O)` atom is numbered by its first occurrence in the whole
atom.  When the kernel applies a sink's template, a variable occurring there for the first
time gets the next number after a running count of introduced variables, and a later
occurrence names its number in the whole atom.  For a comma input the running count starts at
the input's variables and advances over every sink.  For an `(I …)` input with an `(O …)`
output it starts at the input's variables in every sink (`transform_multi_multi_io` does not
carry it from one sink to the next), so after a sink that introduces a variable, a later
sink's first occurrences and its repeated occurrences are numbered differently.
`kernelOutput` renames the output variables of such a directive by the numbers the kernel
gives them, which is the identity on variables up to renaming whenever the count is not
behind. -/

/-- The model's name for the output variable the kernel numbers `index`.  A parsed program
cannot spell it: variable names contain no space. -/
def kernelVarName (index : ℕ) : String := " o" ++ toString index

mutual
  /-- Variables in order of first occurrence, after `seen`. -/
  def firstVars : List String → Atom → List String
    | seen, .var name => if seen.contains name then seen else seen ++ [name]
    | seen, .expression children => firstVarsList seen children
    | seen, _ => seen
  def firstVarsList : List String → List Atom → List String
    | seen, [] => seen
    | seen, atom :: rest => firstVarsList (firstVars seen atom) rest
end

mutual
  /-- Rename the output variables of one sink: `seen` lists the output variables met so far in
  the whole atom, `fresh` the first occurrences met so far in this sink. -/
  def ioRename (bound : List String) (newBase refBase : ℕ) :
      List String × ℕ → Atom → Atom × (List String × ℕ)
    | state, .var name =>
        if bound.contains name then (.var name, state)
        else
          match state.1.idxOf? name with
          | some index => (.var (kernelVarName (refBase + index)), state)
          | none => (.var (kernelVarName (newBase + state.2)), (state.1 ++ [name], state.2 + 1))
    | state, .expression children =>
        let renamed := ioRenameList bound newBase refBase state children
        (.expression renamed.1, renamed.2)
    | state, atom => (atom, state)
  def ioRenameList (bound : List String) (newBase refBase : ℕ) :
      List String × ℕ → List Atom → List Atom × (List String × ℕ)
    | state, [] => ([], state)
    | state, atom :: rest =>
        let first := ioRename bound newBase refBase state atom
        let others := ioRenameList bound newBase refBase first.2 rest
        (first.1 :: others.1, others.2)
end

/-- Rename every sink, the count of first occurrences restarting at each sink. -/
def ioRenameSinks (bound : List String) (newBase refBase : ℕ) : List String → List Atom → List Atom
  | _, [] => []
  | seen, sink :: rest =>
      let renamed := ioRename bound newBase refBase (seen, 0) sink
      renamed.1 :: ioRenameSinks bound newBase refBase renamed.2.1 rest

/-- The output as the kernel numbers it: renamed for an `(I …)` input with an `(O …)` output,
unchanged otherwise. -/
def kernelOutput (location input output : Atom) : Atom :=
  match input, output with
  | .expression (.symbol "I" :: _), .expression (.symbol "O" :: sinks) =>
      let locationVars := firstVars [] location
      let bound := firstVars locationVars input
      .expression (.symbol "O" ::
        ioRenameSinks bound (bound.length - locationVars.length) bound.length [] sinks)
  | _, _ => output

/-- What the kernel does with a selected `(exec loc input output)` shell.  An input or
output of the wrong shape (including the empty expression `()`) is reported by the
interpreter and consumed with no effect (`ok none`); an unrecognized sink or factor, or a
missing feature, aborts.  The kernel constructs the sinks before it opens the sources. -/
def decodeDirective (profile : BuildProfile) (raw : RawExecFact) :
    Except MainlineFault (Option MainlineDirective) :=
  match decodeInput profile raw.inputExpr,
      decodeOutput profile (kernelOutput raw.loc raw.inputExpr raw.templateExpr) with
  | some input, some output => do
      let output ← output
      let input ← input
      pure (some ⟨raw.atom, input, output⟩)
  | _, _ => .ok none

/-- A decoded directive keeps its atom and the decoded output. -/
theorem decodeDirective_some {profile : BuildProfile} {raw : RawExecFact}
    {directive : MainlineDirective} {output : MainlineOutput}
    (outputDecoded : decodeOutput profile (kernelOutput raw.loc raw.inputExpr raw.templateExpr) =
      some (.ok output))
    (decoded : decodeDirective profile raw = .ok (some directive)) :
    directive.atom = raw.atom ∧ directive.output = output := by
  unfold decodeDirective at decoded
  rw [outputDecoded] at decoded
  cases inputDecoded : decodeInput profile raw.inputExpr with
  | none => simp [inputDecoded] at decoded
  | some input =>
      cases input with
      | error fault => simp [inputDecoded, bind, Except.bind] at decoded
      | ok input =>
          simp only [inputDecoded, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
            Option.some.injEq] at decoded
          subst decoded
          exact ⟨rfl, rfl⟩

/-! ### Dispatch canaries -/

/-- `(count (all $k) $k (cux $x))` is an aggregate. -/
example : recognizeSink (.expression [.symbol "count", .expression [.symbol "all", .var "k"],
    .var "k", .expression [.symbol "cux", .var "x"]]) =
      .ok (.aggregate .count (.expression [.symbol "all", .var "k"]) (.var "k")
        (.expression [.symbol "cux", .var "x"])) := by decide +kernel

/-- An unknown head under `O` aborts. -/
example : recognizeSink (.expression [.symbol "call", .symbol "f", .symbol "a"]) =
    .error (.unrecognizedSink (.expression [.symbol "call", .symbol "f", .symbol "a"])) := by
  decide +kernel

/-- `(+ x y)` is not an add: the kernel requires arity two. -/
example : recognizeSink (.expression [.symbol "+", .symbol "x", .symbol "y"]) =
    .error (.unrecognizedSink (.expression [.symbol "+", .symbol "x", .symbol "y"])) := by
  decide +kernel

/-- `(head 0 x)` aborts: extrema counts are positive. -/
example : recognizeSink (.expression [.symbol "head", .symbol "0", .symbol "x"]) =
    .error (.malformed (.expression [.symbol "head", .symbol "0", .symbol "x"])) := by
  decide +kernel

/-- The default build decodes `pure` and aborts on `z3` and `wasm`. -/
theorem default_profile_gating :
    (decodeSink defaultProfile (.expression [.symbol "pure", .var "t", .var "r", .var "c"])).toBool
        = true ∧
      decodeSink defaultProfile (.expression [.symbol "z3", .symbol "s", .var "x"]) =
        .error (.missingFeature .z3 (.expression [.symbol "z3", .symbol "s", .var "x"])) ∧
      decodeSink defaultProfile (.expression [.symbol "wasm", .var "p", .var "x"]) =
        .error (.missingFeature .wasm (.expression [.symbol "wasm", .var "p", .var "x"])) := by
  decide +kernel

/-- A build without grounding cannot decode `pure`. -/
theorem pure_requires_grounding (profile : BuildProfile)
    (missing : Feature.grounding ∉ profile.features) (template result call : Atom) :
    decodeSink profile (.expression [.symbol "pure", template, result, call]) =
      .error (.missingFeature .grounding (.expression [.symbol "pure", template, result, call])) := by
  simp [decodeSink, recognizeSink, requireFeature, MainlineSink.feature?, missing, bind,
    Except.bind]


/-! ## Foreign computation and persistent state -/

/-- What a firing delegates to code outside the calculus. -/
structure Primitives where
  /-- The `pure` registry on a call term; `none` is an evaluation error, which skips the
  row. -/
  eval : Atom → Option Atom
  /-- The most general unifier of a nonempty batch; `none` when the batch conflicts. -/
  unify : List Atom → Option Atom
  /-- The least general generalization of a nonempty batch. -/
  antiUnify : List Atom → Option Atom
  /-- A numeric aggregate other than `count` over a group's payloads; `none` when the
  kernel cannot read a payload as a number. -/
  aggregate : AggregateKind → List Atom → Option Atom
  /-- The model atoms a solver reports for the statements it has received; empty when
  they are unsatisfiable. -/
  model : List Atom → List Atom
  /-- A wasm program's output on one instance; `none` is a trap. -/
  wasm : Atom → Atom → Option Atom

/-- State that outlives a firing: files written by `ACT` sinks and solver instances
created by `z3` sinks.  An absent file or solver is `none`. -/
structure ExternalState where
  files : String → Option (List Atom)
  solvers : String → Option (List Atom)

/-- No files and no solvers. -/
def ExternalState.empty : ExternalState := ⟨fun _ => none, fun _ => none⟩

/-! ## The kernel's matcher

The kernel unifies.  A pattern constant meets a stored variable, a repeated stored
variable constrains the pattern, a stored atom's variables are local to that atom, and one
stored atom read by two factors is two independent copies.

`solveEquations` is Martelli–Montanari unification with an occurs check over a solved,
idempotent substitution.  Its outer budget is the number of distinct variables, which
every elimination lowers; its inner budget is the size of the equations, which every other
step lowers and which is recomputed after each elimination.  Both recursions are
structural, and `solveEquations_ne_exhausted` shows that the budgets never run out. -/

/-- Nodes of an atom. -/
def atomSize : Atom → ℕ
  | .expression children => atomSizeList children + 1
  | _ => 1
where
  atomSizeList : List Atom → ℕ
    | [] => 0
    | atom :: rest => atomSize atom + atomSizeList rest

/-- Equations between atoms. -/
abbrev Equations := List (Atom × Atom)

/-- Total size of a list of equations. -/
def equationsSize : Equations → ℕ
  | [] => 0
  | equation :: rest => atomSize equation.1 + atomSize equation.2 + equationsSize rest

/-- The variables of a list of equations, without repeats. -/
def equationsVars (equations : Equations) : List String :=
  (equations.flatMap fun equation => atomFreeVars equation.1 ++ atomFreeVars equation.2).dedup

/-- The outcome of unification.  `exhausted` never occurs (`solveEquations_ne_exhausted`);
it exists so that the recursion can be structural. -/
inductive Unification where
  | solved (substitution : Subst)
  | clash
  | exhausted
  deriving Repr, DecidableEq

/-- Bind `name := value` in a solved substitution, updating the earlier bindings, so the
substitution stays idempotent. -/
def bindSolved (θ : Subst) (name : String) (value : Atom) : Subst :=
  (name, value) :: θ.map fun binding => (binding.1, applySubst [(name, value)] binding.2)

/-- Substitute `name := value` in every equation. -/
def substituteEquations (name : String) (value : Atom) (equations : Equations) : Equations :=
  equations.map fun equation =>
    (applySubst [(name, value)] equation.1, applySubst [(name, value)] equation.2)

/-- The steps that do not eliminate a variable; an elimination is handed to `eliminate`. -/
def solveWithin (eliminate : Equations → Subst → Unification) :
    ℕ → Equations → Subst → Unification
  | 0, _, _ => .exhausted
  | _ + 1, [], θ => .solved θ
  | fuel + 1, (left, right) :: rest, θ =>
      if left = right then solveWithin eliminate fuel rest θ
      else
        match left, right with
        | .var name, value =>
            if (atomFreeVars value).contains name then .clash
            else eliminate (substituteEquations name value rest) (bindSolved θ name value)
        | value, .var name =>
            if (atomFreeVars value).contains name then .clash
            else eliminate (substituteEquations name value rest) (bindSolved θ name value)
        | .expression lefts, .expression rights =>
            if lefts.length = rights.length then
              solveWithin eliminate fuel (lefts.zip rights ++ rest) θ
            else .clash
        | _, _ => .clash

/-- Unification with the outer budget counting variables. -/
def solveEquations : ℕ → Equations → Subst → Unification
  | 0, equations, θ =>
      solveWithin (fun _ _ => .exhausted) (equationsSize equations + 1) equations θ
  | budget + 1, equations, θ =>
      solveWithin (fun next θ' => solveEquations budget next θ') (equationsSize equations + 1)
        equations θ

/-- Unify equations under a solved substitution: apply it, then solve. -/
def unifyUnder (θ : Subst) (equations : Equations) : Unification :=
  let applied := equations.map fun equation => (applySubst θ equation.1, applySubst θ equation.2)
  solveEquations (equationsVars applied).length applied θ

/-- The solved substitution, when unification succeeds. -/
def unifyOption (θ : Subst) (equations : Equations) : Option Subst :=
  match unifyUnder θ equations with
  | .solved next => some next
  | _ => none

/-! ### The budgets never run out -/

theorem atomSize_pos : ∀ atom : Atom, 0 < atomSize atom
  | .expression _ => Nat.succ_pos _
  | .var _ => Nat.one_pos
  | .symbol _ => Nat.one_pos
  | .grounded _ => Nat.one_pos

theorem equationsSize_append : ∀ (first second : Equations),
    equationsSize (first ++ second) = equationsSize first + equationsSize second
  | [], _ => by simp [equationsSize]
  | equation :: rest, second => by
      simp only [List.cons_append, equationsSize, equationsSize_append rest second]
      omega

theorem equationsSize_zip : ∀ (lefts rights : List Atom), lefts.length = rights.length →
    equationsSize (lefts.zip rights) = atomSize.atomSizeList lefts + atomSize.atomSizeList rights
  | [], [], _ => rfl
  | [], _ :: _, sameLength => by simp at sameLength
  | _ :: _, [], sameLength => by simp at sameLength
  | left :: lefts, right :: rights, sameLength => by
      simp only [List.zip_cons_cons, equationsSize, atomSize.atomSizeList,
        equationsSize_zip lefts rights (by simpa using sameLength)]
      omega

theorem mem_equationsVars {name : String} {equations : Equations} :
    name ∈ equationsVars equations ↔
      ∃ equation ∈ equations, name ∈ atomFreeVars equation.1 ∨ name ∈ atomFreeVars equation.2 := by
  simp [equationsVars, List.mem_dedup, List.mem_flatMap]

theorem lookup_single (name other : String) (value : Atom) :
    Subst.lookup [(name, value)] other = if name = other then some value else none := by
  by_cases same : name = other
  · subst same; simp [Subst.lookup]
  · have different : (name == other) = false := by simpa using same
    simp [Subst.lookup, List.find?, different, same]

/-- A variable of `atom[name := value]` is a variable of `atom` other than `name`, or a
variable of `value`. -/
theorem mem_atomFreeVars_applySubst_single (name : String) (value : Atom) (w : String) :
    ∀ atom : Atom, w ∈ atomFreeVars (applySubst [(name, value)] atom) →
      (w ∈ atomFreeVars atom ∧ w ≠ name) ∨ w ∈ atomFreeVars value
  | .var other => by
      intro member
      by_cases same : name = other
      · subst same
        right
        simpa [applySubst, lookup_single] using member
      · left
        simp only [applySubst, lookup_single, same, if_false, Option.getD_none, atomFreeVars,
          List.mem_singleton] at member
        subst member
        exact ⟨by simp [atomFreeVars], fun equal => same equal.symm⟩
  | .symbol _ => by simp [applySubst, atomFreeVars]
  | .grounded _ => by simp [applySubst, atomFreeVars]
  | .expression children => by
      intro member
      simp only [applySubst, atomFreeVars] at member ⊢
      exact listCase children member
where
  listCase : ∀ children : List Atom,
      w ∈ atomFreeVars.atomFreeVarsList (applySubst.applySubstList [(name, value)] children) →
        (w ∈ atomFreeVars.atomFreeVarsList children ∧ w ≠ name) ∨
          w ∈ atomFreeVars value
    | [] => by simp [applySubst.applySubstList, atomFreeVars.atomFreeVarsList]
    | child :: rest => by
        intro member
        simp only [applySubst.applySubstList, atomFreeVars.atomFreeVarsList, List.mem_append]
          at member ⊢
        rcases member with member | member
        · rcases mem_atomFreeVars_applySubst_single name value w child member with
            ⟨inChild, distinct⟩ | inValue
          · exact Or.inl ⟨Or.inl inChild, distinct⟩
          · exact Or.inr inValue
        · rcases listCase rest member with ⟨inRest, distinct⟩ | inValue
          · exact Or.inl ⟨Or.inr inRest, distinct⟩
          · exact Or.inr inValue

/-- A deduplicated list contained in another is no longer than it. -/
theorem length_le_of_nodup_subset {first second : List String} (nodup : first.Nodup)
    (contained : ∀ name ∈ first, name ∈ second) : first.length ≤ second.length :=
  (nodup.subperm contained).length_le

/-- Eliminating a variable that does not occur in its value lowers the variable count. -/
theorem equationsVars_substitute_lt (name : String) (value : Atom) (rest : Equations)
    (fresh : (atomFreeVars value).contains name = false) (equation : Atom × Atom)
    (named : name ∈ atomFreeVars equation.1 ∨ name ∈ atomFreeVars equation.2)
    (valued : ∀ w ∈ atomFreeVars value,
      w ∈ atomFreeVars equation.1 ∨ w ∈ atomFreeVars equation.2) :
    (equationsVars (substituteEquations name value rest)).length <
      (equationsVars (equation :: rest)).length := by
  have notInValue : name ∉ atomFreeVars value := by simpa using fresh
  have inside : ∀ w ∈ equationsVars (substituteEquations name value rest),
      w ∈ (equationsVars (equation :: rest)).erase name := by
    intro w member
    rw [mem_equationsVars] at member
    obtain ⟨substituted, substitutedMember, occurs⟩ := member
    simp only [substituteEquations, List.mem_map] at substitutedMember
    obtain ⟨original, originalMember, rfl⟩ := substitutedMember
    have cases : (w ∈ atomFreeVars original.1 ∨ w ∈ atomFreeVars original.2) ∧
        w ≠ name ∨ w ∈ atomFreeVars value := by
      rcases occurs with occurs | occurs
      · rcases mem_atomFreeVars_applySubst_single name value w _ occurs with
          ⟨inside, distinct⟩ | inValue
        · exact Or.inl ⟨Or.inl inside, distinct⟩
        · exact Or.inr inValue
      · rcases mem_atomFreeVars_applySubst_single name value w _ occurs with
          ⟨inside, distinct⟩ | inValue
        · exact Or.inl ⟨Or.inr inside, distinct⟩
        · exact Or.inr inValue
    have nodup : (equationsVars (equation :: rest)).Nodup := List.nodup_dedup _
    rcases cases with ⟨inOriginal, distinct⟩ | inValue
    · rw [nodup.mem_erase_iff]
      exact ⟨distinct, mem_equationsVars.2 ⟨original, List.mem_cons_of_mem _ originalMember,
        inOriginal⟩⟩
    · have distinct : w ≠ name := fun same => notInValue (same ▸ inValue)
      rw [nodup.mem_erase_iff]
      exact ⟨distinct, mem_equationsVars.2 ⟨equation, List.mem_cons_self .., valued w inValue⟩⟩
  have named' : name ∈ equationsVars (equation :: rest) :=
    mem_equationsVars.2 ⟨equation, List.mem_cons_self .., named⟩
  have bound := length_le_of_nodup_subset (List.nodup_dedup _) inside
  rw [List.length_erase_of_mem named'] at bound
  have positive : 0 < (equationsVars (equation :: rest)).length := List.length_pos_of_mem named'
  exact Nat.lt_of_le_of_lt bound (Nat.sub_lt positive Nat.one_pos)

/-- Equations taken from a list have no more variables than the list. -/
theorem equationsVars_length_le_of_subset {first second : Equations}
    (contained : ∀ w ∈ equationsVars first, w ∈ equationsVars second) :
    (equationsVars first).length ≤ (equationsVars second).length :=
  length_le_of_nodup_subset (List.nodup_dedup _) contained

theorem solveWithin_ne_exhausted (eliminate : Equations → Subst → Unification) (bound : ℕ)
    (good : ∀ next θ', (equationsVars next).length < bound → eliminate next θ' ≠ .exhausted) :
    ∀ (fuel : ℕ) (equations : Equations) (θ : Subst),
      equationsSize equations < fuel → (equationsVars equations).length ≤ bound →
        solveWithin eliminate fuel equations θ ≠ .exhausted
  | 0, _, _, small, _ => absurd small (Nat.not_lt_zero _)
  | _ + 1, [], θ, _, _ => by simp [solveWithin]
  | fuel + 1, (left, right) :: rest, θ, small, bounded => by
      have leftPos := atomSize_pos left
      have rightPos := atomSize_pos right
      simp only [equationsSize] at small
      have restVars : (equationsVars rest).length ≤ bound :=
        le_trans (equationsVars_length_le_of_subset (fun w member => by
          obtain ⟨equation, equationMember, occurs⟩ := mem_equationsVars.1 member
          exact mem_equationsVars.2 ⟨equation, List.mem_cons_of_mem _ equationMember, occurs⟩))
          bounded
      by_cases same : left = right
      · simp only [solveWithin, same, if_true]
        exact solveWithin_ne_exhausted eliminate bound good fuel rest θ (by omega) restVars
      · simp only [solveWithin, same, if_false]
        cases left with
        | var name =>
            simp only
            split
            · simp
            · rename_i fresh
              apply good
              have lower := equationsVars_substitute_lt name right rest (by simpa using fresh)
                (.var name, right) (Or.inl (by simp [atomFreeVars]))
                (fun w member => Or.inr member)
              omega
        | symbol symbolName =>
            cases right with
            | var name =>
                simp only
                split
                · simp
                · rename_i fresh
                  apply good
                  have lower := equationsVars_substitute_lt name (.symbol symbolName) rest
                    (by simpa using fresh) (.symbol symbolName, .var name)
                    (Or.inr (by simp [atomFreeVars])) (fun w member => Or.inl member)
                  omega
            | symbol _ => simp
            | grounded _ => simp
            | expression _ => simp
        | grounded value =>
            cases right with
            | var name =>
                simp only
                split
                · simp
                · rename_i fresh
                  apply good
                  have lower := equationsVars_substitute_lt name (.grounded value) rest
                    (by simpa using fresh) (.grounded value, .var name)
                    (Or.inr (by simp [atomFreeVars])) (fun w member => Or.inl member)
                  omega
            | symbol _ => simp
            | grounded _ => simp
            | expression _ => simp
        | expression lefts =>
            cases right with
            | var name =>
                simp only
                split
                · simp
                · rename_i fresh
                  apply good
                  have lower := equationsVars_substitute_lt name (.expression lefts) rest
                    (by simpa using fresh) (.expression lefts, .var name)
                    (Or.inr (by simp [atomFreeVars])) (fun w member => Or.inl member)
                  omega
            | symbol _ => simp
            | grounded _ => simp
            | expression rights =>
                simp only
                split
                · rename_i sameLength
                  apply solveWithin_ne_exhausted eliminate bound good fuel _ θ
                  · rw [equationsSize_append, equationsSize_zip lefts rights sameLength]
                    simp only [atomSize] at small
                    omega
                  · refine le_trans (equationsVars_length_le_of_subset ?_) bounded
                    intro w member
                    obtain ⟨equation, equationMember, occurs⟩ := mem_equationsVars.1 member
                    rcases List.mem_append.1 equationMember with zipped | inRest
                    · obtain ⟨leftChild, rightChild⟩ := equation
                      have leftIn := List.of_mem_zip zipped
                      refine mem_equationsVars.2 ⟨(.expression lefts, .expression rights),
                        List.mem_cons_self .., ?_⟩
                      simp only [atomFreeVars]
                      rcases occurs with occurs | occurs
                      · exact Or.inl (mem_atomFreeVarsList_of_mem leftIn.1 occurs)
                      · exact Or.inr (mem_atomFreeVarsList_of_mem leftIn.2 occurs)
                    · exact mem_equationsVars.2 ⟨equation, List.mem_cons_of_mem _ inRest, occurs⟩
                · simp

/-- **Unification never exhausts its budgets.** -/
theorem solveEquations_ne_exhausted : ∀ (budget : ℕ) (equations : Equations) (θ : Subst),
    (equationsVars equations).length ≤ budget → solveEquations budget equations θ ≠ .exhausted
  | 0, equations, θ, bounded =>
      solveWithin_ne_exhausted _ 0 (fun _ _ small => absurd small (Nat.not_lt_zero _)) _ equations θ
        (Nat.lt_succ_self _) bounded
  | budget + 1, equations, θ, bounded =>
      solveWithin_ne_exhausted _ (budget + 1)
        (fun next θ' small => solveEquations_ne_exhausted budget next θ' (Nat.lt_succ_iff.mp small))
        _ equations θ (Nat.lt_succ_self _) bounded

theorem unifyUnder_ne_exhausted (θ : Subst) (equations : Equations) :
    unifyUnder θ equations ≠ .exhausted :=
  solveEquations_ne_exhausted _ _ _ le_rfl

/-! ### Ground values -/

theorem atomFreeVars_of_ground : ∀ atom : Atom, isGroundAtom atom = true → atomFreeVars atom = []
  | .var _, ground => by simp [isGroundAtom] at ground
  | .symbol _, _ => rfl
  | .grounded _, _ => rfl
  | .expression children, ground => by
      simp only [atomFreeVars]
      exact listCase children (by simpa [isGroundAtom] using ground)
where
  listCase : ∀ children : List Atom, isGroundAtom.isGroundList children = true →
      atomFreeVars.atomFreeVarsList children = []
    | [], _ => rfl
    | child :: rest, ground => by
        simp only [isGroundAtom.isGroundList, Bool.and_eq_true] at ground
        simp [atomFreeVars.atomFreeVarsList, atomFreeVars_of_ground child ground.1,
          listCase rest ground.2]

theorem applySubst_of_ground (σ : Subst) : ∀ atom : Atom, isGroundAtom atom = true →
    applySubst σ atom = atom
  | .var _, ground => by simp [isGroundAtom] at ground
  | .symbol _, _ => rfl
  | .grounded _, _ => rfl
  | .expression children, ground => by
      simp only [applySubst]
      congr 1
      exact listCase children (by simpa [isGroundAtom] using ground)
where
  listCase : ∀ children : List Atom, isGroundAtom.isGroundList children = true →
      applySubst.applySubstList σ children = children
    | [], _ => rfl
    | child :: rest, ground => by
        simp only [isGroundAtom.isGroundList, Bool.and_eq_true] at ground
        simp [applySubst.applySubstList, applySubst_of_ground σ child ground.1, listCase rest ground.2]

theorem isGroundList_of_mem {children : List Atom} (ground : isGroundAtom.isGroundList children = true)
    {child : Atom} (member : child ∈ children) : isGroundAtom child = true := by
  induction children with
  | nil => simp at member
  | cons head tail ih =>
      simp only [isGroundAtom.isGroundList, Bool.and_eq_true] at ground
      rcases List.mem_cons.1 member with rfl | inTail
      · exact ground.1
      · exact ih ground.2 inTail

theorem zip_all_eq_iff : ∀ (lefts rights : List Atom), lefts.length = rights.length →
    (((lefts.zip rights).all fun equation => decide (equation.1 = equation.2)) = true ↔ lefts = rights)
  | [], [], _ => by simp
  | [], _ :: _, sameLength => by simp at sameLength
  | _ :: _, [], sameLength => by simp at sameLength
  | left :: lefts, right :: rights, sameLength => by
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true, decide_eq_true_eq,
        List.cons.injEq]
      rw [zip_all_eq_iff lefts rights (by simpa using sameLength)]

/-- **Equations between ground atoms are solved exactly when each is an identity.** -/
theorem solveWithin_ground (eliminate : Equations → Subst → Unification) :
    ∀ (fuel : ℕ) (equations : Equations) (θ : Subst),
      (∀ equation ∈ equations, isGroundAtom equation.1 = true ∧ isGroundAtom equation.2 = true) →
      equationsSize equations < fuel →
        solveWithin eliminate fuel equations θ =
          if (equations.all fun equation => decide (equation.1 = equation.2)) then .solved θ
          else .clash
  | 0, _, _, _, small => absurd small (Nat.not_lt_zero _)
  | _ + 1, [], θ, _, _ => by simp [solveWithin]
  | fuel + 1, (left, right) :: rest, θ, ground, small => by
      have leftGround := (ground (left, right) List.mem_cons_self).1
      have rightGround := (ground (left, right) List.mem_cons_self).2
      have restGround : ∀ equation ∈ rest,
          isGroundAtom equation.1 = true ∧ isGroundAtom equation.2 = true :=
        fun equation member => ground equation (List.mem_cons_of_mem _ member)
      have leftPos := atomSize_pos left
      have rightPos := atomSize_pos right
      simp only [equationsSize] at small
      by_cases same : left = right
      · simp only [solveWithin, same, if_true, List.all_cons, decide_true, Bool.true_and]
        exact solveWithin_ground eliminate fuel rest θ restGround (by omega)
      · simp only [solveWithin, same, if_false, List.all_cons, decide_false, Bool.false_and,
          Bool.false_eq_true]
        cases left with
        | var _ => simp [isGroundAtom] at leftGround
        | symbol _ =>
            cases right with
            | var _ => simp [isGroundAtom] at rightGround
            | symbol _ => rfl
            | grounded _ => rfl
            | expression _ => rfl
        | grounded _ =>
            cases right with
            | var _ => simp [isGroundAtom] at rightGround
            | symbol _ => rfl
            | grounded _ => rfl
            | expression _ => rfl
        | expression lefts =>
            cases right with
            | var _ => simp [isGroundAtom] at rightGround
            | symbol _ => rfl
            | grounded _ => rfl
            | expression rights =>
                simp only
                split
                · rename_i sameLength
                  have zippedGround : ∀ equation ∈ lefts.zip rights ++ rest,
                      isGroundAtom equation.1 = true ∧ isGroundAtom equation.2 = true := by
                    intro equation member
                    rcases List.mem_append.1 member with zipped | inRest
                    · obtain ⟨leftChild, rightChild⟩ := equation
                      have members := List.of_mem_zip zipped
                      exact ⟨isGroundList_of_mem (by simpa [isGroundAtom] using leftGround) members.1,
                        isGroundList_of_mem (by simpa [isGroundAtom] using rightGround) members.2⟩
                    · exact restGround equation inRest
                  rw [solveWithin_ground eliminate fuel _ θ zippedGround (by
                    rw [equationsSize_append, equationsSize_zip lefts rights sameLength]
                    simp only [atomSize] at small
                    omega)]
                  have different : lefts ≠ rights := fun equal => same (by rw [equal])
                  have notAll : ((lefts.zip rights).all fun equation =>
                      decide (equation.1 = equation.2)) = false := by
                    cases allEq : ((lefts.zip rights).all fun equation =>
                        decide (equation.1 = equation.2)) with
                    | false => rfl
                    | true => exact absurd ((zip_all_eq_iff lefts rights sameLength).1 allEq) different
                  simp [List.all_append, notAll]
                · rfl

/-- **Ground atoms unify exactly when they are equal.** -/
theorem unifyOption_ground (θ : Subst) (left right : Atom) (leftGround : isGroundAtom left = true)
    (rightGround : isGroundAtom right = true) :
    unifyOption θ [(left, right)] = if left = right then some θ else none := by
  unfold unifyOption unifyUnder
  simp only [List.map_cons, List.map_nil, applySubst_of_ground θ left leftGround,
    applySubst_of_ground θ right rightGround]
  have vars : equationsVars [(left, right)] = [] := by
    simp [equationsVars, atomFreeVars_of_ground _ leftGround, atomFreeVars_of_ground _ rightGround]
  rw [vars]
  simp only [List.length_nil, solveEquations]
  rw [solveWithin_ground _ _ _ θ (by simp [leftGround, rightGround]) (Nat.lt_succ_self _)]
  by_cases same : left = right <;> simp [same]

/-- **Binding a variable to a ground value** is one elimination. -/
theorem unifyOption_var_ground (θ : Subst) (name : String) (value : Atom)
    (unbound : Subst.lookup θ name = none) (ground : isGroundAtom value = true) :
    unifyOption θ [(.var name, value)] = some (bindSolved θ name value) := by
  have noVars := atomFreeVars_of_ground value ground
  have notVar : (Atom.var name = value) ↔ False := by
    constructor
    · rintro rfl; simp [isGroundAtom] at ground
    · exact False.elim
  simp only [unifyOption, unifyUnder, List.map_cons, List.map_nil, applySubst, unbound,
    Option.getD_none, applySubst_of_ground θ value ground]
  have vars : equationsVars [(.var name, value)] = [name] := by
    simp [equationsVars, atomFreeVars, noVars]
  rw [vars]
  simp only [List.length_singleton, solveEquations, equationsSize, solveWithin, notVar,
    if_false, noVars, List.contains_nil, Bool.false_eq_true, substituteEquations, List.map_nil]

/-! ### Renaming apart and the level reading of `!=` -/

/-- The longest variable name of an atom. -/
def longestVariable (atom : Atom) : ℕ :=
  ((atomFreeVars atom).map String.length).foldl max 0

/-- The variable tag of factor `index` in a firing of `directive`: longer than every
variable of the directive, and different for different indices, so renamed stored atoms
share no variable with the directive or with each other. -/
def factorTag (directive : Atom) (index : ℕ) : String :=
  String.ofList (List.replicate (longestVariable directive + 1) '#') ++ toString index ++ "|"

/-- A stored atom with every variable renamed by a tag. -/
def renameApart (tag : String) (atom : Atom) : Atom :=
  applySubst ((atomFreeVars atom).map fun name => (name, .var (tag ++ name))) atom

theorem renameApart_ground (tag : String) (atom : Atom) (ground : isGroundAtom atom = true) :
    renameApart tag atom = atom := by
  simp [renameApart, atomFreeVars_of_ground atom ground, applySubst_nil]

/-- The kernel's reading of an atom's variables by encoding level.  A first occurrence
introduces level `base` plus the number of earlier first occurrences; a repeated
occurrence names the index of its first occurrence among this atom's own first
occurrences, without `base`. -/
def levelRead (base : ℕ) : List String → Atom → Atom × List String
  | seen, .var name =>
      match compactVariableIndex name seen with
      | some index => (.var (toString index), seen)
      | none => (.var (toString (base + seen.length)), seen ++ [name])
  | seen, .symbol name => (.symbol name, seen)
  | seen, .grounded value => (.grounded value, seen)
  | seen, .expression children =>
      let read := levelReadList base seen children
      (.expression read.1, read.2)
where
  levelReadList (base : ℕ) : List String → List Atom → List Atom × List String
    | seen, [] => ([], seen)
    | seen, atom :: rest =>
        let first := levelRead base seen atom
        let others := levelReadList base first.2 rest
        (first.1 :: others.1, others.2)

/-- How `(!= P W)` reads a stored atom and a different stored atom.  The kernel encodes
the pair as one expression without shifting the second atom (`==` shifts its copy), so the
second atom's first occurrences continue the first atom's levels while its repeated
variables keep their own indices: when the first atom has variables, a repeated variable
of the second atom refers to a variable of the first. -/
def neqReading (first second : Atom) : Atom × Atom :=
  let left := levelRead 0 [] first
  (left.1, (levelRead left.2.length [] second).1)

/-! ## Sources -/

/-- Rows of one factor over the read copy, extending the substitution of the factors
before it.  Each stored atom is renamed apart with the factor's tag.  `(BTM p)` unifies
`p` with a stored atom; `(== P W)` unifies `P` with a stored atom and `W` with an
independent copy of it; `(!= P W)` unifies `P` and `W` with the level reading of a stored
atom and a stored atom of a different key; files and solver models come from the external
state. -/
def sourceRows (prims : Primitives) (external : ExternalState) (tag : ℕ → String)
    (index : ℕ) (θ : Subst) (read : List Atom) : MainlineSource → List Subst
  | .core (.btm pattern) =>
      read.filterMap fun stored => unifyOption θ [(pattern, renameApart (tag (2 * index)) stored)]
  | .core (.eqConstraint pattern witness) =>
      read.filterMap fun stored =>
        unifyOption θ [(pattern, renameApart (tag (2 * index)) stored),
          (witness, renameApart (tag (2 * index + 1)) stored)]
  | .core (.neqConstraint pattern witness) =>
      read.flatMap fun stored =>
        (read.filter fun other => !sameMorkSupportAtom other stored).filterMap fun other =>
          unifyOption θ [(pattern, renameApart (tag (2 * index)) (neqReading stored other).1),
            (witness, renameApart (tag (2 * index)) (neqReading stored other).2)]
  | .act file pattern =>
      ((external.files file).getD []).filterMap fun stored =>
        unifyOption θ [(pattern, renameApart (tag (2 * index)) stored)]
  | .z3 solver pattern =>
      (((external.solvers solver).map prims.model).getD []).filterMap fun stored =>
        unifyOption θ [(pattern, renameApart (tag (2 * index)) stored)]

/-- The relational product of factors, threading the substitution. -/
def productRows (prims : Primitives) (external : ExternalState) (tag : ℕ → String)
    (read : List Atom) : ℕ → Subst → List MainlineSource → List Subst
  | _, θ, [] => [θ]
  | index, θ, source :: rest =>
      (sourceRows prims external tag index θ read source).flatMap fun next =>
        productRows prims external tag read (index + 1) next rest

/-- The rows of a comma conjunction: each pattern, in order, unified with a renamed stored
atom. -/
def conjunctionRows (tag : ℕ → String) (read : List Atom) : ℕ → Subst → List Atom → List Subst
  | _, θ, [] => [θ]
  | index, θ, pattern :: rest =>
      (read.filterMap fun stored => unifyOption θ [(pattern, renameApart (tag index) stored)]).flatMap
        fun next => conjunctionRows tag read (index + 1) next rest

/-- The resource a factor opens before matching starts, if it is missing. -/
def missingResource (external : ExternalState) : MainlineSource → Option MainlineFault
  | .act file _ => if (external.files file).isSome then none else some (.missingFile file)
  | .z3 solver _ => if (external.solvers solver).isSome then none else some (.missingSolver solver)
  | .core _ => none

/-- The solved substitutions of an input over the read copy.  Every file and solver is
opened before any row is produced, so a missing one aborts whether or not a row would
reach it. -/
def mainlineRows (prims : Primitives) (external : ExternalState) (tag : ℕ → String)
    (read : List Atom) : MainlineInput → Except MainlineFault (List Subst)
  | .compat patterns => .ok (conjunctionRows tag read 0 [] patterns)
  | .explicit sources =>
      match sources.findSome? (missingResource external) with
      | some fault => .error fault
      | none => .ok (productRows prims external tag read 0 [] sources)

/-- The row a solved substitution gives the outputs: the value of each input variable. -/
def inputRow (names : List String) (θ : Subst) : Subst :=
  names.map fun name => (name, applySubst θ (.var name))

/-- **Over ground atoms, a ground pattern finds its copies**: one row, the substitution
unchanged, for each stored atom equal to the pattern. -/
theorem conjunctionRows_single_ground (tag : ℕ → String) (index : ℕ) (θ : Subst) (pattern : Atom)
    (groundPattern : isGroundAtom pattern = true) :
    ∀ (read : List Atom), (∀ atom ∈ read, isGroundAtom atom = true) →
      conjunctionRows tag read index θ [pattern] =
        (read.filter fun atom => atom = pattern).map fun _ => θ
  | [], _ => rfl
  | stored :: rest, groundRead => by
      have storedGround := groundRead stored List.mem_cons_self
      have restRows := conjunctionRows_single_ground tag index θ pattern groundPattern rest
        (fun atom member => groundRead atom (List.mem_cons_of_mem _ member))
      simp only [conjunctionRows, List.flatMap_singleton'] at restRows ⊢
      rw [List.filterMap_cons, renameApart_ground _ stored storedGround,
        unifyOption_ground θ pattern stored groundPattern storedGround]
      by_cases same : stored = pattern
      · subst same
        simp only [if_true, List.filter_cons, decide_true, List.map_cons, List.cons.injEq, true_and]
        exact restRows
      · have different : ¬ pattern = stored := fun equal => same equal.symm
        simp only [different, if_false, List.filter_cons, same, decide_false, Bool.false_eq_true]
        exact restRows

/-- The factor that has the same variables as a mainline factor.  Output coverage
depends only on which variables an input mentions. -/
def MainlineSource.coverageFactor : MainlineSource → SourceFactor
  | .core factor => factor
  | .act _ pattern => .btm pattern
  | .z3 _ pattern => .btm pattern

/-- The input specification used for rule-scoped output coverage. -/
def MainlineInput.coverage : MainlineInput → InputSpec
  | .compat patterns => .compat ⟨patterns⟩
  | .explicit sources => .explicit (sources.map MainlineSource.coverageFactor)

/-! ## Staging -/

/-- The template a sink instantiates on each row. -/
def MainlineSink.template : MainlineSink → Atom
  | .core sink => sink.atom
  | .unify body => body
  | .antiUnify body => body
  | .aggregate _ context count payload => .expression [context, count, payload]
  | .act _ body => body
  | .pure template result call => .expression [template, result, call]
  | .z3 _ statement => statement
  | .wasm _ body => body

/-- One instance per row that binds the template's input variables, repeats included. -/
def instances (input : InputSpec) (rows : List Subst) (template : Atom) : List Atom :=
  rows.filterMap fun row => instantiateRuleTemplateAtom? input row template

/-- The staged support of a template: its instances with repeated physical keys removed. -/
def staged (input : InputSpec) (rows : List Subst) (template : Atom) : List Atom :=
  (instances input rows template).foldl morkInsertSupport []

theorem foldl_stage_eq (input : InputSpec) (sink : Sink) :
    ∀ (rows : List Subst) (accumulated : List Atom),
      rows.foldl (stageRuleScopedSink input sink) accumulated =
        (rows.filterMap fun row => instantiateRuleTemplateAtom? input row sink.atom).foldl
          morkInsertSupport accumulated
  | [], _ => rfl
  | row :: rest, accumulated => by
      simp only [List.foldl_cons, List.filterMap_cons, stageRuleScopedSink]
      cases instantiateRuleTemplateAtom? input row sink.atom with
      | none => exact foldl_stage_eq input sink rest accumulated
      | some instantiated => exact foldl_stage_eq input sink rest _

/-- The core stage of the rule-scoped executor is `staged`. -/
theorem stage_eq_staged (input : InputSpec) (rows : List Subst) (sink : Sink) :
    rows.foldl (stageRuleScopedSink input sink) [] = staged input rows sink.atom :=
  foldl_stage_eq input sink rows []

/-! ## Finalization -/

/-- Atoms an eager sink writes while the matches are enumerated. -/
def eagerOutputs (prims : Primitives) (input : InputSpec) (rows : List Subst) :
    MainlineSink → List Atom
  | .core (.add body) => staged input rows body
  | .wasm program body => (staged input rows body).filterMap (prims.wasm program)
  | _ => []

/-- The value of an aggregate over one group's payloads.  `count` writes the decimal
number of distinct payloads; the numeric aggregates are primitives. -/
def aggregateValue (prims : Primitives) : AggregateKind → List Atom → Option Atom
  | .count, payloads => some (.symbol (toString payloads.length))
  | kind, payloads => prims.aggregate kind payloads

/-- The group key `(C N)` of a staged aggregate instance `(C N P)`. -/
def groupKey : Atom → Option Atom
  | .expression [context, count, _] => some (.expression [context, count])
  | _ => none

/-- Distinct group keys of a staged aggregate. -/
def groupKeys (triples : List Atom) : List Atom :=
  (triples.filterMap groupKey).foldl morkInsertSupport []

/-- The payloads of one group. -/
def groupPayloads (triples : List Atom) (key : Atom) : List Atom :=
  triples.filterMap fun triple =>
    match triple with
    | .expression [context, count, payload] =>
        if sameMorkSupportAtom (.expression [context, count]) key then some payload else none
    | _ => none

/-- What one aggregate group writes.  A count position that is a variable of the
context receives the value; a literal equal to the value, or a fresh variable, writes
the context itself, which the kernel keys correctly only when the template context is a
variable. -/
def aggregateWrite (templateContext context count value : Atom) :
    Except MainlineFault (Option Atom) :=
  let guarded : Except MainlineFault (Option Atom) :=
    match templateContext with
    | .var _ => .ok (some context)
    | _ => .error (.misKeyedAggregate templateContext)
  match count with
  | .var name =>
      if (atomFreeVars context).contains name then
        .ok (some (applySubst [(name, value)] context))
      else guarded
  | .symbol _ => if count = value then guarded else .ok none
  | _ => .ok none

/-- What one staged `pure` instance `(T R C)` writes.  A result variable of the template
receives the call's value; a fresh result variable writes the template unevaluated; any
other result position is unimplemented in the kernel. -/
def pureWrite (prims : Primitives) (form template result call : Atom) :
    Except MainlineFault (Option Atom) :=
  match result with
  | .var name =>
      if (atomFreeVars template).contains name then
        .ok ((prims.eval call).map fun value => applySubst [(name, value)] template)
      else .ok (some template)
  | _ => .error (.unimplementedPureShape form)

/-- The atoms a list of optional writes contributes. -/
def written (writes : List (Option Atom)) : List Atom := writes.filterMap id

/-- What an aggregate sink writes, group by group, or the fault that stops it. -/
def aggregateWrites (prims : Primitives) (input : InputSpec) (rows : List Subst)
    (kind : AggregateKind) (context count payload : Atom) : Except MainlineFault (List (Option Atom)) :=
  let triples := staged input rows (.expression [context, count, payload])
  (groupKeys triples).mapM fun key =>
    match key with
    | .expression [groupContext, groupCount] =>
        match aggregateValue prims kind (groupPayloads triples key) with
        | some value => aggregateWrite context groupContext groupCount value
        | none => .error (.aggregateValue payload)
    | _ => .ok none

/-- What a `pure` sink writes, instance by instance, or the fault that stops it. -/
def pureWrites (prims : Primitives) (input : InputSpec) (rows : List Subst)
    (template result call : Atom) : Except MainlineFault (List (Option Atom)) :=
  (staged input rows (.expression [template, result, call])).mapM fun triple =>
    match triple with
    | .expression [instanceTemplate, instanceResult, instanceCall] =>
        pureWrite prims (.expression [template, result, call]) instanceTemplate instanceResult
          instanceCall
    | _ => .ok none

/-- Finalize one sink, from left to right after the eager writes. -/
def finalizeMainlineSink (prims : Primitives) (input : InputSpec) (rows : List Subst)
    (state : List Atom × ExternalState) (sink : MainlineSink) :
    Except MainlineFault (List Atom × ExternalState) :=
  let space := state.1
  let external := state.2
  match sink with
  | .core (.add _) => .ok state
  | .wasm .. => .ok state
  | .core (.remove body) => .ok (morkSubtractSupport space (staged input rows body), external)
  | .core (.head count body) =>
      if (((instances input rows body).map morkSupportKey).Nodup ∨
          (staged input rows body).length < count) then
        .ok (finalizeRuleScopedSink (.head count body) (staged input rows body) space, external)
      else .error (.extremaDuplicate body)
  | .core (.tail count body) =>
      if (((instances input rows body).map morkSupportKey).Nodup ∨
          (staged input rows body).length < count) then
        .ok (finalizeRuleScopedSink (.tail count body) (staged input rows body) space, external)
      else .error (.extremaDuplicate body)
  | .unify body =>
      match staged input rows body with
      | [] => .ok state
      | batch@(_ :: _) =>
          match prims.unify batch with
          | some unified => .ok (morkInsertSupport space unified, external)
          | none => .ok state
  | .antiUnify body =>
      if (instances input rows body).length = 1 then .error (.antiUnifySingleRow body)
      else
        match staged input rows body with
        | [] => .ok state
        | batch@(_ :: _) =>
            match prims.antiUnify batch with
            | some general => .ok (morkInsertSupport space general, external)
            | none => .ok state
  | .aggregate kind context count payload =>
      match aggregateWrites prims input rows kind context count payload with
      | .ok writes => .ok (morkUnionSupport space (written writes), external)
      | .error fault => .error fault
  | .act file body =>
      .ok (space, { external with
        files := Function.update external.files file (some (staged input rows body)) })
  | .z3 solver statement =>
      .ok (space, { external with
        solvers := Function.update external.solvers solver
          (some ((external.solvers solver).getD [] ++ staged input rows statement)) })
  | .pure template result call =>
      match pureWrites prims input rows template result call with
      | .ok writes => .ok (morkUnionSupport space (written writes), external)
      | .error fault => .error fault

/-- Apply a whole output: eager writes, then every sink finalized from left to right. -/
def applyMainlineSinks (prims : Primitives) (input : InputSpec) (rows : List Subst)
    (space : List Atom) (external : ExternalState) (sinks : List MainlineSink) :
    Except MainlineFault (List Atom × ExternalState) :=
  let eager := sinks.foldl (fun current sink =>
    morkUnionSupport current (eagerOutputs prims input rows sink)) space
  sinks.foldlM (finalizeMainlineSink prims input rows) (eager, external)

/-- **One firing.**  The selected directive leaves the live space, its input is matched
against the read copy that contains it, and its output is applied to the live space. -/
def fireDirective (prims : Primitives) (external : ExternalState) (space : List Atom)
    (directive : MainlineDirective) : Except MainlineFault (List Atom × ExternalState) := do
  let live := morkEraseSupport space directive.atom
  let read := morkInsertSupport live directive.atom
  let solved ← mainlineRows prims external (factorTag directive.atom) read directive.input
  let input := directive.input.coverage
  let rows := solved.map (inputRow (inputSpecVariables input))
  match directive.output with
  | .compat templates =>
      pure (templates.foldl (fun current template =>
        morkUnionSupport current (staged input rows template)) live, external)
  | .sinks sinks => applyMainlineSinks prims input rows live external sinks

/-- The result of one scheduler step. -/
inductive StepOutcome where
  /-- No `(exec …)` atom remains. -/
  | quiescent
  /-- The least directive fired, or was consumed without effect. -/
  | next (space : List Atom) (external : ExternalState)
  /-- The kernel panicked: the run ends without a final space. -/
  | aborted (fault : MainlineFault)

/-- **One step of the kernel.**  The least `(exec …)` atom by compact key is removed and
interpreted.  A directive of the wrong shape is consumed with no effect. -/
def mainlineStep (profile : BuildProfile) (prims : Primitives) (external : ExternalState)
    (space : List Atom) : StepOutcome :=
  match selectNextScheduled (WQComputable.cRawExecFacts space) with
  | none => .quiescent
  | some raw =>
      match decodeDirective profile raw with
      | .error fault => .aborted fault
      | .ok none => .next (morkEraseSupport space raw.atom) external
      | .ok (some directive) =>
          match fireDirective prims external space directive with
          | .error fault => .aborted fault
          | .ok (next, after) => .next next after

/-- The space after a step, if the step fired or consumed a directive. -/
def StepOutcome.space? : StepOutcome → Option (List Atom)
  | .next space _ => some space
  | _ => none

/-- The fault that ended a step, if it aborted. -/
def StepOutcome.fault? : StepOutcome → Option MainlineFault
  | .aborted fault => some fault
  | _ => none

/-- Runs with exact fuel: the final space, the external state, and the fault that ended
the run, if any. -/
def mainlineRun (profile : BuildProfile) (prims : Primitives) :
    ℕ → ExternalState → List Atom → List Atom × ExternalState × Option MainlineFault
  | 0, external, space => (space, external, none)
  | fuel + 1, external, space =>
      match mainlineStep profile prims external space with
      | .quiescent => (space, external, none)
      | .aborted fault => (space, external, some fault)
      | .next next after => mainlineRun profile prims fuel after next


/-! ## Laws -/

/-- Primitives that never compute anything: every call errs, batches never unify, and
solvers report empty models.  Used where a law or example involves no foreign code. -/
def inertPrimitives : Primitives :=
  ⟨fun _ => none, fun _ => none, fun _ => none, fun _ _ => none, fun _ => [], fun _ _ => none⟩

/-! ### Idle firings -/

theorem staged_no_rows (input : InputSpec) (template : Atom) : staged input [] template = [] := rfl

/-- With no rows, no sink changes the space.  An `ACT` sink still empties its file and a
`z3` sink still creates its solver. -/
theorem finalizeMainlineSink_no_rows (prims : Primitives) (input : InputSpec)
    (space : List Atom) (external : ExternalState) (sink : MainlineSink) :
    ∃ after, finalizeMainlineSink prims input [] (space, external) sink = .ok (space, after) := by
  cases sink with
  | core sink =>
      cases sink with
      | add _ => exact ⟨external, rfl⟩
      | remove _ => exact ⟨external, rfl⟩
      | head count body =>
          refine ⟨external, ?_⟩
          simp [finalizeMainlineSink, instances, staged, finalizeRuleScopedSink, morkUnionSupport,
            compactExtremaList]
      | tail count body =>
          refine ⟨external, ?_⟩
          simp [finalizeMainlineSink, instances, staged, finalizeRuleScopedSink, morkUnionSupport,
            compactExtremaList]
  | unify _ => exact ⟨external, rfl⟩
  | antiUnify _ => exact ⟨external, rfl⟩
  | aggregate kind context count payload => exact ⟨external, rfl⟩
  | act file body => exact ⟨_, rfl⟩
  | pure template result call => exact ⟨external, rfl⟩
  | z3 solver statement => exact ⟨_, rfl⟩
  | wasm program body => exact ⟨external, rfl⟩

theorem eager_no_rows (prims : Primitives) (input : InputSpec) :
    ∀ (sinks : List MainlineSink) (space : List Atom),
      sinks.foldl (fun current sink => morkUnionSupport current (eagerOutputs prims input [] sink))
        space = space
  | [], _ => rfl
  | sink :: rest, space => by
      have none : eagerOutputs prims input [] sink = [] := by
        cases sink with
        | core sink => cases sink <;> rfl
        | wasm _ _ => rfl
        | _ => rfl
      simp only [List.foldl_cons, none]
      exact eager_no_rows prims input rest space

theorem foldl_finalize_no_rows (prims : Primitives) (input : InputSpec) (space : List Atom) :
    ∀ (sinks : List MainlineSink) (external : ExternalState),
      ∃ after, sinks.foldlM (finalizeMainlineSink prims input []) (space, external) =
        .ok (space, after)
  | [], external => ⟨external, rfl⟩
  | sink :: rest, external => by
      obtain ⟨middle, first⟩ := finalizeMainlineSink_no_rows prims input space external sink
      obtain ⟨after, tail⟩ := foldl_finalize_no_rows prims input space rest middle
      exact ⟨after, by simp [List.foldlM_cons, first, tail, bind, Except.bind]⟩

/-- **An idle firing only removes its directive.** -/
theorem fireDirective_no_rows (prims : Primitives) (external : ExternalState)
    (space : List Atom) (directive : MainlineDirective)
    (idle : mainlineRows prims external (factorTag directive.atom)
      (morkInsertSupport (morkEraseSupport space directive.atom) directive.atom)
      directive.input = .ok []) :
    ∃ after, fireDirective prims external space directive =
      .ok (morkEraseSupport space directive.atom, after) := by
  obtain ⟨atom, input, output⟩ := directive
  simp only at idle
  cases output with
  | compat templates =>
      refine ⟨external, ?_⟩
      have keep : ∀ (templates current : List Atom),
          templates.foldl (fun current template =>
            morkUnionSupport current (staged input.coverage [] template)) current = current := by
        intro templates
        induction templates with
        | nil => intro current; rfl
        | cons head tail ih => intro current; exact ih current
      simp [fireDirective, idle, bind, Except.bind, keep, pure, Except.pure]
  | sinks sinks =>
      simp only [fireDirective, idle, bind, Except.bind]
      show ∃ after, applyMainlineSinks prims input.coverage [] (morkEraseSupport space atom)
        external sinks = .ok (morkEraseSupport space atom, after)
      simp only [applyMainlineSinks, eager_no_rows]
      exact foldl_finalize_no_rows prims _ _ sinks external

/-! ### Every factor is monotone in the read copy -/

/-- Each factor's rows over a smaller read copy are rows over a larger one.  Files and
solver models do not depend on the read copy at all. -/
theorem sourceRows_mono (prims : Primitives) (external : ExternalState) (tag : ℕ → String)
    (index : ℕ) (θ : Subst) {small large : List Atom} (included : ∀ atom ∈ small, atom ∈ large)
    (source : MainlineSource) :
    ∀ row ∈ sourceRows prims external tag index θ small source,
      row ∈ sourceRows prims external tag index θ large source := by
  intro row member
  cases source with
  | core factor =>
      cases factor with
      | btm pattern =>
          simp only [sourceRows, List.mem_filterMap] at member ⊢
          obtain ⟨atom, atomMember, found⟩ := member
          exact ⟨atom, included atom atomMember, found⟩
      | eqConstraint pattern witness =>
          simp only [sourceRows, List.mem_filterMap] at member ⊢
          obtain ⟨atom, atomMember, found⟩ := member
          exact ⟨atom, included atom atomMember, found⟩
      | neqConstraint pattern witness =>
          simp only [sourceRows, List.mem_flatMap, List.mem_filterMap, List.mem_filter] at member ⊢
          obtain ⟨atom, atomMember, other, ⟨otherMember, distinct⟩, found⟩ := member
          exact ⟨atom, included atom atomMember, other, ⟨included other otherMember, distinct⟩, found⟩
  | act file pattern => exact member
  | z3 solver pattern => exact member

theorem productRows_mono (prims : Primitives) (external : ExternalState) (tag : ℕ → String)
    {small large : List Atom} (included : ∀ atom ∈ small, atom ∈ large) :
    ∀ (sources : List MainlineSource) (index : ℕ) (θ : Subst),
      ∀ row ∈ productRows prims external tag small index θ sources,
        row ∈ productRows prims external tag large index θ sources
  | [], _, _ => fun row member => member
  | source :: rest, index, θ => by
      intro row member
      simp only [productRows, List.mem_flatMap] at member ⊢
      obtain ⟨found, foundMember, nested⟩ := member
      exact ⟨found, sourceRows_mono prims external tag index θ included source found foundMember,
        productRows_mono prims external tag included rest (index + 1) found row nested⟩

theorem conjunctionRows_mono (tag : ℕ → String) {small large : List Atom}
    (included : ∀ atom ∈ small, atom ∈ large) :
    ∀ (patterns : List Atom) (index : ℕ) (θ : Subst),
      ∀ row ∈ conjunctionRows tag small index θ patterns,
        row ∈ conjunctionRows tag large index θ patterns
  | [], _, _ => fun row member => member
  | pattern :: rest, index, θ => by
      intro row member
      simp only [conjunctionRows, List.mem_flatMap, List.mem_filterMap] at member ⊢
      obtain ⟨found, ⟨atom, atomMember, unified⟩, nested⟩ := member
      exact ⟨found, ⟨atom, included atom atomMember, unified⟩,
        conjunctionRows_mono tag included rest (index + 1) found row nested⟩

/-- **Every input is monotone in the read copy**, and whether it aborts does not depend
on the read copy. -/
theorem mainlineRows_mono (prims : Primitives) (external : ExternalState) (tag : ℕ → String)
    {small large : List Atom} (included : ∀ atom ∈ small, atom ∈ large)
    (input : MainlineInput) {smallRows largeRows : List Subst}
    (smallOk : mainlineRows prims external tag small input = .ok smallRows)
    (largeOk : mainlineRows prims external tag large input = .ok largeRows) :
    ∀ row ∈ smallRows, row ∈ largeRows := by
  cases input with
  | compat patterns =>
      simp only [mainlineRows, Except.ok.injEq] at smallOk largeOk
      subst smallOk largeOk
      exact conjunctionRows_mono tag included patterns 0 []
  | explicit sources =>
      unfold mainlineRows at smallOk largeOk
      cases missing : sources.findSome? (missingResource external) with
      | some fault => simp [missing] at smallOk
      | none =>
          simp only [missing, Except.ok.injEq] at smallOk largeOk
          subst smallOk largeOk
          exact productRows_mono prims external tag included sources 0 []

theorem mainlineRows_aborts_independently (prims : Primitives) (external : ExternalState)
    (tag : ℕ → String) (small large : List Atom) (input : MainlineInput) :
    (∃ rows, mainlineRows prims external tag small input = .ok rows) ↔
      (∃ rows, mainlineRows prims external tag large input = .ok rows) := by
  cases input with
  | compat patterns => exact ⟨fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩⟩
  | explicit sources =>
      cases found : sources.findSome? (missingResource external) with
      | some fault => simp [mainlineRows, found]
      | none => simp [mainlineRows, found]

/-! ### The rule-scoped executor is the add-first fragment -/

theorem eagerOutputs_add (prims : Primitives) (input : InputSpec) (rows : List Subst)
    (body : Atom) : eagerOutputs prims input rows (.core (.add body)) = staged input rows body := rfl

theorem eagerOutputs_remove (prims : Primitives) (input : InputSpec) (rows : List Subst)
    (body : Atom) : eagerOutputs prims input rows (.core (.remove body)) = [] := rfl

theorem eagerOutputs_head (prims : Primitives) (input : InputSpec) (rows : List Subst)
    (count : ℕ) (body : Atom) : eagerOutputs prims input rows (.core (.head count body)) = [] := rfl

theorem eagerOutputs_tail (prims : Primitives) (input : InputSpec) (rows : List Subst)
    (count : ℕ) (body : Atom) : eagerOutputs prims input rows (.core (.tail count body)) = [] := rfl

theorem union_nil (space : List Atom) : morkUnionSupport space [] = space := rfl

theorem eager_core (prims : Primitives) (input : InputSpec) (rows : List Subst) :
    ∀ (sinks : List Sink) (space : List Atom),
      (sinks.map MainlineSink.core).foldl
          (fun current sink => morkUnionSupport current (eagerOutputs prims input rows sink)) space =
        eagerWrites input rows space sinks
  | [], _ => rfl
  | sink :: rest, space => by
      rw [List.map_cons, List.foldl_cons]
      cases sink with
      | add body =>
          rw [eagerOutputs_add, eager_core prims input rows rest]
          simp only [eagerWrites, List.foldl_cons, writesEagerly, if_true, finalizeRuleScopedSink,
            stage_eq_staged, Sink.atom]
      | remove body =>
          rw [eagerOutputs_remove, union_nil, eager_core prims input rows rest]
          simp only [eagerWrites, List.foldl_cons, writesEagerly]
          rfl
      | head count body =>
          rw [eagerOutputs_head, union_nil, eager_core prims input rows rest]
          simp only [eagerWrites, List.foldl_cons, writesEagerly]
          rfl
      | tail count body =>
          rw [eagerOutputs_tail, union_nil, eager_core prims input rows rest]
          simp only [eagerWrites, List.foldl_cons, writesEagerly]
          rfl

/-- A core sink that is an add or a remove. -/
def addOrRemove : Sink → Bool
  | .add _ | .remove _ => true
  | _ => false

theorem finalize_core_addRemove (prims : Primitives) (input : InputSpec) (rows : List Subst)
    (external : ExternalState) :
    ∀ (sinks : List Sink) (space : List Atom), (∀ sink ∈ sinks, addOrRemove sink = true) →
      (sinks.map MainlineSink.core).foldlM (finalizeMainlineSink prims input rows) (space, external) =
        .ok (ruleScopedBatch input rows space (sinks.filter fun sink => !writesEagerly sink), external)
  | [], _, _ => rfl
  | sink :: rest, space, admitted => by
      have restAdmitted : ∀ other ∈ rest, addOrRemove other = true :=
        fun other member => admitted other (by simp [member])
      cases sink with
      | add body =>
          simp only [List.map_cons, List.foldlM_cons, finalizeMainlineSink, writesEagerly,
            List.filter_cons, Bool.not_true]
          exact finalize_core_addRemove prims input rows external rest space restAdmitted
      | remove body =>
          simp only [List.map_cons, List.foldlM_cons, finalizeMainlineSink, writesEagerly,
            List.filter_cons, Bool.not_false, if_true, bind, Except.bind]
          rw [finalize_core_addRemove prims input rows external rest _ restAdmitted]
          simp only [ruleScopedBatch, cApplyRuleScopedSinkBatch, finalizeRuleScopedSink,
            stage_eq_staged, Sink.atom]
          rfl
      | head count body => simp [addOrRemove] at admitted
      | tail count body => simp [addOrRemove] at admitted

/-- **Conservativity over the rule-scoped executor.**  On add and remove sinks with every
add first, the mainline output is the left-to-right batch. -/
theorem applyMainlineSinks_core (prims : Primitives) (input : InputSpec) (rows : List Subst)
    (space : List Atom) (external : ExternalState) (adds rest : List Sink)
    (eager : ∀ sink ∈ adds, writesEagerly sink = true)
    (removes : ∀ sink ∈ rest, ∃ body, sink = .remove body) :
    applyMainlineSinks prims input rows space external ((adds ++ rest).map MainlineSink.core) =
      .ok (ruleScopedBatch input rows space (adds ++ rest), external) := by
  have admitted : ∀ sink ∈ adds ++ rest, addOrRemove sink = true := by
    intro sink member
    rcases List.mem_append.mp member with member | member
    · have isAdd := eager sink member
      cases sink <;> simp_all [writesEagerly, addOrRemove]
    · obtain ⟨body, rfl⟩ := removes sink member
      rfl
  have lazy : ∀ sink ∈ rest, writesEagerly sink = false := by
    intro sink member
    obtain ⟨body, rfl⟩ := removes sink member
    rfl
  unfold applyMainlineSinks
  rw [eager_core, finalize_core_addRemove prims input rows external _ _ admitted,
    ← mainline_eq_ruleScoped_of_addsFirst input rows space adds rest eager lazy]
  rfl

/-! ### Separations from the core factor semantics -/

/-- Factor tags for the examples below; no example directive has a variable named with `#`. -/
def exampleTag (index : ℕ) : String := "#" ++ toString index ++ "|"

/-- `(foo a)` and the stored `(foo $q)`. -/
def fooA : Atom := .expression [.symbol "foo", .symbol "a"]
def fooQ : Atom := .expression [.symbol "foo", .var "q"]

/-- **The kernel unifies; the support model's matcher does not.**  The pattern `(foo a)`
meets the stored `(foo $q)` in the kernel and finds nothing in the one-way matcher shared
by the rule-scoped executor and the support work queue. -/
theorem unification_separates :
    Conformance.Computable.cmatchPattern [] [fooQ] ⟨[fooA]⟩ = [] ∧
      conjunctionRows exampleTag [fooQ] 0 [] [fooA] = [[("#0|q", .symbol "a")]] := by
  decide +kernel

/-- `(VAL s)`. -/
def valAtom (name : String) : Atom := .expression [.symbol "VAL", .symbol name]

/-- **Inequality needs a stored left side.**  Over `(VAL X)` alone, `(!= (VAL Y) $w)` has a
row in the core factor semantics and none in the kernel. -/
theorem neq_requires_stored_left :
    cMatchSourceFactorMork [] [valAtom "X"] (.neqConstraint (valAtom "Y") (.var "w")) =
        [([("w", valAtom "X")], valAtom "X")] ∧
      sourceRows inertPrimitives ExternalState.empty exampleTag 0 [] [valAtom "X"]
        (.core (.neqConstraint (valAtom "Y") (.var "w"))) = [] := by
  decide +kernel

/-- `(pair x y)`. -/
def pairAtom (first second : Atom) : Atom := .expression [.symbol "pair", first, second]

/-- `(pair a a)`, `(pair a b)` and the bare symbol `a`. -/
def pairSpace : List Atom :=
  [pairAtom (.symbol "a") (.symbol "a"), pairAtom (.symbol "a") (.symbol "b"), .symbol "a"]

/-- **Equality is solved jointly with the other factors.**  `(I (== $x $y) (BTM (pair $x $y)))`
has the row `x = y = a` in the kernel; the threaded core semantics looks up the
unbound `$x` and finds nothing. -/
theorem eq_solved_jointly :
    cMatchSourceFactorsMork [] pairSpace
        [.eqConstraint (.var "x") (.var "y"), .btm (pairAtom (.var "x") (.var "y"))] = [] ∧
      productRows inertPrimitives ExternalState.empty exampleTag pairSpace 0 []
        [.core (.eqConstraint (.var "x") (.var "y")), .core (.btm (pairAtom (.var "x") (.var "y")))] =
        [[("y", .symbol "a"), ("x", .symbol "a")]] := by
  decide +kernel

/-- `(p x v)`. -/
def pTriple (first second : String) : Atom := .expression [.symbol "p", .symbol first, .symbol second]

/-- `(exec 0 (, (p $x $v)) (O (count (n $k) $k $v)))`. -/
def countExec : Atom :=
  .expression [.symbol "exec", .grounded (.int 0),
    .expression [.symbol ",", .expression [.symbol "p", .var "x", .var "v"]],
    .expression [.symbol "O",
      .expression [.symbol "count", .expression [.symbol "n", .var "k"], .var "k", .var "v"]]]

/-- **`count` counts distinct payloads and writes a symbol no stored atom contains.**
Three rows with payloads `1`, `1`, `2` give `(n 2)`. -/
theorem count_counts_support :
    (mainlineStep defaultProfile inertPrimitives ExternalState.empty
        [pTriple "a" "1", pTriple "b" "1", pTriple "c" "2", countExec]).space? =
      some [pTriple "a" "1", pTriple "b" "1", pTriple "c" "2",
        .expression [.symbol "n", .symbol "2"]] := by
  decide +kernel


/-! ### Staging is support-valued -/

theorem insert_of_contains (support : List Atom) (atom : Atom)
    (present : morkSupportContains support atom = true) :
    morkInsertSupport support atom = support := by
  simp [morkInsertSupport, present]

theorem foldl_insert_of_all_contained :
    ∀ (support atoms : List Atom), (∀ atom ∈ atoms, morkSupportContains support atom = true) →
      atoms.foldl morkInsertSupport support = support
  | _, [], _ => rfl
  | support, atom :: rest, contained => by
      rw [List.foldl_cons, insert_of_contains support atom (contained atom (by simp))]
      exact foldl_insert_of_all_contained support rest
        (fun other member => contained other (by simp [member]))

theorem contains_of_mem (atoms : List Atom) (atom : Atom) (member : atom ∈ atoms) :
    morkSupportContains atoms atom = true :=
  (morkSupportContains_eq_true_iff_key_mem atoms atom).2 (List.mem_map_of_mem member)

/-- **Repeating every row stages the same support.**  Whatever a sink writes is a
function of its staged support, so no sink can observe how many rows produced an
instance. -/
theorem staged_append_self (input : InputSpec) (rows : List Subst) (template : Atom) :
    staged input (rows ++ rows) template = staged input rows template := by
  unfold staged instances
  rw [List.filterMap_append, List.foldl_append]
  apply foldl_insert_of_all_contained
  intro atom member
  exact morkSupportContains_morkUnionSupport_of_staged_contains_core [] _ atom
    (contains_of_mem _ atom member)

/-- **The kernel's `count` is the support count of the support model's aggregator**, written
as a decimal symbol where the support model writes a grounded integer. -/
theorem count_value_eq_support_count (prims : Primitives) (payloads : List Atom)
    (distinct : payloads.Nodup) :
    aggregateValue prims .count payloads =
        some (.symbol (toString (resultSupport payloads).card)) ∧
      applyAggregator .count payloads = some (.grounded (.int (resultSupport payloads).card)) := by
  refine ⟨?_, rfl⟩
  simp [aggregateValue, resultSupport, List.toFinset_card_of_nodup distinct]

/-! ### A `pure` call returns within its firing -/

/-- `(exec 0 (,) (O (pure (g $r) $r (seven))))`. -/
def pureCallerExec : Atom :=
  .expression [.symbol "exec", .grounded (.int 0), .expression [.symbol ","],
    .expression [.symbol "O",
      .expression [.symbol "pure", .expression [.symbol "g", .var "r"], .var "r",
        .expression [.symbol "seven"]]]]

/-- Primitives whose registry evaluates `(seven)` to `7`. -/
def sevenPrimitives : Primitives :=
  { inertPrimitives with
    eval := fun call => if call = .expression [.symbol "seven"] then some (.symbol "7") else none }

/-- **The caller's own firing writes the call's value.** -/
theorem pure_returns_in_firing :
    (mainlineStep defaultProfile sevenPrimitives ExternalState.empty [pureCallerExec]).space? =
      some [.expression [.symbol "g", .symbol "7"]] := by
  decide +kernel

/-- The value is local to the `pure` sink's template: a sibling sink sees the result
variable unbound.  `(O (pure (g $r) $r (seven)) (+ (sibling $r)))` writes `(g 7)` and
`(sibling $r)`. -/
theorem pure_result_local_to_its_template :
    (mainlineStep defaultProfile sevenPrimitives ExternalState.empty
        [.expression [.symbol "exec", .grounded (.int 0), .expression [.symbol ","],
          .expression [.symbol "O",
            .expression [.symbol "pure", .expression [.symbol "g", .var "r"], .var "r",
              .expression [.symbol "seven"]],
            .expression [.symbol "+", .expression [.symbol "sibling", .var "r"]]]]]).space? =
      some [.expression [.symbol "sibling", .var "r"], .expression [.symbol "g", .symbol "7"]] := by
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.MORK.Mainline
