import Mettapedia.GSLT.LanguageDef.IndexedInductiveCaseElaboration
import Mettapedia.GSLT.LanguageDef.ModuleSource.Syntax
import Mettapedia.OSLF.MeTTaIL.Match

/-!
# Finite named operation expressions for constructor-clause elaboration

The common module reader already retains first-order expression patterns.
This adapter resolves their free names in an explicit finite scope and
instantiates declared symbol templates by capture-safe substitution. It
refuses unsupported binding forms, unknown names and incorrect arities.
The result still requires the independent dependent typing checker.

Symbol templates are source-expansion data, not inference rules or opaque
proof constants. Their connection to a selected source library is separate
from the generic resolution and substitution laws here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.OperationSource

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.OSLF.MeTTaIL.Syntax

variable {Head : Type} {n m : Nat}

/-- A selected direct module retains both declaration and operation blocks.
This fragment refuses imports and composition until their elaboration route
is supplied; it does not silently drop another block or entry. -/
structure DirectModule where
  moduleName : String
  theoryName : String
  families : List ModuleSource.InductiveSyntax.Family
  rules : List RewriteRule

def DirectModule.assemble (selected : DirectModule) : ModuleSource.Module :=
  ⟨[], selected.moduleName,
    [⟨selected.theoryName, [], .extend none [.inductives selected.families, .rewrites selected.rules]⟩],
    some ([selected.theoryName], [])⟩

def DirectModule.declarations (selected : DirectModule) : ModuleSource.Module :=
  ⟨[], selected.moduleName,
    [⟨selected.theoryName, [], .extend none [.inductives selected.families]⟩],
    some ([selected.theoryName], [])⟩

def selectModule : ModuleSource.Module → Option DirectModule
  | ⟨[], moduleName, [⟨theoryName, [], .extend none [.inductives families, .rewrites rules]⟩],
      some ([entry], [])⟩ =>
      if entry = theoryName then some ⟨moduleName, theoryName, families, rules⟩ else none
  | _ => none

theorem selectModule_exact (source : ModuleSource.Module) (selected : DirectModule)
    (accepted : selectModule source = some selected) : selected.assemble = source := by
  unfold selectModule at accepted
  split at accepted
  · split at accepted
    · rename_i same
      cases Option.some.inj accepted
      simp only [DirectModule.assemble, same]
    · cases accepted
  · cases accepted

structure Symbol (Head : Type) where
  name : String
  arity : Nat
  body : Tm Head arity

/-- Arguments are written in lexical order, whereas the template's newest
binder has index zero. The conversion to a simultaneous assignment reverses
the list exactly once. -/
def Symbol.instantiate (symbol : Symbol Head) (arguments : List (Tm Head n)) :
    Option (Tm Head n) :=
  if length : arguments.reverse.length = symbol.arity then
    some (subst (SchemaTableConversionCode.argumentSub arguments.reverse length) symbol.body)
  else none

theorem Symbol.instantiate_substitute (symbol : Symbol Head) (substitution : Sub Head n m)
    (arguments : List (Tm Head n)) :
    symbol.instantiate (arguments.map (subst substitution)) =
      (symbol.instantiate arguments).map (subst substitution) := by
  by_cases length : arguments.reverse.length = symbol.arity
  · have mapped : (arguments.map (subst substitution)).reverse.length = symbol.arity := by
      simpa only [List.length_reverse, List.length_map] using length
    have assignments : SchemaTableConversionCode.argumentSub
        (arguments.map (subst substitution)).reverse mapped =
        fun index => subst substitution (SchemaTableConversionCode.argumentSub arguments.reverse length index) := by
      funext index
      simp [SchemaTableConversionCode.argumentSub, List.getElem_reverse]
    simp only [instantiate, dif_pos length, dif_pos mapped, Option.map_some, assignments, subst_comp]
  · have mapped : ¬ (arguments.map (subst substitution)).reverse.length = symbol.arity := by
      simpa only [List.length_reverse, List.length_map] using length
    simp only [instantiate, dif_neg length, dif_neg mapped, Option.map_none]

def findSymbol (symbols : List (Symbol Head)) (name : String) : Option (Symbol Head) :=
  match symbols.filter (fun symbol => symbol.name == name) with
  | [symbol] => some symbol
  | _ => none

def applySymbol (symbols : List (Symbol Head)) (name : String) (arguments : List (Tm Head n)) :
    Option (Tm Head n) :=
  (findSymbol symbols name).bind (fun symbol => symbol.instantiate arguments)

/-- Literal pattern variables and declaration-resolved operation identifiers
are different source policies. Only a uniquely declared nullary symbol is
resolved by the latter; an authored local cannot shadow that declaration. -/
inductive NamePolicy where
  | literalVariables
  | declaredNullary
  deriving DecidableEq, Repr

def nullaryNames (symbols : List (Symbol Head)) : List String :=
  symbols.filterMap fun symbol =>
    if symbol.arity == 0 && (findSymbol symbols symbol.name).isSome then some symbol.name else none

/-- Reuse the maintained module/LanguageDef resolver. The source profile
supplies its admitted nullary labels; no private resolver is introduced. -/
def resolveNames (symbols : List (Symbol Head)) (policy : NamePolicy) (pattern : Pattern) : Pattern :=
  match policy with
  | .literalVariables => pattern
  | .declaredNullary => pattern.resolveNullary (nullaryNames symbols) []

def resolveRule (symbols : List (Symbol Head)) (policy : NamePolicy) (rule : RewriteRule) : RewriteRule :=
  match policy with
  | .literalVariables => rule
  | .declaredNullary => rule.resolveNullary (nullaryNames symbols)

theorem applySymbol_substitute (symbols : List (Symbol Head)) (name : String)
    (substitution : Sub Head n m) (arguments : List (Tm Head n)) :
    applySymbol symbols name (arguments.map (subst substitution)) =
      (applySymbol symbols name arguments).map (subst substitution) := by
  cases found : findSymbol symbols name with
  | none => simp [applySymbol, found]
  | some symbol =>
      simpa [applySymbol, found] using symbol.instantiate_substitute substitution arguments

abbrev Environment (Head : Type) (n : Nat) := String → Option (Tm Head n)

def mapEnvironment (substitution : Sub Head n m) (environment : Environment Head n) :
    Environment Head m := fun name => (environment name).map (subst substitution)

/-- Fuel limits this untrusted recursive producer; failure supplies no
negative typing or source-uninterpretability judgment. -/
def lower (symbols : List (Symbol Head)) (environment : Environment Head n) :
    Nat → Pattern → Option (Tm Head n)
  | 0, _ => none
  | _ + 1, .fvar name => environment name
  | fuel + 1, .apply name arguments => do
      let arguments ← arguments.mapM (lower symbols environment fuel)
      applySymbol symbols name arguments
  | _ + 1, _ => none

theorem lower_substitute (symbols : List (Symbol Head)) (environment : Environment Head n)
    (substitution : Sub Head n m) (fuel : Nat) (pattern : Pattern) :
    lower symbols (mapEnvironment substitution environment) fuel pattern =
      (lower symbols environment fuel pattern).map (subst substitution) := by
  induction fuel generalizing pattern with
  | zero => rfl
  | succ fuel ih =>
      cases pattern with
      | fvar name => rfl
      | apply name arguments =>
          have mapped : arguments.mapM (lower symbols (mapEnvironment substitution environment) fuel) =
              (arguments.mapM (lower symbols environment fuel)).map (List.map (subst substitution)) := by
            induction arguments with
            | nil => rfl
            | cons first rest restIH =>
                rw [List.mapM_cons, List.mapM_cons, ih, restIH]
                cases lower symbols environment fuel first <;>
                  cases rest.mapM (lower symbols environment fuel) <;> rfl
          simp only [lower, mapped]
          cases found : arguments.mapM (lower symbols environment fuel) with
          | none => rfl
          | some terms =>
              simpa using applySymbol_substitute symbols name substitution terms
      | bvar _ | lambda _ _ | multiLambda _ _ _ | subst _ _ | collection _ _ _ => rfl

/-- Position lookup is intrinsically bounded. The nearest lexical occurrence
is selected; callers separately enforce their desired linearity policy. -/
def findName : (names : List String) → String → Option (Fin names.length)
  | [], _ => none
  | first :: rest, name =>
      if first = name then some ⟨0, by simp⟩ else (findName rest name).map Fin.succ

def fieldEnvironment (names : List String) (ambient : Nat) :
    Environment Head (ambient + names.length) :=
  fun name => (findName names name).map fun index =>
    .var ⟨names.length - 1 - index.val, by omega⟩

/-- A source profile constructs the expected constructor-pattern shape and
the exact scope of each placeholder. Placeholder names are distinct from
the variable names chosen by the authored clause. -/
structure Header (ambient : Nat) where
  constructor : String
  fields : Nat
  left : Pattern
  slots : List (String × Fin (ambient + fields))

/-- A clause header retains every original field. Ambient arguments are
written oldest first; constructor parameters select their existing ambient
slots. Generated placeholders are distinct from authored variable names.
The reader still checks the actual match, linearity and source metadata. -/
def Header.fromPlan (plan : CaseElaboration.BranchPlan Head n)
    (operation : String) (constructorParameters : List (Fin n)) : Header n where
  constructor := plan.name
  fields := plan.fields
  left := .apply operation
    ((List.finRange n).reverse.map (fun i => .fvar ("ambient." ++ toString i.val)) ++
      [.apply plan.name
        (constructorParameters.map (fun i => .fvar ("ambient." ++ toString i.val)) ++
          (List.range plan.fields).map (fun i => .fvar ("field." ++ toString i)))])
  slots :=
    (List.finRange n).map (fun i =>
      ("ambient." ++ toString i.val, ⟨plan.fields + i.val, by omega⟩)) ++
    (List.finRange plan.fields).map (fun i =>
      ("field." ++ toString i.val, ⟨plan.fields - 1 - i.val, by omega⟩))

theorem Header.fromPlan_slot_count (plan : CaseElaboration.BranchPlan Head n)
    (operation : String) (constructorParameters : List (Fin n)) :
    (Header.fromPlan plan operation constructorParameters).slots.length = n + plan.fields := by
  simp [Header.fromPlan]

def sourceVariables (header : Header n) (bindings : Mettapedia.OSLF.MeTTaIL.Match.Bindings) :
    Option (List (String × Fin (n + header.fields))) := do
  let names ← header.slots.mapM fun (slot, index) =>
    match bindings.lookup slot with
    | some (.fvar name) => some (name, index)
    | _ => none
  if decide (header.slots.map Prod.fst).Nodup && decide (names.map Prod.fst).Nodup then
    some names
  else none

def variableEnvironment (boundNames : List (String × Fin n)) : Environment Head n :=
  fun name => (boundNames.find? (fun entry => entry.1 == name)).map (fun entry => .var entry.2)

/-- The literal left-hand side is reconstructed after matching. The retained
receipt is syntax evidence, with no claim of typing or inference authority. -/
structure ReadClause (Head : Type) (header : Header n) (rule : RewriteRule) where
  bindings : Mettapedia.OSLF.MeTTaIL.Match.Bindings
  leftExact : Mettapedia.OSLF.MeTTaIL.Match.applyBindings bindings header.left = rule.left
  boundNames : List (String × Fin (n + header.fields))
  body : Tm Head (n + header.fields)

def ReadClause.toClause {header : Header n} {rule : RewriteRule}
    (read : ReadClause Head header rule) : CaseElaboration.Clause Head n :=
  ⟨header.constructor, header.fields, read.body⟩

/-- Only the declared unconditional first-order clause fragment is consumed.
Missing/ambiguous matches, non-variable binders, aliasing and ignored metadata
are refused before the body is resolved. -/
def readRule (symbols : List (Symbol Head)) (fuel : Nat) (header : Header n)
    (rule : RewriteRule) : Option (ReadClause Head header rule) := do
  if !(rule.typeContext.isEmpty && rule.premises.isEmpty && rule.bindings.isNone) then none else do
    match Mettapedia.OSLF.MeTTaIL.Match.matchPattern header.left rule.left with
    | [bindings] =>
        if exactLeft : Mettapedia.OSLF.MeTTaIL.Match.applyBindings bindings header.left = rule.left then do
          let boundNames ← sourceVariables header bindings
          let body ← lower symbols (variableEnvironment boundNames) fuel rule.right
          return ⟨bindings, exactLeft, boundNames, body⟩
        else none
    | _ => none

/-- Successful reading retains the exact lowering of the written right-hand
side under the resolved source names. -/
theorem readRule_body_exact (symbols : List (Symbol Head)) (fuel : Nat) (header : Header n)
    (rule : RewriteRule) (read : ReadClause Head header rule)
    (accepted : readRule symbols fuel header rule = some read) :
    lower symbols (variableEnvironment read.boundNames) fuel rule.right = some read.body := by
  unfold readRule at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · rename_i bindings matching
      split at accepted
      · rename_i exactLeft
        cases named : sourceVariables header bindings with
        | none => simp [named] at accepted
        | some boundNames =>
            cases lowered : lower symbols (variableEnvironment boundNames) fuel rule.right with
            | none => simp [named, lowered] at accepted
            | some body =>
                have same : (⟨bindings, exactLeft, boundNames, body⟩ : ReadClause Head header rule) = read := by
                  simpa [named, lowered] using accepted
                cases same
                exact lowered
      · cases accepted
    · cases accepted

section Compilation

variable [DecidableEq Head]

/-- Read one named source rule and abstract its declared recursive calls.
The caller supplies a plan derived from the admitted inventory; this producer
does not authorize calls or grant a typing judgment. -/
def compileRule (symbols : List (Symbol Head)) (fuel : Nat) (forbidden : DeclName)
    (header : Header n) (recursiveCalls : List (Tm Head (n + header.fields)))
    (rule : RewriteRule) : Option (Tm Head n) := do
  let read ← readRule symbols fuel header rule
  CaseElaboration.compilePlan ⟨header.constructor, header.fields, recursiveCalls⟩ forbidden read.toClause

/-- An accepted method restores the actual resolved source body by beta
reduction, retaining the exact matched left side and source scope. -/
theorem compileRule_reconstructs
    {R : Rules Head}
    (symbols : List (Symbol Head)) (fuel : Nat) (forbidden : DeclName)
    (header : Header n) (recursiveCalls : List (Tm Head (n + header.fields)))
    (rule : RewriteRule) (compiled : Tm Head n)
    (accepted : compileRule symbols fuel forbidden header recursiveCalls rule = some compiled) :
    ∃ read : ReadClause Head header rule,
      readRule symbols fuel header rule = some read ∧
      Mettapedia.OSLF.MeTTaIL.Match.applyBindings read.bindings header.left = rule.left ∧
      lower symbols (variableEnvironment read.boundNames) fuel rule.right = some read.body ∧
      TypedEquality.Reduces R
        (TypedEquality.Normalization.appSpine
          (rename (TypedEquality.Normalization.wkN header.fields) compiled)
          (TypedEquality.Normalization.fieldVars n header.fields ++ recursiveCalls)) read.body := by
  cases found : readRule symbols fuel header rule with
  | none => simp [compileRule, found] at accepted
  | some read =>
      have compiledRule : CaseElaboration.compilePlan
          ⟨header.constructor, header.fields, recursiveCalls⟩ forbidden read.toClause = some compiled := by
        simpa [compileRule, found] using accepted
      obtain ⟨source, adapted, reduction⟩ :=
        CaseElaboration.compilePlan_reduces (R := R) _ forbidden read.toClause compiled compiledRule
      have sourceSame : read.body = source := by
        simpa [CaseElaboration.adaptFields, ReadClause.toClause] using adapted
      exact ⟨read, rfl, read.leftExact, readRule_body_exact symbols fuel header rule read found,
        sourceSame ▸ reduction⟩

end Compilation

namespace Controls

def symbols : List (Symbol Unit) :=
  [⟨"Zero", 0, .const `zero⟩, ⟨"Succ", 1, .app (.const `succ) (.var 0)⟩,
    ⟨"Pair", 2, .pair (.var 1) (.var 0)⟩]

def environment : Environment Unit 2 := fieldEnvironment ["first", "second"] 0

def verdicts : List (String × Bool) := [
  ("operation names preserve source argument order",
    lower symbols environment 5 (.apply "Pair" [.fvar "first", .fvar "second"]) ==
      some (.pair (.var 1) (.var 0))),
  ("operation nested constructor expansion",
    lower symbols environment 5 (.apply "Succ" [.apply "Zero" []]) ==
      some (.app (.const `succ) (.const `zero))),
  ("operation unknown free name refuses", (lower symbols environment 5 (.fvar "missing")).isNone),
  ("operation unknown symbol refuses", (lower symbols environment 5 (.apply "Missing" [])).isNone),
  ("operation wrong arity refuses", (lower symbols environment 5 (.apply "Succ" [])).isNone),
  ("operation unsupported binder refuses", (lower symbols environment 5 (.lambda none (.bvar 0))).isNone),
  ("operation exhausted producer refuses", (lower symbols environment 0 (.fvar "first")).isNone)]

def header : Header 1 := ⟨"Succ", 1,
  .apply "Function" [.fvar "parameter", .apply "Succ" [.fvar "field"]],
  [("parameter", 1), ("field", 0)]⟩

def row (parameter field : String) : RewriteRule :=
  ⟨"Step", [], [], .apply "Function" [.fvar parameter, .apply "Succ" [.fvar field]],
    .apply "Pair" [.fvar parameter, .fvar field], none⟩

def readBody (source : RewriteRule) : Option (Tm Unit 2) :=
  (readRule symbols 8 header source).map (·.body)

def recursiveSymbols : List (Symbol Unit) := symbols ++
  [⟨"Recursive", 1, .app (.const `sourceFunction) (.var 0)⟩]

def recursiveRow : RewriteRule :=
  { row "a" "n" with right := .apply "Recursive" [.fvar "n"] }

def clauseVerdicts : List (String × Bool) := [
  ("named method reconstructs the resolved clause",
    compileRule symbols 8 `sourceFunction header [] (row "a" "n") ==
      some (.lam (.pair (.var 1) (.var 0)))),
  ("named method abstracts the declared recursive child",
    compileRule recursiveSymbols 8 `sourceFunction header
      [.app (.const `sourceFunction) (.var 0)] recursiveRow == some (.lam (.lam (.var 0)))),
  ("named method refuses an undeclared recursive call",
    (compileRule recursiveSymbols 8 `sourceFunction header [] recursiveRow).isNone),
  ("named method refuses a call on another argument",
    (compileRule recursiveSymbols 8 `sourceFunction header
      [.app (.const `sourceFunction) (.var 1)] recursiveRow).isNone),
  ("named clause resolves distinct ambient and field binders",
    readBody (row "a" "n") == some (.pair (.var 1) (.var 0))),
  ("named clause is invariant under source binder renaming",
    readBody (row "element" "previous") == readBody (row "a" "n")),
  ("named clause refuses aliased source binders", (readBody (row "same" "same")).isNone),
  ("named clause refuses a changed constructor", (readBody
    { row "a" "n" with left := .apply "Function" [.fvar "a", .apply "Zero" []] }).isNone),
  ("named clause refuses unbound body names", (readBody
    { row "a" "n" with right := .fvar "missing" }).isNone),
  ("named clause refuses ignored binding metadata", (readBody
    { row "a" "n" with bindings := some ⟨[], []⟩ }).isNone),
  ("named operation refuses ambiguous expansion names", (lower (symbols ++ [⟨"Zero", 0, .const `other⟩])
    environment 5 (.apply "Zero" [])).isNone),
  ("declared nullary source identifier resolves as a constructor",
    resolveNames symbols .declaredNullary (.fvar "Zero") == .apply "Zero" []),
  ("literal pattern variable retains its distinct source meaning",
    resolveNames symbols .literalVariables (.fvar "Zero") == .fvar "Zero"),
  ("explicit nullary application already has the resolved meaning",
    resolveNames symbols .declaredNullary (.apply "Zero" []) == .apply "Zero" [])]

theorem all_verdicts : verdicts.all (·.2) = true := by decide +kernel
theorem all_clauseVerdicts : clauseVerdicts.all (·.2) = true := by decide +kernel

end Controls
end Mettapedia.GSLT.LanguageDef.IndexedInductive.OperationSource
