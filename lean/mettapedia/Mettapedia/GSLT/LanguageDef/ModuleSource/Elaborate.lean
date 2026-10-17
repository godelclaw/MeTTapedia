import Mettapedia.GSLT.LanguageDef.ModuleSource.Syntax
import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.Presentation
import Mettapedia.OSLF.MeTTaIL.Substitution

/-!
# Elaborating `.module` into `LanguageDef`

A theory value is an ordered fragment of `ModuleAlgebra.Presentation` entries. Each declaration
carries its origin: the instance that introduced it and its name there. Applying a theory makes
a fresh instance, so two applications are two independent structures, while one `let`-bound
value used twice is one structure. A join is `Presentation.orderedJoin?`: entries with one origin
are identified when they agree, and a join is refused exactly when one origin is declared two
ways or one label names two origins.

A name written `(One)` in an equation or a rewrite is the nullary constructor `One` when the
theory declares one at that point, its own or its base's; otherwise it is a variable. Names are
resolved where they are written, so a later replacement of `One` reaches them.

Equations are anonymous in the format: each instance's equations are its own declarations, so
an equation's label and name carry its instance.

`Replacements` replace a constructor and `Exports` may rename a sort; both keep the origin, so a
replaced constructor stays the same declaration for every later join. References follow: a
replaced constructor is rewritten in every equation and rewrite, with its arguments matched by
parameter name, and a binary operation replaced by a bag constructor of its sort collects its
arguments into the bag.

Facts:
- `joinValues_isSome_iff`: a join succeeds exactly when the two fragments are compatible;
- `joinEntries_presentation`: a computed join is `Presentation.join`, a pushout over the shared
  entries; `evalExpr_join`: elaborating a join joins the elaborations;
- `joinEntries_self`: a fragment joined with itself is itself, so sharing never duplicates;
- `replace_origins`, `renameSort_origins`: replacing and renaming keep every origin;
- `fresh_lt`: every application gets an instance id larger than every earlier one.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleSource

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.ModuleAlgebra (Entry)

instance : DecidableEq Equation := fun first second => by
  cases first
  cases second
  exact decidable_of_iff' _ (Iff.of_eq (Equation.mk.injEq _ _ _ _ _ _ _ _ _ _ _ _))

instance : DecidableEq RewriteRule := fun first second => by
  cases first
  cases second
  exact decidable_of_iff' _ (Iff.of_eq (RewriteRule.mk.injEq _ _ _ _ _ _ _ _ _ _ _ _))

/-! ## Builders, for the readers -/

def mkExport (sort : String) (renamed : Option String) : Export := ⟨sort, renamed⟩
def mkReplacement (old : String) (rule : GrammarRule) : Replacement := ⟨old, rule⟩
def mkParam (param : String) (target : Path) : Param := ⟨param, target⟩
def mkTheory (theoryName : String) (params : List Param) (body : Expr) : Theory := ⟨theoryName, params, body⟩
def mkImport (file qualifier : String) : Import := ⟨file, qualifier⟩
def mkModule (imports : List Import) (moduleName : String) (theories : List Theory)
    (entry : Option (Path × List Expr)) : Module := ⟨imports, moduleName, theories, entry⟩
abbrev ModuleData := Module

/-- The one rule of a single-row fragment. -/
def singleRule : List GrammarRule → GrammarRule
  | [rule] => rule
  | _ => { label := "", category := "", params := [], syntaxPattern := [] }

/-! ## Declarations and values -/

/-- The instance that introduced a declaration, and the declaration's name there. -/
structure Origin where
  inst : Nat
  name : String
  deriving DecidableEq, Repr

/-- Sorts, constructors, equations and rewrites have separate name spaces. -/
inductive Kind where
  | sort | term | equation | rewrite
  deriving DecidableEq, Repr

abbrev Label := Kind × String

inductive Decl where
  | sort (name : String)
  | term (rule : GrammarRule)
  | equation (row : Equation)
  | rewrite (row : RewriteRule)
  deriving DecidableEq

abbrev Item := Entry Origin Label Decl

/-- A theory value: its declarations in order, its exported sorts, and the theories it is an
instance of. -/
structure Value where
  entries : List Item
  exports : List String := []
  instanceOf : List String := []

/-- Why a module does not elaborate. -/
inductive Error where
  | unknownName (name : String)
  | unknownTheory (path : Path)
  | arity (theory : String) (expected given : Nat)
  | notInstance (theory param : String) (expected : String)
  | collision (witness : Option (Item × Item))
  | replaceMissing (label : String)
  | replaceShape (old new : String)
  | renameMissing (sort : String)
  | importMissing (file : String)
  | noEntry

instance : Repr Error where
  reprPrec
    | .unknownName name, _ => s!"unknown name {name}"
    | .unknownTheory path, _ => s!"unknown theory {".".intercalate path}"
    | .arity theory expected given, _ => s!"{theory} takes {expected} arguments, given {given}"
    | .notInstance theory param expected, _ => s!"{theory}: argument {param} is not an instance of {expected}"
    | .collision (some (left, right)), _ =>
        s!"join collision: {repr left.label} from instance {left.origin.inst} ({left.origin.name}) " ++
          s!"against {repr right.label} from instance {right.origin.inst} ({right.origin.name})"
    | .collision none, _ => "join collision"
    | .replaceMissing label, _ => s!"no constructor {label} to replace"
    | .replaceShape old new, _ => s!"cannot map the arguments of {old} onto {new}"
    | .renameMissing sort, _ => s!"no sort {sort} to export"
    | .importMissing file, _ => s!"import {file} is not available"
    | .noEntry, _ => "the module has no entry theory"

/-- Elaboration threads the next instance id. -/
abbrev M := StateT Nat (Except Error)

def fresh : M Nat := modifyGet fun next => (next, next + 1)

theorem fresh_lt (next : Nat) : ∀ result, fresh.run next = .ok result → result.1 = next ∧ result.2 = next + 1 := by
  intro result ran
  simp only [fresh, StateT.run, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure, Except.pure,
    Except.ok.injEq] at ran
  subst ran
  exact ⟨rfl, rfl⟩

/-! ## Joins -/

/-- The first incompatible pair, for the diagnostic. -/
def firstCollision (items : List Item) : Option (Item × Item) :=
  items.findSome? fun first =>
    (items.find? fun second => !ModuleAlgebra.entryCompatible first second).map (first, ·)

/-- Add entries to a fragment, refusing collisions. -/
def joinEntries (first second : List Item) : Except Error (List Item) :=
  match ModuleAlgebra.orderedJoin? first second with
  | some joined => .ok joined
  | none => .error (.collision (firstCollision (first ++ second)))

def joinValues (left right : Value) : Except Error Value := do
  let entries ← joinEntries left.entries right.entries
  pure { entries, exports := (left.exports ++ right.exports).eraseDups,
         instanceOf := (left.instanceOf ++ right.instanceOf).eraseDups }

theorem joinEntries_isSome_iff (first second : List Item) :
    (∃ joined, joinEntries first second = .ok joined) ↔
      ModuleAlgebra.Valid (first.toFinset ∪ second.toFinset) := by
  rw [← ModuleAlgebra.orderedJoin_isSome_iff]
  unfold joinEntries
  cases joined : ModuleAlgebra.orderedJoin? first second with
  | some result => simp
  | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, iff_false, not_exists]
      intro result refused
      cases refused

/-- **A join succeeds exactly when the two fragments are compatible.** -/
theorem joinValues_isSome_iff (left right : Value) :
    (∃ joined, joinValues left right = .ok joined) ↔
      ModuleAlgebra.Valid (left.entries.toFinset ∪ right.entries.toFinset) := by
  rw [← joinEntries_isSome_iff]
  unfold joinValues
  cases joined : joinEntries left.entries right.entries with
  | ok entries => simp [bind, Except.bind, pure, Except.pure]
  | error failure => simp [bind, Except.bind]

/-- **A computed join is the presentation join**, whose square is a pushout over the shared
entries (`ModuleAlgebra.join_isPushout`). -/
theorem joinEntries_presentation (first second joined : List Item)
    (validFirst : ModuleAlgebra.Valid first.toFinset) (validSecond : ModuleAlgebra.Valid second.toFinset)
    (computed : joinEntries first second = .ok joined) :
    ∃ result, ModuleAlgebra.join ⟨first.toFinset, validFirst⟩ ⟨second.toFinset, validSecond⟩ = some result ∧
      result.val = joined.toFinset := by
  have ordered : ModuleAlgebra.orderedJoin? first second = some joined := by
    unfold joinEntries at computed
    cases found : ModuleAlgebra.orderedJoin? first second with
    | some result => rw [found] at computed; cases computed; rfl
    | none => rw [found] at computed; cases computed
  have agrees := ModuleAlgebra.orderedJoin_agrees first second
  rw [ordered, Option.bind_some] at agrees
  have union : joined.toFinset = first.toFinset ∪ second.toFinset := by
    simpa only [ModuleAlgebra.orderedJoin?, List.toFinset_append] using
      ModuleAlgebra.orderedCheck_toFinset (first ++ second) joined ordered
  have valid : ModuleAlgebra.Valid joined.toFinset := by
    have isSome := (ModuleAlgebra.orderedJoin_isSome_iff first second).mp (by simp [ordered])
    rwa [union]
  refine ⟨⟨joined.toFinset, valid⟩, ?_, rfl⟩
  show ModuleAlgebra.check (first.toFinset ∪ second.toFinset) = _
  rw [← union]
  simp [ModuleAlgebra.check, valid]

/-- Inserting an entry already present in a compatible fragment changes nothing. -/
theorem insert_member (kept : List Item) (accepted : List.AllCompatible ModuleAlgebra.entryCompatible kept)
    (entry : Item) (member : entry ∈ kept) :
    List.insertCompatible? ModuleAlgebra.entryCompatible entry kept = some kept := by
  induction kept with
  | nil => cases member
  | cons first rest ih =>
    by_cases same : entry = first
    · simp [List.insertCompatible?, same]
    · have inRest : entry ∈ rest := by
        rcases List.mem_cons.mp member with equal | inside
        · exact absurd equal same
        · exact inside
      have compatible : ModuleAlgebra.entryCompatible first entry = true :=
        accepted first (by simp) entry (by simp [inRest])
      have later := ih (accepted.mono (fun item inside => by simp [inside])) inRest
      simp [List.insertCompatible?, same, compatible, later]

/-- Adding entries that are all present changes nothing. -/
theorem union_members (kept : List Item) (accepted : List.AllCompatible ModuleAlgebra.entryCompatible kept) :
    ∀ incoming : List Item, (∀ entry ∈ incoming, entry ∈ kept) →
      List.unionCompatible? ModuleAlgebra.entryCompatible kept incoming = some kept
  | [], _ => rfl
  | entry :: rest, inside => by
    simp only [List.unionCompatible?, insert_member kept accepted entry (inside entry (by simp)),
      Option.bind_eq_bind, Option.bind_some]
    exact union_members kept accepted rest (fun other member => inside other (by simp [member]))

/-- A checked fragment is compatible. -/
theorem checked_allCompatible (items : List Item) (checked : ModuleAlgebra.orderedCheck? items = some items) :
    List.AllCompatible ModuleAlgebra.entryCompatible items :=
  List.unionCompatible?_allCompatible _ ModuleAlgebra.entryCompatible_self ModuleAlgebra.entryCompatible_symm
    [] items items (by simp) checked

/-- **Sharing never duplicates**: a checked fragment joined with itself is itself. -/
theorem joinEntries_self (items : List Item) (checked : ModuleAlgebra.orderedCheck? items = some items) :
    joinEntries items items = .ok items := by
  have joined : ModuleAlgebra.orderedJoin? items items = some items := by
    unfold ModuleAlgebra.orderedJoin? ModuleAlgebra.orderedCheck? at *
    rw [List.unionCompatible?_append, checked, Option.bind_some]
    exact union_members items (checked_allCompatible items checked) items (fun _ member => member)
  simp [joinEntries, joined]

/-! ## Renaming a sort -/

section Rename

variable (old new : String)

def renameName (name : String) : String := if name = old then new else name

def renameType : TypeExpr → TypeExpr
  | .base name => .base (renameName old new name)
  | .arrow domain codomain => .arrow (renameType domain) (renameType codomain)
  | .multiBinder body => .multiBinder (renameType body)
  | .collection kind element => .collection kind (renameType element)

def renameParam : TermParam → TermParam
  | .simple name type => .simple name (renameType old new type)
  | .abstractionNamed binder name type => .abstractionNamed binder name (renameType old new type)
  | .multiAbstractionNamed binders name type => .multiAbstractionNamed binders name (renameType old new type)

def renamePremise : Premise → Premise
  | .freshness condition => .freshness condition
  | .congruence source target => .congruence source target
  | .scopedStep step => .scopedStep { step with binders := step.binders.map (renameType old new),
                                                resultType := renameType old new step.resultType }
  | .relationQuery relation arguments => .relationQuery relation arguments
  | .forAll index element body => .forAll index element (renamePremise body)

def renameSpec (spec : RuleBindingSpec) : RuleBindingSpec :=
  { spec with dependencies := spec.dependencies.map fun entry => (entry.1, entry.2.map (renameType old new)) }

def renameContext (context : List (String × TypeExpr)) : List (String × TypeExpr) :=
  context.map fun entry => (entry.1, renameType old new entry.2)

def renameDecl : Decl → Decl
  | .sort name => .sort (renameName old new name)
  | .term rule => .term { rule with category := renameName old new rule.category,
                                    params := rule.params.map (renameParam old new) }
  | .equation row => .equation { row with typeContext := renameContext old new row.typeContext,
                                          premises := row.premises.map (renamePremise old new),
                                          bindings := row.bindings.map (renameSpec old new) }
  | .rewrite row => .rewrite { row with typeContext := renameContext old new row.typeContext,
                                        premises := row.premises.map (renamePremise old new),
                                        bindings := row.bindings.map (renameSpec old new) }

def renameItem (item : Item) : Item :=
  { item with label := if item.label = (.sort, old) then (.sort, new) else item.label,
              body := renameDecl old new item.body }

/-- **Renaming a sort keeps every origin.** -/
theorem renameSort_origins (items : List Item) :
    (items.map (renameItem old new)).map (·.origin) = items.map (·.origin) := by
  simp [renameItem, Function.comp_def]

end Rename

/-! ## Replacing a constructor -/

def paramName : TermParam → String
  | .simple name _ => name
  | .abstractionNamed _ name _ => name
  | .multiAbstractionNamed _ name _ => name

/-- How the old constructor's arguments become the new one's: by parameter name, or, for a bag
constructor of the old parameters' sort, collected into the bag. -/
def argumentMap (old new : GrammarRule) : Option (List Pattern → List Pattern) :=
  let oldNames := old.params.map paramName
  let newNames := new.params.map paramName
  if newNames.length = oldNames.length && newNames.all oldNames.contains && newNames.Nodup then
    some fun arguments => newNames.map fun name => (arguments[oldNames.idxOf name]?).getD (.fvar name)
  else
    match new.params with
    | [.simple _ (.collection kind (.base element))] =>
        if old.params.all (fun param => match param with
            | .simple _ (.base sort) => sort = element
            | _ => false) then
          some fun arguments => [.collection kind arguments none]
        else none
    | _ => none

section Constructor

variable (old new : String) (map : List Pattern → List Pattern)

def renameConstructor : Pattern → Pattern
  | .bvar index => .bvar index
  | .fvar name => .fvar name
  | .apply label arguments =>
      let inner := arguments.map renameConstructor
      if label = old then .apply new (map inner) else .apply label inner
  | .lambda binder body => .lambda binder (renameConstructor body)
  | .multiLambda arity binders body => .multiLambda arity binders (renameConstructor body)
  | .subst body replacement => .subst (renameConstructor body) (renameConstructor replacement)
  | .collection kind elements rest => .collection kind (elements.map renameConstructor) rest
decreasing_by all_goals sizeOf_pattern_dec

def replacePremise : Premise → Premise
  | .freshness condition => .freshness { condition with term := renameConstructor old new map condition.term }
  | .congruence source target =>
      .congruence (renameConstructor old new map source) (renameConstructor old new map target)
  | .scopedStep step => .scopedStep { step with source := renameConstructor old new map step.source,
                                                target := renameConstructor old new map step.target }
  | .relationQuery relation arguments => .relationQuery relation (arguments.map (renameConstructor old new map))
  | .forAll index element body => .forAll index element (replacePremise body)

def replaceDecl : Decl → Decl
  | .equation row => .equation { row with premises := row.premises.map (replacePremise old new map),
                                          left := renameConstructor old new map row.left,
                                          right := renameConstructor old new map row.right }
  | .rewrite row => .rewrite { row with premises := row.premises.map (replacePremise old new map),
                                        left := renameConstructor old new map row.left,
                                        right := renameConstructor old new map row.right }
  | other => other

end Constructor

/-- The constructor `old` becomes `rule`, keeping its origin; every reference follows. -/
def replaceItems (items : List Item) (row : Replacement) (map : List Pattern → List Pattern) : List Item :=
  items.map fun item =>
    if item.label = (.term, row.old) then { item with label := (.term, row.rule.label), body := .term row.rule }
    else { item with body := replaceDecl row.old row.rule.label map item.body }

/-- **Replacing a constructor keeps every origin.** -/
theorem replace_origins (items : List Item) (row : Replacement) (map : List Pattern → List Pattern) :
    (replaceItems items row map).map (·.origin) = items.map (·.origin) := by
  simp only [replaceItems, List.map_map]
  apply List.map_congr_left
  intro item _
  simp only [Function.comp_apply]
  split <;> rfl

/-! ## Blocks -/

/-- Re-admit a fragment after renaming or replacing. -/
def recheck (items : List Item) : Except Error (List Item) :=
  match ModuleAlgebra.orderedCheck? items with
  | some checked => .ok checked
  | none => .error (.collision (firstCollision items))

def newItem (inst : Nat) (kind : Kind) (name : String) (body : Decl) : Item := ⟨⟨inst, name⟩, (kind, name), body⟩

def exportRow (value : Value) (row : Export) : Except Error Value := do
  unless value.entries.any (·.label == (.sort, row.sort)) do throw (.renameMissing row.sort)
  match row.renamed with
  | none => pure { value with exports := value.exports ++ [row.sort] }
  | some target =>
      let entries ← recheck (value.entries.map (renameItem row.sort target))
      pure { value with entries, exports := value.exports.map (renameName row.sort target) ++ [target] }

def replaceRow (value : Value) (row : Replacement) : Except Error Value := do
  let some found := value.entries.find? (·.label == (.term, row.old)) | throw (.replaceMissing row.old)
  let .term oldRule := found.body | throw (.replaceMissing row.old)
  let some map := argumentMap oldRule row.rule | throw (.replaceShape row.old row.rule.label)
  let entries ← recheck (replaceItems value.entries row map)
  pure { value with entries }

/-- The nullary constructors a value declares. -/
def nullaries (value : Value) : List String :=
  value.entries.filterMap fun item => match item.body with
    | .term rule => if rule.params.isEmpty then some rule.label else none
    | _ => none

def applyBlock (inst : Nat) (value : Value) : Block → Except Error Value
  | .types sorts => add (sorts.map fun sort => newItem inst .sort sort (.sort sort))
  | .terms rules => add (rules.map fun rule => newItem inst .term rule.label (.term rule))
  | .equations rows => add (rows.map fun row =>
      let label := s!"{row.name}@{inst}"
      ⟨⟨inst, row.name⟩, (.equation, label), .equation (Equation.resolveNullary (nullaries value) { row with name := label })⟩)
  | .rewrites rows => add (rows.map fun row =>
      newItem inst .rewrite row.name (.rewrite (RewriteRule.resolveNullary (nullaries value) row)))
  | .exports rows => rows.foldlM exportRow value
  | .replacements rows => rows.foldlM replaceRow value
where
  add (fresh : List Item) : Except Error Value := do
    let entries ← joinEntries value.entries fresh
    pure { value with entries }

/-! ## Theories and modules -/

/-- A theory ready to apply: its canonical name, its parameters' theories, and its body. -/
structure Closure where
  name : String
  params : List (String × String)
  run : List Value → M Value

/-- What names mean while a theory body is elaborated. -/
structure Scope where
  theories : List (Path × Closure)
  values : List (String × Value) := []

def lookupTheory (scope : Scope) (path : Path) : Except Error Closure :=
  match scope.theories.find? (·.1 == path) with
  | some entry => .ok entry.2
  | none => .error (.unknownTheory path)

def liftExcept {α : Type} (result : Except Error α) : M α := StateT.lift result

mutual

def evalExpr (scope : Scope) (inst : Nat) : Expr → M Value
  | .ref name =>
      match scope.values.find? (·.1 == name) with
      | some entry => pure entry.2
      | none => throw (.unknownName name)
  | .apply path args => do
      let closure ← liftExcept (lookupTheory scope path)
      let values ← evalList scope inst args
      closure.run values
  | .join left right => do
      let first ← evalExpr scope inst left
      let second ← evalExpr scope inst right
      liftExcept (joinValues first second)
  | .extend base blocks => do
      let start ← match base with
        | some expr => evalExpr scope inst expr
        | none => pure { entries := [] }
      liftExcept (blocks.foldlM (applyBlock inst) start)
  | .letIn name value body => do
      let bound ← evalExpr scope inst value
      evalExpr { scope with values := (name, bound) :: scope.values } inst body

def evalList (scope : Scope) (inst : Nat) : List Expr → M (List Value)
  | [] => pure []
  | expr :: rest => do
      let head ← evalExpr scope inst expr
      let tail ← evalList scope inst rest
      pure (head :: tail)

end

/-- **Elaborating a join joins the elaborations**, in order, threading instance ids. -/
theorem evalExpr_join (scope : Scope) (inst : Nat) (left right : Expr) (next : Nat) :
    (evalExpr scope inst (.join left right)).run next =
      ((evalExpr scope inst left).run next).bind fun (first, afterLeft) =>
        ((evalExpr scope inst right).run afterLeft).bind fun (second, afterRight) =>
          (joinValues first second).map (·, afterRight) := by
  simp only [evalExpr, liftExcept, StateT.run, bind, StateT.bind, StateT.lift]
  cases (evalExpr scope inst left next) with
  | error failure => rfl
  | ok pair =>
    cases (evalExpr scope inst right pair.2) with
    | error failure => rfl
    | ok second =>
      simp only [Except.bind]
      cases (joinValues pair.1 second.1) <;> rfl

/-- The closure of a theory: applying it makes a fresh instance. -/
def closure (theories : List (Path × Closure)) (canonical : String) (theory : Theory) : Except Error Closure := do
  let params ← theory.params.mapM fun param => do
    let target ← lookupTheory { theories } param.theory
    pure (param.name, target.name)
  pure { name := canonical, params, run := fun args => do
    if args.length ≠ params.length then throw (.arity canonical params.length args.length)
    for (param, arg) in params.zip args do
      unless arg.instanceOf.contains param.2 do throw (.notInstance canonical param.1 param.2)
    let inst ← fresh
    let value ← evalExpr { theories, values := (params.map (·.1)).zip args } inst theory.body
    pure { value with instanceOf := (canonical :: value.instanceOf).eraseDups } }

/-- The theories a module defines, with those of its imports under their qualifiers. A module is
found in `library` by its file name; `fuel` bounds the import depth. -/
def theoriesOf (library : List (String × Module)) : Nat → Module → Except Error (List (Path × Closure))
  | 0, _ => .error (.importMissing "(import depth)")
  | fuel + 1, module => do
      let mut scope : List (Path × Closure) := []
      for imported in module.imports do
        let some dependency := library.find? (·.1 == imported.file) | throw (.importMissing imported.file)
        let theirs ← theoriesOf library fuel dependency.2
        scope := scope ++ (theirs.filter (·.1.length == 1)).map fun entry => (imported.qualifier :: entry.1, entry.2)
      for theory in module.theories do
        let made ← closure scope (module.name ++ "." ++ theory.name) theory
        scope := scope ++ [([theory.name], made)]
      pure scope

/-- A value's declarations in order, before nullary names are resolved. -/
def flattenRaw (name : String) (value : Value) : LanguageDef where
  name := name
  types := value.entries.filterMap fun item => match item.body with
    | .sort sort => some (TypeDecl.plain sort) | _ => none
  terms := value.entries.filterMap fun item => match item.body with
    | .term rule => some rule | _ => none
  equations := value.entries.filterMap fun item => match item.body with
    | .equation row => some row | _ => none
  rewrites := value.entries.filterMap fun item => match item.body with
    | .rewrite row => some row | _ => none

/-- A value as a `LanguageDef`, its declarations in order. -/
def flatten (name : String) (value : Value) : LanguageDef := flattenRaw name value

/-- The value of applying a theory to arguments, within a module. -/
def applyTheory (library : List (String × Module)) (module : Module) (path : Path) (args : List Expr) :
    Except Error (String × Value) := do
  let theories ← theoriesOf library (library.length + 1) module
  let made ← lookupTheory { theories } path
  let value ← (evalExpr { theories } 0 (.apply path args)).run' 0
  pure (made.name, value)

/-- **A module's `LanguageDef`**: its entry theory, elaborated. -/
def elaborate (library : List (String × Module)) (module : Module) : Except Error LanguageDef := do
  let some (path, args) := module.entry | throw .noEntry
  let (name, value) ← applyTheory library module path args
  pure (flatten name value)

end Mettapedia.GSLT.LanguageDef.ModuleSource
