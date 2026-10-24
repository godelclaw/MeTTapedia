import Mettapedia.OSLF.Framework.FiniteModelContexts
import Mettapedia.OSLF.Framework.FiniteModelContextual

/-!
# Finding certificates

A certificate has two parts: a finite model, which selects the native types that matter, and a
preorder, which says how they move. Both can be found by computation, and every result is checked by
the same verdicts as a hand-written certificate, so the search itself carries no proof obligation.

- **The preorder from the model** (`abstractBelow`): the reflexive-transitive closure of the rules'
  abstract steps under every table, closed under the declared congruence sites. A certificate from a
  model (`Certificate.ofModel`) needs only the model.
- **Models as cells.** A signature lists what a model interprets (`Slot`): constructors with their
  numbers of arguments, abstraction over one variable or several, and the unit and join of each
  collection kind. Each
  slot is a finite table over its inputs, which for an abstraction are the graphs of the functions it
  takes, and a model reads its cells (`cellModel`) from full tables (`tableModel`) or from assigned
  cells (`sparseModel`, `Certificate.ofCells`).
- **Every model** (`models`): all tables over the carrier `Fin size`. The verdict holds when one of them
  yields a checked certificate (`cannotReachBySearch_of_check`); the kernel runs the search and stops at
  the first success, which suits small signatures.
- **Cell by cell** (`findCells`): a depth-first search that evaluates everything the verdict evaluates
  under a partial model (`partialModel`, whose values may wait for a cell), assigns the first cell an
  evaluation waits for, and abandons a partial model once the state reaches a goal value through steps
  already determined, or a collection join already fails to commute. Both failures persist under more
  assignments, so abandoning loses no certificate. Its result is a list of cells for the kernel to
  check. A new cell tries the values already in use and one fresh value (`tryValues`), which loses
  nothing up to renaming the values.
- **The contextual semantics** (`Semantics.contextual`): a rule with congruence premises forces its
  step once the pairs its premises need are in the relation, so the preorder is a least fixed point
  (`contextualBelow`, `Certificate.ofContextualCells`), and the finder searches for it the same way,
  assigning only the cells of steps whose premises already hold.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.FiniteModels

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.Framework.BackwardSearch
open Mettapedia.OSLF.Framework.HerbrandBridge (languageSpan Goal)

variable {A : Type} [DecidableEq A]

/-! ## The preorder from the model -/

section Synthesis

variable (elements : List A) (model : FiniteModel A)

/-- The abstract steps of the rules: the values of each rule's two sides under every table. -/
def ruleSteps (language : LanguageDef) : List (A × A) :=
  language.rewrites.flatMap fun rule =>
    (tables elements (ruleSpec rule)).map fun table =>
      (eval model (tableValuation model elements table) [] rule.left,
        eval model (tableValuation model elements table) [] rule.right)

/-- The steps a relation induces at the declared sites. -/
def siteSteps (sites : List Site) (relation : List (A × A)) : List (A × A) :=
  sites.flatMap fun site =>
    (vectors elements site.2.1).flatMap fun arguments =>
      relation.filterMap fun pair =>
        if arguments.getD site.2.2 model.junk == pair.1 then
          some (model.operation site.1 arguments, model.operation site.1 (arguments.set site.2.2 pair.2))
        else none

/-- One round: add the site steps and the compositions. -/
def closeOnce (sites : List Site) (relation : List (A × A)) : List (A × A) :=
  (relation ++ siteSteps elements model sites relation ++
    relation.flatMap fun first => relation.filterMap fun second =>
      if first.2 == second.1 then some (first.1, second.2) else none).dedup

/-- Rounds until nothing changes, at most one per pair of elements. -/
def closeRounds (sites : List Site) : ℕ → List (A × A) → List (A × A)
  | 0, relation => relation
  | rounds + 1, relation =>
      let next := closeOnce elements model sites relation
      if next.length == relation.length then relation else closeRounds sites rounds next

/-- **The preorder from the model**: the least relation the rules and sites force, read reflexively. -/
def abstractBelow (language : LanguageDef) (sites : List Site) : A → A → Bool :=
  let closure := closeRounds elements model sites (elements.length * elements.length + 1)
    (ruleSteps elements model language).dedup
  fun first second => first == second || (first, second) ∈ closure

end Synthesis

namespace Certificate

/-- **A certificate from a model alone**: its preorder is computed. -/
def ofModel (elements : List A) (complete : ∀ entry : A, entry ∈ elements) (model : FiniteModel A)
    (language : LanguageDef) (sites : List Site := []) : Certificate A where
  elements := elements
  complete := complete
  model := model
  below := abstractBelow elements model language sites

end Certificate

/-! ## Models by search -/

/-- What a model interprets: a constructor with its number of arguments, abstraction over one
variable or over several at once, and the unit and join of each collection kind. -/
inductive Slot where
  | operation (label : String) (arity : ℕ)
  | abstraction
  | multiAbstraction (arity : ℕ)
  | collectionUnit (kind : CollType)
  | collectionJoin (kind : CollType)
  deriving DecidableEq, Repr

/-- A signature: the slots a model interprets. -/
abbrev Signature := List Slot

section Cells

variable (elements : List A) (junk : A)

/-- The inputs of a slot: argument vectors, or the graphs of the functions an abstraction takes. -/
def inputs : Slot → List (List A)
  | .operation _ arity => vectors elements arity
  | .abstraction => vectors elements elements.length
  | .multiAbstraction arity => vectors elements (vectors elements arity).length
  | .collectionUnit _ => [[]]
  | .collectionJoin _ => vectors elements 2

/-- The graph of a function of several values, over the vectors of their number. -/
def graphMulti (arity : ℕ) (function : (Fin arity → A) → A) : List A :=
  (vectors elements arity).map fun vector => function fun index => vector.getD index junk

/-- Read a slot at an input from cells addressed by the slot's position in the signature and the
input's position among the slot's inputs; a missing cell reads `junk`. -/
def readCell (signature : Signature) (cell : ℕ → ℕ → Option A) (slot : Slot) (input : List A) : A :=
  (cell (signature.idxOf slot) ((inputs elements slot).idxOf input)).getD junk

/-- **The model of a reading of cells.** -/
def cellModel (signature : Signature) (cell : ℕ → ℕ → Option A) : FiniteModel A where
  junk := junk
  lam function := readCell elements junk signature cell .abstraction (elements.map function)
  lamMulti arity function :=
    readCell elements junk signature cell (.multiAbstraction arity) (graphMulti elements junk arity function)
  collectionUnit kind := readCell elements junk signature cell (.collectionUnit kind) []
  collectionJoin kind first second := readCell elements junk signature cell (.collectionJoin kind) [first, second]
  operation label arguments := readCell elements junk signature cell (.operation label arguments.length) arguments

/-- A model from full tables: for each slot, its outputs on its inputs in enumeration order. -/
def tableModel (signature : Signature) (outputs : List (List A)) : FiniteModel A :=
  cellModel elements junk signature fun slot input => outputs[slot]?.bind (·[input]?)

/-- Cells assigned one by one: a slot position, an input position, and the value there. -/
abbrev Cells (A : Type) := List ((ℕ × ℕ) × A)

/-- A model from assigned cells; every other cell reads `junk`. -/
def sparseModel (signature : Signature) (cells : Cells A) : FiniteModel A :=
  cellModel elements junk signature fun slot input => cells.lookup (slot, input)

end Cells

/-- All lists of a length over the elements. -/
def allLists (elements : List A) (length : ℕ) : List (List A) := vectors elements length

/-- Every assignment of tables to a signature. -/
def tableChoices (elements : List A) : Signature → List (List (List A))
  | [] => [[]]
  | slot :: rest =>
      (allLists elements (inputs elements slot).length).flatMap fun table =>
        (tableChoices elements rest).map (table :: ·)

/-- **Every model over the elements** for a signature, with a fixed value for ill-formed patterns. -/
def models (elements : List A) (junk : A) (signature : Signature) : List (FiniteModel A) :=
  (tableChoices elements signature).map (tableModel elements junk signature)

variable {language : LanguageDef} {goals : List Pattern}

/-- The values the goal patterns take in a model, under every table: the least set a goal check
accepts. -/
def goalValues (elements : List A) (model : FiniteModel A) (goals : List Pattern) : List A :=
  goals.flatMap fun goal =>
    (tables elements (firstDepths (occurrences 0 goal))).map fun table =>
      eval model (tableValuation model elements table) [] goal

/-- **Search for a certificate**: some model over the elements, with its computed preorder and the goal
values as accepted set, passes the verdict. -/
def cannotReachBySearch (elements : List A) (complete : ∀ entry : A, entry ∈ elements) (junk : A)
    (signature : Signature) (language : LanguageDef) (goals : List Pattern) (state : Pattern) : Bool :=
  (models elements junk signature).any fun model =>
    (Certificate.ofModel elements complete model language).cannotReach language goals
      (fun entry => entry ∈ goalValues elements model goals) state

theorem cannotReachBySearch_of_check {elements : List A} {complete : ∀ entry : A, entry ∈ elements} {junk : A}
    {signature : Signature} {state : Pattern}
    (checked : cannotReachBySearch elements complete junk signature language goals state = true) :
    ¬ Reaches (between (languageSpan language) ObjectState) (Goal goals) state := by
  obtain ⟨model, _, found⟩ := List.any_eq_true.mp checked
  exact Certificate.cannotReach_of_check found

namespace Certificate

/-- **A certificate from assigned cells**: the model they give, with its computed preorder. -/
def ofCells (elements : List A) (complete : ∀ entry : A, entry ∈ elements) (junk : A) (signature : Signature)
    (cells : Cells A) (language : LanguageDef) (sites : List Site := []) : Certificate A :=
  ofModel elements complete (sparseModel elements junk signature cells) language sites

/-- The accepted set of a certificate from cells: the values of the goals. -/
def goalAccept (certificate : Certificate A) (goals : List Pattern) (entry : A) : Bool :=
  entry ∈ goalValues certificate.elements certificate.model goals

end Certificate

/-! ## Finding a model cell by cell

The finder assigns only the cells an evaluation reaches, in the order it reaches them, and abandons a
partial model as soon as the state reaches a goal value through steps that are already determined:
assigning more cells only determines more steps, so such a partial model has no completion. What it
returns is a list of cells, which the kernel checks as a certificate; the finder itself carries no
proof obligation. -/

/-- A value under a partial model: known, or waiting for a cell. -/
inductive CellValue (A : Type) where
  | known (value : A)
  | waiting (slot input : ℕ)
  deriving DecidableEq, Repr

namespace CellValue

def value? {A : Type} : CellValue A → Option A
  | known value => some value
  | waiting _ _ => none

/-- The first value of a list that waits for a cell. -/
def firstWait {A : Type} (values : List (CellValue A)) : Option (CellValue A) := values.find? (·.value?.isNone)

end CellValue

open CellValue

section Finder

variable (elements : List A) (junk : A) (signature : Signature) (cells : Cells A)

/-- Read a slot under assigned cells: wait for the first input that waits, or for the cell itself. -/
def readPartial (slot : Slot) (input : List (CellValue A)) : CellValue A :=
  match firstWait input with
  | some wait => wait
  | none =>
      let values := input.filterMap value?
      let position := signature.idxOf slot
      let index := (inputs elements slot).idxOf values
      if position < signature.length then
        match cells.lookup (position, index) with
        | some value => .known value
        | none => .waiting position index
      else .known junk

/-- **The partial model of assigned cells**: a value waits for the first unassigned cell it reads. -/
def partialModel : FiniteModel (CellValue A) where
  junk := .known junk
  lam function := readPartial elements junk signature cells .abstraction (elements.map fun entry => function (.known entry))
  lamMulti arity function := readPartial elements junk signature cells (.multiAbstraction arity)
    ((vectors elements arity).map fun vector => function fun index => .known (vector.getD index junk))
  collectionUnit kind := readPartial elements junk signature cells (.collectionUnit kind) []
  collectionJoin kind first second := readPartial elements junk signature cells (.collectionJoin kind) [first, second]
  operation label arguments := readPartial elements junk signature cells (.operation label arguments.length) arguments

/-- A table read in an environment that may wait. -/
def partialValuation (table : Table A) : Valuation (CellValue A) := fun name env =>
  match table.find? (·.1 == name) with
  | some (_, depth, outputs) =>
      match firstWait (env.take depth) with
      | some wait => wait
      | none => .known (outputs.getD ((vectors elements depth).idxOf ((env.take depth).filterMap value?)) junk)
  | none => .known junk

/-- The outcome of evaluating everything a certificate check evaluates under assigned cells. -/
inductive Outcome where
  | fails
  | needs (slot input : ℕ)
  | holds
  deriving DecidableEq, Repr

/-- Evaluate a pattern under a table of the metavariables and assigned cells. -/
def partialEval (table : Table A) (pattern : Pattern) : CellValue A :=
  eval (partialModel elements junk signature cells) (partialValuation elements junk table) [] pattern

/-- A step a rule forces under one table: the pairs its congruence premises need, and the values of
its two sides. -/
abbrev ForcedStep (A : Type) := List (A × A) × CellValue A × CellValue A

/-- **The least relation the steps force**, closed under the sites and composition: a step joins once
the pairs it needs are in, reflexively. Also the cells that ready steps and site steps still wait for. -/
def partialClosure (sites : List Site) (steps : List (ForcedStep A)) :
    ℕ → List (A × A) → List (A × A) × List (CellValue A)
  | 0, relation => (relation, [])
  | rounds + 1, relation =>
      let model := partialModel elements junk signature cells
      let holds := fun (pair : A × A) => pair.1 == pair.2 || pair ∈ relation
      let ready := steps.filter fun step => step.1.all holds
      let forced := ready.filterMap fun step => (step.2.1.value?).bind fun first => (step.2.2.value?).map (first, ·)
      let siteValues := sites.flatMap fun site =>
        (vectors elements site.2.1).flatMap fun arguments =>
          relation.filterMap fun pair =>
            if arguments.getD site.2.2 junk == pair.1 then
              some (model.operation site.1 (arguments.map .known),
                model.operation site.1 ((arguments.set site.2.2 pair.2).map .known))
            else none
      let determined := siteValues.filterMap fun pair => (pair.1.value?).bind fun first => (pair.2.value?).map (first, ·)
      let waits := (ready.flatMap fun step => [step.2.1, step.2.2]).filter (·.value?.isNone) ++
        siteValues.flatMap fun pair => [pair.1, pair.2].filter (·.value?.isNone)
      let next := (relation ++ forced ++ determined ++ relation.flatMap fun first => relation.filterMap fun second =>
        if first.2 == second.1 then some (first.1, second.2) else none).dedup
      if next.length == relation.length then (relation, waits) else partialClosure sites steps rounds next

/-- Which steps the language takes: root steps of its rules, or its contextual semantics, where
congruence premises make steps conditional. -/
inductive Semantics where
  | root
  | contextual
  deriving DecidableEq, Repr

/-- The steps the rules force under every table, for a semantics. -/
def forcedSteps (language : LanguageDef) : Semantics → List (ForcedStep A)
  | .root => language.rewrites.flatMap fun rule =>
      (tables elements (ruleSpec rule)).map fun table =>
        ([], partialEval elements junk signature cells table rule.left,
          partialEval elements junk signature cells table rule.right)
  | .contextual => language.rewrites.flatMap fun rule =>
      (tables elements (contextualSpec rule)).map fun table =>
        let valuation := outerValuation (fun name => (depthIn rule name).getD 0)
          (partialValuation elements junk table)
        let needs := rule.premises.flatMap fun premise =>
          match congruencePair? premise with
          | some (source, target) =>
              (vectors elements ((depthIn rule source).getD 0)).filterMap fun env =>
                (((valuation source (env.map .known)).value?).bind fun first =>
                  ((valuation target (env.map .known)).value?).map (first, ·))
          | none => []
        (needs, eval (partialModel elements junk signature cells) valuation [] rule.left,
          eval (partialModel elements junk signature cells) valuation [] rule.right)

/-- **Analyze assigned cells**: fail when the state already reaches a goal value or a collection join
already fails to commute, need the first cell some evaluation waits for, or hold. -/
def analyze (language : LanguageDef) (semantics : Semantics) (sites : List Site) (goals : List Pattern)
    (state : Pattern) : Outcome :=
  let start := partialEval elements junk signature cells [] state
  let goalValues := goals.flatMap fun goal =>
    (tables elements (firstDepths (occurrences 0 goal))).map fun table => partialEval elements junk signature cells table goal
  let model := partialModel elements junk signature cells
  let commutations := [CollType.hashBag, CollType.hashSet].flatMap fun kind =>
    if signature.contains (.collectionJoin kind) then
      elements.flatMap fun first => elements.flatMap fun second => elements.map fun rest =>
        (model.collectionJoin kind (.known first) (model.collectionJoin kind (.known second) (.known rest)),
          model.collectionJoin kind (.known second) (model.collectionJoin kind (.known first) (.known rest)))
    else []
  let (closure, stepWaits) := partialClosure elements junk signature cells sites
    (forcedSteps elements junk signature cells language semantics) (elements.length * elements.length + 1) []
  let reaches := match start with
    | .known first => goalValues.any fun goal => match goal with
        | .known second => first == second || (first, second) ∈ closure
        | .waiting _ _ => false
    | .waiting _ _ => false
  let clash := commutations.any fun pair => match pair with
    | (.known first, .known second) => first != second
    | _ => false
  if reaches || clash then .fails else
    match firstWait (start :: goalValues ++ stepWaits ++ commutations.flatMap fun pair => [pair.1, pair.2]) with
    | some (.waiting slot input) => .needs slot input
    | _ => .holds

/-- The values worth trying for a new cell: those already in use and one fresh value, in the order of
the elements. Any other fresh value gives the same model up to renaming the values. -/
def tryValues (cells : Cells A) : List A :=
  let used := junk :: cells.map (·.2)
  let fresh := elements.find? (· ∉ used)
  elements.filter fun entry => entry ∈ used || some entry == fresh

/-- **Depth-first search over the cells evaluations reach**, one fresh value at a time. -/
def explore (language : LanguageDef) (semantics : Semantics) (sites : List Site) (goals : List Pattern)
    (state : Pattern) : ℕ → Cells A → Option (Cells A)
  | 0, _ => none
  | fuel + 1, cells =>
      match analyze elements junk signature cells language semantics sites goals state with
      | .fails => none
      | .holds => some cells
      | .needs slot input => (tryValues elements junk cells).findSome? fun entry =>
          explore language semantics sites goals state fuel (((slot, input), entry) :: cells)

end Finder

/-- **Find cells for a certificate**: at most one assignment per cell of the signature. -/
def findCells (elements : List A) (junk : A) (signature : Signature) (language : LanguageDef)
    (sites : List Site) (goals : List Pattern) (state : Pattern) (semantics : Semantics := .root) :
    Option (Cells A) :=
  explore elements junk signature language semantics sites goals state
    ((signature.map fun slot => (inputs elements slot).length).sum + 1) []

/-! ## The preorder the contextual semantics forces -/

section ContextualPreorder

variable (elements : List A) (model : FiniteModel A)

/-- The steps the rules force under every table, with the pairs their congruence premises need. -/
def contextualSteps (language : LanguageDef) : List (List (A × A) × A × A) :=
  language.rewrites.flatMap fun rule =>
    (tables elements (contextualSpec rule)).map fun table =>
      let valuation := outerValuation (fun name => (depthIn rule name).getD 0) (tableValuation model elements table)
      (rule.premises.flatMap fun premise =>
          match congruencePair? premise with
          | some (source, target) =>
              (vectors elements ((depthIn rule source).getD 0)).map fun env => (valuation source env, valuation target env)
          | none => [],
        eval model valuation [] rule.left, eval model valuation [] rule.right)

/-- **The least relation the rules force**: a step joins once the pairs its premises need are in. -/
def contextualClosure (steps : List (List (A × A) × A × A)) : ℕ → List (A × A) → List (A × A)
  | 0, relation => relation
  | rounds + 1, relation =>
      let holds := fun (pair : A × A) => pair.1 == pair.2 || pair ∈ relation
      let forced := steps.filterMap fun step => if step.1.all holds then some step.2 else none
      let next := (relation ++ forced ++ relation.flatMap fun first => relation.filterMap fun second =>
        if first.2 == second.1 then some (first.1, second.2) else none).dedup
      if next.length == relation.length then relation else contextualClosure steps rounds next

/-- The preorder the contextual semantics forces, read reflexively. -/
def contextualBelow (language : LanguageDef) : A → A → Bool :=
  let closure := contextualClosure (contextualSteps elements model language) (elements.length * elements.length + 1) []
  fun first second => first == second || (first, second) ∈ closure

end ContextualPreorder

namespace Certificate

/-- **A certificate for the contextual semantics from assigned cells**: the model they give, with the
preorder its rules force. -/
def ofContextualCells (elements : List A) (complete : ∀ entry : A, entry ∈ elements) (junk : A) (signature : Signature)
    (cells : Cells A) (language : LanguageDef) : Certificate A where
  elements := elements
  complete := complete
  model := sparseModel elements junk signature cells
  below := contextualBelow elements (sparseModel elements junk signature cells) language

end Certificate

end Mettapedia.OSLF.Framework.FiniteModels
