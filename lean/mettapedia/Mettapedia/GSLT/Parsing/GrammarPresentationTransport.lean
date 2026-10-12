import Mettapedia.OSLF.Framework.GrammarDerives
import Mettapedia.GSLT.Core.SemanticInvariant

/-!
# Changing terminal notation in authored language grammars

A terminal bijection changes a `LanguageDef`'s concrete notation while
retaining constructor labels, categories, parameter scopes and all equations
and rewrites. The existing grammar derivation relation is preserved and
reflected with the exact same syntax tree. Its bounded complete enumerator
therefore recognizes exactly the same trees, including ambiguity.

This boundary starts at tokens. It does not identify a host reader with a
source lexer, or claim a byte parser or packed-forest realization.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.GrammarPresentationTransport

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.GrammarDerives

/-- The supported derivation fragment uses terminals and first-order
nonterminals. Unsupported syntax items are retained and remain unsupported. -/
def mapItem (tokens : String ≃ String) : SyntaxItem → SyntaxItem
  | .terminal token => .terminal (tokens token)
  | other => other

def mapRule (tokens : String ≃ String) (rule : GrammarRule) : GrammarRule :=
  { rule with syntaxPattern := rule.syntaxPattern.map (mapItem tokens) }

def mapLanguage (tokens : String ≃ String) (lang : LanguageDef) : LanguageDef :=
  { lang with terms := lang.terms.map (mapRule tokens) }

@[simp] theorem paramSort_mapRule (tokens : String ≃ String)
    (rule : GrammarRule) (name : String) :
    paramSort? (mapRule tokens rule) name = paramSort? rule name := rfl

@[simp] theorem mapItem_inverse (tokens : String ≃ String) (item : SyntaxItem) :
    mapItem tokens.symm (mapItem tokens item) = item := by
  cases item <;> simp [mapItem]

@[simp] theorem mapRule_inverse (tokens : String ≃ String) (rule : GrammarRule) :
    mapRule tokens.symm (mapRule tokens rule) = rule := by
  cases rule
  simp [mapRule, List.map_map, Function.comp_def]

@[simp] theorem mapLanguage_inverse (tokens : String ≃ String) (lang : LanguageDef) :
    mapLanguage tokens.symm (mapLanguage tokens lang) = lang := by
  cases lang
  simp [mapLanguage, List.map_map, Function.comp_def]

theorem mapLanguage_comp (first second : String ≃ String) (lang : LanguageDef) :
    mapLanguage second (mapLanguage first lang) = mapLanguage (first.trans second) lang := by
  have itemLaw : ∀ item, mapItem second (mapItem first item) =
      mapItem (first.trans second) item := by
    intro item
    cases item <;> rfl
  have ruleLaw : ∀ rule, mapRule second (mapRule first rule) =
      mapRule (first.trans second) rule := by
    intro rule
    cases rule
    simp [mapRule, List.map_map, Function.comp_def, itemLaw]
  cases lang
  simp [mapLanguage, List.map_map, Function.comp_def, ruleLaw]

/-- Every source derivation remains valid with the same complete tree. -/
theorem derives_map (tokens : String ≃ String) {lang : LanguageDef}
    {sort : String} {input : List String} {tree : Pattern}
    (derivation : Derives lang sort input tree) :
    Derives (mapLanguage tokens lang) sort (input.map tokens) tree := by
  apply Derives.rec
    (motive_1 := fun sort input tree _ =>
      Derives (mapLanguage tokens lang) sort (input.map tokens) tree)
    (motive_2 := fun rule items input children _ =>
      DerivesItems (mapLanguage tokens lang) (mapRule tokens rule)
        (items.map (mapItem tokens)) (input.map tokens) children)
    (t := derivation)
  · intro rule member category same input children _ mappedItems
    exact .rule (mapRule tokens rule) (List.mem_map.mpr ⟨rule, member, rfl⟩)
      category same _ children mappedItems
  · intro rule
    exact .nil _
  · intro rule token rest input children _ mappedTail
    exact .terminal _ _ _ _ _ mappedTail
  · intro rule name sort lookup sub tree _ rest input children _ mappedSub mappedTail
    simpa only [List.map_cons, List.map_append, mapItem] using
      (DerivesItems.nonTerminal (mapRule tokens rule) name sort lookup
        (sub.map tokens) tree mappedSub (rest.map (mapItem tokens))
        (input.map tokens) children mappedTail)

/-- Reflection rules out invented parses after a notation change. -/
theorem derives_map_iff (tokens : String ≃ String) (lang : LanguageDef)
    (sort : String) (input : List String) (tree : Pattern) :
    Derives (mapLanguage tokens lang) sort (input.map tokens) tree ↔
      Derives lang sort input tree := by
  constructor
  · intro derivation
    have reflected := derives_map tokens.symm derivation
    simpa only [mapLanguage_inverse, List.map_map, Equiv.symm_comp_self,
      List.map_id] using reflected
  · exact derives_map tokens

/-- Any fixed constructor-directed lowering sees the same results through
either notation. Correctness of the lowering itself is a separate theorem. -/
theorem lowered_map_iff {Payload : Type} (tokens : String ≃ String) (lang : LanguageDef)
    (sort : String) (input : List String) (lower : Pattern → Option Payload)
    (payload : Payload) :
    (∃ tree, Derives (mapLanguage tokens lang) sort (input.map tokens) tree ∧
      lower tree = some payload) ↔
    (∃ tree, Derives lang sort input tree ∧ lower tree = some payload) := by
  simp only [derives_map_iff]

/-- The existing complete bounded producer has identical tree membership;
no second parser or enumeration semantics is introduced. -/
theorem enumDerives_map_iff (tokens : String ≃ String) (lang : LanguageDef)
    (fuel : Nat) (sort : String) (input : List String) (tree : Pattern) :
    tree ∈ enumDerives (mapLanguage tokens lang) fuel sort (input.map tokens) ↔
      tree ∈ enumDerives lang fuel sort input := by
  rw [mem_enumDerives_iff, mem_enumDerives_iff, derives_map_iff]

theorem uniqueDerivation_map_iff (tokens : String ≃ String) (lang : LanguageDef)
    (sort : String) (input : List String) :
    UniqueDerivation (mapLanguage tokens lang) sort (input.map tokens) ↔
      UniqueDerivation lang sort input := by
  constructor
  · intro unique first second hfirst hsecond
    exact unique first second (derives_map tokens hfirst) (derives_map tokens hsecond)
  · intro unique first second hfirst hsecond
    exact unique first second ((derives_map_iff tokens lang sort input first).mp hfirst)
      ((derives_map_iff tokens lang sort input second).mp hsecond)

/-! ## A reified grammar-edit program

Commands and presentation descriptors are data in the operational state.
History records the change of vocabulary, so the independent observer can
ask about every input in the original vocabulary, not only one sample.
-/

namespace NotationMachine

open Mettapedia.GSLT

abbrev Command := String × String

def vocabulary (commands : List Command) : String ≃ String :=
  commands.foldr (fun command rest => (Equiv.swap command.1 command.2).trans rest)
    (Equiv.refl String)

@[simp] theorem vocabulary_nil : vocabulary [] = Equiv.refl String := rfl

@[simp] theorem vocabulary_cons (command : Command) (rest : List Command) :
    vocabulary (command :: rest) = (Equiv.swap command.1 command.2).trans (vocabulary rest) :=
  rfl

theorem vocabulary_append (first second : List Command) :
    vocabulary (first ++ second) = (vocabulary first).trans (vocabulary second) := by
  induction first with
  | nil => rfl
  | cons command rest ih =>
      apply Equiv.ext
      intro token
      simp only [List.cons_append, vocabulary_cons, ih, Equiv.coe_trans,
        Function.comp_apply]

structure State where
  presentation : LanguageDef
  history : List Command
  pending : List Command

/-- A command changes the actual grammar descriptor and its vocabulary map,
and is then consumed. Equation and rewrite declarations are retained. -/
inductive Step : State → State → Prop where
  | edit (presentation : LanguageDef) (history : List Command)
      (command : Command) (rest : List Command) :
      Step ⟨presentation, history, command :: rest⟩
        ⟨mapLanguage (Equiv.swap command.1 command.2) presentation,
          history ++ [command], rest⟩

def execute (state : State) : Option State :=
  match state.pending with
  | [] => none
  | command :: rest => some
      ⟨mapLanguage (Equiv.swap command.1 command.2) state.presentation,
        state.history ++ [command], rest⟩

/-- Execution implements exactly the authored command rule. -/
theorem execute_iff_step (first second : State) :
    execute first = some second ↔ Step first second := by
  constructor
  · rcases first with ⟨presentation, history, pending⟩
    cases pending with
    | nil => simp [execute]
    | cons command rest =>
        intro equal
        have same := Option.some.inj equal
        subst second
        exact .edit presentation history command rest
  · intro step
    cases step
    rfl

def system : GSLT where
  Term := State
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Step
  rewrites_resp_left := by
    intro first other target equal step
    cases equal
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro first target other step equal
    cases equal
    exact step

/-- The observer is the independent source-grammar derivation relation at
every category, input and complete syntax tree in the original vocabulary. -/
def observe (state : State) : String → List String → Pattern → Prop :=
  fun sort input tree =>
    Derives state.presentation sort (input.map (vocabulary state.history)) tree

theorem step_observe {first second : State} (step : Step first second) :
    observe first = observe second := by
  cases step with
  | edit presentation history command rest =>
      funext sort input tree
      apply propext
      change Derives presentation sort (input.map (vocabulary history)) tree ↔
        Derives (mapLanguage (Equiv.swap command.1 command.2) presentation) sort
          (input.map (vocabulary (history ++ [command]))) tree
      rw [vocabulary_append]
      simpa only [vocabulary_cons, vocabulary_nil, List.map_map, Equiv.coe_trans, Equiv.coe_refl,
        Function.comp_def, id] using
        (derives_map_iff (Equiv.swap command.1 command.2) presentation sort
          (input.map (vocabulary history)) tree).symm

/-- Whole-program semantic preservation follows from the common GSLT path
invariant, rather than a second grammar-program semantics. -/
def invariant : SemanticInvariant system (String → List String → Pattern → Prop) where
  denote := observe
  equation := fun equal => congrArg observe equal
  rewrite := step_observe

theorem path_observe {first second : State}
    (path : IndexedOperational.ExecutionPath system first second) :
    observe first = observe second := invariant.executionPath_eq path

end NotationMachine

end Mettapedia.GSLT.Parsing.GrammarPresentationTransport
