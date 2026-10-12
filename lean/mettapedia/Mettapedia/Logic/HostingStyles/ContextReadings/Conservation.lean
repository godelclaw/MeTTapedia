import Mettapedia.Logic.HostingStyles.ContextReadings.PresentedReadings
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceInteraction

/-!
# What the linear reading buys: nothing that fills a hole is lost or doubled

Count the constructor applications of a pattern whose label is in a chosen
class (`tokens`).  A pattern with holes adds the tokens of what fills it, each
filling as often as its hole occurs (`tokens_fill`).  Hence:

* **Filling a linear context keeps the count**: the tokens of the filled
  context are those of the context and of each filling, once
  (`linear_fill_tokens`).  A step from one linear context of a datum to
  another neither loses nor doubles the tokens of the datum
  (`tokens_transfer`).
* A context of a reading counts each filling as often as its hole occurs in
  its pattern, and exactly once at a hole of an interface that is not declared
  (`reading_fill_tokens`).

## The two readings of a space

A small presented language (`cellLanguage`) has a space that holds one datum
and two ways of receiving it:

    take (cell d)  ⟶  got d                 the datum leaves the space
    read (cell d)  ⟶  seen d (cell d)       the datum stays

* The consuming receive is linear in the datum: both sides are linear
  contexts of it (`takeBefore`, `takeAfter`), the step is a transition between
  their fillings (`take_transition`), and it keeps the tokens of the datum
  (`take_keeps_tokens`).
* The read copies the datum: its right side uses the hole twice.  It is a
  context of the reading in which data may be copied (`readAfter`), the step
  is a transition (`read_transition`), it doubles the tokens of the datum
  (`read_doubles_tokens`), and **no linear context does what it does**
  (`readAfter_not_linear`).

The same two readings on the existing model of a space as a bag of
occurrences: a linear take hands over the datum and leaves a store that
together with it has the occurrences of the store it was taken from
(`linearTake_count`); a persistent read leaves the store as it is, so the
store together with the datum handed over has one occurrence more
(`persistentRead_count`).  Between two locations of a network a consuming
receive keeps the number of occurrences of every atom
(`consumingReceive_count`), and an observing one adds an occurrence of the
datum (`observingReceive_count`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.ContextReadings

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule_eq_syntactic)
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution (applyBindingsForRule_eq_applyBindings)
open Mettapedia.Logic.HostingStyles.PrimeCandidate

/-! ## Counting tokens -/

mutual
  /-- **The tokens of a pattern**: the number of its constructor applications
  whose label is counted. -/
  def tokens (counted : String → Bool) : Pattern → Nat
    | .bvar _ => 0
    | .fvar _ => 0
    | .apply label arguments => (if counted label then 1 else 0) + tokensList counted arguments
    | .lambda _ body => tokens counted body
    | .multiLambda _ _ body => tokens counted body
    | .subst body replacement => tokens counted body + tokens counted replacement
    | .collection _ elements _ => tokensList counted elements

  /-- The tokens of a list of patterns. -/
  def tokensList (counted : String → Bool) : List Pattern → Nat
    | [] => 0
    | pattern :: patterns => tokens counted pattern + tokensList counted patterns
end

mutual
  /-- The tokens of a pattern with holes, its holes not counted. -/
  def contextTokens {ι : Type} (counted : String → Bool) : MultiHoleContext ι → Nat
    | .hole _ => 0
    | .bvar _ => 0
    | .fvar _ => 0
    | .apply label arguments =>
        (if counted label then 1 else 0) + contextTokensList counted arguments
    | .lambda _ body => contextTokens counted body
    | .multiLambda _ _ body => contextTokens counted body
    | .subst body replacement => contextTokens counted body + contextTokens counted replacement
    | .collection _ elements _ => contextTokensList counted elements

  /-- The tokens of a list of patterns with holes. -/
  def contextTokensList {ι : Type} (counted : String → Bool) : List (MultiHoleContext ι) → Nat
    | [] => 0
    | context :: contexts => contextTokens counted context + contextTokensList counted contexts
end

mutual
  /-- **A pattern with holes adds the tokens of what fills its holes**, each
  as often as its hole occurs. -/
  theorem tokens_fill {ι : Type} (counted : String → Bool) (filling : ι → Pattern) :
      ∀ context : MultiHoleContext ι,
        tokens counted (context.fill filling) =
          contextTokens counted context +
            (context.holes.map fun index => tokens counted (filling index)).sum
    | .hole index => by
        simp [MultiHoleContext.fill, contextTokens, MultiHoleContext.holes]
    | .bvar index => by
        simp [MultiHoleContext.fill, contextTokens, MultiHoleContext.holes, tokens]
    | .fvar name => by
        simp [MultiHoleContext.fill, contextTokens, MultiHoleContext.holes, tokens]
    | .apply label arguments => by
        rw [MultiHoleContext.fill, tokens, contextTokens, MultiHoleContext.holes,
          tokensList_fillList counted filling arguments]
        omega
    | .lambda binder body => by
        rw [MultiHoleContext.fill, tokens, contextTokens, MultiHoleContext.holes,
          tokens_fill counted filling body]
    | .multiLambda arity binders body => by
        rw [MultiHoleContext.fill, tokens, contextTokens, MultiHoleContext.holes,
          tokens_fill counted filling body]
    | .subst body replacement => by
        rw [MultiHoleContext.fill, tokens, contextTokens, MultiHoleContext.holes,
          tokens_fill counted filling body, tokens_fill counted filling replacement,
          List.map_append, List.sum_append]
        omega
    | .collection kind elements rest => by
        rw [MultiHoleContext.fill, tokens, contextTokens, MultiHoleContext.holes,
          tokensList_fillList counted filling elements]

  /-- The same along a list of patterns with holes. -/
  theorem tokensList_fillList {ι : Type} (counted : String → Bool) (filling : ι → Pattern) :
      ∀ contexts : List (MultiHoleContext ι),
        tokensList counted (MultiHoleContext.fillList filling contexts) =
          contextTokensList counted contexts +
            ((MultiHoleContext.holesList contexts).map fun index =>
              tokens counted (filling index)).sum
    | [] => by
        simp [MultiHoleContext.fillList, tokensList, contextTokensList,
          MultiHoleContext.holesList]
    | context :: contexts => by
        rw [MultiHoleContext.fillList, tokensList, contextTokensList, MultiHoleContext.holesList,
          tokens_fill counted filling context, tokensList_fillList counted filling contexts,
          List.map_append, List.sum_append]
        omega
end

/-- The sum over a list is the sum over its members, each as often as it
occurs. -/
theorem sum_map_eq_sum_count {α : Type} [Fintype α] [DecidableEq α] (list : List α)
    (value : α → Nat) : (list.map value).sum = ∑ index, list.count index * value index := by
  induction list with
  | nil => simp
  | cons head tail ih =>
      rw [List.map_cons, List.sum_cons, ih]
      have split : ∀ index, (head :: tail).count index * value index =
          tail.count index * value index + if head = index then value index else 0 := by
        intro index
        by_cases same : head = index
        · subst same
          simp [add_mul]
        · simp [same]
      simp only [split, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      omega

/-! ## Filling a linear context keeps the count -/

/-- **Filling a linear context keeps the count of tokens**: the tokens of the
filled context are those of the context and those of each filling, once. -/
theorem linear_fill_tokens {presentation : ValidatedLanguageDef} {arity : Type} [Fintype arity]
    {holes : arity → Contexts.Interface} {result : Contexts.Interface}
    (context : Contexts.Context presentation holes result) (counted : String → Bool)
    (filling : (index : arity) → Contexts.Term presentation.language (holes index)) :
    tokens counted (context.fill filling).1 =
      contextTokens counted context.shape + ∑ index, tokens counted (filling index).1 := by
  classical
  show tokens counted (context.shape.fill fun index => (filling index).1) = _
  rw [tokens_fill, ← List.sum_toFinset _ context.linear.1]
  congr 2
  exact Finset.eq_univ_iff_forall.mpr fun index => List.mem_toFinset.mpr (context.linear.2 index)

/-- **A linear context of one hole carries the tokens of what fills it.** -/
theorem label_tokens {base : BasePremiseEvaluator} {presentation : ValidatedLanguageDef}
    {source target : Contexts.Interface}
    (label : (contextTheory base presentation).Label source target) (counted : String → Bool)
    (term : Contexts.Term presentation.language source) :
    tokens counted ((contextTheory base presentation).apply label term).1 =
      contextTokens counted label.shape + tokens counted term.1 := by
  have filled := linear_fill_tokens label counted fun _ => term
  rwa [Fintype.sum_unique] at filled

/-- **From one linear context of a datum to another, the tokens of the datum
are neither lost nor doubled**: the two counts differ by what the contexts
themselves hold. -/
theorem tokens_transfer {base : BasePremiseEvaluator} {presentation : ValidatedLanguageDef}
    {source target : Contexts.Interface}
    (before after : (contextTheory base presentation).Label source target)
    (counted : String → Bool) (term : Contexts.Term presentation.language source) :
    tokens counted ((contextTheory base presentation).apply after term).1 +
        contextTokens counted before.shape =
      tokens counted ((contextTheory base presentation).apply before term).1 +
        contextTokens counted after.shape := by
  rw [label_tokens, label_tokens]
  omega

/-- **A context of a reading counts each filling as often as its hole occurs
in its pattern**, and once at a hole of an interface that is not declared. -/
theorem reading_fill_tokens {base : BasePremiseEvaluator} {presentation : ValidatedLanguageDef}
    {declared : Contexts.Interface → Prop} {arity : Type} [Fintype arity] [DecidableEq arity]
    {holes : arity → Contexts.Interface} {result : Contexts.Interface}
    (context : (contextTheory base presentation).RegionContext declared holes result) :
    ∃ shape : MultiHoleContext arity,
      (∀ index, ¬ declared (holes index) → shape.holes.count index = 1) ∧
      ∀ (counted : String → Bool)
        (filling : (index : arity) → Contexts.Term presentation.language (holes index)),
        tokens counted (context.act filling).1 =
          contextTokens counted shape +
            ∑ index, shape.holes.count index * tokens counted (filling index).1 := by
  obtain ⟨shape, acts, once⟩ := exists_shape context
  refine ⟨shape, once, fun counted filling => ?_⟩
  rw [acts, tokens_fill, sum_map_eq_sum_count]

/-! ## A space that holds a datum, received in two ways -/

/-- A datum with no part. -/
def tokenRule : GrammarRule :=
  { label := "token", category := "Datum", params := [], syntaxPattern := [] }

/-- A datum made from a datum. -/
def markRule : GrammarRule :=
  { label := "mark", category := "Datum", params := [.simple "inner" (.base "Datum")]
    syntaxPattern := [] }

/-- The space that holds one datum. -/
def cellRule : GrammarRule :=
  { label := "cell", category := "Space", params := [.simple "content" (.base "Datum")]
    syntaxPattern := [] }

/-- The request to take the datum out of a space. -/
def takeRule : GrammarRule :=
  { label := "take", category := "Process", params := [.simple "store" (.base "Space")]
    syntaxPattern := [] }

/-- The request to read the datum of a space. -/
def readRule : GrammarRule :=
  { label := "read", category := "Process", params := [.simple "store" (.base "Space")]
    syntaxPattern := [] }

/-- The datum that was taken. -/
def gotRule : GrammarRule :=
  { label := "got", category := "Process", params := [.simple "datum" (.base "Datum")]
    syntaxPattern := [] }

/-- The datum that was read, beside the space it was read from. -/
def seenRule : GrammarRule :=
  { label := "seen", category := "Process"
    params := [.simple "datum" (.base "Datum"), .simple "store" (.base "Space")]
    syntaxPattern := [] }

/-- **The consuming receive**: `take (cell datum) ⟶ got datum`. -/
def takeRewrite : RewriteRule :=
  { name := "take-consumes"
    typeContext := [("datum", .base "Datum")]
    premises := []
    left := .apply "take" [.apply "cell" [.fvar "datum"]]
    right := .apply "got" [.fvar "datum"] }

/-- **The read that leaves the datum in place**:
`read (cell datum) ⟶ seen datum (cell datum)`. -/
def readRewrite : RewriteRule :=
  { name := "read-keeps"
    typeContext := [("datum", .base "Datum")]
    premises := []
    left := .apply "read" [.apply "cell" [.fvar "datum"]]
    right := .apply "seen" [.fvar "datum", .apply "cell" [.fvar "datum"]] }

/-- **A space that holds one datum, with a consuming receive and a read.** -/
def cellLanguage : LanguageDef :=
  { name := "cell"
    types := [TypeDecl.plain "Datum", TypeDecl.plain "Space", TypeDecl.plain "Process"]
    terms := [tokenRule, markRule, cellRule, takeRule, readRule, gotRule, seenRule]
    equations := []
    rewrites := [takeRewrite, readRewrite] }

/-- The language of the cell passes the declaration gate. -/
theorem cellLanguage_validate : cellLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  case hequations => rfl
  case htypes => decide +kernel
  case hconstructors => decide +kernel
  case hrewrites => decide +kernel
  case hcategory => decide +kernel
  case hparams => decide +kernel
  case hsyntax => decide +kernel
  case hrewriteValid =>
    intro rewrite member
    exact LanguageDef.validateRewrite_eq_nil_of_plainRewriteOk
      (List.all_eq_true.mp
        (by decide +kernel :
          cellLanguage.rewrites.all (LanguageDef.plainRewriteOk cellLanguage) = true)
        rewrite member)

/-- The language of the cell, as a presentation. -/
def cellPresentation : ValidatedLanguageDef := ⟨cellLanguage, cellLanguage_validate⟩

/-- The closed data. -/
def datumInterface : Contexts.Interface := ⟨.base "Datum", []⟩

/-- The closed spaces. -/
def spaceInterface : Contexts.Interface := ⟨.base "Space", []⟩

/-- The closed processes of the cell. -/
def cellProcess : Contexts.Interface := ⟨.base "Process", []⟩

/-- The language of the cell has no equation, no bag, no set and no collection
algebra; so it keeps the weight of patterns (`keptWeight_of_equationFree`). -/
theorem cellLanguage_equationFree : cellLanguage.isEquationFree = true := by
  decide

/-- The consuming receive, on every datum. -/
theorem take_step (base : BasePremiseEvaluator) (datum : Pattern) :
    Step base cellLanguage (.apply "take" [.apply "cell" [datum]]) (.apply "got" [datum]) := by
  refine ⟨1, .rule (rule := takeRewrite) (initialBindings := [("datum", datum)])
    (by simp [cellLanguage]) ?_ (.nil _) ?_⟩
  · simp [matchPatternForRule_eq_syntactic, takeRewrite, matchPattern, matchArgs, mergeBindings]
  · rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide)]
    simp [takeRewrite, applyBindings]

/-- The read, on every datum. -/
theorem read_step (base : BasePremiseEvaluator) (datum : Pattern) :
    Step base cellLanguage (.apply "read" [.apply "cell" [datum]])
      (.apply "seen" [datum, .apply "cell" [datum]]) := by
  refine ⟨1, .rule (rule := readRewrite) (initialBindings := [("datum", datum)])
    (by simp [cellLanguage]) ?_ (.nil _) ?_⟩
  · simp [matchPatternForRule_eq_syntactic, readRewrite, matchPattern, matchArgs, mergeBindings]
  · rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide)]
    simp [readRewrite, applyBindings]

/-! ### The contexts of the datum -/

section CellContexts

variable (base : BasePremiseEvaluator)

/-- The space that holds what fills the hole. -/
def cellOf : (contextTheory base cellPresentation).Label datumInterface spaceInterface :=
  unaryContext cellPresentation (rule := cellRule) (name := "content") (by decide) rfl rfl []

/-- The request to take from the space that fills the hole. -/
def takeOf : (contextTheory base cellPresentation).Label spaceInterface cellProcess :=
  unaryContext cellPresentation (rule := takeRule) (name := "store") (by decide) rfl rfl []

/-- The request to read the space that fills the hole. -/
def readOf : (contextTheory base cellPresentation).Label spaceInterface cellProcess :=
  unaryContext cellPresentation (rule := readRule) (name := "store") (by decide) rfl rfl []

/-- **The left side of the consuming receive**, a linear context of the
datum: `take (cell □)`. -/
def takeBefore : (contextTheory base cellPresentation).Label datumInterface cellProcess :=
  (contextTheory base cellPresentation).compose (takeOf base) (cellOf base)

/-- **The right side of the consuming receive**, a linear context of the
datum: `got □`. -/
def takeAfter : (contextTheory base cellPresentation).Label datumInterface cellProcess :=
  unaryContext cellPresentation (rule := gotRule) (name := "datum") (by decide) rfl rfl []

/-- The left side of the read, a linear context of the datum:
`read (cell □)`. -/
def readBefore : (contextTheory base cellPresentation).Label datumInterface cellProcess :=
  (contextTheory base cellPresentation).compose (readOf base) (cellOf base)

/-- The datum beside a space: a linear context of two holes. -/
def seenOf :
    (contextTheory base cellPresentation).Context
      (fun index : Bool =>
        (⟨.base (bif index then "Space" else "Datum"), []⟩ : Contexts.Interface)) cellProcess :=
  binaryContext cellPresentation (rule := seenRule) (firstName := "datum") (secondName := "store")
    (fun index => bif index then "Space" else "Datum") (by decide) rfl rfl []

/-- `seen □ (cell □)`: a linear context of two data, one beside the space
that holds the other. -/
def seenBesideCell :
    (contextTheory base cellPresentation).Context
      (fun _ : Σ _ : Bool, Unit => datumInterface) cellProcess :=
  (contextTheory base cellPresentation).plug (innerArity := fun _ => Unit)
    (innerHoles := fun _ _ => datumInterface) (seenOf base) fun index =>
      match index with
      | false => (contextTheory base cellPresentation).identity datumInterface
      | true => cellOf base

/-- The data of the cell: the reading in which a datum may be discarded and
copied. -/
def cellData : Contexts.Interface → Prop := ofSorts ["Datum"]

/-- **Positive**: the closed data are data. -/
theorem cellData_datum : cellData datumInterface := ofSorts_base (by decide) []

/-- **Negative**: the closed processes are not. -/
theorem not_cellData_process : ¬ cellData cellProcess := not_ofSorts_base (by decide) []

/-- **The right side of the read**: `seen □ (cell □)` with one datum at both
holes.  A context of the reading in which data may be copied. -/
def readAfter :
    ((contextTheory base cellPresentation).regionReading cellData).Label datumInterface
      cellProcess :=
  ContextTheory.RegionContext.rename (theory := contextTheory base cellPresentation)
    (declared := cellData) (holes := fun _ : Unit => datumInterface)
    (fun _ : Σ _ : Bool, Unit => ()) (fun _ linear => (linear cellData_datum).elim)
    (ContextTheory.RegionContext.ofContext (seenBesideCell base)
      fun free => (not_cellData_process free).elim)

/-- The left side of the consuming receive, filled. -/
theorem apply_takeBefore (datum : Contexts.Term cellLanguage datumInterface) :
    ((contextTheory base cellPresentation).apply (takeBefore base) datum).1 =
      .apply "take" [.apply "cell" [datum.1]] :=
  congrArg Subtype.val
    ((contextTheory base cellPresentation).apply_compose (takeOf base) (cellOf base) datum)

/-- The right side of the consuming receive, filled. -/
theorem apply_takeAfter (datum : Contexts.Term cellLanguage datumInterface) :
    ((contextTheory base cellPresentation).apply (takeAfter base) datum).1 =
      .apply "got" [datum.1] :=
  rfl

/-- The left side of the read, filled. -/
theorem apply_readBefore (datum : Contexts.Term cellLanguage datumInterface) :
    ((contextTheory base cellPresentation).apply (readBefore base) datum).1 =
      .apply "read" [.apply "cell" [datum.1]] :=
  congrArg Subtype.val
    ((contextTheory base cellPresentation).apply_compose (readOf base) (cellOf base) datum)

/-- The right side of the read, filled: the datum occurs twice. -/
theorem act_readAfter (datum : Contexts.Term cellLanguage datumInterface) :
    ((readAfter base).act fun _ => datum).1 =
      .apply "seen" [datum.1, .apply "cell" [datum.1]] :=
  rfl

/-- **The consuming receive is a transition between two linear contexts of
the datum.** -/
theorem take_transition (datum : Contexts.Term cellLanguage datumInterface) :
    (contextTheory base cellPresentation).rewrites
      ((contextTheory base cellPresentation).apply (takeBefore base) datum)
      ((contextTheory base cellPresentation).apply (takeAfter base) datum) := by
  refine ⟨_, _, Relation.EqvGen.refl _, ?_, Relation.EqvGen.refl _⟩
  rw [apply_takeBefore, apply_takeAfter]
  exact take_step base datum.1

/-- **The read is a transition from a linear context of the datum to a
context that uses it twice.** -/
theorem read_transition (datum : Contexts.Term cellLanguage datumInterface) :
    (contextTheory base cellPresentation).rewrites
      ((contextTheory base cellPresentation).apply (readBefore base) datum)
      ((readAfter base).act fun _ => datum) := by
  refine ⟨_, _, Relation.EqvGen.refl _, ?_, Relation.EqvGen.refl _⟩
  rw [apply_readBefore, act_readAfter]
  exact read_step base datum.1

/-- **The consuming receive keeps the tokens of the datum**: for every count
that does not count the constructors of the rule itself. -/
theorem take_keeps_tokens (counted : String → Bool) (take : counted "take" = false)
    (cell : counted "cell" = false) (got : counted "got" = false)
    (datum : Contexts.Term cellLanguage datumInterface) :
    tokens counted ((contextTheory base cellPresentation).apply (takeAfter base) datum).1 =
      tokens counted ((contextTheory base cellPresentation).apply (takeBefore base) datum).1 := by
  rw [apply_takeBefore, apply_takeAfter]
  simp [tokens, tokensList, take, cell, got]

/-- **The read doubles the tokens of the datum.** -/
theorem read_doubles_tokens (counted : String → Bool) (read : counted "read" = false)
    (cell : counted "cell" = false) (seen : counted "seen" = false)
    (datum : Contexts.Term cellLanguage datumInterface) :
    tokens counted ((readAfter base).act fun _ => datum).1 =
      tokens counted ((contextTheory base cellPresentation).apply (readBefore base) datum).1 +
        tokens counted datum.1 := by
  rw [apply_readBefore, act_readAfter]
  simp [tokens, tokensList, read, cell, seen]

/-- The token, a closed datum. -/
def tokenTerm : Contexts.Term cellLanguage datumInterface :=
  ⟨.apply "token" [], checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- The marked token, a closed datum. -/
def markedTerm : Contexts.Term cellLanguage datumInterface :=
  ⟨.apply "mark" [.apply "token" []], checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- **No linear context does what the right side of the read does**: a linear
context adds the weight of the datum once, the read twice. -/
theorem readAfter_not_linear :
    ¬ ∃ label : (contextTheory base cellPresentation).Label datumInterface cellProcess,
      ∀ datum : Contexts.Term cellLanguage datumInterface,
        ((contextTheory base cellPresentation).equations cellProcess).r
          ((contextTheory base cellPresentation).apply label datum)
          ((readAfter base).act fun _ => datum) := by
  rintro ⟨label, agrees⟩
  let sized := (keptWeight_of_equationFree cellLanguage_equationFree base).linearSize
    (presentation := cellPresentation)
  obtain ⟨labelWeight, adds⟩ := sized.additive label
  have once : ∀ datum : Contexts.Term cellLanguage datumInterface,
      weight ((readAfter base).act fun _ => datum).1 = labelWeight + weight datum.1 := by
    intro datum
    have counted := adds fun _ => datum
    rw [Fintype.sum_unique] at counted
    exact (sized.respects (agrees datum)).symm.trans counted
  have first := once tokenTerm
  have second := once markedTerm
  rw [act_readAfter] at first second
  have firstValue :
      weight (Pattern.apply "seen" [tokenTerm.1, .apply "cell" [tokenTerm.1]]) = 4 := by decide
  have firstDatum : weight tokenTerm.1 = 1 := by decide
  have secondValue :
      weight (Pattern.apply "seen" [markedTerm.1, .apply "cell" [markedTerm.1]]) = 6 := by decide
  have secondDatum : weight markedTerm.1 = 2 := by decide
  rw [firstValue, firstDatum] at first
  rw [secondValue, secondDatum] at second
  omega

end CellContexts

/-! ## The same two readings on a bag of occurrences -/

section Stores

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceChannelBoundary
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceInteraction
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceInteraction.GuardedTransaction

universe u v

variable {Location : Type u} {Atom : Type v} [DecidableEq Atom]

/-- **A linear take is linear in the datum**: the datum handed over and the
store that is left have together the occurrences of the store it was taken
from. -/
theorem linearTake_count {datum : Atom} {source target : Store Atom}
    (step : LinearTake datum source target) (atom : Atom) :
    (datum ::ₘ target).count atom = source.count atom := by
  cases step
  rfl

/-- **A persistent read copies the datum**: the store is left as it is, so
together with the datum handed over it has one occurrence more. -/
theorem persistentRead_count {datum : Atom} {source target : Store Atom}
    (step : PersistentRead datum source target) (atom : Atom) :
    (datum ::ₘ target).count atom = source.count atom + if atom = datum then 1 else 0 := by
  cases step
  exact Multiset.count_cons atom datum source

variable [DecidableEq Location]

/-- **A consuming receive between two locations keeps the occurrences of every
atom**: the datum is taken at one location and published at the other. -/
theorem consumingReceive_count {space receiver : Location} (apart : space ≠ receiver)
    {datum : Atom} {source middle : Network Location Atom}
    (step : LocatedStep .consume space datum source middle) (atom : Atom) :
    (publish ⟨receiver, datum⟩ middle space).count atom +
        (publish ⟨receiver, datum⟩ middle receiver).count atom =
      (source space).count atom + (source receiver).count atom := by
  cases step with
  | consume rest atLocation =>
      simp only [publish, Function.update_of_ne apart, Function.update_self,
        Function.update_of_ne (Ne.symm apart), atLocation, Multiset.count_cons]
      omega

/-- **An observing receive adds an occurrence of the datum**: the space is
left as it is and the datum is published at the other location. -/
theorem observingReceive_count {space receiver : Location} (apart : space ≠ receiver)
    {datum : Atom} {source middle : Network Location Atom}
    (step : LocatedStep .observe space datum source middle) (atom : Atom) :
    (publish ⟨receiver, datum⟩ middle space).count atom +
        (publish ⟨receiver, datum⟩ middle receiver).count atom =
      (source space).count atom + (source receiver).count atom +
        if atom = datum then 1 else 0 := by
  cases step with
  | observe present =>
      simp only [publish, Function.update_of_ne apart, Function.update_self,
        Multiset.count_cons]
      omega

end Stores

#print axioms tokens_fill
#print axioms sum_map_eq_sum_count
#print axioms linear_fill_tokens
#print axioms tokens_transfer
#print axioms reading_fill_tokens
#print axioms cellLanguage_validate
#print axioms take_step
#print axioms read_step
#print axioms take_transition
#print axioms read_transition
#print axioms take_keeps_tokens
#print axioms read_doubles_tokens
#print axioms readAfter_not_linear
#print axioms linearTake_count
#print axioms persistentRead_count
#print axioms consumingReceive_count
#print axioms observingReceive_count

end Mettapedia.Logic.HostingStyles.ContextReadings
