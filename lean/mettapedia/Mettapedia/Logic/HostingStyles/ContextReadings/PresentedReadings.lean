import Mettapedia.Logic.HostingStyles.ContextReadings.Multiplicity
import Mettapedia.Logic.HostingStyles.ContextReadings.EquationShapes

/-!
# The readings of a presented language

The contexts of a presented language (`Contexts.contextTheory`) are linear
patterns with holes.  Its readings (`ContextTheory.regionReading`) are then
theories of patterns in which a hole may occur any number of times:

* a context of a reading is a pattern with holes
  (`exists_shape`): what it does to its fillings is filling that pattern, and
  a hole of an interface that is not declared occurs in it exactly once;
* the contexts of a presented language have finitely many holes
  (`contextTheory_finiteHoles`), so a weight that the static equivalence keeps
  is a size of every reading that counts each hole as often as it occurs
  (`KeptWeight.readingSize`);
* for such a language with a term, the cartesian reading has contexts that the
  language lacks: the identity on terms into it is hosting and not exhausting
  (`KeptWeight.toCartesian_not_exhausting`).

## Regions given by sorts

`ofSorts sorts` declares the interfaces of the listed sorts, beneath any
binders.  On the signature, a list of sorts is *closed* when every
constructor of a listed sort takes plain arguments of listed sorts only
(`sortsClosed`).  This is a condition on the declarations.  It does not make
the generated theory promote the listed sorts, by the defect below.

## Where a presented language reduces

Every step of a presented language fires a rewrite at the root, so a term that
reduces is headed by the constructor that heads the left side of a rewrite.
When the left sides of all rewrites are headed by constructors of the sorts
of a list (`rewritesHeadedIn`), only the interfaces of those sorts reduce
(`termStep_ofSorts`), for every evaluator of premises.  A region of data
sorts apart from that list is then a region in which nothing reduces, and
**the reading with that region receives no transition-preserving map from a
theory that discards where it computes** (`KeptWeight.regions_not_preserves`):
the map has to send that interface to data.

## A defect of the generated contexts that the regions expose

A context of a presented language is a linear pattern that sorts every filling
of its holes.  An interface whose type is a multi-binder type beneath no
binder has no term in any presentation (`not_hasType_multiBinder`), so every
linear pattern with a hole of that interface is a context into every
interface: there is no filling for it to sort (`junkContext`; the hole itself
is `junkLabel`).  Three consequences:

* **the generated theory promotes no nonempty class of sorts**
  (`not_promotes_ofSorts`), although its signature may be closed;
* such a context joins every interface to every other, so **a map from a
  presented language into a reading sends every interface to a declared one,
  or none** (`contextMap_declared_all_or_none`).  No map into a reading with
  regions keeps one sort of the language as data and another apart from the
  data;
* at such an interface every presented language discards
  (`contextTheory_discards_emptyInterface`): the statements that a language
  does not discard are about the interfaces that have a term.

The comparison of the readings is therefore made from the other side, into
the cartesian reading (`ContextTheory.regionToCartesian`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.ContextReadings

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles

/-! ## Finitely many holes, and the size of a reading -/

/-- **A context of a presented language has finitely many holes**: each
names an occurrence in a pattern. -/
theorem contextTheory_finiteHoles (base : BasePremiseEvaluator)
    (presentation : ValidatedLanguageDef) : (contextTheory base presentation).FiniteHoles := by
  intro arity holes result context
  classical
  exact @Finite.of_fintype _ (Fintype.ofList context.shape.holes context.linear.2)

/-- **A weight that the static equivalence keeps is a size of every reading**,
each hole counted as often as it is used. -/
def KeptWeight.readingSize {base : BasePremiseEvaluator} {presentation : ValidatedLanguageDef}
    (kept : KeptWeight base presentation.language)
    (declared : Contexts.Interface → Prop) :
    ((contextTheory base presentation).regionReading declared).MultiplicitySize :=
  kept.linearSize.regionReading (contextTheory_finiteHoles base presentation) declared

/-- **The cartesian reading of a presented language whose static equivalence
keeps a weight adds contexts**: the identity on terms into it is hosting and,
as soon as some interface has a term, not exhausting. -/
theorem KeptWeight.toCartesian_not_exhausting {base : BasePremiseEvaluator}
    {presentation : ValidatedLanguageDef} (kept : KeptWeight base presentation.language)
    {interface : Contexts.Interface} (term : Contexts.Term presentation.language interface) :
    (contextTheory base presentation).toCartesianReading.Hosting ∧
      ¬ (contextTheory base presentation).toCartesianReading.Exhausting :=
  ⟨(contextTheory base presentation).toCartesianReading_hosting, fun exhausting =>
    kept.not_discards term
      (ContextTheory.discards_of_toCartesianReading_exhausting (contextTheory base presentation)
        exhausting interface)⟩

/-! ## A context of a reading is a pattern with holes -/

/-- **A context of a reading of a presented language is a pattern with
holes**: it fills that pattern, and a hole of an interface that is not
declared occurs in it exactly once. -/
theorem exists_shape {base : BasePremiseEvaluator} {presentation : ValidatedLanguageDef}
    {declared : Contexts.Interface → Prop} {arity : Type} [DecidableEq arity]
    {holes : arity → Contexts.Interface} {result : Contexts.Interface}
    (context : (contextTheory base presentation).RegionContext declared holes result) :
    ∃ shape : MultiHoleContext arity,
      (∀ filling : (index : arity) → Contexts.Term presentation.language (holes index),
        (context.act filling).1 = shape.fill fun index => (filling index).1) ∧
      ∀ index, ¬ declared (holes index) → shape.holes.count index = 1 := by
  obtain ⟨positions, place, inner, admits, acts⟩ := context.realized
  refine ⟨inner.shape.relabel place, fun filling => ?_, fun index linear => ?_⟩
  · exact (congrArg Subtype.val (acts filling)).trans
      (MultiHoleContext.fill_relabel (fun index => (filling index).1) place inner.shape).symm
  · classical
    obtain ⟨position, placed, only⟩ := admits.once index linear
    have counted : (inner.shape.holes.map place).count index = inner.shape.holes.count position := by
      rw [List.count_eq_countP, List.countP_map, List.count_eq_countP]
      apply List.countP_congr
      intro other _
      simp only [Function.comp, beq_iff_eq]
      exact ⟨fun same => only other same, fun same => same ▸ placed⟩
    rw [MultiHoleContext.holes_relabel, counted]
    exact inner.linear.count_eq_one position

/-! ## Regions given by sorts -/

/-- **The interfaces of the listed sorts**, beneath any binders. -/
def ofSorts (sorts : List String) (interface : Contexts.Interface) : Prop :=
  ∃ sort ∈ sorts, interface.type = .base sort

/-- An interface of a listed sort is declared. -/
theorem ofSorts_base {sorts : List String} {sort : String} (listed : sort ∈ sorts)
    (stage : List TypeExpr) : ofSorts sorts ⟨.base sort, stage⟩ :=
  ⟨sort, listed, rfl⟩

/-- An interface of another sort is not. -/
theorem not_ofSorts_base {sorts : List String} {sort : String} (other : sort ∉ sorts)
    (stage : List TypeExpr) : ¬ ofSorts sorts ⟨.base sort, stage⟩ := by
  rintro ⟨listed, member, same⟩
  obtain rfl : sort = listed := TypeExpr.base.inj same
  exact other member

/-- A constructor takes plain arguments of the listed sorts only. -/
def takesOnly (sorts : List String) (rule : GrammarRule) : Bool :=
  rule.params.all fun parameter =>
    match parameter with
    | .simple _ (.base sort) => sorts.contains sort
    | _ => false

/-- **A list of sorts is closed in a language**: every constructor of a
listed sort takes plain arguments of listed sorts only. -/
def sortsClosed (lang : LanguageDef) (sorts : List String) : Bool :=
  lang.terms.all fun rule => !sorts.contains rule.category || takesOnly sorts rule

/-- **Positive**: in the candidate presentation atoms and names take atoms
and names only. -/
theorem language_data_closed :
    sortsClosed Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.language
      ["Atom", "CandidateName"] = true := by
  decide

/-- **Negative**: its processes take atoms and spaces. -/
theorem language_process_not_closed :
    sortsClosed Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.language ["Process"] =
      false := by
  decide

/-! ## Where a presented language reduces -/

/-- **The left side of every rewrite of a language is headed by a constructor
of a listed sort.** -/
def rewritesHeadedIn (lang : LanguageDef) (sorts : List String) : Bool :=
  lang.rewrites.all fun rewrite =>
    match rewrite.left with
    | .apply label _ =>
        lang.terms.all fun rule => rule.label != label || sorts.contains rule.category
    | _ => false

/-- **A term that reduces is of a sort in which a rewrite is headed**, for
every evaluator of premises. -/
theorem termStep_ofSorts {base : BasePremiseEvaluator} {lang : LanguageDef} {sorts : List String}
    (headed : rewritesHeadedIn lang sorts = true) {interface : Contexts.Interface}
    {source target : Contexts.Term lang interface} (step : TermStep base lang source target) :
    ofSorts sorts interface := by
  obtain ⟨redex, contractum, -, fired, -⟩ := step
  obtain ⟨rule, member, -, initial, final, matched, -, -⟩ := exists_rule_of_step fired
  have test := List.all_eq_true.mp headed rule member
  cases left : rule.left with
  | apply label parameters =>
      rw [left] at test matched
      obtain ⟨arguments, shape⟩ := eq_apply_of_head? (head?_of_matched matched)
      have typed := redex.2.1
      rw [shape] at typed
      obtain ⟨constructor, declared, sameLabel, type⟩ := declared_constructor_of_hasType_apply typed
      have listed := List.all_eq_true.mp test constructor declared
      simp only [sameLabel, bne_self_eq_false, Bool.false_or, List.contains_iff_mem] at listed
      exact ⟨constructor.category, listed, type⟩
  | bvar _ => rw [left] at test; cases test
  | fvar _ => rw [left] at test; cases test
  | lambda _ _ => rw [left] at test; cases test
  | multiLambda _ _ _ => rw [left] at test; cases test
  | subst _ _ => rw [left] at test; cases test
  | collection _ _ _ => rw [left] at test; cases test

/-- **A region of sorts in which no rewrite is headed receives a source that
discards as data**: a map into the reading with that region, from a theory
that discards at an interface, preserves no step taken at that interface. -/
theorem KeptWeight.regions_not_preserves {base : BasePremiseEvaluator}
    {presentation : ValidatedLanguageDef} (kept : KeptWeight base presentation.language)
    {data active : List String} (headed : rewritesHeadedIn presentation.language active = true)
    (apart : ∀ sort ∈ data, sort ∉ active) {source : ContextTheory.{0}}
    (map : ContextMap source ((contextTheory base presentation).regionReading (ofSorts data)))
    {interface : source.Interface} (discards : source.Discards interface)
    {term next : source.Term interface} (step : source.rewrites term next) :
    ¬ map.PreservesTransitions :=
  kept.linearSize.not_preserves_of_discards_of_static
    (fun _ declared _ _ taken => by
      obtain ⟨sort, member, same⟩ := declared
      obtain ⟨other, listed, type⟩ := termStep_ofSorts headed taken
      obtain rfl : sort = other := TypeExpr.base.inj (same.symm.trans type)
      exact apart sort member listed)
    map discards step

/-! ## Contexts at an interface that has no term -/

/-- **No pattern beneath no binder has a multi-binder type**, in any
language. -/
theorem not_hasType_multiBinder {lang : LanguageDef} {pattern : Pattern} {body : TypeExpr}
    (typed : HasType lang FreeTypeContext.empty [] pattern (.multiBinder body))
    (object : isObjectPattern pattern = true) : False := by
  generalize same : TypeExpr.multiBinder body = type at typed
  cases typed with
  | bvar found => simp at found
  | fvar found => simp [FreeTypeContext.empty] at found
  | constructor _ _ _ => cases same
  | lambda _ => cases same
  | multiLambda _ => cases same
  | subst _ _ => simp [isObjectPattern] at object
  | collection _ => cases same
  | collectionConstructor _ _ _ => cases same

/-- An interface that has no term in any presentation. -/
def emptyInterface : Contexts.Interface := ⟨.multiBinder (.base "Datum"), []⟩

/-- **The hole of an interface that has no term is a context into every
interface**: there is no filling for it to sort. -/
def junkLabel (presentation : ValidatedLanguageDef) (result : Contexts.Interface) :
    Contexts.Context presentation (fun _ : Unit => emptyInterface) result where
  shape := .hole ()
  linear := MultiHoleContext.linear_hole
  sorted := fun _ filling =>
    (not_hasType_multiBinder (filling ()).2.1 (filling ()).2.2.2.1).elim

/-- **The generated theory promotes no nonempty class of sorts.** -/
theorem not_promotes_ofSorts (base : BasePremiseEvaluator) (presentation : ValidatedLanguageDef)
    {sorts : List String} {sort : String} (listed : sort ∈ sorts) :
    ¬ (contextTheory base presentation).Promotes (ofSorts sorts) := by
  intro promotes
  obtain ⟨_, _, impossible⟩ := promotes (junkLabel presentation ⟨.base sort, []⟩)
    (ofSorts_base listed []) ()
  cases impossible

/-- **Positive**, for `Promotes` on a presented language: the empty class. -/
theorem promotes_ofSorts_nil (base : BasePremiseEvaluator) (presentation : ValidatedLanguageDef) :
    (contextTheory base presentation).Promotes (ofSorts []) := by
  rintro arity holes result context ⟨sort, member, -⟩
  cases member

/-- **Every linear pattern with a hole of an interface that has no term is a
context into every interface**: there is no filling for it to sort. -/
def junkContext (presentation : ValidatedLanguageDef) {arity : Type}
    {holes : arity → Contexts.Interface} (shape : MultiHoleContext arity) (linear : shape.Linear)
    (index : arity) (empty : holes index = emptyInterface) (result : Contexts.Interface) :
    Contexts.Context presentation holes result where
  shape := shape
  linear := linear
  sorted := fun _ filling => by
    have term := filling index
    rw [empty] at term
    exact (not_hasType_multiBinder term.2.1 term.2.2.2.1).elim

/-- **A map from a presented language into a reading sends every interface
to a declared one, or none.**  A pattern of two holes, one of an interface
that has no term, is a context from any interface into any other, and a
reading asks a context into a declared interface to have declared holes. -/
theorem contextMap_declared_all_or_none (base : BasePremiseEvaluator)
    (presentation : ValidatedLanguageDef) {target : ContextTheory.{0}}
    {declared : target.Interface → Prop}
    (map : ContextMap (contextTheory base presentation) (target.regionReading declared))
    {result : Contexts.Interface} (free : declared (map.interface result))
    (other : Contexts.Interface) : declared (map.interface other) :=
  target.declared_of_contextMap declared map
    (junkContext presentation
      (holes := fun index : Bool => bif index then other else emptyInterface)
      (.apply "junk" [.hole false, .hole true])
      ⟨by simp [MultiHoleContext.holes, MultiHoleContext.holesList],
        fun index => by cases index <;> simp [MultiHoleContext.holes, MultiHoleContext.holesList]⟩
      false rfl result) free true

/-- **Negative**, for the hypothesis of `KeptWeight.not_discards` that the
interface has a term: at an interface that has no term every presented
language discards.  The equation that says so has no filling to hold of. -/
theorem contextTheory_discards_emptyInterface (base : BasePremiseEvaluator)
    (presentation : ValidatedLanguageDef) :
    (contextTheory base presentation).Discards emptyInterface :=
  ⟨junkContext presentation (holes := fun _ : Bool => emptyInterface)
      (.apply "junk" [.hole false, .hole true])
      ⟨by simp [MultiHoleContext.holes, MultiHoleContext.holesList],
        fun index => by cases index <;> simp [MultiHoleContext.holes, MultiHoleContext.holesList]⟩
      false rfl emptyInterface,
    fun filling => (not_hasType_multiBinder (filling false).2.1 (filling false).2.2.2.1).elim⟩

#print axioms contextTheory_finiteHoles
#print axioms KeptWeight.readingSize
#print axioms KeptWeight.toCartesian_not_exhausting
#print axioms exists_shape
#print axioms language_data_closed
#print axioms language_process_not_closed
#print axioms termStep_ofSorts
#print axioms KeptWeight.regions_not_preserves
#print axioms not_hasType_multiBinder
#print axioms junkLabel
#print axioms not_promotes_ofSorts
#print axioms promotes_ofSorts_nil
#print axioms junkContext
#print axioms contextMap_declared_all_or_none
#print axioms contextTheory_discards_emptyInterface

end Mettapedia.Logic.HostingStyles.ContextReadings
