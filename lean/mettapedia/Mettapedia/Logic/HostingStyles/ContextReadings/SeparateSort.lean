import Mettapedia.Logic.HostingStyles.ContextReadings.Conservation
import Mettapedia.Logic.HostingStyles.ContextReadings.ProbeReadings

/-!
# Reduction in a sort that no constructor takes: what it costs with contexts

The candidate presentation computes in the sort of processes, and no
constructor takes a process.  On terms this defect blocks nothing: the
candidate extended with a run constructor hosts every theory given by a
table, under a suitable evaluator of its premises.  With contexts it blocks
every reading, the cartesian one included.

Count the constructors of the reducing sort in a term (`tokens` of
`sortLabels`).  When every parameter of every constructor is plain and of
another sort (`takesNoneOf`), a term of the reducing sort has at most one such
constructor and a term of another sort none (`tokens_le_of_hasType`), and a
term that reduces has exactly one (`tokens_eq_one_of_step`).  A context of a reading adds the tokens
of its fillings, each as often as its hole occurs.  So **a context of two
holes filled with two terms that reduce cannot use both**: the image of a
context that pairs two terms uses one of its holes at most, and cannot keep
apart what differs in the other.

**No reading of such a presentation hosts a theory that pairs terms that
reduce** (`not_hosting_of_separateSort`): a context of two holes of one
interface, a term with a step, and two terms that the context keeps apart on
each side.  The rule-table evaluator is such a theory, by application.  Hence
**under every evaluator of its premises, no reading of the candidate with a
run constructor hosts the rule-table evaluator with its contexts**
(`readingRun_not_hosting_tableEvaluator`): the hosting of that extension on
terms does not lift to contexts, and the obstruction is where reduction
lives.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.ContextReadings

open Mettapedia.GSLT
open Mettapedia.GSLT.Dedukti (tableEvaluator Tabled TabledContext omega_step)
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles

/-! ## The constructors of a sort, counted -/

/-- **The labels of the constructors of a sort.** -/
def sortLabels (lang : LanguageDef) (sort : String) (label : String) : Bool :=
  lang.terms.any fun rule => rule.label == label && rule.category == sort

/-- A parameter is plain and of a base sort other than the given one. -/
def plainOther (sort : String) : TermParam → Bool
  | .simple _ (.base other) => other != sort
  | _ => false

/-- **No constructor takes a term of the sort**: every parameter of every
constructor is plain, of a base sort other than it. -/
def takesNoneOf (lang : LanguageDef) (sort : String) : Bool :=
  lang.terms.all fun rule => rule.params.all (plainOther sort)

/-- A list of patterns without token has none. -/
theorem tokensList_eq_zero {counted : String → Bool} :
    ∀ {patterns : List Pattern}, (∀ pattern ∈ patterns, tokens counted pattern = 0) →
      tokensList counted patterns = 0
  | [], _ => rfl
  | head :: tail, zero => by
      rw [tokensList, zero head List.mem_cons_self,
        tokensList_eq_zero fun pattern member => zero pattern (List.mem_cons_of_mem _ member)]

/-- A context of one hole adds the tokens of what fills it. -/
theorem tokens_fill_oneHole (counted : String → Bool) (context : OneHoleContext)
    (pattern : Pattern) :
    tokens counted (context.fill pattern) =
      contextTokens counted (MultiHoleContext.ofOneHole context) + tokens counted pattern := by
  have filled := tokens_fill counted (fun _ : Unit => pattern) (MultiHoleContext.ofOneHole context)
  rw [MultiHoleContext.fill_ofOneHole, MultiHoleContext.holes_ofOneHole] at filled
  simpa using filled

/-- Patterns that the equation of quotation and dropping identifies have the
same count, for every count that does not count those two. -/
theorem _root_.Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles.QuoteDropOnly.tokens_equiv
    {lang : LanguageDef} (only : QuoteDropOnly lang) {base : BasePremiseEvaluator}
    {counted : String → Bool} (quote : counted "prime-quote" = false)
    (drop : counted "prime-drop" = false) {left right : Pattern}
    (equivalent : EquationEquiv base lang left right) :
    tokens counted left = tokens counted right := by
  have generated : ∀ pattern : Pattern,
      tokens counted (quoted (dropped pattern)) = tokens counted pattern := by
    intro pattern
    simp [quoted, dropped, tokens, tokensList, quote, drop]
  induction equivalent with
  | rel _ _ step =>
      cases step with
      | inContext context generator =>
          rw [tokens_fill_oneHole, tokens_fill_oneHole]
          rcases only.generator generator with rfl | rfl
          · rw [generated]
          · rw [generated]
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- **The static equivalence of quotation and dropping keeps every count that
does not count those two.** -/
theorem _root_.Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles.QuoteDropOnly.tokens_eq
    {lang : LanguageDef} (only : QuoteDropOnly lang) {base : BasePremiseEvaluator}
    {counted : String → Bool} (quote : counted "prime-quote" = false)
    (drop : counted "prime-drop" = false) {interface : Contexts.Interface}
    {first second : Contexts.Term lang interface}
    (related : (termSetoid base lang interface).r first second) :
    tokens counted first.1 = tokens counted second.1 :=
  only.tokens_equiv quote drop (equationEquiv_of_termSetoid related)

/-- The arguments of a constructor whose parameters are plain and of other
sorts are terms of other sorts. -/
theorem arguments_baseTyped {lang : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {sort : String} :
    ∀ (arguments : List Pattern) (params : List TermParam),
      ArgumentsHaveTypes lang free bound arguments params →
      params.all (plainOther sort) = true →
      ∀ argument ∈ arguments, ∃ other : String,
        other ≠ sort ∧ HasType lang free bound argument (.base other)
  | [], _, _, _, _, member => by cases member
  | _ :: _, [], typed, _, _, _ => by cases typed
  | head :: tail, parameter :: parameters, typed, plain, argument, member => by
      cases typed with
      | cons representation parameterType headTyped tailTyped =>
          simp only [List.all_cons, Bool.and_eq_true] at plain
          rcases List.mem_cons.mp member with rfl | inTail
          · cases parameter with
            | simple name type =>
                cases type with
                | base other =>
                    simp only [parameterType?, Option.some.injEq] at parameterType
                    subst parameterType
                    exact ⟨other, by simpa [plainOther] using plain.1, headTyped⟩
                | arrow _ _ => simp [plainOther] at plain
                | multiBinder _ => simp [plainOther] at plain
                | collection _ _ => simp [plainOther] at plain
            | abstractionNamed _ _ _ => simp [plainOther] at plain
            | multiAbstractionNamed _ _ _ => simp [plainOther] at plain
          · exact arguments_baseTyped tail parameters tailTyped plain.2 argument inTail

/-- **A term has at most one constructor of a sort that no constructor
takes**, and none when it is of another sort. -/
theorem tokens_le_of_hasType {lang : LanguageDef} (valid : lang.validate = []) {sort : String}
    (closed : takesNoneOf lang sort = true) {free : FreeTypeContext} (pattern : Pattern) :
    ∀ {bound : List TypeExpr} {other : String}, HasType lang free bound pattern (.base other) →
      isObjectPattern pattern = true →
        tokens (sortLabels lang sort) pattern ≤ 1 ∧
          (other ≠ sort → tokens (sortLabels lang sort) pattern = 0) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro bound other _ _
      simp [tokens]
  | hfvar name =>
      intro bound other _ _
      simp [tokens]
  | happly label arguments ih =>
      intro bound other typed object
      cases typed with
      | @constructor _ rule _ membership notBare argumentsTyped =>
          have plainRule := List.all_eq_true.mp closed rule membership
          have objects := BagNormalForm.isObjectPatternList_iff.mp
            (by simpa [isObjectPattern] using object)
          have inner : tokensList (sortLabels lang sort) arguments = 0 :=
            tokensList_eq_zero fun argument member => by
              obtain ⟨argumentSort, apart, argumentTyped⟩ :=
                arguments_baseTyped arguments rule.params argumentsTyped plainRule argument member
              exact (ih argument member argumentTyped (objects argument member)).2 apart
          rw [tokens, inner]
          refine ⟨by split_ifs <;> omega, fun apart => ?_⟩
          have unlabelled : sortLabels lang sort rule.label = false := by
            by_contra labelled
            have found : sortLabels lang sort rule.label = true := by
              simpa using labelled
            obtain ⟨twin, twinMember, twinTest⟩ := List.any_eq_true.mp found
            simp only [Bool.and_eq_true, beq_iff_eq] at twinTest
            have same : twin = rule :=
              List.inj_on_of_nodup_map
                (LanguageDef.constructorLabels_nodup_of_validate_eq_nil lang valid) twinMember
                membership twinTest.1
            exact apart (same ▸ twinTest.2)
          simp [unlabelled]
  | hlambda binder body _ =>
      intro bound other typed _
      cases typed
  | hmultiLambda arity binders body _ =>
      intro bound other typed _
      cases typed
  | hsubst body replacement _ _ =>
      intro bound other _ object
      simp [isObjectPattern] at object
  | hcollection kind elements rest _ =>
      intro bound other typed _
      cases typed with
      | collectionConstructor membership parameters elementsTyped =>
          have plainRule := List.all_eq_true.mp closed _ membership
          have fullParameters := ((GrammarRule.bareParams_cons_iff _ _ _).mp parameters).2
          rw [fullParameters] at plainRule
          simp [plainOther] at plainRule

/-- **A term that reduces has exactly one constructor of the reducing sort**,
when every rewrite is headed in that sort and no constructor takes a term of
it. -/
theorem tokens_eq_one_of_step {base : BasePremiseEvaluator} {lang : LanguageDef}
    (valid : lang.validate = []) {active : String}
    (headed : rewritesHeadedIn lang [active] = true) (closed : takesNoneOf lang active = true)
    (keeps : ∀ {interface : Contexts.Interface} {first second : Contexts.Term lang interface},
      (termSetoid base lang interface).r first second →
        tokens (sortLabels lang active) first.1 = tokens (sortLabels lang active) second.1)
    {interface : Contexts.Interface} {source target : Contexts.Term lang interface}
    (step : TermStep base lang source target) :
    tokens (sortLabels lang active) source.1 = 1 := by
  obtain ⟨redex, contractum, before, fired, -⟩ := step
  rw [keeps before]
  obtain ⟨rule, member, -, initial, final, matched, -, -⟩ := exists_rule_of_step fired
  have test := List.all_eq_true.mp headed rule member
  cases left : rule.left with
  | apply label parameters =>
      rw [left] at test matched
      obtain ⟨arguments, shape⟩ := eq_apply_of_head? (head?_of_matched matched)
      have typed := redex.2.1
      have object := redex.2.2.2.1
      rw [shape] at typed object ⊢
      obtain ⟨constructor, declared, sameLabel, type⟩ := declared_constructor_of_hasType_apply typed
      have listed := List.all_eq_true.mp test constructor declared
      simp only [sameLabel, bne_self_eq_false, Bool.false_or, List.contains_iff_mem,
        List.mem_singleton] at listed
      rw [type] at typed
      have atMost := (tokens_le_of_hasType valid closed _ typed object).1
      have labelled : sortLabels lang active label = true :=
        List.any_eq_true.mpr ⟨constructor, declared, by simp [sameLabel, listed]⟩
      have atLeast : 1 ≤ tokens (sortLabels lang active) (Pattern.apply label arguments) := by
        rw [tokens, labelled]
        simp
      omega
  | bvar _ => rw [left] at test; cases test
  | fvar _ => rw [left] at test; cases test
  | lambda _ _ => rw [left] at test; cases test
  | multiLambda _ _ _ => rw [left] at test; cases test
  | subst _ _ => rw [left] at test; cases test
  | collection _ _ _ => rw [left] at test; cases test

/-! ## No reading hosts a theory that pairs terms that reduce -/

/-- **A presentation that reduces in a sort that no constructor takes hosts,
under no reading, a theory that pairs terms that reduce.**  The source has a
context of two holes of one interface, a term with a step, and two terms that
the context keeps apart at either hole beside the term with a step. -/
theorem not_hosting_of_separateSort {base : BasePremiseEvaluator}
    {presentation : ValidatedLanguageDef} {active : String}
    (headed : rewritesHeadedIn presentation.language [active] = true)
    (closed : takesNoneOf presentation.language active = true)
    (keeps : ∀ {interface : Contexts.Interface}
      {first second : Contexts.Term presentation.language interface},
      (termSetoid base presentation.language interface).r first second →
        tokens (sortLabels presentation.language active) first.1 =
          tokens (sortLabels presentation.language active) second.1)
    {declared : Contexts.Interface → Prop} {source : ContextTheory.{0}}
    (map : ContextMap source ((contextTheory base presentation).regionReading declared))
    {interface : source.Interface} (pair : source.Context (fun _ : Bool => interface) interface)
    {moving next still other : source.Term interface} (step : source.rewrites moving next)
    (right : ¬ (source.equations interface).r
      (source.fill pair fun index => bif index then still else moving)
      (source.fill pair fun index => bif index then other else moving))
    (left : ¬ (source.equations interface).r
      (source.fill pair fun index => bif index then moving else still)
      (source.fill pair fun index => bif index then moving else other)) :
    ¬ map.Hosting := by
  intro hosting
  have reflects : map.ReflectsEquations := map.reflectsEquations_of_faithful hosting.faithful
  have moved : TermStep base presentation.language (map.term moving) (map.term next) :=
    map.preservesRewrites_of_transitions hosting.preserves step
  have one : tokens (sortLabels presentation.language active) (map.term moving).1 = 1 :=
    tokens_eq_one_of_step presentation.valid headed closed keeps moved
  obtain ⟨sort, listed, type⟩ := termStep_ofSorts headed moved
  obtain rfl : active = sort := (List.mem_singleton.mp listed).symm
  obtain ⟨shape, acts, -⟩ := exists_shape (map.context pair)
  have image : ∀ filling : Bool → source.Term interface,
      (termSetoid base presentation.language (map.interface interface)).r
        (map.term (source.fill pair filling))
        ((map.context pair).act fun index => map.term (filling index)) :=
    fun filling => map.equivariant pair filling
  have both : tokens (sortLabels presentation.language active)
        (map.term (source.fill pair fun _ => moving)).1 =
      tokens (sortLabels presentation.language active)
        ((map.context pair).act fun _ => map.term moving).1 := keeps (image fun _ => moving)
  have typed : HasType presentation.language FreeTypeContext.empty
      (map.interface interface).stage (map.term (source.fill pair fun _ => moving)).1
      (.base active) :=
    Eq.subst (motive := fun expected => HasType presentation.language FreeTypeContext.empty
      (map.interface interface).stage (map.term (source.fill pair fun _ => moving)).1 expected)
      type (map.term (source.fill pair fun _ => moving)).2.1
  have atMost := (tokens_le_of_hasType presentation.valid closed _ typed
    (map.term (source.fill pair fun _ => moving)).2.2.2.1).1
  have counted : tokens (sortLabels presentation.language active)
        ((map.context pair).act fun _ => map.term moving).1 =
      contextTokens (sortLabels presentation.language active) shape +
        (shape.holes.count true + shape.holes.count false) := by
    have shaped := congrArg (tokens (sortLabels presentation.language active))
      (acts fun _ => map.term moving)
    rw [tokens_fill, sum_map_eq_sum_count, Fintype.sum_bool] at shaped
    simpa only [one, Nat.mul_one] using shaped
  have bound : shape.holes.count true + shape.holes.count false ≤ 1 := by omega
  have unused : ∀ index : Bool, shape.holes.count index = 0 →
      ∀ first second : Bool → source.Term interface,
        (∀ position, position ≠ index → first position = second position) →
          (source.equations interface).r (source.fill pair first) (source.fill pair second) := by
    intro index absent first second agree
    apply reflects
    have same : (map.context pair).act (fun position => map.term (first position)) =
        (map.context pair).act fun position => map.term (second position) := by
      apply Subtype.ext
      refine (acts fun position => map.term (first position)).trans
        (Eq.trans ?_ (acts fun position => map.term (second position)).symm)
      apply MultiHoleContext.fill_congr
      intro position member
      have apart : position ≠ index := fun same =>
        (List.count_eq_zero.mp absent) (same ▸ member)
      show (map.term (first position)).1 = (map.term (second position)).1
      rw [agree position apart]
    exact (termSetoid base presentation.language _).iseqv.trans (image first)
      ((termSetoid base presentation.language _).iseqv.trans
        (ContextMap.equations_of_eq
          (target := (contextTheory base presentation).regionReading declared) same)
        ((termSetoid base presentation.language _).iseqv.symm (image second)))
  by_cases second : shape.holes.count true = 0
  · exact right (unused true second _ _ fun position apart => by
      cases position with
      | false => rfl
      | true => exact (apart rfl).elim)
  · have first : shape.holes.count false = 0 := by omega
    exact left (unused false first _ _ fun position apart => by
      cases position with
      | false => exact (apart rfl).elim
      | true => rfl)

/-! ## The candidate with a run constructor, under every reading -/

/-- No constructor of the extension takes a process. -/
theorem probeWithRun_takesNoneOf_process : takesNoneOf probeWithRun "Process" = true := by
  decide

/-- Quotation and dropping are not constructors of processes. -/
theorem probeWithRun_quote_not_process :
    sortLabels probeWithRun "Process" "prime-quote" = false ∧
      sortLabels probeWithRun "Process" "prime-drop" = false := by
  decide

/-- **Positive**, for `takesNoneOf`: the candidate presentation and its
processes. -/
theorem language_takesNoneOf_process :
    takesNoneOf Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.language "Process" =
      true := by
  decide

/-- **Negative**: its atoms take atoms. -/
theorem language_not_takesNoneOf_atom :
    takesNoneOf Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.language "Atom" =
      false := by
  decide

/-- The context of the rule-table evaluator that applies its first hole to
its second. -/
def tabledApplication : tableEvaluator.Context (fun _ : Bool => ()) () :=
  (⟨∅, .app (.hole false) (.hole true)⟩ : TabledContext Bool)

/-- **Under every evaluator of its premises, no reading of the candidate with
a run constructor hosts the rule-table evaluator with its contexts.**  The
image of the application context can use one of its two holes at most. -/
theorem readingRun_not_hosting_tableEvaluator (base : BasePremiseEvaluator)
    (declared : Contexts.Interface → Prop)
    (map : ContextMap tableEvaluator
      ((contextTheory base runPresentation).regionReading declared)) : ¬ map.Hosting :=
  not_hosting_of_separateSort (presentation := runPresentation) (active := "Process")
    probeWithRun_headedIn_process probeWithRun_takesNoneOf_process
    (fun related => probeWithRun_quoteDropOnly.tokens_eq probeWithRun_quote_not_process.1
      probeWithRun_quote_not_process.2 related)
    map tabledApplication
    (moving := (⟨∅, Dedukti.omega⟩ : Tabled)) (next := (⟨∅, Dedukti.omega⟩ : Tabled))
    (still := (⟨∅, .srt .type⟩ : Tabled)) (other := (⟨∅, .srt .kind⟩ : Tabled))
    ⟨rfl, omega_step _⟩
    (fun same => absurd (congrArg Tabled.term same) (by decide))
    (fun same => absurd (congrArg Tabled.term same) (by decide))

/-- In particular the cartesian reading of that extension does not. -/
theorem cartesianRun_not_hostedBy_tableEvaluator (base : BasePremiseEvaluator) :
    ¬ HostedBy tableEvaluator (contextTheory base runPresentation).cartesianReading :=
  fun ⟨map, hosting⟩ => readingRun_not_hosting_tableEvaluator base (fun _ => True) map hosting

#print axioms QuoteDropOnly.tokens_eq
#print axioms arguments_baseTyped
#print axioms tokens_le_of_hasType
#print axioms tokens_eq_one_of_step
#print axioms not_hosting_of_separateSort
#print axioms probeWithRun_takesNoneOf_process
#print axioms language_takesNoneOf_process
#print axioms language_not_takesNoneOf_atom
#print axioms readingRun_not_hosting_tableEvaluator
#print axioms cartesianRun_not_hostedBy_tableEvaluator

end Mettapedia.Logic.HostingStyles.ContextReadings
