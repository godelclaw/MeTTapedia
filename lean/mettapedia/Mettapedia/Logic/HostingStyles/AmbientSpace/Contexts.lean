import Mettapedia.Logic.HostingStyles.AmbientSpace.Hosting
import Mettapedia.Logic.HostingStyles.AmbientSpace.ShapedContexts

/-!
# With contexts: a theory given by a table is hosted by the member at the space of its table

The candidate with a run hosts a theory given by a table on terms, by reading
a term as the run of its atom, and no map that reads a term as one run is
hosting with contexts (`not_hosting_of_singleRun`).  In the ambient form the
image of a term is its plain atom, which a context of patterns handles.

* **Hosting, with all contexts** (`scopedMemberMap_hosting`,
  `member_hostOf_scopedTabularAt`).  For a table of rules without binder
  whose right sides mention only variables of their left sides, and for every
  `width`: every theory given by the table, on the terms with free variables
  below `width` and with all the contexts of those terms (a hole beneath a
  binder captures), is hosted by the member at the space of the table, under
  every reading in which the holes of atoms are free.  A term is read as its
  atom beneath `width` binders, a context as the pattern of the same shape;
  one step is one step.
* The terms with free variables below a width are closed under the steps of
  such a theory (`wellScoped_of_listStep`): an instance of a right side
  mentions only what its left side matched.
* **On one source, the two candidates are apart** (`closedChoice_separates`):
  the closed terms of the calculus with choice, with all their contexts, are
  hosted by the cartesian reading of the member at the space of the two rules
  of choice, and by no reading of the candidate with a run through a map that
  reads a term as one run.

What is not reached, with witnesses:

* with its contexts as they are a member receives no map from these theories
  (`ambientMember_isEmpty_contextMap_scoped`): its contexts use each hole
  once.  The readings in which the holes of atoms are free are needed;
* all terms at once: the reading of every term as its atom beneath `width`
  binders is the map on terms of no map of theories
  (`ambient_atomReading_not_contextMap`).  The stage of an interface is
  finite; this obstruction is not about the space.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AmbientSpace

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti
  (Theory RuleTable rewritingTheory TermContext inst substitute inst_eq_substitute patternVars
    usesOnly withChoice chooseLeft chooseRight choose choiceTable)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Logic.HostingStyles.PrimeCandidate
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.ContextReadings

/-! ## The steps of a table keep the free variables of a term below a bound -/

/-- The values that an instance of a side without binder gives to its
variables have their free variables below the bound of the instance. -/
theorem wellScoped_of_substitute {assignment : Nat → LF.Term} {depth : Nat} :
    ∀ {side : LF.Term}, Dedukti.binderFree side = true →
      LF.WellScoped depth (substitute assignment side) →
        ∀ index ∈ patternVars side, LF.WellScoped depth (assignment index) := by
  intro side
  induction side with
  | var index =>
      intro _ within other member
      rw [List.mem_singleton.mp member]
      exact within
  | srt sort => intro _ _ other member; simp [patternVars] at member
  | con name => intro _ _ other member; simp [patternVars] at member
  | app function argument ihFunction ihArgument =>
      intro free within other member
      simp only [Dedukti.binderFree, Bool.and_eq_true] at free
      have shaped : LF.WellScoped depth
          (.app (substitute assignment function) (substitute assignment argument)) := within
      cases shaped with
      | app functionScoped argumentScoped =>
          rcases List.mem_append.mp member with inFunction | inArgument
          · exact ihFunction free.1 functionScoped other inFunction
          · exact ihArgument free.2 argumentScoped other inArgument
  | lam domain body _ _ => intro free; simp [Dedukti.binderFree] at free
  | pi domain body _ _ => intro free; simp [Dedukti.binderFree] at free

/-- An instance of a side without binder has its free variables below a
bound when the values of its variables have. -/
theorem wellScoped_substitute {assignment : Nat → LF.Term} {depth : Nat} :
    ∀ {side : LF.Term}, Dedukti.binderFree side = true →
      (∀ index ∈ patternVars side, LF.WellScoped depth (assignment index)) →
        LF.WellScoped depth (substitute assignment side) := by
  intro side
  induction side with
  | var index => intro _ values; exact values index (List.mem_singleton.mpr rfl)
  | srt sort => intro _ _; exact .srt
  | con name => intro _ _; exact .con
  | app function argument ihFunction ihArgument =>
      intro free values
      simp only [Dedukti.binderFree, Bool.and_eq_true] at free
      exact .app (ihFunction free.1 fun index member => values index (List.mem_append_left _ member))
        (ihArgument free.2 fun index member => values index (List.mem_append_right _ member))
  | lam domain body _ _ => intro free; simp [Dedukti.binderFree] at free
  | pi domain body _ _ => intro free; simp [Dedukti.binderFree] at free

/-- **A step of a theory whose rules are first-order with bound right sides,
at any position, keeps the free variables of a term below a bound.** -/
theorem wellScoped_of_listStep {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    {theory : Theory} (listed : ∀ rule, theory.rule rule → rule ∈ rules)
    (undefined : ∀ name, theory.body name = none) {source target : LF.Term}
    (step : Dedukti.Step theory source target) {depth : Nat}
    (within : LF.WellScoped depth source) : LF.WellScoped depth target := by
  cases step with
  | inContext context root =>
      refine wellScoped_plug context (fun {inner} redex => ?_) within
      cases root with
      | beta domain body argument =>
          cases redex with
          | app functionScoped argumentScoped =>
              cases functionScoped with
              | lam _ bodyScoped =>
                  exact wellScoped_subst bodyScoped argumentScoped (Nat.zero_le _)
      | delta defined =>
          rw [undefined] at defined
          cases defined
      | @rule rule assignment member =>
          obtain ⟨left, right⟩ := firstOrder rule (listed rule member)
          rw [inst_eq_substitute assignment left] at redex
          rw [inst_eq_substitute assignment right]
          have values := wellScoped_of_substitute left redex
          exact wellScoped_substitute right fun index inRight =>
            values index (patternVars_of_usesOnly right (bound rule (listed rule member)) index inRight)

/-- **Negative**: the rule `c ⟶ x`, whose right side has a variable that its
left side does not bind, sends the closed constant `c` to a term that is not
closed. -/
theorem freeRule_leaves_closed :
    LF.WellScoped 0 (.con "c") ∧
      Dedukti.Step (Theory.ofTable {Dedukti.ConfluenceExamples.freeRule}) (.con "c") (.var 0) ∧
        ¬ LF.WellScoped 0 (.var 0) :=
  ⟨.con, freeRule_step _, not_wellScoped_var 0⟩

/-! ## The hosting map -/

variable {declared : Contexts.Interface → Prop}

/-- **A theory on the terms with free variables below a width, in a reading
of the member at the space of a list of rules**: a term is read as its atom
beneath `width` binders, a context as the pattern of the same shape. -/
def scopedListMap (theory : Theory) (rules : List Dedukti.RewriteRule)
    (free : AtomsFree declared) (width : Nat) :
    ContextMap (scopedRewriting width theory)
      ((ambientTheory (listSpace rules)).regionReading declared) where
  interface := fun _ => atomInterface width
  term := fun term => atomTerm width term.1
  context := fun context =>
    shapeContextAt ambientPresentation ambient_carriesAtoms (ambientEvaluator (ruleSpace rules))
      free width (fun extra term => atomTerm (width + extra) term) 0 context.1
  term_resp := fun {_ first second} related => by
    have same : first = second := related
    rw [same]
    exact Relation.EqvGen.refl _
  equivariant := fun context filling =>
    ContextMap.equations_of_eq
      (target := (ambientTheory (listSpace rules)).regionReading declared)
      (Subtype.ext
        ((act_shapeContextAt ambientPresentation ambient_carriesAtoms
            (ambientEvaluator (ruleSpace rules)) free width
            (fun extra term => atomTerm (width + extra) term)
            (fun slot => atomTerm width (filling slot).1) context.1 0).trans
          (shapePatternAt_atoms width (fun slot => (filling slot).1)
            (fun slot => (filling slot).2) context.1 0)).symm)

/-- **Under every reading in which the holes of atoms are free, the member at
the space of a list of first-order rules with bound right sides hosts every
theory with those rules and no definition, on the terms with free variables
below a width, with all the contexts of those terms.** -/
theorem scopedListMap_hosting {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    {theory : Theory} (rulesIff : ∀ rule, theory.rule rule ↔ rule ∈ rules)
    (undefined : ∀ name, theory.body name = none) (free : AtomsFree declared) (width : Nat) :
    (scopedListMap theory rules free width).Hosting := by
  refine ⟨(scopedListMap theory rules free width).faithful_of_reflectsEquations ?_,
    (scopedListMap theory rules free width).preservesTransitions_of_rewrites ?_,
    (scopedListMap theory rules free width).reflectsTransitions_of_rewrites ?_⟩
  · intro _ first second related
    have same : atomTerm width second.1 = atomTerm width first.1 :=
      eq_atomTerm_of_related (base := ambientEvaluator (ruleSpace rules)) (depth := width) related
    exact Subtype.ext (atomTerm_injective width same).symm
  · intro _ term next step
    exact (termStep_atomTerm_iff firstOrder bound rulesIff undefined (depth := width)).mpr
      ⟨next.1, step, rfl⟩
  · intro _ term next step
    obtain ⟨nextTerm, sourceStep, rfl⟩ :=
      (termStep_atomTerm_iff firstOrder bound rulesIff undefined (depth := width)).mp step
    exact ⟨⟨nextTerm, wellScoped_of_listStep firstOrder bound
        (fun rule member => (rulesIff rule).mp member) undefined sourceStep term.2⟩, sourceStep,
      Relation.EqvGen.refl _⟩

/-- A theory given by a table, on the terms with free variables below a
width, in a reading of the member at the space of the table. -/
noncomputable def scopedMemberMap (theory : Theory) (table : RuleTable)
    (free : AtomsFree declared) (width : Nat) :
    ContextMap (scopedRewriting width theory)
      ((ambientTheory (tableSpace table)).regionReading declared) :=
  scopedListMap theory table.toList free width

/-- **With contexts: the member at the space of a table of first-order rules
with bound right sides hosts every theory given by the table**, on the terms
with free variables below a width and with all the contexts of those terms,
under every reading in which the holes of atoms are free. -/
theorem scopedMemberMap_hosting {theory : Theory} {table : RuleTable}
    (tabular : theory.Tabular table) (admitted : BoundFirstOrder table)
    (free : AtomsFree declared) (width : Nat) :
    (scopedMemberMap theory table free width).Hosting :=
  scopedListMap_hosting admitted.listed.1 admitted.listed.2
    (fun rule => (tabular.rules rule).trans Finset.mem_toList.symm) tabular.undefined free width

/-- **The sentence, with contexts**: a reading of the member at the space of
a table in which the holes of atoms are free is a host, with all contexts, of
the theories given by that table on the terms with free variables below a
width, for every width. -/
theorem member_hostOf_scopedTabularAt {table : RuleTable} (admitted : BoundFirstOrder table)
    (free : AtomsFree declared) :
    HostOf ((ambientTheory (tableSpace table)).regionReading declared)
      (fun source => ∃ (theory : Theory) (width : Nat),
        theory.Tabular table ∧ source = scopedRewriting width theory)
      .contexts .hosting := by
  rintro reading ⟨theory, width, tabular, rfl⟩
  exact ⟨scopedMemberMap theory table free width,
    scopedMemberMap_hosting tabular admitted free width⟩

/-- The cartesian reading of the member. -/
theorem member_cartesian_hostOf_scopedTabularAt {table : RuleTable}
    (admitted : BoundFirstOrder table) :
    HostOf (ambientTheory (tableSpace table)).cartesianReading
      (fun source => ∃ (theory : Theory) (width : Nat),
        theory.Tabular table ∧ source = scopedRewriting width theory)
      .contexts .hosting :=
  member_hostOf_scopedTabularAt admitted atomsFree_all

/-- The reading in which an atom may be discarded and copied, and a name and
a space are used once. -/
theorem member_atomRegions_hostOf_scopedTabularAt {table : RuleTable}
    (admitted : BoundFirstOrder table) :
    HostOf ((ambientTheory (tableSpace table)).regionReading (ofSorts ["Atom"]))
      (fun source => ∃ (theory : Theory) (width : Nat),
        theory.Tabular table ∧ source = scopedRewriting width theory)
      .contexts .hosting :=
  member_hostOf_scopedTabularAt admitted atomsFree_atoms

/-! ## On one source: the closed terms of the calculus with choice -/

/-- The context that applies its first hole to its second, among the terms
with free variables below a width. -/
def scopedApplication (width : Nat) (theory : Theory) :
    (scopedRewriting width theory).Context (fun _ : Bool => ()) () :=
  (⟨.app (.hole false) (.hole true), trivial, trivial⟩ :
    {context : TermContext Bool // ScopedContext width context})

/-- **No map that reads every term as one run is hosting**, from a theory on
the terms with free variables below a width and into any reading of the
candidate with a run. -/
theorem singleRun_not_hosting_scoped {theory : Theory} {width : Nat}
    (map : ContextMap (scopedRewriting width theory) (atomsReduceTheory.regionReading declared))
    (single : ∀ term : (scopedRewriting width theory).Term (),
      tokens runLabel (map.term term).1 = 1) : ¬ map.Hosting :=
  not_hosting_of_uniform_tokens atomsReduce_quoteDropOnly (counted := runLabel) (by decide)
    (by decide) map (scopedApplication width theory) Nat.one_pos single
    (fixed := ⟨.srt .type, .srt⟩) (still := ⟨.srt .type, .srt⟩) (other := ⟨.srt .kind, .srt⟩)
    (fun same => absurd (show LF.Term.app (.srt .type) (.srt .type) =
      .app (.srt .type) (.srt .kind) from congrArg Subtype.val same) (by decide))
    (fun same => absurd (show LF.Term.app (.srt .type) (.srt .type) =
      .app (.srt .kind) (.srt .type) from congrArg Subtype.val same) (by decide))

/-- **The closed terms of the calculus with choice, with all their contexts,
are hosted by the cartesian reading of the member at the space of the two
rules of choice.** -/
theorem closedChoice_hosted :
    HostedBy (scopedRewriting 0 (withChoice Theory.empty)) (ambientTheory choiceSpace).cartesianReading :=
  ⟨scopedListMap (withChoice Theory.empty) [chooseLeft, chooseRight] atomsFree_all 0,
    scopedListMap_hosting choiceRules_admitted.1 choiceRules_admitted.2 withChoice_rules
      (fun _ => rfl) atomsFree_all 0⟩

/-- **With contexts, on one source, the two candidates are apart.**  The
closed terms of the calculus with choice, with all their contexts, are hosted
by the cartesian reading of the member at the space of the two rules of
choice; and no map into a reading of the candidate with a run that reads each
term as one run is hosting. -/
theorem closedChoice_separates :
    HostedBy (scopedRewriting 0 (withChoice Theory.empty))
        (ambientTheory choiceSpace).cartesianReading ∧
      ∀ (regions : Contexts.Interface → Prop)
        (map : ContextMap (scopedRewriting 0 (withChoice Theory.empty))
          (atomsReduceTheory.regionReading regions)),
        (∀ term : (scopedRewriting 0 (withChoice Theory.empty)).Term (),
          tokens runLabel (map.term term).1 = 1) → ¬ map.Hosting :=
  ⟨closedChoice_hosted, fun _ map single => singleRun_not_hosting_scoped map single⟩

/-- The closed terms of the calculus with choice pair terms that reduce: the
application of `choose heads tails` to itself has a step in its function and
a step in its argument. -/
theorem closedChoice_pairs :
    Dedukti.Step (withChoice Theory.empty) (.app coin coin) (.app (.con "heads") coin) ∧
      Dedukti.Step (withChoice Theory.empty) (.app coin coin) (.app coin (.con "tails")) :=
  ⟨(Dedukti.step_choose_left Theory.empty _ _).plug (.appFunction .hole coin),
    (Dedukti.step_choose_right Theory.empty _ _).plug (.appArgument coin .hole)⟩

/-! ## With its contexts as they are -/

/-- A theory on the terms with free variables below a width discards: the
context that returns its first hole. -/
theorem scopedRewriting_discards (width : Nat) (theory : Theory) :
    (scopedRewriting width theory).Discards () :=
  ⟨(⟨.hole false, trivial⟩ : {context : TermContext Bool // ScopedContext width context}),
    fun _ => rfl⟩

/-- **With its contexts as they are, a member receives no map from a theory
of the λΠ-calculus modulo**: its contexts use each hole once. -/
theorem ambientMember_isEmpty_contextMap (space : SpaceTerm) (theory : Theory) :
    IsEmpty (ContextMap (rewritingTheory theory) (ambientTheory space)) :=
  (QuoteDropOnly.linearSize ambientPresentation ambient_quoteDropOnly
    (ambientEvaluator space.1)).isEmpty_contextMap_of_discards (rewritingTheory_discards theory)
    ⟨(.srt .type : LF.Term)⟩

/-- **Nor from such a theory on the terms with free variables below a
width.**  The readings in which the holes of atoms are free are needed. -/
theorem ambientMember_isEmpty_contextMap_scoped (space : SpaceTerm) (width : Nat)
    (theory : Theory) :
    IsEmpty (ContextMap (scopedRewriting width theory) (ambientTheory space)) :=
  (QuoteDropOnly.linearSize ambientPresentation ambient_quoteDropOnly
    (ambientEvaluator space.1)).isEmpty_contextMap_of_discards
    (scopedRewriting_discards width theory)
    ⟨(⟨.srt .type, .srt⟩ : {term : LF.Term // LF.WellScoped width term})⟩

/-! ## All terms at once: the stage of an interface is finite -/

/-- **No map of theories from a theory of the λΠ-calculus modulo, into any
reading of a member, gives every term as many variable atoms as its atom
beneath `width` binders has.**  The context `λ. □` binds the variable `width`
of what fills it and leaves the variable `width + 1` free. -/
theorem ambient_not_contextMap_of_counts_variables {space : SpaceTerm} {theory : Theory}
    (width : Nat)
    (map : ContextMap (rewritingTheory theory) ((ambientTheory space).regionReading declared))
    (counts : ∀ term : (rewritingTheory theory).Term (),
      tokens variableLabel (map.term term).1 = tokens variableLabel (atomAt width term)) :
    False := by
  let binder : (rewritingTheory theory).Context (fun _ : Unit => ()) () :=
    (TermContext.lam (.srt .type) (.hole ()) : TermContext Unit)
  obtain ⟨shape, acts, -⟩ := exists_shape (map.context binder)
  have image : ∀ term : LF.Term,
      tokens variableLabel (atomAt width (.lam (.srt .type) term)) =
        contextTokens variableLabel shape +
          shape.holes.count () * tokens variableLabel (atomAt width term) := by
    intro term
    have related : (termSetoid (ambientEvaluator space.1) ambient (map.interface ())).r
        (map.term (origin := ()) (LF.Term.lam (.srt .type) term))
        ((map.context binder).act fun _ => map.term (origin := ()) term) :=
      map.equivariant binder fun _ => term
    have same : tokens variableLabel (map.term (origin := ()) (LF.Term.lam (.srt .type) term)).1 =
        tokens variableLabel ((map.context binder).act fun _ => map.term (origin := ()) term).1 :=
      ambient_quoteDropOnly.tokens_eq (by decide) (by decide) related
    have shaped := congrArg (tokens variableLabel) (acts fun _ => map.term (origin := ()) term)
    rw [tokens_fill, sum_map_eq_sum_count, Fintype.sum_unique] at shaped
    exact (counts (LF.Term.lam (.srt .type) term)).symm.trans (same.trans (shaped.trans
      (congrArg (fun value => contextTokens variableLabel shape + shape.holes.count () * value)
        (counts term))))
  have captured := image (.var width)
  have shifted := image (.var (width + 1))
  rw [tokens_variable_binder, tokens_variable_var] at captured shifted
  split_ifs at captured shifted <;> omega

/-- **The reading of every term as its atom beneath `width` binders is the
map on terms of no map of theories**, from any theory of the λΠ-calculus
modulo and into any reading of any member. -/
theorem ambient_atomReading_not_contextMap {space : SpaceTerm} {theory : Theory} (width : Nat)
    (map : ContextMap (rewritingTheory theory) ((ambientTheory space).regionReading declared))
    (reads : ∀ term : (rewritingTheory theory).Term (), (map.term term).1 = atomAt width term) :
    False :=
  ambient_not_contextMap_of_counts_variables width map fun term => by rw [reads]

#print axioms wellScoped_of_listStep
#print axioms freeRule_leaves_closed
#print axioms scopedListMap_hosting
#print axioms scopedMemberMap_hosting
#print axioms member_hostOf_scopedTabularAt
#print axioms member_cartesian_hostOf_scopedTabularAt
#print axioms member_atomRegions_hostOf_scopedTabularAt
#print axioms singleRun_not_hosting_scoped
#print axioms closedChoice_hosted
#print axioms closedChoice_separates
#print axioms closedChoice_pairs
#print axioms ambientMember_isEmpty_contextMap
#print axioms ambientMember_isEmpty_contextMap_scoped
#print axioms ambient_not_contextMap_of_counts_variables
#print axioms ambient_atomReading_not_contextMap

end Mettapedia.Logic.HostingStyles.AmbientSpace
