import Mettapedia.Logic.HostingStyles.AmbientRegions.Inclusions
import Mettapedia.Logic.HostingStyles.AmbientSpace.Contexts

/-!
# Nothing is lost: each presentation hosts the theories of a table at the space of the table

A term without a run is the atom of a λΠ term, and such a term steps in both
presentations as in the ambient presentation (`runFree_step_iff_contained`,
`runFree_step_iff_scoped`).  So what the member of the ambient family hosts is
hosted by both, at the same ambient space, on terms and with all contexts.

* **On patterns** (`contained_atom_step_iff`, `scoped_atom_step_iff`): under a
  guard that admits the atoms of terms (`AdmitsAtoms`), the steps of each
  presentation at the space of a list of first-order rules with bound right
  sides, from the atom of a term, are the atoms of the steps of the term in a
  theory with those rules.  At every depth, one step for one step.
* **On terms and with contexts**, for every presentation that carries atoms
  and has such steps (`termsMapIn_hosting`, `scopedMapIn_hosting`): a term is
  read as its plain atom, a context as the pattern of its shape.
* **The sentences** (`contained_hostOf_tabularAt`,
  `contained_hostOf_scopedTabularAt`, `scoped_hostOf_tabularAt`,
  `scoped_hostOf_scopedTabularAt`): the class and the level of
  `member_hostOf_tabularAt` and `member_hostOf_scopedTabularAt`.

**Negative**: under the guard that admits nothing no rule of the space fires
(`refuseAll_choice_normal`): the hypothesis on the guard is needed.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AmbientRegions

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti
  (Theory RuleTable rewritingTheory TermContext inst patternVars usesOnly withChoice chooseLeft
    chooseRight normal_of_normalTest)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.AmbientSpace
open Mettapedia.Logic.HostingStyles.ContextReadings

/-! ## Guards under which the atoms of terms are admitted -/

/-- **A guard admits the atoms of λΠ terms**, at every depth. -/
def AdmitsAtoms (admits : Pattern → Bool) : Prop :=
  ∀ (depth : Nat) (term : LF.Term), admits (atomAt depth term) = true

/-- **Positive**: no guard. -/
theorem anySubject_admitsAtoms : AdmitsAtoms anySubject := fun _ _ => rfl

/-- **Positive**: the guard that admits what is no run. -/
theorem notRun_admitsAtoms : AdmitsAtoms notRun := by
  intro depth term
  rcases atomAt_shape depth term with ⟨index, shape⟩ | ⟨label, arguments, shape, listed⟩
  · rw [shape]
    rfl
  · rw [shape]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
    rcases listed with rfl | rfl | rfl | rfl | rfl <;> simp [notRun]

/-- **Positive**: the guard that admits what has the head of an atom. -/
theorem atomHead_admitsAtoms : AdmitsAtoms atomHead := by
  intro depth term
  rcases atomAt_shape depth term with ⟨index, shape⟩ | ⟨label, arguments, shape, listed⟩
  · rw [shape]
    rfl
  · rw [shape]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
    rcases listed with rfl | rfl | rfl | rfl | rfl <;> simp [atomHead]

/-- **Positive**: the guard that admits an atom that is no run. -/
theorem atomNotRun_admitsAtoms : AdmitsAtoms atomNotRun := fun depth term => by
  simp [atomNotRun, atomHead_admitsAtoms depth term, notRun_admitsAtoms depth term]

/-- The guard that admits nothing. -/
def noSubject : Pattern → Bool := fun _ => false

/-- **Negative**: the guard that admits nothing. -/
theorem noSubject_not_admitsAtoms : ¬ AdmitsAtoms noSubject :=
  fun admitted => absurd (admitted 0 (.srt .type)) (by decide)

variable {admits : Pattern → Bool}

/-! ## On patterns -/

/-- **Every step of a term, in a theory whose rules are those of a list and
which has no definition, is a step of the ambient presentation between the
atoms**, under every guard that admits the atoms of terms.  At every
depth. -/
theorem guarded_stepAt_complete (admitsAtoms : AdmitsAtoms admits)
    {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    {theory : Theory} (listed : ∀ rule, theory.rule rule → rule ∈ rules)
    (undefined : ∀ name, theory.body name = none) {source next : LF.Term}
    (step : Dedukti.Step theory source next) :
    ∀ depth : Nat, ∃ fuel, StepAt (regionEvaluator admits (ruleSpace rules)) ambient fuel
      (atomAt depth source) (atomAt depth next) := by
  cases step with
  | @inContext context redex contractum root =>
      induction context with
      | hole =>
          intro depth
          cases root with
          | beta domain body argument => exact ⟨1, ambient_beta_stepAt depth domain body argument⟩
          | delta defined =>
              rw [undefined] at defined
              cases defined
          | @rule rule assignment member =>
              refine ⟨1, step_ambientRoot (by simp [ambient_rewrites]) ?_⟩
              refine mem_admittedAnswers.mpr ⟨?_, ?_⟩
              · rw [contract_atomAt]
                exact admitsAtoms _ _
              · rw [contract_ruleSpace, contract_atomAt]
                exact atomAt_mem_matchResults firstOrder bound (listed rule member) depth assignment
      | appFunction rest argument ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih depth
          exact ⟨fuel + 1, step_appFunction (by simp [ambient_rewrites])
            (atomAt depth argument) inner⟩
      | appArgument function rest ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih depth
          exact ⟨fuel + 1, step_appArgument (by simp [ambient_rewrites])
            (atomAt depth function) inner⟩
      | piDomain rest body ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih depth
          exact ⟨fuel + 1, step_piDomain (by simp [ambient_rewrites])
            (atomAt (depth + 1) body) none inner⟩
      | piBody domain rest ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih (depth + 1)
          exact ⟨fuel + 1, step_piBody (by simp [ambient_rewrites])
            (atomAt depth domain) none inner⟩
      | lamDomain rest body ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih depth
          exact ⟨fuel + 1, step_lamDomain (by simp [ambient_rewrites])
            (atomAt (depth + 1) body) none inner⟩
      | lamBody domain rest ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih (depth + 1)
          exact ⟨fuel + 1, step_lamBody (by simp [ambient_rewrites])
            (atomAt depth domain) none inner⟩

/-- **Under a guard that admits the atoms of terms, the ambient presentation
computes on the atom of a term as its member does**: by beta and by the rules
that the ambient space stores. -/
theorem guarded_atom_step_iff (admitsAtoms : AdmitsAtoms admits)
    {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    {theory : Theory} (rulesIff : ∀ rule, theory.rule rule ↔ rule ∈ rules)
    (undefined : ∀ name, theory.body name = none) {depth : Nat} {source : LF.Term}
    {target : Pattern} :
    Step (regionEvaluator admits (ruleSpace rules)) ambient (atomAt depth source) target ↔
      ∃ next, target = atomAt depth next ∧ Dedukti.Step theory source next := by
  constructor
  · intro step
    obtain ⟨fuel, bounded⟩ := step_ambientEvaluator_of_guarded step
    exact ambient_stepAt_sound firstOrder bound (fun rule member => (rulesIff rule).mpr member)
      fuel bounded
  · rintro ⟨next, rfl, step⟩
    exact guarded_stepAt_complete admitsAtoms firstOrder bound
      (fun rule member => (rulesIff rule).mp member) undefined step depth

/-- The atom of a term has no run. -/
theorem tokens_run_atomAt (term : LF.Term) (depth : Nat) : tokens runLabel (atomAt depth term) = 0 :=
  tokens_atomAt (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) term depth

/-- **The contained presentation computes, on the atom of a term, by beta and
by the rules that the ambient space stores**: its steps from the atom, at the
space of a list of rules, are the atoms of the steps of the term in a theory
with those rules.  At every depth, and one step for one step. -/
theorem contained_atom_step_iff (admitsAtoms : AdmitsAtoms admits)
    {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    {theory : Theory} (rulesIff : ∀ rule, theory.rule rule ↔ rule ∈ rules)
    (undefined : ∀ name, theory.body name = none) {depth : Nat} {source : LF.Term}
    {target : Pattern} :
    Step (regionEvaluator admits (ruleSpace rules)) containedRun (atomAt depth source) target ↔
      ∃ next, target = atomAt depth next ∧ Dedukti.Step theory source next :=
  (runFree_step_iff_contained (tokens_run_atomAt source depth)).trans
    (guarded_atom_step_iff admitsAtoms firstOrder bound rulesIff undefined)

/-- **The scoped presentation computes, on the atom of a term, by beta and by
the rules that the ambient space stores.** -/
theorem scoped_atom_step_iff (admitsAtoms : AdmitsAtoms admits)
    {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    {theory : Theory} (rulesIff : ∀ rule, theory.rule rule ↔ rule ∈ rules)
    (undefined : ∀ name, theory.body name = none) {depth : Nat} {source : LF.Term}
    {target : Pattern} :
    Step (regionEvaluator admits (ruleSpace rules)) scopedRun (atomAt depth source) target ↔
      ∃ next, target = atomAt depth next ∧ Dedukti.Step theory source next :=
  (runFree_step_iff_scoped (tokens_run_atomAt source depth)).trans
    (guarded_atom_step_iff admitsAtoms firstOrder bound rulesIff undefined)

/-- **Negative**: under the guard that admits nothing the atom of
`choose heads tails` has no step at the space of the two rules of choice, in
the ambient presentation. -/
theorem refuseAll_choice_normal (target : Pattern) :
    ¬ Step (regionEvaluator noSubject (ruleSpace [chooseLeft, chooseRight])) ambient
      (atomAt 0 coin) target := by
  intro step
  have atEmpty : Step (regionEvaluator noSubject (ruleSpace [])) ambient (atomAt 0 coin) target := by
    obtain ⟨fuel, bounded⟩ := step
    exact ⟨fuel, stepAt_of_answers_subset
      (fun subject answer found => absurd (mem_admittedAnswers.mp found).1 (by simp [noSubject]))
      bounded⟩
  obtain ⟨fuel, bounded⟩ := step_ambientEvaluator_of_guarded atEmpty
  obtain ⟨next, -, sourceStep⟩ := ambient_stepAt_sound (rules := []) noRules_admitted.1
    noRules_admitted.2 (theory := Theory.empty) (fun _ member => absurd member List.not_mem_nil)
    fuel bounded
  exact normal_of_normalTest pureCover _ (by decide) _ sourceStep

/-! ## On terms and with contexts, for every presentation that carries atoms -/

section Reading

variable {presentation : ValidatedLanguageDef}

/-- **The atom of a term**, as a term of a presentation that carries atoms,
at the stage of `depth` binders. -/
def atomTermIn (carries : CarriesAtoms presentation.language) (depth : Nat) (term : LF.Term) :
    Contexts.Term presentation.language (atomInterface depth) :=
  ⟨atomAt depth term, atomAt_wellSorted_of carries term depth⟩

@[simp] theorem atomTermIn_val (carries : CarriesAtoms presentation.language) (depth : Nat)
    (term : LF.Term) : (atomTermIn carries depth term).1 = atomAt depth term :=
  rfl

theorem atomTermIn_injective (carries : CarriesAtoms presentation.language) (depth : Nat) :
    Function.Injective (atomTermIn carries depth) :=
  fun _ _ same => atomAt_injective depth (congrArg Subtype.val same)

/-- **The atom of a term is the only term of its class**, in every
presentation whose static equivalence is that of quotation and dropping and
in which names are taken by dropping alone. -/
theorem eq_atomTermIn_of_related (carries : CarriesAtoms presentation.language)
    (only : QuoteDropOnly presentation.language) (sorted : QuoteDropSorted presentation.language)
    (names : NamesOnlyDropped presentation.language unquotedSorts) {base : BasePremiseEvaluator}
    {depth : Nat} {term : LF.Term}
    {other : Contexts.Term presentation.language (atomInterface depth)}
    (related : (termSetoid base presentation.language (atomInterface depth)).r
      (atomTermIn carries depth term) other) :
    other = atomTermIn carries depth term := by
  apply Subtype.ext
  have same : contract other.1 = atomAt depth term :=
    (only.contract_eq related).symm.trans (contract_atomAt term depth)
  show other.1 = atomAt depth term
  rw [← same]
  exact (contract_of_dropFree names sorted other.2.1
    (show resultIn unquotedSorts (.base "Atom") = true by decide) other.2.2.2.1
    (by rw [same]; exact tokens_drop_atomAt term depth)).symm

/-- **The transitions of the atom of a term are the atoms of its steps**, in
every such presentation and under every evaluator whose steps from the atoms
of terms are the atoms of the steps of a theory. -/
theorem termStep_atomTermIn_iff (carries : CarriesAtoms presentation.language)
    (only : QuoteDropOnly presentation.language) (sorted : QuoteDropSorted presentation.language)
    (names : NamesOnlyDropped presentation.language unquotedSorts) {base : BasePremiseEvaluator}
    {theory : Theory}
    (steps : ∀ {depth : Nat} {source : LF.Term} {target : Pattern},
      Step base presentation.language (atomAt depth source) target ↔
        ∃ next, target = atomAt depth next ∧ Dedukti.Step theory source next)
    {depth : Nat} {source : LF.Term}
    {target : Contexts.Term presentation.language (atomInterface depth)} :
    TermStep base presentation.language (atomTermIn carries depth source) target ↔
      ∃ next, Dedukti.Step theory source next ∧ target = atomTermIn carries depth next := by
  constructor
  · rintro ⟨redex, contractum, before, fired, after⟩
    obtain rfl := eq_atomTermIn_of_related carries only sorted names before
    obtain ⟨next, shape, step⟩ := steps.mp fired
    have same : contractum = atomTermIn carries depth next := Subtype.ext shape
    rw [same] at after
    exact ⟨next, step, eq_atomTermIn_of_related carries only sorted names after⟩
  · rintro ⟨next, step, rfl⟩
    exact ⟨atomTermIn carries depth source, atomTermIn carries depth next,
      Relation.EqvGen.refl _, steps.mpr ⟨next, rfl, step⟩, Relation.EqvGen.refl _⟩

/-- **A theory, in a presentation that carries atoms**, on terms: a term is
read as its plain atom. -/
def termsMapIn (theory : Theory) (base : BasePremiseEvaluator)
    (carries : CarriesAtoms presentation.language) :
    ContextMap ((rewritingTheory theory).gslt ()).termsAlone (contextTheory base presentation) :=
  ContextMap.ofTerms (source := (rewritingTheory theory).gslt ())
    (target := contextTheory base presentation) AtomsReduce.closedAtom
    (fun term => atomTermIn carries 0 term)
    (fun {first second} related => by
      have same : first = second := related
      rw [same]
      exact Relation.EqvGen.refl _)

/-- **That map is hosting**, when the steps of the presentation from the
atoms of terms are the atoms of the steps of the theory. -/
theorem termsMapIn_hosting (carries : CarriesAtoms presentation.language)
    (only : QuoteDropOnly presentation.language) (sorted : QuoteDropSorted presentation.language)
    (names : NamesOnlyDropped presentation.language unquotedSorts) {base : BasePremiseEvaluator}
    {theory : Theory}
    (steps : ∀ {depth : Nat} {source : LF.Term} {target : Pattern},
      Step base presentation.language (atomAt depth source) target ↔
        ∃ next, target = atomAt depth next ∧ Dedukti.Step theory source next) :
    (termsMapIn theory base carries).Hosting := by
  refine (ContextMap.ofTerms_hosting_iff (source := (rewritingTheory theory).gslt ())
    (target := contextTheory base presentation) AtomsReduce.closedAtom
    (fun term => atomTermIn carries 0 term)
    (fun {first second} related => by
      have same : first = second := related
      rw [same]
      exact Relation.EqvGen.refl _)).mpr ⟨?_, ?_, ?_⟩
  · intro first second related
    have same : atomTermIn carries 0 second = atomTermIn carries 0 first :=
      eq_atomTermIn_of_related carries only sorted names (base := base) (depth := 0) related
    exact (atomTermIn_injective carries 0 same).symm
  · intro first next step
    exact (termStep_atomTermIn_iff carries only sorted names steps (depth := 0)).mpr
      ⟨next, step, rfl⟩
  · intro first next step
    obtain ⟨nextTerm, sourceStep, rfl⟩ :=
      (termStep_atomTermIn_iff carries only sorted names steps (depth := 0)).mp step
    exact ⟨nextTerm, sourceStep, Relation.EqvGen.refl _⟩

variable {declared : Contexts.Interface → Prop}

/-- **A theory on the terms with free variables below a width, in a reading
of a presentation that carries atoms**: a term is read as its atom beneath
`width` binders, a context as the pattern of the same shape. -/
def scopedMapIn (theory : Theory) (base : BasePremiseEvaluator)
    (carries : CarriesAtoms presentation.language) (free : AtomsFree declared) (width : Nat) :
    ContextMap (scopedRewriting width theory)
      ((contextTheory base presentation).regionReading declared) where
  interface := fun _ => atomInterface width
  term := fun term => atomTermIn carries width term.1
  context := fun context =>
    shapeContextAt presentation carries base free width
      (fun extra term => atomTermIn carries (width + extra) term) 0 context.1
  term_resp := fun {_ first second} related => by
    have same : first = second := related
    rw [same]
    exact Relation.EqvGen.refl _
  equivariant := fun context filling =>
    ContextMap.equations_of_eq
      (target := (contextTheory base presentation).regionReading declared)
      (Subtype.ext
        ((act_shapeContextAt presentation carries base free width
            (fun extra term => atomTermIn carries (width + extra) term)
            (fun slot => atomTermIn carries width (filling slot).1) context.1 0).trans
          (shapePatternAt_atoms width (fun slot => (filling slot).1)
            (fun slot => (filling slot).2) context.1 0)).symm)

/-- **That map is hosting**, when the steps of the presentation from the
atoms of terms are the atoms of the steps of the theory and those steps keep
the free variables of a term below a bound. -/
theorem scopedMapIn_hosting (carries : CarriesAtoms presentation.language)
    (only : QuoteDropOnly presentation.language) (sorted : QuoteDropSorted presentation.language)
    (names : NamesOnlyDropped presentation.language unquotedSorts) {base : BasePremiseEvaluator}
    {theory : Theory}
    (steps : ∀ {depth : Nat} {source : LF.Term} {target : Pattern},
      Step base presentation.language (atomAt depth source) target ↔
        ∃ next, target = atomAt depth next ∧ Dedukti.Step theory source next)
    (closed : ∀ {source target : LF.Term}, Dedukti.Step theory source target → ∀ {depth : Nat},
      LF.WellScoped depth source → LF.WellScoped depth target)
    (free : AtomsFree declared) (width : Nat) :
    (scopedMapIn theory base carries free width).Hosting := by
  refine ⟨(scopedMapIn theory base carries free width).faithful_of_reflectsEquations ?_,
    (scopedMapIn theory base carries free width).preservesTransitions_of_rewrites ?_,
    (scopedMapIn theory base carries free width).reflectsTransitions_of_rewrites ?_⟩
  · intro _ first second related
    have same : atomTermIn carries width second.1 = atomTermIn carries width first.1 :=
      eq_atomTermIn_of_related carries only sorted names (base := base) (depth := width) related
    exact Subtype.ext (atomTermIn_injective carries width same).symm
  · intro _ term next step
    exact (termStep_atomTermIn_iff carries only sorted names steps (depth := width)).mpr
      ⟨next.1, step, rfl⟩
  · intro _ term next step
    obtain ⟨nextTerm, sourceStep, rfl⟩ :=
      (termStep_atomTermIn_iff carries only sorted names steps (depth := width)).mp step
    exact ⟨⟨nextTerm, closed sourceStep term.2⟩, sourceStep, Relation.EqvGen.refl _⟩

end Reading

/-! ## The two presentations -/

/-- In the contained presentation a name is taken by dropping alone. -/
theorem contained_namesOnlyDropped : NamesOnlyDropped containedRun unquotedSorts :=
  atomsReduce_namesOnlyDropped

/-- In the scoped presentation a name is taken by dropping alone. -/
theorem scoped_namesOnlyDropped : NamesOnlyDropped scopedRun unquotedSorts :=
  atomsReduce_namesOnlyDropped

variable {declared : Contexts.Interface → Prop}

/-- **On terms: the contained presentation, at the space of a table of
first-order rules with bound right sides, is a host of the theories given by
that table**, under every guard that admits the atoms of terms. -/
theorem contained_hostOf_tabularAt (admitsAtoms : AdmitsAtoms admits) {table : RuleTable}
    (admitted : BoundFirstOrder table) :
    HostOf (containedTheory admits (tableSpace table).1)
      (fun source => ∃ theory : Theory, theory.Tabular table ∧ source = rewritingTheory theory)
      .terms .hosting := by
  rintro reading ⟨source, ⟨theory, tabular, rfl⟩, interface, rfl⟩
  exact ⟨termsMapIn theory _ region_carriesAtoms.1,
    termsMapIn_hosting region_carriesAtoms.1 contained_quoteDropOnly contained_quoteDropSorted
      contained_namesOnlyDropped
      (contained_atom_step_iff admitsAtoms admitted.listed.1 admitted.listed.2
        (fun rule => (tabular.rules rule).trans Finset.mem_toList.symm) tabular.undefined)⟩

/-- **With contexts: a reading of the contained presentation, at the space of
a table, in which the holes of atoms are free is a host, with all contexts,
of the theories given by that table** on the terms with free variables below
a width, for every width. -/
theorem contained_hostOf_scopedTabularAt (admitsAtoms : AdmitsAtoms admits) {table : RuleTable}
    (admitted : BoundFirstOrder table) (free : AtomsFree declared) :
    HostOf ((containedTheory admits (tableSpace table).1).regionReading declared)
      (fun source => ∃ (theory : Theory) (width : Nat),
        theory.Tabular table ∧ source = scopedRewriting width theory)
      .contexts .hosting := by
  rintro reading ⟨theory, width, tabular, rfl⟩
  exact ⟨scopedMapIn theory _ region_carriesAtoms.1 free width,
    scopedMapIn_hosting region_carriesAtoms.1 contained_quoteDropOnly contained_quoteDropSorted
      contained_namesOnlyDropped
      (contained_atom_step_iff admitsAtoms admitted.listed.1 admitted.listed.2
        (fun rule => (tabular.rules rule).trans Finset.mem_toList.symm) tabular.undefined)
      (fun sourceStep _ within => wellScoped_of_listStep admitted.listed.1 admitted.listed.2
        (fun rule member => ((tabular.rules rule).trans Finset.mem_toList.symm).mp member)
        tabular.undefined sourceStep within)
      free width⟩

/-- **On terms: the scoped presentation, at the space of a table, is a host
of the theories given by that table.** -/
theorem scoped_hostOf_tabularAt (admitsAtoms : AdmitsAtoms admits) {table : RuleTable}
    (admitted : BoundFirstOrder table) :
    HostOf (scopedTheory admits (tableSpace table).1)
      (fun source => ∃ theory : Theory, theory.Tabular table ∧ source = rewritingTheory theory)
      .terms .hosting := by
  rintro reading ⟨source, ⟨theory, tabular, rfl⟩, interface, rfl⟩
  exact ⟨termsMapIn theory _ region_carriesAtoms.2,
    termsMapIn_hosting region_carriesAtoms.2 scoped_quoteDropOnly scoped_quoteDropSorted
      scoped_namesOnlyDropped
      (scoped_atom_step_iff admitsAtoms admitted.listed.1 admitted.listed.2
        (fun rule => (tabular.rules rule).trans Finset.mem_toList.symm) tabular.undefined)⟩

/-- **With contexts: a reading of the scoped presentation, at the space of a
table, in which the holes of atoms are free is a host, with all contexts, of
the theories given by that table** on the terms with free variables below a
width, for every width. -/
theorem scoped_hostOf_scopedTabularAt (admitsAtoms : AdmitsAtoms admits) {table : RuleTable}
    (admitted : BoundFirstOrder table) (free : AtomsFree declared) :
    HostOf ((scopedTheory admits (tableSpace table).1).regionReading declared)
      (fun source => ∃ (theory : Theory) (width : Nat),
        theory.Tabular table ∧ source = scopedRewriting width theory)
      .contexts .hosting := by
  rintro reading ⟨theory, width, tabular, rfl⟩
  exact ⟨scopedMapIn theory _ region_carriesAtoms.2 free width,
    scopedMapIn_hosting region_carriesAtoms.2 scoped_quoteDropOnly scoped_quoteDropSorted
      scoped_namesOnlyDropped
      (scoped_atom_step_iff admitsAtoms admitted.listed.1 admitted.listed.2
        (fun rule => (tabular.rules rule).trans Finset.mem_toList.symm) tabular.undefined)
      (fun sourceStep _ within => wellScoped_of_listStep admitted.listed.1 admitted.listed.2
        (fun rule member => ((tabular.rules rule).trans Finset.mem_toList.symm).mp member)
        tabular.undefined sourceStep within)
      free width⟩

/-- **The sentences for the members, with the evaluator named**, without a
guard: at the space of a table each member is a host of the theories given by
that table, on terms. -/
theorem members_host_tabularAt {table : RuleTable} (admitted : BoundFirstOrder table) :
    (containedMember anySubject (containedSpaceOf (tableSpace table))).Hosts
        (fun source => ∃ theory : Theory, theory.Tabular table ∧ source = rewritingTheory theory)
        .terms .hosting ∧
      (scopedMember anySubject (scopedSpaceOf (tableSpace table))).Hosts
        (fun source => ∃ theory : Theory, theory.Tabular table ∧ source = rewritingTheory theory)
        .terms .hosting :=
  ⟨contained_hostOf_tabularAt anySubject_admitsAtoms admitted,
    scoped_hostOf_tabularAt anySubject_admitsAtoms admitted⟩

/-- **One step of the theory is one step of each presentation**, at the space
of the table. -/
theorem contained_steps {theory : Theory} {table : RuleTable} (admitsAtoms : AdmitsAtoms admits)
    (tabular : theory.Tabular table) (admitted : BoundFirstOrder table) {count : Nat}
    {first final : LF.Term}
    (steps : ((rewritingTheory theory).gslt ()).termsAlone.Steps (interface := PUnit.unit) count
      first final) :
    (containedTheory admits (tableSpace table).1).Steps count
      (atomTermIn region_carriesAtoms.1 0 first) (atomTermIn region_carriesAtoms.1 0 final) :=
  (termsMapIn theory _ region_carriesAtoms.1).steps_of_preserves
    (termsMapIn_hosting region_carriesAtoms.1 contained_quoteDropOnly contained_quoteDropSorted
      contained_namesOnlyDropped
      (contained_atom_step_iff admitsAtoms admitted.listed.1 admitted.listed.2
        (fun rule => (tabular.rules rule).trans Finset.mem_toList.symm)
        tabular.undefined)).preserves steps

#print axioms notRun_admitsAtoms
#print axioms atomHead_admitsAtoms
#print axioms guarded_stepAt_complete
#print axioms guarded_atom_step_iff
#print axioms contained_atom_step_iff
#print axioms scoped_atom_step_iff
#print axioms refuseAll_choice_normal
#print axioms eq_atomTermIn_of_related
#print axioms termStep_atomTermIn_iff
#print axioms termsMapIn_hosting
#print axioms scopedMapIn_hosting
#print axioms contained_hostOf_tabularAt
#print axioms contained_hostOf_scopedTabularAt
#print axioms scoped_hostOf_tabularAt
#print axioms scoped_hostOf_scopedTabularAt
#print axioms members_host_tabularAt
#print axioms contained_steps
#print axioms anySubject_admitsAtoms
#print axioms atomNotRun_admitsAtoms
#print axioms noSubject_not_admitsAtoms
#print axioms tokens_run_atomAt
#print axioms atomTermIn_injective
#print axioms contained_namesOnlyDropped
#print axioms scoped_namesOnlyDropped

end Mettapedia.Logic.HostingStyles.AmbientRegions
