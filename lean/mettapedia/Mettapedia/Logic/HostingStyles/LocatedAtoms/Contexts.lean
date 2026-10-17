import Mettapedia.Logic.HostingStyles.LocatedAtoms.Reading
import Mettapedia.Logic.HostingStyles.AmbientSpace.Sum

/-!
# Located atoms host a table with its contexts

A term is read as the run of its atom in the space of the table.  In the
candidate in which atoms reduce no such reading is hosting with contexts
(`not_hosting_of_singleRun`): the run is one node at the root, and the image
of a context cannot place a second run.  With the equations of a run this
reading is hosting.

## The image of a context

* **The plain pattern of a context does not do** (`plainPattern_not_equivariant`).
  If the image of the context `c □`, a constant applied to a hole, is the
  pattern `App(c, □)`, then filling it with the run of an atom gives
  `App(c, run(space, t))`, in which the constant is in no space; the run of
  the filled context is `run(space, App(c, t))`, in which it is in `space`.
  The two are different terms of the candidate
  (`run_application_ne_plain_function`).  A context with no other leaf than
  its holes has this defect not: the obstruction is a leaf that is no hole.
* **The pattern with its leaves located does**: the image of a context is the
  pattern of the same shape in which a sort, a constant and a variable of the
  context are runs in the space, and a hole is a hole.  The run of the filled
  context is equal to this pattern filled with the runs of the fillings
  (`runShape_related`): the equations of a run, one node at a time.

## Hosting

* **With contexts** (`locatedListMap_hosting`,
  `located_hostOf_scopedFirstOrderTabular`): under every reading in which the
  holes of atoms are free, the one candidate with located atoms is a host,
  with all contexts, of every theory given by a table of rules without binder
  whose right sides mention only variables of their left sides, on the terms
  with free variables below a width, for every table and every width.  No two
  terms get one image, and one step is one transition, in both directions.
* **On terms** it is a host of the same class as the candidate in which atoms
  reduce (`located_hostOf_firstOrderTabular`).

One candidate hosts all tables: the space is in the term.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.LocatedAtoms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti
  (Theory RuleTable rewritingTheory TermContext inst patternVars usesOnly)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.ContextReadings
open Mettapedia.Logic.HostingStyles.AmbientSpace
  (shapeContextAt shapePatternAt act_shapeContextAt wellScoped_of_listStep
    ScopedFirstOrderTabular)

variable {base : BasePremiseEvaluator}

/-! ## The image of a context, with its leaves located -/

/-- Two terms with one pattern are equal. -/
theorem related_of_val_eq {interface : Contexts.Interface}
    {first second : Contexts.Term located interface} (same : first.1 = second.1) :
    (termSetoid base located interface).r first second := by
  obtain rfl : first = second := Subtype.ext same
  exact .refl _

/-- The pattern of a context with its leaves located in the space of a list
of rules, filled with the runs of the atoms of terms. -/
def runShape (rules : List Dedukti.RewriteRule) (width : Nat) {slots : Type}
    (filling : slots → LF.Term) (extra : Nat) (context : TermContext slots) : Pattern :=
  shapePatternAt (fun extra term => runPattern (ruleSpace rules) (atomAt (width + extra) term))
    (fun slot => runPattern (ruleSpace rules) (atomAt width (filling slot))) extra context

/-- **The run of a filled context is equal to the context with its leaves
located, filled with the runs of the fillings.**  The run distributes over
the nodes of the context, down to its leaves and to its holes. -/
theorem runShape_related (rules : List Dedukti.RewriteRule) (width : Nat) {slots : Type}
    (filling : slots → LF.Term) (within : ∀ slot, LF.WellScoped width (filling slot)) :
    ∀ (context : TermContext slots) (extra : Nat)
      (sorted : OpenPatternWellSorted located FreeTypeContext.empty
        (List.replicate (width + extra) (.base "Atom")) (.base "Atom")
        (runShape rules width filling extra context)),
      (termSetoid base located (atomInterface (width + extra))).r
        (runAtom rules (width + extra) (context.fill filling))
        (⟨runShape rules width filling extra context, sorted⟩ :
          Contexts.Term located (atomInterface (width + extra))) := by
  intro context
  induction context with
  | hole slot =>
      intro extra sorted
      refine related_of_val_eq ?_
      show runPattern (ruleSpace rules) (atomAt (width + extra) (filling slot)) =
        runPattern (ruleSpace rules) (atomAt width (filling slot))
      rw [atomAt_of_wellScoped (within slot) extra]
  | srt sort => intro extra sorted; exact related_of_val_eq rfl
  | con name => intro extra sorted; exact related_of_val_eq rfl
  | var index => intro extra sorted; exact related_of_val_eq rfl
  | app function argument ihFunction ihArgument =>
      intro extra sorted
      obtain ⟨sortedFunction, sortedArgument⟩ := wellSorted_app_inv sorted
      exact .trans _ _ _
        (runTerm_app (spaceAt (ruleSpaceTerm rules) _)
          (locatedAtom (width + extra) (function.fill filling))
          (locatedAtom (width + extra) (argument.fill filling)))
        (appTerm_related (ihFunction extra sortedFunction) (ihArgument extra sortedArgument))
  | lam domain body ihDomain ihBody =>
      intro extra sorted
      obtain ⟨sortedDomain, sortedBody⟩ := wellSorted_binder_inv (label := "Lam") (.inl rfl) sorted
      exact .trans _ _ _
        (runTerm_lam (ruleSpaceTerm rules) (locatedAtom (width + extra) (domain.fill filling))
          (locatedAtom (width + extra + 1) (body.fill filling)))
        (lamTerm_related (ihDomain extra sortedDomain) (ihBody (extra + 1) sortedBody))
  | pi domain body ihDomain ihBody =>
      intro extra sorted
      obtain ⟨sortedDomain, sortedBody⟩ := wellSorted_binder_inv (label := "Pi") (.inr rfl) sorted
      exact .trans _ _ _
        (runTerm_pi (ruleSpaceTerm rules) (locatedAtom (width + extra) (domain.fill filling))
          (locatedAtom (width + extra + 1) (body.fill filling)))
        (piTerm_related (ihDomain extra sortedDomain) (ihBody (extra + 1) sortedBody))

/-! ## The hosting map -/

variable {declared : Contexts.Interface → Prop}

/-- **A theory on the terms with free variables below a width, in a reading
of the candidate with located atoms**: a term is read as the run of its atom
in the space of a list of rules, a context as the pattern of the same shape
with its leaves located in that space. -/
def locatedListMap (theory : Theory) (rules : List Dedukti.RewriteRule)
    (free : AtomsFree declared) (width : Nat) :
    ContextMap (scopedRewriting width theory) (locatedTheory.regionReading declared) where
  interface := fun _ => atomInterface width
  term := fun term => runAtom rules width term.1
  context := fun context =>
    shapeContextAt locatedPresentation located_carriesAtoms locatedEvaluator free width
      (fun extra term => runAtom rules (width + extra) term) 0 context.1
  term_resp := fun {_ first second} related => by
    have same : first = second := related
    rw [same]
    exact Relation.EqvGen.refl _
  equivariant := fun context filling => by
    have shaped := act_shapeContextAt locatedPresentation located_carriesAtoms locatedEvaluator
      free width (fun extra term => runAtom rules (width + extra) term)
      (fun slot => runAtom rules width (filling slot).1) context.1 0
    have sorted := ((shapeContextAt locatedPresentation located_carriesAtoms locatedEvaluator
      free width (fun extra term => runAtom rules (width + extra) term) 0 context.1).act
        fun slot => runAtom rules width (filling slot).1).2
    rw [shaped] at sorted
    exact .trans _ _ _
      (runShape_related (base := locatedEvaluator) rules width (fun slot => (filling slot).1)
        (fun slot => (filling slot).2) context.1 0 sorted)
      (related_of_val_eq shaped.symm)

/-- **Under every reading in which the holes of atoms are free, the candidate
with located atoms hosts every theory whose rules are those of a list of
first-order rules with bound right sides and which has no definition, on the
terms with free variables below a width, with all the contexts of those
terms.** -/
theorem locatedListMap_hosting {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    {theory : Theory} (rulesIff : ∀ rule, theory.rule rule ↔ rule ∈ rules)
    (undefined : ∀ name, theory.body name = none) (free : AtomsFree declared) (width : Nat) :
    (locatedListMap theory rules free width).Hosting := by
  refine ⟨(locatedListMap theory rules free width).faithful_of_reflectsEquations ?_,
    (locatedListMap theory rules free width).preservesTransitions_of_rewrites ?_,
    (locatedListMap theory rules free width).reflectsTransitions_of_rewrites ?_⟩
  · intro _ first second related
    exact Subtype.ext (runAtom_related_iff.mp related)
  · intro _ term next step
    exact runAtom_termStep firstOrder bound (fun rule member => (rulesIff rule).mp member)
      undefined step width
  · intro _ term next step
    obtain ⟨nextTerm, sourceStep, related⟩ :=
      runAtom_termStep_inv firstOrder bound (fun rule member => (rulesIff rule).mpr member) step
    exact ⟨⟨nextTerm, wellScoped_of_listStep firstOrder bound
        (fun rule member => (rulesIff rule).mp member) undefined sourceStep term.2⟩, sourceStep,
      related⟩

/-- A theory given by a table, on the terms with free variables below a
width, in a reading of the candidate with located atoms. -/
noncomputable def locatedTableMap (theory : Theory) (table : RuleTable)
    (free : AtomsFree declared) (width : Nat) :
    ContextMap (scopedRewriting width theory) (locatedTheory.regionReading declared) :=
  locatedListMap theory table.toList free width

/-- **With contexts: the candidate with located atoms hosts every theory given
by a table of first-order rules with bound right sides**, on the terms with
free variables below a width and with all the contexts of those terms, under
every reading in which the holes of atoms are free. -/
theorem locatedTableMap_hosting {theory : Theory} {table : RuleTable}
    (tabular : theory.Tabular table) (admitted : BoundFirstOrder table)
    (free : AtomsFree declared) (width : Nat) :
    (locatedTableMap theory table free width).Hosting :=
  locatedListMap_hosting admitted.listed.1 admitted.listed.2
    (fun rule => (tabular.rules rule).trans Finset.mem_toList.symm) tabular.undefined free width

/-- **The sentence, with contexts**: a reading of the candidate with located
atoms in which the holes of atoms are free is a host, with all contexts, of
the theories given by a table of first-order rules with bound right sides on
the terms with free variables below a width, for every table and every
width. -/
theorem located_hostOf_scopedFirstOrderTabular (free : AtomsFree declared) :
    HostOf (locatedTheory.regionReading declared) ScopedFirstOrderTabular .contexts .hosting := by
  rintro reading ⟨theory, table, width, tabular, admitted, rfl⟩
  exact ⟨locatedTableMap theory table free width,
    locatedTableMap_hosting tabular admitted free width⟩

/-- The cartesian reading. -/
theorem locatedCartesian_hostOf_scopedFirstOrderTabular :
    HostOf locatedTheory.cartesianReading ScopedFirstOrderTabular .contexts .hosting :=
  located_hostOf_scopedFirstOrderTabular atomsFree_all

/-- The reading in which an atom may be discarded and copied, and a name and
a space are used once. -/
theorem locatedAtomRegions_hostOf_scopedFirstOrderTabular :
    HostOf (locatedTheory.regionReading (ofSorts ["Atom"])) ScopedFirstOrderTabular .contexts
      .hosting :=
  located_hostOf_scopedFirstOrderTabular atomsFree_atoms

/-! ## On terms -/

/-- A theory in a reading of the candidate with located atoms, on terms: a
term is read as the run of its atom in the space of a list of rules. -/
def locatedTermsMap (regions : Contexts.Interface → Prop) (theory : Theory)
    (rules : List Dedukti.RewriteRule) :
    ContextMap ((rewritingTheory theory).gslt ()).termsAlone
      (locatedTheory.regionReading regions) :=
  ContextMap.ofTerms (source := (rewritingTheory theory).gslt ())
    (target := locatedTheory.regionReading regions) AtomsReduce.closedAtom
    (fun term => runAtom rules 0 term)
    (fun {first second} related => by
      have same : first = second := related
      rw [same]
      exact Relation.EqvGen.refl _)

/-- **On terms the candidate with located atoms hosts every theory whose
rules are those of a list of first-order rules with bound right sides and
which has no definition.** -/
theorem locatedTermsMap_hosting (regions : Contexts.Interface → Prop)
    {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    {theory : Theory} (rulesIff : ∀ rule, theory.rule rule ↔ rule ∈ rules)
    (undefined : ∀ name, theory.body name = none) :
    (locatedTermsMap regions theory rules).Hosting := by
  refine (ContextMap.ofTerms_hosting_iff (source := (rewritingTheory theory).gslt ())
    (target := locatedTheory.regionReading regions) AtomsReduce.closedAtom
    (fun term => runAtom rules 0 term)
    (fun {first second} related => by
      have same : first = second := related
      rw [same]
      exact Relation.EqvGen.refl _)).mpr ⟨?_, ?_, ?_⟩
  · intro first second related
    exact runAtom_related_iff.mp related
  · intro first next step
    exact runAtom_termStep firstOrder bound (fun rule member => (rulesIff rule).mp member)
      undefined step 0
  · intro first next step
    obtain ⟨nextTerm, sourceStep, related⟩ :=
      runAtom_termStep_inv (depth := 0) firstOrder bound
        (fun rule member => (rulesIff rule).mpr member) step
    exact ⟨nextTerm, sourceStep, related⟩

/-- **The sentence, on terms**: every reading of the candidate with located
atoms is a host, on terms, of the theories given by a table of first-order
rules with bound right sides. -/
theorem located_hostOf_firstOrderTabular (regions : Contexts.Interface → Prop) :
    HostOf (locatedTheory.regionReading regions) FirstOrderTabular .terms .hosting := by
  rintro reading ⟨source, ⟨theory, table, tabular, admitted, rfl⟩, interface, rfl⟩
  exact ⟨locatedTermsMap regions theory table.toList,
    locatedTermsMap_hosting regions admitted.listed.1 admitted.listed.2
      (fun rule => (tabular.rules rule).trans Finset.mem_toList.symm) tabular.undefined⟩

/-! ## The plain pattern of a context -/

/-- **The run of an application is not the application of the plain function
to the run of the argument**: in the first the function is located, in the
second it is in no space. -/
theorem run_application_ne_plain_function (base : BasePremiseEvaluator)
    (rules : List Dedukti.RewriteRule) (depth : Nat) (function argument : LF.Term) :
    ¬ EquationEquiv base located
      (runPattern (ruleSpace rules) (atomAt depth (.app function argument)))
      (.apply "App" [atomAt depth function, runPattern (ruleSpace rules) (atomAt depth argument)]) := by
  intro equivalent
  have same := settle_eq_of_equiv equivalent
  rw [settle_run_atomAt, settle_app, settle_atomAt, settle_run_atomAt] at same
  have pushed : push (ruleSpace rules) (atomAt depth (.app function argument)) =
      .apply "App" [push (ruleSpace rules) (atomAt depth function),
        push (ruleSpace rules) (atomAt depth argument)] := push_app _ _ _
  rw [pushed] at same
  simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
  have positive := tokens_push_pos (ruleSpace rules) (atomAt depth function)
  rw [same, tokens_atomAt (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) function depth] at positive
  exact absurd positive (by decide)

/-- The context that applies the constant `c` to its hole, among the terms
with free variables below a width. -/
def constantApplication (width : Nat) (theory : Theory) :
    (scopedRewriting width theory).Context (fun _ : Unit => ()) () :=
  (⟨.app (.con "c") (.hole ()), trivial, trivial⟩ :
    {context : TermContext Unit // ScopedContext width context})

/-- **The plain pattern of a context is the image of that context under no
map that reads a term as the run of its atom**: with the image of the context
`c □` acting as the pattern `App(c, □)`, the map would not be equivariant.
Witness: the filling by the sort of types. -/
theorem plainPattern_not_equivariant {theory : Theory} {rules : List Dedukti.RewriteRule}
    {width : Nat}
    (map : ContextMap (scopedRewriting width theory) (locatedTheory.regionReading declared))
    (runs : ∀ term : (scopedRewriting width theory).Term (),
      (map.term term).1 = runPattern (ruleSpace rules) (atomAt width term.1))
    (plain : ∀ filling : Unit → Contexts.Term located (map.interface ()),
      ((map.context (constantApplication width theory)).act filling).1 =
        .apply "App" [atomAt width (.con "c"), (filling ()).1]) : False := by
  have image := map.equivariant (constantApplication width theory)
    (fun _ => (⟨.srt .type, .srt⟩ : (scopedRewriting width theory).Term ()))
  have equivalent := equationEquiv_of_termSetoid image
  have source : (map.term ((scopedRewriting width theory).fill (constantApplication width theory)
      fun _ => (⟨.srt .type, .srt⟩ : (scopedRewriting width theory).Term ()))).1 =
      runPattern (ruleSpace rules) (atomAt width (.app (.con "c") (.srt .type))) := runs _
  have target : ((locatedTheory.regionReading declared).fill
      (map.context (constantApplication width theory))
      fun _ => map.term (⟨.srt .type, .srt⟩ : (scopedRewriting width theory).Term ())).1 =
      .apply "App" [atomAt width (.con "c"),
        runPattern (ruleSpace rules) (atomAt width (.srt .type))] :=
    (plain fun _ => map.term (⟨.srt .type, .srt⟩ : (scopedRewriting width theory).Term ())).trans
      (congrArg (fun leaf => Pattern.apply "App" [atomAt width (.con "c"), leaf])
        (runs ⟨.srt .type, .srt⟩))
  have apart := run_application_ne_plain_function locatedEvaluator rules width (.con "c")
    (.srt .type)
  rw [← source, ← target] at apart
  exact apart equivalent

#print axioms runShape_related
#print axioms locatedListMap_hosting
#print axioms locatedTableMap_hosting
#print axioms located_hostOf_scopedFirstOrderTabular
#print axioms locatedCartesian_hostOf_scopedFirstOrderTabular
#print axioms locatedAtomRegions_hostOf_scopedFirstOrderTabular
#print axioms locatedTermsMap_hosting
#print axioms located_hostOf_firstOrderTabular
#print axioms run_application_ne_plain_function
#print axioms plainPattern_not_equivariant

end Mettapedia.Logic.HostingStyles.LocatedAtoms
