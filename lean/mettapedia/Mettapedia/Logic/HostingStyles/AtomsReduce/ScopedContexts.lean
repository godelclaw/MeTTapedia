import Mettapedia.Logic.HostingStyles.AtomsReduce.PureFragment
import Mettapedia.Logic.HostingStyles.AtomsReduce.Contexts

/-!
# The pure calculus with its contexts, in the candidate in which atoms reduce

Abstraction, application and beta are constructors and rewrites of the
candidate, so a context of the pure λΠ-calculus has an image: a constructor
of the calculus is a constructor of atoms, a hole is a hole.  This module
says how far that goes.

* **Hosting, with all contexts.**  For every `width`, the pure calculus on
  the terms whose free variables are below `width`, with all the contexts of
  those terms (a hole beneath a binder captures), is hosted by every reading
  of the candidate in which the holes of atoms may be used any number of
  times, under every evaluator of its premises (`scopedMap_hosting`,
  `atomsFree_hostOf_scoped`).  The cartesian reading is one such reading
  (`cartesian_hostOf_scoped`); the reading with atoms free and names and
  spaces used once is another (`atomRegions_hostOf_scoped`).  A term is read
  as its atom beneath `width` binders, a context as the pattern of the same
  shape; one step is one step.  The terms with free variables below `width`
  are a part of the calculus that its steps and its contexts do not leave
  (`includeScoped_hosting`), and every term belongs to one of them
  (`exists_wellScoped`).  Already the closed terms have what no reading of a
  presentation that reduces in a sort no constructor takes can host: a
  context of two holes, a term with a step, and two terms that the context
  keeps apart at either hole beside it (`pairing_hosted`).
* **Not all terms at once, by that reading.**  The calculus has one interface
  for all its terms, and an interface of the candidate has finitely many
  binders in scope.  The reading of every term as its atom beneath `width`
  binders is the map on terms of no map of theories, into any reading: the
  context `λ. □` binds the variable `width` of what fills it, which that
  reading wrote as a variable atom (`not_contextMap_of_counts_variables`,
  `atomReading_not_contextMap`).

So what stops the candidate from hosting a theory given by a table with its
contexts is not that atoms reduce: it is the run that carries the space
(`not_hosting_of_singleRun`), and, for the terms of all widths at once, the
finite stage of an interface.

Restated here because its existing form is stated for another carrier: a
term of a stage is a term of the stage extended by binders that none of its
variables reaches (`wellSorted_extendOuter`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AtomsReduce

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.LanguageDef.LFTyping (lift subst subst0)
open Mettapedia.GSLT.Dedukti (Theory rewritingTheory TermContext HoleSyntax)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
open Mettapedia.Logic.HostingStyles.ContextReadings

/-! ## Beta keeps the free variables of a term below a bound -/

/-- Lifting keeps a term well scoped, at the depth raised by the amount. -/
theorem wellScoped_lift {term : LF.Term} {depth : Nat} (within : LF.WellScoped depth term) :
    ∀ amount cutoff : Nat, LF.WellScoped (depth + amount) (lift amount cutoff term) := by
  induction within with
  | srt => intro amount cutoff; exact .srt
  | con => intro amount cutoff; exact .con
  | @var depth index bound =>
      intro amount cutoff
      show LF.WellScoped (depth + amount) (.var (if index < cutoff then index else index + amount))
      refine .var ?_
      split <;> omega
  | pi _ _ ihDomain ihBody =>
      intro amount cutoff
      have body := ihBody amount (cutoff + 1)
      rw [Nat.add_right_comm] at body
      exact .pi (ihDomain amount cutoff) body
  | lam _ _ ihDomain ihBody =>
      intro amount cutoff
      have body := ihBody amount (cutoff + 1)
      rw [Nat.add_right_comm] at body
      exact .lam (ihDomain amount cutoff) body
  | app _ _ ihFunction ihArgument =>
      intro amount cutoff
      exact .app (ihFunction amount cutoff) (ihArgument amount cutoff)

/-- **Substitution for a variable of a term gives a term with one free
variable fewer.** -/
theorem wellScoped_subst {body : LF.Term} :
    ∀ {depth target : Nat} {replacement : LF.Term}, LF.WellScoped (depth + 1) body →
      LF.WellScoped depth replacement → target ≤ depth →
        LF.WellScoped depth (subst target replacement body) := by
  induction body with
  | var index =>
      intro depth target replacement within replaced below
      cases within with
      | var bound =>
          show LF.WellScoped depth
            (if index = target then replacement else if target < index then .var (index - 1)
              else .var index)
          split
          · exact replaced
          · split
            · exact .var (by omega)
            · exact .var (by omega)
  | srt sort => intro depth target replacement _ _ _; exact .srt
  | con name => intro depth target replacement _ _ _; exact .con
  | pi domain body ihDomain ihBody =>
      intro depth target replacement within replaced below
      cases within with
      | pi domainScoped bodyScoped =>
          exact .pi (ihDomain domainScoped replaced below)
            (ihBody bodyScoped (wellScoped_lift replaced 1 0) (Nat.succ_le_succ below))
  | lam domain body ihDomain ihBody =>
      intro depth target replacement within replaced below
      cases within with
      | lam domainScoped bodyScoped =>
          exact .lam (ihDomain domainScoped replaced below)
            (ihBody bodyScoped (wellScoped_lift replaced 1 0) (Nat.succ_le_succ below))
  | app function argument ihFunction ihArgument =>
      intro depth target replacement within replaced below
      cases within with
      | app functionScoped argumentScoped =>
          exact .app (ihFunction functionScoped replaced below)
            (ihArgument argumentScoped replaced below)

/-- What keeps the hole of a context well scoped keeps the plugged context
well scoped. -/
theorem wellScoped_plug (context : LFContextualBetaEta.Context) {source target : LF.Term}
    (inner : ∀ {depth : Nat}, LF.WellScoped depth source → LF.WellScoped depth target) :
    ∀ {depth : Nat}, LF.WellScoped depth (context.plug source) →
      LF.WellScoped depth (context.plug target) := by
  induction context with
  | hole => intro depth within; exact inner within
  | piDomain rest body ih =>
      intro depth within
      have shaped : LF.WellScoped depth (.pi (rest.plug source) body) := within
      cases shaped with
      | pi domainScoped bodyScoped => exact .pi (ih domainScoped) bodyScoped
  | piBody domain rest ih =>
      intro depth within
      have shaped : LF.WellScoped depth (.pi domain (rest.plug source)) := within
      cases shaped with
      | pi domainScoped bodyScoped => exact .pi domainScoped (ih bodyScoped)
  | lamDomain rest body ih =>
      intro depth within
      have shaped : LF.WellScoped depth (.lam (rest.plug source) body) := within
      cases shaped with
      | lam domainScoped bodyScoped => exact .lam (ih domainScoped) bodyScoped
  | lamBody domain rest ih =>
      intro depth within
      have shaped : LF.WellScoped depth (.lam domain (rest.plug source)) := within
      cases shaped with
      | lam domainScoped bodyScoped => exact .lam domainScoped (ih bodyScoped)
  | appFunction rest argument ih =>
      intro depth within
      have shaped : LF.WellScoped depth (.app (rest.plug source) argument) := within
      cases shaped with
      | app functionScoped argumentScoped => exact .app (ih functionScoped) argumentScoped
  | appArgument function rest ih =>
      intro depth within
      have shaped : LF.WellScoped depth (.app function (rest.plug source)) := within
      cases shaped with
      | app functionScoped argumentScoped => exact .app functionScoped (ih argumentScoped)

/-- **A step of beta, at any position, keeps the free variables of a term
below a bound.** -/
theorem wellScoped_of_step {source target : LF.Term}
    (step : Dedukti.Step Theory.empty source target) {depth : Nat}
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
      | delta defined => cases defined
      | rule assignment member => exact member.elim

/-- **Every term has its free variables below some bound.** -/
theorem exists_wellScoped (term : LF.Term) : ∃ width : Nat, LF.WellScoped width term := by
  induction term with
  | var index => exact ⟨index + 1, .var (Nat.lt_succ_self index)⟩
  | srt sort => exact ⟨0, .srt⟩
  | con name => exact ⟨0, .con⟩
  | pi domain body ihDomain ihBody =>
      obtain ⟨first, domainScoped⟩ := ihDomain
      obtain ⟨second, bodyScoped⟩ := ihBody
      exact ⟨max first second, .pi (domainScoped.mono (Nat.le_max_left _ _))
        (bodyScoped.mono (Nat.le_succ_of_le (Nat.le_max_right _ _)))⟩
  | lam domain body ihDomain ihBody =>
      obtain ⟨first, domainScoped⟩ := ihDomain
      obtain ⟨second, bodyScoped⟩ := ihBody
      exact ⟨max first second, .lam (domainScoped.mono (Nat.le_max_left _ _))
        (bodyScoped.mono (Nat.le_succ_of_le (Nat.le_max_right _ _)))⟩
  | app function argument ihFunction ihArgument =>
      obtain ⟨first, functionScoped⟩ := ihFunction
      obtain ⟨second, argumentScoped⟩ := ihArgument
      exact ⟨max first second, .app (functionScoped.mono (Nat.le_max_left _ _))
        (argumentScoped.mono (Nat.le_max_right _ _))⟩

/-! ## The terms with free variables below a width, with their contexts -/

/-- **A context whose variables are below a scope**: beneath a binder of the
context the scope is one more.  A hole is not constrained. -/
def ScopedContext {slots : Type} : Nat → TermContext slots → Prop
  | _, .hole _ => True
  | _, .srt _ => True
  | _, .con _ => True
  | scope, .var index => index < scope
  | scope, .pi domain body => ScopedContext scope domain ∧ ScopedContext (scope + 1) body
  | scope, .lam domain body => ScopedContext scope domain ∧ ScopedContext (scope + 1) body
  | scope, .app function argument => ScopedContext scope function ∧ ScopedContext scope argument

/-- **Positive**: the abstraction of a hole, which binds a variable of what
fills it. -/
theorem scopedContext_binder :
    ScopedContext 0 (.lam (.srt .type) (.hole ()) : TermContext Unit) :=
  ⟨trivial, trivial⟩

/-- **Negative**: a variable that no binder of the context binds. -/
theorem not_scopedContext_variable : ¬ ScopedContext 0 (.var 0 : TermContext Unit) :=
  fun within => absurd (show 0 < 0 from within) (Nat.lt_irrefl 0)

theorem ScopedContext.mono {slots : Type} {context : TermContext slots} :
    ∀ {scope larger : Nat}, ScopedContext scope context → scope ≤ larger →
      ScopedContext larger context := by
  induction context with
  | hole slot => intro scope larger _ _; trivial
  | srt sort => intro scope larger _ _; trivial
  | con name => intro scope larger _ _; trivial
  | var index =>
      intro scope larger within ordered
      exact Nat.lt_of_lt_of_le (show index < scope from within) ordered
  | pi domain body ihDomain ihBody =>
      intro scope larger within ordered
      exact ⟨ihDomain within.1 ordered, ihBody within.2 (Nat.succ_le_succ ordered)⟩
  | lam domain body ihDomain ihBody =>
      intro scope larger within ordered
      exact ⟨ihDomain within.1 ordered, ihBody within.2 (Nat.succ_le_succ ordered)⟩
  | app function argument ihFunction ihArgument =>
      intro scope larger within ordered
      exact ⟨ihFunction within.1 ordered, ihArgument within.2 ordered⟩

/-- A context with variables below a scope, filled with terms with free
variables below a width that the scope reaches, is a term with free variables
below the scope. -/
theorem scoped_fill {slots : Type} {context : TermContext slots} {width : Nat}
    {filling : slots → LF.Term} (fillings : ∀ slot, LF.WellScoped width (filling slot)) :
    ∀ {scope : Nat}, ScopedContext scope context → width ≤ scope →
      LF.WellScoped scope (context.fill filling) := by
  induction context with
  | hole slot => intro scope _ ordered; exact (fillings slot).mono ordered
  | srt sort => intro scope _ _; exact .srt
  | con name => intro scope _ _; exact .con
  | var index => intro scope within _; exact .var within
  | pi domain body ihDomain ihBody =>
      intro scope within ordered
      exact .pi (ihDomain within.1 ordered) (ihBody within.2 (Nat.le_succ_of_le ordered))
  | lam domain body ihDomain ihBody =>
      intro scope within ordered
      exact .lam (ihDomain within.1 ordered) (ihBody within.2 (Nat.le_succ_of_le ordered))
  | app function argument ihFunction ihArgument =>
      intro scope within ordered
      exact .app (ihFunction within.1 ordered) (ihArgument within.2 ordered)

theorem scoped_bind {slots inner : Type} {context : TermContext slots} {width : Nat}
    {plugged : slots → TermContext inner}
    (pluggings : ∀ slot, ScopedContext width (plugged slot)) :
    ∀ {scope : Nat}, ScopedContext scope context → width ≤ scope →
      ScopedContext scope (context.bind plugged) := by
  induction context with
  | hole slot => intro scope _ ordered; exact (pluggings slot).mono ordered
  | srt sort => intro scope _ _; trivial
  | con name => intro scope _ _; trivial
  | var index => intro scope within _; exact within
  | pi domain body ihDomain ihBody =>
      intro scope within ordered
      exact ⟨ihDomain within.1 ordered, ihBody within.2 (Nat.le_succ_of_le ordered)⟩
  | lam domain body ihDomain ihBody =>
      intro scope within ordered
      exact ⟨ihDomain within.1 ordered, ihBody within.2 (Nat.le_succ_of_le ordered)⟩
  | app function argument ihFunction ihArgument =>
      intro scope within ordered
      exact ⟨ihFunction within.1 ordered, ihArgument within.2 ordered⟩

theorem scoped_ofTerm {slots : Type} {term : LF.Term} {scope : Nat}
    (within : LF.WellScoped scope term) :
    ScopedContext scope (TermContext.ofTerm term : TermContext slots) := by
  induction within with
  | srt => trivial
  | con => trivial
  | var bound => exact bound
  | pi _ _ ihDomain ihBody => exact ⟨ihDomain, ihBody⟩
  | lam _ _ ihDomain ihBody => exact ⟨ihDomain, ihBody⟩
  | app _ _ ihFunction ihArgument => exact ⟨ihFunction, ihArgument⟩

/-- **The terms with free variables below a width, as a syntax with holes.**
Filling is that of all the terms: textual, so a hole beneath a binder
captures. -/
def scopedShape (width : Nat) : HoleSyntax {term : LF.Term // LF.WellScoped width term} where
  Hole := fun slots => {context : TermContext slots // ScopedContext width context}
  fill := fun filling context =>
    ⟨context.1.fill fun slot => (filling slot).1,
      scoped_fill (fun slot => (filling slot).2) context.2 (Nat.le_refl width)⟩
  bind := fun plugged context =>
    ⟨context.1.bind fun slot => (plugged slot).1,
      scoped_bind (fun slot => (plugged slot).2) context.2 (Nat.le_refl width)⟩
  hole := fun slot => ⟨.hole slot, trivial⟩
  constant := fun term => ⟨TermContext.ofTerm term.1, scoped_ofTerm term.2⟩
  fill_bind := fun _ _ context => Subtype.ext (TermContext.fill_bind _ _ context.1)
  fill_hole := fun _ _ => rfl
  fill_constant := fun _ term => Subtype.ext (TermContext.fill_ofTerm _ term.1)

/-- **A calculus as it runs, on the terms with free variables below a
width**, with the contexts of those terms. -/
def scopedRewriting (width : Nat) (theory : Theory) : ContextTheory.{0} :=
  (scopedShape width).theory
    ⟨Eq, ⟨fun _ => rfl, fun same => same.symm, fun first second => first.trans second⟩⟩
    (fun source target => Dedukti.Step theory source.1 target.1)
    (fun context _ _ same =>
      congrArg (fun filling => (scopedShape width).fill filling context) (funext same))
    (fun same step => ⟨_, same ▸ step, rfl⟩)
    (fun step same => same ▸ step)

/-- **Positive**: among the terms with one free variable, the abstraction of
a hole filled with that variable is the identity function, a closed term:
the hole captured. -/
theorem scopedShape_captures :
    ((scopedShape 1).fill (fun _ : Unit => ⟨.var 0, .var Nat.zero_lt_one⟩)
        ⟨.lam (.srt .type) (.hole ()), trivial, trivial⟩).1 = .lam (.srt .type) (.var 0) ∧
      LF.WellScoped 0 (.lam (.srt .type) (.var 0)) :=
  ⟨rfl, .lam .srt (.var Nat.zero_lt_one)⟩

/-- **Negative**: the variable `width` is no term among those with free
variables below `width`. -/
theorem not_wellScoped_var (width : Nat) : ¬ LF.WellScoped width (.var width) := by
  intro within
  cases within with
  | var bound => exact Nat.lt_irrefl _ bound

/-- The inclusion of the terms with free variables below a width. -/
def includeScoped (width : Nat) (theory : Theory) :
    ContextMap (scopedRewriting width theory) (rewritingTheory theory) where
  interface := fun _ => ()
  term := fun term => term.1
  context := fun context => context.1
  term_resp := fun same => congrArg Subtype.val same
  equivariant := fun _ _ => rfl

/-- **The terms with free variables below a width are a part of the pure
calculus that its steps and its contexts do not leave**: the inclusion is
hosting. -/
theorem includeScoped_hosting (width : Nat) : (includeScoped width Theory.empty).Hosting := by
  rw [ContextMap.hosting_iff]
  refine ⟨fun same => Subtype.ext same, ?_, ?_⟩
  · intro _ _ label term next step
    exact step
  · intro _ _ label term next step
    have within : LF.WellScoped width (label.1.fill fun _ => term.1) :=
      scoped_fill (fun _ => term.2) label.2 (Nat.le_refl width)
    exact ⟨⟨next, wellScoped_of_step step within⟩, step, rfl⟩

/-! ## Contexts of the candidate -/

/-- The candidate under an evaluator of its premises. -/
abbrev candidateUnder (base : BasePremiseEvaluator) : ContextTheory.{0} :=
  contextTheory base atomsReducePresentation

/-- A term of a stage is a term of the stage extended by binders that none of
its variables reaches. -/
theorem wellSorted_extendOuter {lang : LanguageDef} {bound : List TypeExpr} {type : TypeExpr}
    {pattern : Pattern}
    (sorted : OpenPatternWellSorted lang FreeTypeContext.empty bound type pattern)
    (outer : List TypeExpr) :
    OpenPatternWellSorted lang FreeTypeContext.empty (bound ++ outer) type pattern :=
  ⟨sorted.1.extendOuter outer, sorted.2.1, sorted.2.2.1,
    Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedAt_mono sorted.2.2.2 (by simp)⟩

/-- **A hole for atoms beneath `width` binders, placed beneath `extra`
more.**  What fills it is read there as it is written: its first `extra`
variables are those binders. -/
def placedHole (width extra : Nat) :
    Contexts.Context atomsReducePresentation (fun _ : Unit => atomInterface width)
      (atomInterface (width + extra)) where
  shape := .hole ()
  linear := MultiHoleContext.linear_hole
  sorted := fun {target} morphism filling => by
    have extended := wellSorted_extendOuter (filling ()).2
      (List.replicate extra (mapTypeExpr morphism.symbols (.base "Atom")))
    have stage : ((atomInterface (width + extra)).map morphism.symbols).stage =
        ((atomInterface width).map morphism.symbols).stage ++
          List.replicate extra (mapTypeExpr morphism.symbols (.base "Atom")) := by
      show (List.replicate (width + extra) (TypeExpr.base "Atom")).map
          (mapTypeExpr morphism.symbols) =
        (List.replicate width (TypeExpr.base "Atom")).map (mapTypeExpr morphism.symbols) ++
          List.replicate extra (mapTypeExpr morphism.symbols (.base "Atom"))
      simp only [List.replicate_add, List.map_append, List.map_replicate]
    show OpenPatternWellSorted target.language FreeTypeContext.empty
      ((atomInterface (width + extra)).map morphism.symbols).stage
      ((atomInterface width).map morphism.symbols).type (filling ()).1
    rw [stage]
    exact extended

/-- Filling the placed hole returns what fills it, as it is written. -/
theorem fill_placedHole (width extra : Nat)
    (filling : (index : Unit) → Contexts.Term atomsReduce (atomInterface width)) :
    ((placedHole width extra).fill filling).1 = (filling ()).1 :=
  rfl

/-- **Negative**: a variable bound by the first binder of a stage is no
closed atom; a hole is placed beneath more binders, not beneath fewer. -/
theorem bvar_not_closedAtom :
    ¬ OpenPatternWellSorted atomsReduce FreeTypeContext.empty [] (.base "Atom") (.bvar 0) := by
  intro sorted
  have scope : (Pattern.bvar 0).isWellScopedAt 0 = true := sorted.2.2.2
  simp [Pattern.isWellScopedAt] at scope

/-- **A declared constructor of a plain argument and an argument beneath a
binder, as a context of two holes**: the hole at `true` is beneath the
binder, at the stage with the bound sort added. -/
def binderContext (presentation : ValidatedLanguageDef) {rule : GrammarRule}
    {name binder bodyName result : String} (sort bodySort : String)
    (declared : rule ∈ presentation.language.terms) (category : rule.category = result)
    (params : rule.params =
      [.simple name (.base sort), .abstractionNamed (some binder) bodyName (.base bodySort)])
    (stage : List TypeExpr) :
    Contexts.Context presentation
      (fun index : Bool =>
        bif index then (⟨.base bodySort, .base bodySort :: stage⟩ : Contexts.Interface)
        else ⟨.base sort, stage⟩)
      ⟨.base result, stage⟩ where
  shape := .apply rule.label [.hole false, .lambda none (.hole true)]
  linear := ⟨by simp [MultiHoleContext.holes, MultiHoleContext.holesList],
    fun index => by cases index <;> simp [MultiHoleContext.holes, MultiHoleContext.holesList]⟩
  sorted := fun {target} morphism filling => by
    subst category
    have plain : ¬ UsesBareCollection rule := by
      rintro ⟨_, _, _, bare⟩
      rw [params] at bare
      simp at bare
    have typed : ArgumentsHaveTypes target.language FreeTypeContext.empty
        (stage.map (mapTypeExpr morphism.symbols))
        [(filling false).1, .lambda none (filling true).1]
        (rule.params.map (mapTermParam morphism.symbols)) := by
      rw [params]
      exact .cons trivial rfl (filling false).2.1
        (.cons trivial rfl (.lambda (filling true).2.1) .nil)
    exact apply_wellSorted morphism declared plain typed
      (fun argument (member : argument ∈ [(filling false).1, .lambda none (filling true).1]) => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact (filling false).2.2.1
        · simpa [Pattern.hasCanonicalBinderMetadata] using (filling true).2.2.1)
      (fun argument (member : argument ∈ [(filling false).1, .lambda none (filling true).1]) => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact (filling false).2.2.2.1
        · simpa [isObjectPattern] using (filling true).2.2.2.1)

/-- Filling the context of a binding constructor applies it to the first
filling and to the abstraction of the second. -/
theorem fill_binderContext {presentation : ValidatedLanguageDef} {rule : GrammarRule}
    {name binder bodyName result : String} (sort bodySort : String)
    (declared : rule ∈ presentation.language.terms) (category : rule.category = result)
    (params : rule.params =
      [.simple name (.base sort), .abstractionNamed (some binder) bodyName (.base bodySort)])
    (stage : List TypeExpr)
    (filling : (index : Bool) → Contexts.Term presentation.language
      (bif index then (⟨.base bodySort, .base bodySort :: stage⟩ : Contexts.Interface)
        else ⟨.base sort, stage⟩)) :
    ((binderContext presentation sort bodySort declared category params stage).fill filling).1 =
      .apply rule.label [(filling false).1, .lambda none (filling true).1] :=
  rfl

/-! ## The image of a context -/

/-- **A class of interfaces in which the holes of atoms are free**: every
interface of atoms, beneath any binders, belongs to it. -/
def AtomsFree (declared : Contexts.Interface → Prop) : Prop :=
  ∀ stage : List TypeExpr, declared ⟨.base "Atom", stage⟩

/-- **Positive**: every interface, the class of the cartesian reading. -/
theorem atomsFree_all : AtomsFree fun _ => True := fun _ => trivial

/-- **Positive**: the atoms alone; names and spaces are used once. -/
theorem atomsFree_atoms : AtomsFree (ofSorts ["Atom"]) := fun stage => ofSorts_base (by decide) stage

/-- **Negative**: the names and the spaces. -/
theorem not_atomsFree_data : ¬ AtomsFree candidateData :=
  fun free => not_candidateData_closedAtom (free [])

variable {declared : Contexts.Interface → Prop}

/-- **The image of a context of terms**, beneath `extra` of its binders: the
pattern of the same shape, as a context of a reading in which the holes of
atoms are free.  A hole is placed as it is, beneath the binders above it; a
variable, a sort and a constant are their atoms. -/
def atomContextAt (base : BasePremiseEvaluator) (free : AtomsFree declared) (width : Nat)
    {slots : Type} : (extra : Nat) → TermContext slots →
      (candidateUnder base).RegionContext declared (fun _ : slots => atomInterface width)
        (atomInterface (width + extra))
  | extra, .hole slot =>
      ContextTheory.RegionContext.substitute
        (ContextTheory.RegionContext.ofContext (theory := candidateUnder base)
          (declared := declared) (placedHole width extra) fun _ _ => free _)
        (fun _ : Unit => ContextTheory.RegionContext.project (theory := candidateUnder base)
          (declared := declared) (fun _ : slots => atomInterface width) slot fun _ => free _)
        fun _ => free _
  | extra, .srt sort =>
      ContextTheory.discardingConstant (theory := candidateUnder base) (declared := declared)
        (fun _ : slots => atomInterface width) (fun _ => free _)
        (atomTermAt (width + extra) (.srt sort))
  | extra, .con name =>
      ContextTheory.discardingConstant (theory := candidateUnder base) (declared := declared)
        (fun _ : slots => atomInterface width) (fun _ => free _)
        (atomTermAt (width + extra) (.con name))
  | extra, .var index =>
      ContextTheory.discardingConstant (theory := candidateUnder base) (declared := declared)
        (fun _ : slots => atomInterface width) (fun _ => free _)
        (atomTermAt (width + extra) (.var index))
  | extra, .app function argument =>
      ContextTheory.RegionContext.substitute
        (ContextTheory.RegionContext.ofContext (theory := candidateUnder base)
          (declared := declared)
          (applicationContext (List.replicate (width + extra) (.base "Atom")))
          fun _ _ => free _)
        (fun index : Bool =>
          bif index then atomContextAt base free width extra argument
          else atomContextAt base free width extra function)
        fun _ => free _
  | extra, .lam domain body =>
      ContextTheory.RegionContext.substitute
        (ContextTheory.RegionContext.ofContext (theory := candidateUnder base)
          (declared := declared)
          (binderContext atomsReducePresentation "Atom" "Atom" (rule := abstractionConstructor)
            (name := "a") (binder := "x") (bodyName := "body") (by decide) rfl rfl
            (List.replicate (width + extra) (.base "Atom")))
          fun _ index => by cases index <;> exact free _)
        (fun index : Bool =>
          match index with
          | false => atomContextAt base free width extra domain
          | true => atomContextAt base free width (extra + 1) body)
        fun _ => free _
  | extra, .pi domain body =>
      ContextTheory.RegionContext.substitute
        (ContextTheory.RegionContext.ofContext (theory := candidateUnder base)
          (declared := declared)
          (binderContext atomsReducePresentation "Atom" "Atom" (rule := productConstructor)
            (name := "a") (binder := "x") (bodyName := "body") (by decide) rfl rfl
            (List.replicate (width + extra) (.base "Atom")))
          fun _ index => by cases index <;> exact free _)
        (fun index : Bool =>
          match index with
          | false => atomContextAt base free width extra domain
          | true => atomContextAt base free width (extra + 1) body)
        fun _ => free _

/-- **The atom of a term with free variables below a depth is the same
beneath more binders**: all its variables are bound. -/
theorem atomAt_of_wellScoped {term : LF.Term} {depth : Nat} (within : LF.WellScoped depth term) :
    ∀ extra : Nat, atomAt (depth + extra) term = atomAt depth term := by
  induction within with
  | srt => intro extra; rw [atomAt_srt, atomAt_srt]
  | con => intro extra; rfl
  | @var depth index bound =>
      intro extra
      rw [atomAt_var_of_lt bound,
        atomAt_var_of_lt (Nat.lt_of_lt_of_le bound (Nat.le_add_right _ _))]
  | pi _ _ ihDomain ihBody =>
      intro extra
      have body := ihBody extra
      rw [Nat.add_right_comm] at body
      simp only [atomAt, ihDomain extra, body]
  | lam _ _ ihDomain ihBody =>
      intro extra
      have body := ihBody extra
      rw [Nat.add_right_comm] at body
      simp only [atomAt, ihDomain extra, body]
  | app _ _ ihFunction ihArgument =>
      intro extra
      simp only [atomAt, ihFunction extra, ihArgument extra]

/-- **The image of a context, filled with the atoms of terms with free
variables below the width, is the atom of the filled context.** -/
theorem act_atomContextAt (base : BasePremiseEvaluator) (free : AtomsFree declared) (width : Nat)
    {slots : Type} (filling : slots → LF.Term)
    (within : ∀ slot, LF.WellScoped width (filling slot)) :
    ∀ (context : TermContext slots) (extra : Nat),
      ((atomContextAt base free width extra context).act fun slot =>
        atomTermAt width (filling slot)).1 = atomAt (width + extra) (context.fill filling) := by
  intro context
  induction context with
  | hole slot =>
      intro extra
      show atomAt width (filling slot) = atomAt (width + extra) (filling slot)
      exact (atomAt_of_wellScoped (within slot) extra).symm
  | srt sort => intro extra; rfl
  | con name => intro extra; rfl
  | var index => intro extra; rfl
  | app function argument ihFunction ihArgument =>
      intro extra
      show Pattern.apply "App"
          [((atomContextAt base free width extra function).act fun slot =>
              atomTermAt width (filling slot)).1,
            ((atomContextAt base free width extra argument).act fun slot =>
              atomTermAt width (filling slot)).1] = _
      rw [ihFunction extra, ihArgument extra]
      rfl
  | lam domain body ihDomain ihBody =>
      intro extra
      show Pattern.apply "Lam"
          [((atomContextAt base free width extra domain).act fun slot =>
              atomTermAt width (filling slot)).1,
            .lambda none ((atomContextAt base free width (extra + 1) body).act fun slot =>
              atomTermAt width (filling slot)).1] = _
      rw [ihDomain extra, ihBody (extra + 1)]
      rfl
  | pi domain body ihDomain ihBody =>
      intro extra
      show Pattern.apply "Pi"
          [((atomContextAt base free width extra domain).act fun slot =>
              atomTermAt width (filling slot)).1,
            .lambda none ((atomContextAt base free width (extra + 1) body).act fun slot =>
              atomTermAt width (filling slot)).1] = _
      rw [ihDomain extra, ihBody (extra + 1)]
      rfl

/-! ## The hosting map -/

/-- **The pure calculus on the terms with free variables below a width, in a
reading of the candidate in which the holes of atoms are free**: a term is
read as its atom beneath `width` binders, a context as the pattern of the
same shape. -/
def scopedMap (base : BasePremiseEvaluator) (free : AtomsFree declared) (width : Nat) :
    ContextMap (scopedRewriting width Theory.empty)
      ((candidateUnder base).regionReading declared) where
  interface := fun _ => atomInterface width
  term := fun term => atomTermAt width term.1
  context := fun context => atomContextAt base free width 0 context.1
  term_resp := fun {_ first second} related => by
    have same : first = second := related
    rw [same]
    exact Relation.EqvGen.refl _
  equivariant := fun context filling =>
    ContextMap.equations_of_eq (target := (candidateUnder base).regionReading declared)
      (Subtype.ext (act_atomContextAt base free width (fun slot => (filling slot).1)
        (fun slot => (filling slot).2) context.1 0).symm)

/-- **Under every evaluator of its premises, a reading of the candidate in
which the holes of atoms are free hosts the pure calculus on the terms with
free variables below a width, with all the contexts of those terms**: no two
terms get one image, a step is a step of the image, and a step of the image
is the image of a step. -/
theorem scopedMap_hosting (base : BasePremiseEvaluator) (free : AtomsFree declared)
    (width : Nat) : (scopedMap base free width).Hosting := by
  refine ⟨(scopedMap base free width).faithful_of_reflectsEquations ?_,
    (scopedMap base free width).preservesTransitions_of_rewrites ?_,
    (scopedMap base free width).reflectsTransitions_of_rewrites ?_⟩
  · intro _ first second related
    have same : atomTermAt width second.1 = atomTermAt width first.1 :=
      eq_atomTermAt_of_related (base := base) (depth := width) related
    exact Subtype.ext (atomAt_injective width (congrArg Subtype.val same)).symm
  · intro _ term next step
    exact (termStep_atomTermAt_iff (base := base) (depth := width)).mpr ⟨next.1, step, rfl⟩
  · intro _ term next step
    obtain ⟨nextTerm, sourceStep, rfl⟩ :=
      (termStep_atomTermAt_iff (base := base) (depth := width)).mp step
    exact ⟨⟨nextTerm, wellScoped_of_step sourceStep term.2⟩, sourceStep,
      Relation.EqvGen.refl _⟩

/-- **A reading of the candidate in which the holes of atoms are free is a
host, with all contexts, of the pure calculus on the terms with free
variables below a width, for every width.** -/
theorem atomsFree_hostOf_scoped (base : BasePremiseEvaluator) (free : AtomsFree declared) :
    HostOf ((candidateUnder base).regionReading declared)
      (fun source => ∃ width : Nat, source = scopedRewriting width Theory.empty)
      .contexts .hosting := by
  rintro reading ⟨width, rfl⟩
  exact ⟨scopedMap base free width, scopedMap_hosting base free width⟩

/-- The cartesian reading of the candidate, under its evaluator. -/
theorem cartesian_hostOf_scoped :
    HostOf atomsReduceTheory.cartesianReading
      (fun source => ∃ width : Nat, source = scopedRewriting width Theory.empty)
      .contexts .hosting :=
  atomsFree_hostOf_scoped matchingEvaluator atomsFree_all

/-- The reading in which an atom may be discarded and copied, and a name and
a space are used once. -/
abbrev atomRegions : ContextTheory.{0} := atomsReduceTheory.regionReading (ofSorts ["Atom"])

/-- The reading with atoms free and data used once, under the evaluator of
the candidate. -/
theorem atomRegions_hostOf_scoped :
    HostOf atomRegions
      (fun source => ∃ width : Nat, source = scopedRewriting width Theory.empty)
      .contexts .hosting :=
  atomsFree_hostOf_scoped matchingEvaluator atomsFree_atoms

/-! ## The cell that a separate sort of processes refutes -/

/-- `(λ x. x x) (λ x. x x)` is closed. -/
theorem omega_closed : LF.WellScoped 0 Dedukti.omega := Dedukti.wellScoped_of_test _ 0 (by decide)

/-- The context of the closed terms that applies its first hole to its
second. -/
def closedApplication : (scopedRewriting 0 Theory.empty).Context (fun _ : Bool => ()) () :=
  (⟨.app (.hole false) (.hole true), trivial, trivial⟩ :
    {context : TermContext Bool // ScopedContext 0 context})

/-- **The closed terms of the pure calculus pair terms that reduce, and are
hosted with all their contexts.**  They have a context of two holes, a term
with a step, and two terms that the context keeps apart at either hole beside
it; a presentation that reduces in a sort that no constructor takes hosts
such a theory under no reading.  Every reading of the candidate in which the
holes of atoms are free hosts it, under every evaluator. -/
theorem pairing_hosted (base : BasePremiseEvaluator) (free : AtomsFree declared) :
    (∃ moving next still other : (scopedRewriting 0 Theory.empty).Term (),
      (scopedRewriting 0 Theory.empty).rewrites moving next ∧
        ¬ ((scopedRewriting 0 Theory.empty).equations ()).r
          ((scopedRewriting 0 Theory.empty).fill closedApplication fun index =>
            bif index then still else moving)
          ((scopedRewriting 0 Theory.empty).fill closedApplication fun index =>
            bif index then other else moving) ∧
        ¬ ((scopedRewriting 0 Theory.empty).equations ()).r
          ((scopedRewriting 0 Theory.empty).fill closedApplication fun index =>
            bif index then moving else still)
          ((scopedRewriting 0 Theory.empty).fill closedApplication fun index =>
            bif index then moving else other)) ∧
      ∃ map : ContextMap (scopedRewriting 0 Theory.empty)
        ((candidateUnder base).regionReading declared), map.Hosting :=
  ⟨⟨⟨Dedukti.omega, omega_closed⟩, ⟨Dedukti.omega, omega_closed⟩, ⟨.srt .type, .srt⟩,
      ⟨.srt .kind, .srt⟩, Dedukti.omega_step Theory.empty,
      fun same => absurd (show LF.Term.app Dedukti.omega (.srt .type) =
        .app Dedukti.omega (.srt .kind) from congrArg Subtype.val same) (by decide),
      fun same => absurd (show LF.Term.app (.srt .type) Dedukti.omega =
        .app (.srt .kind) Dedukti.omega from congrArg Subtype.val same) (by decide)⟩,
    scopedMap base free 0, scopedMap_hosting base free 0⟩

/-! ## All terms at once: the stage of an interface is finite -/

/-- The label of a variable atom, as a count. -/
def variableLabel (label : String) : Bool := label == "prime-variable"

/-- A variable has one variable atom when it is free beneath the binders, and
none when one of them binds it. -/
theorem tokens_variable_var (depth index : Nat) :
    tokens variableLabel (atomAt depth (.var index)) = if index < depth then 0 else 1 := by
  by_cases below : index < depth
  · rw [atomAt_var_of_lt below, if_pos below]
    rfl
  · rw [atomAt_var_of_le (Nat.le_of_not_lt below), if_neg below]
    have inner : tokens variableLabel (numeral (index - depth)) = 0 :=
      tokens_numeral (by decide) (by decide) _
    simp [variableAtom, tokens, tokensList, variableLabel, inner]

/-- The abstraction of a variable, over a sort: its binder is one more. -/
theorem tokens_variable_binder (depth index : Nat) :
    tokens variableLabel (atomAt depth (.lam (.srt .type) (.var index))) =
      if index < depth + 1 then 0 else 1 := by
  have symbol : tokens variableLabel (symbolAtom 0) = 0 := by
    have inner : tokens variableLabel (numeral 0) = 0 := tokens_numeral (by decide) (by decide) 0
    simp [symbolAtom, tokens, tokensList, variableLabel, inner]
  rw [← tokens_variable_var (depth + 1) index]
  show tokens variableLabel
      (.apply "Lam" [symbolAtom 0, .lambda none (atomAt (depth + 1) (.var index))]) = _
  simp [tokens, tokensList, variableLabel, symbol]

/-- **No map of theories from a theory of the λΠ-calculus modulo, into any
reading of the candidate, gives every term as many variable atoms as its atom
beneath `width` binders has.**  The context `λ. □` binds the variable `width`
of what fills it and leaves the variable `width + 1` free; both fillings have
one variable atom, the first result has none and the second has one. -/
theorem not_contextMap_of_counts_variables {base : BasePremiseEvaluator} {theory : Theory}
    (width : Nat)
    (map : ContextMap (rewritingTheory theory) ((candidateUnder base).regionReading declared))
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
    have related : (termSetoid base atomsReduce (map.interface ())).r
        (map.term (origin := ()) (LF.Term.lam (.srt .type) term))
        ((map.context binder).act fun _ => map.term (origin := ()) term) :=
      map.equivariant binder fun _ => term
    have same : tokens variableLabel (map.term (origin := ()) (LF.Term.lam (.srt .type) term)).1 =
        tokens variableLabel ((map.context binder).act fun _ => map.term (origin := ()) term).1 :=
      atomsReduce_quoteDropOnly.tokens_eq (by decide) (by decide) related
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
modulo and into any reading of the candidate. -/
theorem atomReading_not_contextMap {base : BasePremiseEvaluator} {theory : Theory} (width : Nat)
    (map : ContextMap (rewritingTheory theory) ((candidateUnder base).regionReading declared))
    (reads : ∀ term : (rewritingTheory theory).Term (), (map.term term).1 = atomAt width term) :
    False :=
  not_contextMap_of_counts_variables width map fun term => by rw [reads]

#print axioms wellScoped_of_step
#print axioms includeScoped_hosting
#print axioms act_atomContextAt
#print axioms scopedMap_hosting
#print axioms atomsFree_hostOf_scoped
#print axioms cartesian_hostOf_scoped
#print axioms atomRegions_hostOf_scoped
#print axioms pairing_hosted
#print axioms not_contextMap_of_counts_variables
#print axioms atomReading_not_contextMap

end Mettapedia.Logic.HostingStyles.AtomsReduce
