import Mettapedia.Logic.HostingStyles.SpacesAndRegions.SealedPart

/-!
# A table with its contexts, in a reading of the sealed part

The sealed part of the candidate has the contexts of the candidate that send
sealed terms to a sealed term.  In a reading of it in which the holes of
atoms are free, such a hole may be used any number of times
(`ContextTheory.regionReading`).

* **The contexts out of which the image of a context of λΠ terms is made
  keep sealing**: the hole placed beneath more binders
  (`placedHole_keeps`), the application (`applicationContext_keeps`) and a
  constructor that binds (`binderContext_keeps`).  So each of them is a
  context of the sealed part, and the image of a context of terms is a
  context of the reading of the part (`sealedShapeContextAt`): the pattern of
  the same shape (`act_sealedShapeContextAt`).
* **Hosting of a table with its contexts survives in the reading of the
  sealed part** (`sealedPart_hostOf_scopedTabularAt`): at the space of a
  table of first-order rules with bound right sides none of whose left sides
  is a variable, a reading of the sealed part in which the holes of atoms are
  free is a host, with all contexts, of the theories given by the table on
  the terms with free variables below a width, for every width.  The map is
  that of the candidate on all terms, a term read as its atom and a context
  as the pattern of its shape (`sealedScopedMap`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.SpacesAndRegions

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti (Theory RuleTable rewritingTheory TermContext)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
open Mettapedia.Logic.HostingStyles.AtomsReduce
  (atomAt atomInterface unquotedSorts BoundFirstOrder scopedRewriting AtomsFree binderContext
    applicationConstructor abstractionConstructor productConstructor)
open Mettapedia.Logic.HostingStyles.AmbientSpace
open Mettapedia.Logic.HostingStyles.AmbientRegions

variable {admits : Pattern → Bool} {declared : Contexts.Interface → Prop}

/-! ## Three contexts of the candidate that keep sealing -/

/-- **The hole placed beneath more binders keeps sealing**: what fills it is
read there as it is written, and more binders around a sealed pattern keep it
sealed. -/
theorem placedHole_keeps (width extra : Nat)
    (filling : (index : Unit) → Contexts.Term spacesAndRegions (atomInterface width))
    (kept : ∀ index, SealedTerm (filling index)) :
    SealedTerm ((placedHoleOf spacesAndRegionsPresentation width extra).fill filling) := by
  have one : SealedWithPlainRuns (List.replicate width (TypeExpr.base "Atom")).length
      (contract (filling ()).1) := kept ()
  rw [List.length_replicate] at one
  show SealedWithPlainRuns (List.replicate (width + extra) (TypeExpr.base "Atom")).length
    (contract (filling ()).1)
  rw [List.length_replicate]
  exact one.mono (Nat.le_add_right width extra)

/-- **The application of an atom to an atom keeps sealing.** -/
theorem applicationContext_keeps (stage : List TypeExpr)
    (filling : (index : Bool) → Contexts.Term spacesAndRegions ⟨.base "Atom", stage⟩)
    (kept : ∀ index, SealedTerm (filling index)) :
    SealedTerm ((applicationContextOf spacesAndRegionsPresentation spacesAndRegions_carriesAtoms
      stage).fill filling) := by
  show SealedWithPlainRuns stage.length
    (contract (.apply "App" [(filling false).1, (filling true).1]))
  rw [contract_apply_of_ne (by decide)]
  refine (sealedWithPlainRuns_apply_iff (label := "App") (by decide) _ _).mpr ?_
  intro part member
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact kept false
  · exact kept true

/-- **A constructor of atoms that binds, other than quotation and the run,
keeps sealing**: the atom in its body is sealed beneath one more binder. -/
theorem binderContext_keeps {rule : GrammarRule} {name binder bodyName : String}
    (declaredRule : rule ∈ spacesAndRegionsPresentation.language.terms)
    (category : rule.category = "Atom")
    (params : rule.params =
      [.simple name (.base "Atom"), .abstractionNamed (some binder) bodyName (.base "Atom")])
    (other : quoteOrRun rule.label = false) (stage : List TypeExpr)
    (filling : (index : Bool) → Contexts.Term spacesAndRegions
      (bif index then (⟨.base "Atom", .base "Atom" :: stage⟩ : Contexts.Interface)
        else ⟨.base "Atom", stage⟩))
    (kept : ∀ index, SealedTerm (filling index)) :
    SealedTerm ((binderContext spacesAndRegionsPresentation "Atom" "Atom" declaredRule category
      params stage).fill filling) := by
  have notQuote : rule.label ≠ "prime-quote" := by
    intro same
    rw [same] at other
    exact absurd other (by decide)
  show SealedWithPlainRuns stage.length
    (contract (.apply rule.label [(filling false).1, .lambda none (filling true).1]))
  rw [contract_apply_of_ne notQuote]
  refine (sealedWithPlainRuns_apply_iff other _ _).mpr ?_
  intro part member
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact kept false
  · rw [contract]
    exact (sealedWithPlainRuns_lambda _ _ _).mpr (kept true)

/-- **Negative**: quoting does not keep sealing beneath a binder.  The bound
variable is sealed there, and the dropped quotation of it is not. -/
theorem quotation_not_keeps :
    SealedWithPlainRuns 1 (.bvar 0) ∧ ¬ SealedWithPlainRuns 1 (dropped (quoted (.bvar 0))) :=
  ⟨⟨by decide +kernel, by decide +kernel⟩, fun kept => absurd kept.1 (by decide +kernel)⟩

/-! ## The image of a context of terms, in a reading of the sealed part -/

/-- **The image of a context of λΠ terms among the contexts of a reading of
the sealed part**, beneath `extra` of its binders: the pattern of the same
shape.  A hole is placed as it is beneath the binders above it; a sort, a
constant and a variable of the context are their atoms.  Each piece is a
context of the candidate that keeps sealing.  Positive: filled, it is the
pattern of its shape (`act_sealedShapeContextAt`).  Negative: quoting is no
such piece (`quotation_not_keeps`). -/
def sealedShapeContextAt (admits : Pattern → Bool) (ambientSpace : Pattern)
    (safe : QuotesOnlyQuoted (contract ambientSpace)) (free : AtomsFree declared) (width : Nat)
    {slots : Type} : (extra : Nat) → TermContext slots →
      (sealedPart admits ambientSpace safe).RegionContext declared
        (fun _ : slots => atomInterface width) (atomInterface (width + extra))
  | extra, .hole slot =>
      ContextTheory.RegionContext.substitute
        (ContextTheory.RegionContext.ofContext (theory := sealedPart admits ambientSpace safe)
          (declared := declared)
          ⟨placedHoleOf spacesAndRegionsPresentation width extra, placedHole_keeps width extra⟩
          fun _ _ => free _)
        (fun _ : Unit => ContextTheory.RegionContext.project
          (theory := sealedPart admits ambientSpace safe) (declared := declared)
          (fun _ : slots => atomInterface width) slot fun _ => free _)
        fun _ => free _
  | extra, .srt sort =>
      ContextTheory.discardingConstant (theory := sealedPart admits ambientSpace safe)
        (declared := declared) (fun _ : slots => atomInterface width) (fun _ => free _)
        ⟨atomTermIn (presentation := spacesAndRegionsPresentation) spacesAndRegions_carriesAtoms
          (width + extra) (.srt sort), sealedTerm_atom _ _⟩
  | extra, .con name =>
      ContextTheory.discardingConstant (theory := sealedPart admits ambientSpace safe)
        (declared := declared) (fun _ : slots => atomInterface width) (fun _ => free _)
        ⟨atomTermIn (presentation := spacesAndRegionsPresentation) spacesAndRegions_carriesAtoms
          (width + extra) (.con name), sealedTerm_atom _ _⟩
  | extra, .var index =>
      ContextTheory.discardingConstant (theory := sealedPart admits ambientSpace safe)
        (declared := declared) (fun _ : slots => atomInterface width) (fun _ => free _)
        ⟨atomTermIn (presentation := spacesAndRegionsPresentation) spacesAndRegions_carriesAtoms
          (width + extra) (.var index), sealedTerm_atom _ _⟩
  | extra, .app function argument =>
      ContextTheory.RegionContext.substitute
        (ContextTheory.RegionContext.ofContext (theory := sealedPart admits ambientSpace safe)
          (declared := declared)
          ⟨applicationContextOf spacesAndRegionsPresentation spacesAndRegions_carriesAtoms
              (List.replicate (width + extra) (.base "Atom")),
            applicationContext_keeps (List.replicate (width + extra) (.base "Atom"))⟩
          fun _ _ => free _)
        (fun index : Bool =>
          bif index then sealedShapeContextAt admits ambientSpace safe free width extra argument
          else sealedShapeContextAt admits ambientSpace safe free width extra function)
        fun _ => free _
  | extra, .lam domain body =>
      ContextTheory.RegionContext.substitute
        (ContextTheory.RegionContext.ofContext (theory := sealedPart admits ambientSpace safe)
          (declared := declared)
          ⟨binderContext spacesAndRegionsPresentation "Atom" "Atom"
              (rule := abstractionConstructor) (name := "a") (binder := "x") (bodyName := "body")
              (spacesAndRegions_carriesAtoms _ (by decide)) rfl rfl
              (List.replicate (width + extra) (.base "Atom")),
            binderContext_keeps (rule := abstractionConstructor) (name := "a") (binder := "x")
              (bodyName := "body") (spacesAndRegions_carriesAtoms _ (by decide)) rfl rfl
              (by decide) (List.replicate (width + extra) (.base "Atom"))⟩
          fun _ index => by cases index <;> exact free _)
        (fun index : Bool =>
          match index with
          | false => sealedShapeContextAt admits ambientSpace safe free width extra domain
          | true => sealedShapeContextAt admits ambientSpace safe free width (extra + 1) body)
        fun _ => free _
  | extra, .pi domain body =>
      ContextTheory.RegionContext.substitute
        (ContextTheory.RegionContext.ofContext (theory := sealedPart admits ambientSpace safe)
          (declared := declared)
          ⟨binderContext spacesAndRegionsPresentation "Atom" "Atom"
              (rule := productConstructor) (name := "a") (binder := "x") (bodyName := "body")
              (spacesAndRegions_carriesAtoms _ (by decide)) rfl rfl
              (List.replicate (width + extra) (.base "Atom")),
            binderContext_keeps (rule := productConstructor) (name := "a") (binder := "x")
              (bodyName := "body") (spacesAndRegions_carriesAtoms _ (by decide)) rfl rfl
              (by decide) (List.replicate (width + extra) (.base "Atom"))⟩
          fun _ index => by cases index <;> exact free _)
        (fun index : Bool =>
          match index with
          | false => sealedShapeContextAt admits ambientSpace safe free width extra domain
          | true => sealedShapeContextAt admits ambientSpace safe free width (extra + 1) body)
        fun _ => free _

/-- **That image, filled, is the pattern of its shape**, with the atoms of
the leaves and the fillings as they are written. -/
theorem act_sealedShapeContextAt (admits : Pattern → Bool) (ambientSpace : Pattern)
    (safe : QuotesOnlyQuoted (contract ambientSpace)) (free : AtomsFree declared) (width : Nat)
    {slots : Type}
    (filling : slots → (sealedPart admits ambientSpace safe).Term (atomInterface width)) :
    ∀ (context : TermContext slots) (extra : Nat),
      ((sealedShapeContextAt admits ambientSpace safe free width extra context).act filling).1.1 =
        shapePatternAt (fun extra term => atomAt (width + extra) term)
          (fun slot => (filling slot).1.1) extra context := by
  intro context
  induction context with
  | hole slot => intro extra; rfl
  | srt sort => intro extra; rfl
  | con name => intro extra; rfl
  | var index => intro extra; rfl
  | app function argument ihFunction ihArgument =>
      intro extra
      show Pattern.apply "App"
          [((sealedShapeContextAt admits ambientSpace safe free width extra function).act
              filling).1.1,
            ((sealedShapeContextAt admits ambientSpace safe free width extra argument).act
              filling).1.1] = _
      rw [ihFunction extra, ihArgument extra]
      rfl
  | lam domain body ihDomain ihBody =>
      intro extra
      show Pattern.apply "Lam"
          [((sealedShapeContextAt admits ambientSpace safe free width extra domain).act
              filling).1.1,
            .lambda none ((sealedShapeContextAt admits ambientSpace safe free width (extra + 1)
              body).act filling).1.1] = _
      rw [ihDomain extra, ihBody (extra + 1)]
      rfl
  | pi domain body ihDomain ihBody =>
      intro extra
      show Pattern.apply "Pi"
          [((sealedShapeContextAt admits ambientSpace safe free width extra domain).act
              filling).1.1,
            .lambda none ((sealedShapeContextAt admits ambientSpace safe free width (extra + 1)
              body).act filling).1.1] = _
      rw [ihDomain extra, ihBody (extra + 1)]
      rfl

/-! ## The map, and that it is hosting -/

/-- **A theory on the terms with free variables below a width, in a reading
of the sealed part**: a term is read as its atom beneath `width` binders,
which is sealed, and a context as the pattern of the same shape.  Positive:
at the space of a table it is hosting (`sealedPart_hostOf_scopedTabularAt`).
Negative: at the space of the rule `$0 ⟶ *@$0` there is no sealed part to map
into (`not_quotesOnlyQuoted_quotingSpace`,
`sealedTerm_not_kept_at_quotingSpace`). -/
def sealedScopedMap (theory : Theory) (admits : Pattern → Bool) (ambientSpace : Pattern)
    (safe : QuotesOnlyQuoted (contract ambientSpace)) (free : AtomsFree declared) (width : Nat) :
    ContextMap (scopedRewriting width theory)
      ((sealedPart admits ambientSpace safe).regionReading declared) where
  interface := fun _ => atomInterface width
  term := fun term =>
    ⟨atomTermIn (presentation := spacesAndRegionsPresentation) spacesAndRegions_carriesAtoms width
      term.1, sealedTerm_atom width term.1⟩
  context := fun context => sealedShapeContextAt admits ambientSpace safe free width 0 context.1
  term_resp := fun {_ first second} related => by
    have same : first = second := related
    subst same
    exact ContextMap.equations_of_eq
      (target := (sealedPart admits ambientSpace safe).regionReading declared) rfl
  equivariant := fun context filling =>
    ContextMap.equations_of_eq
      (target := (sealedPart admits ambientSpace safe).regionReading declared)
      (Subtype.ext (Subtype.ext
        ((act_sealedShapeContextAt admits ambientSpace safe free width
            (fun slot =>
              ⟨atomTermIn (presentation := spacesAndRegionsPresentation)
                spacesAndRegions_carriesAtoms width (filling slot).1,
                sealedTerm_atom width (filling slot).1⟩) context.1 0).trans
          (shapePatternAt_atoms width (fun slot => (filling slot).1)
            (fun slot => (filling slot).2) context.1 0)).symm))

/-- **That map is hosting**, when the steps of the candidate from the atoms
of terms are the atoms of the steps of the theory and those steps keep the
free variables of a term below a bound. -/
theorem sealedScopedMap_hosting {theory : Theory} {ambientSpace : Pattern}
    (safe : QuotesOnlyQuoted (contract ambientSpace))
    (steps : ∀ {depth : Nat} {source : LF.Term} {target : Pattern},
      Step (regionEvaluator admits ambientSpace) spacesAndRegions (atomAt depth source) target ↔
        ∃ next, target = atomAt depth next ∧ Dedukti.Step theory source next)
    (closed : ∀ {source target : LF.Term}, Dedukti.Step theory source target → ∀ {depth : Nat},
      LF.WellScoped depth source → LF.WellScoped depth target)
    (free : AtomsFree declared) (width : Nat) :
    (sealedScopedMap theory admits ambientSpace safe free width).Hosting := by
  have transitions := fun (source : LF.Term)
      (target : Contexts.Term spacesAndRegions (atomInterface width)) =>
    termStep_atomTermIn_iff (presentation := spacesAndRegionsPresentation)
      spacesAndRegions_carriesAtoms spacesAndRegions_quoteDropOnly spacesAndRegions_quoteDropSorted
      spacesAndRegions_namesOnlyDropped steps (depth := width) (source := source)
      (target := target)
  refine ⟨(sealedScopedMap theory admits ambientSpace safe free width).faithful_of_reflectsEquations
      ?_,
    (sealedScopedMap theory admits ambientSpace safe free width).preservesTransitions_of_rewrites
      ?_,
    (sealedScopedMap theory admits ambientSpace safe free width).reflectsTransitions_of_rewrites
      ?_⟩
  · intro _ first second related
    have same : atomTermIn (presentation := spacesAndRegionsPresentation)
        spacesAndRegions_carriesAtoms width second.1 =
        atomTermIn spacesAndRegions_carriesAtoms width first.1 :=
      eq_atomTermIn_of_related (presentation := spacesAndRegionsPresentation)
        spacesAndRegions_carriesAtoms spacesAndRegions_quoteDropOnly
        spacesAndRegions_quoteDropSorted spacesAndRegions_namesOnlyDropped
        (base := regionEvaluator admits ambientSpace) (depth := width) related
    exact Subtype.ext (atomTermIn_injective spacesAndRegions_carriesAtoms width same).symm
  · intro _ term next step
    exact (transitions term.1 _).mpr ⟨next.1, step, rfl⟩
  · intro _ term next step
    obtain ⟨nextTerm, sourceStep, same⟩ := (transitions term.1 next.1).mp step
    refine ⟨⟨nextTerm, closed sourceStep term.2⟩, sourceStep, ?_⟩
    show (termSetoid (regionEvaluator admits ambientSpace) spacesAndRegions
      (atomInterface width)).r next.1
        (atomTermIn (presentation := spacesAndRegionsPresentation) spacesAndRegions_carriesAtoms
          width nextTerm)
    rw [same]
    exact Relation.EqvGen.refl _

/-- **Hosting of a table with its contexts survives in a reading of the
sealed part**: at the space of a table of first-order rules with bound right
sides none of whose left sides is a variable, a reading of the sealed part in
which the holes of atoms are free is a host, with all contexts, of the
theories given by the table on the terms with free variables below a width,
for every width. -/
theorem sealedPart_hostOf_scopedTabularAt (admitsAtoms : AdmitsAtoms admits) {table : RuleTable}
    (admitted : BoundFirstOrder table)
    (headed : ∀ rule ∈ table, ∀ index : Nat, rule.lhs ≠ .var index)
    (free : AtomsFree declared) :
    HostOf ((sealedPart admits (tableSpace table).1
        (quotesOnlyQuoted_contract_tableSpace table)).regionReading declared)
      (fun source => ∃ (theory : Theory) (width : Nat),
        theory.Tabular table ∧ source = scopedRewriting width theory)
      .contexts .hosting := by
  rintro reading ⟨theory, width, tabular, rfl⟩
  exact ⟨sealedScopedMap theory admits (tableSpace table).1
      (quotesOnlyQuoted_contract_tableSpace table) free width,
    sealedScopedMap_hosting (quotesOnlyQuoted_contract_tableSpace table)
      (spacesAndRegions_atom_step_iff admitsAtoms admitted.listed.1 admitted.listed.2
        (fun rule member => headed rule (Finset.mem_toList.mp member))
        (fun rule => (tabular.rules rule).trans Finset.mem_toList.symm) tabular.undefined)
      (fun sourceStep _ within => wellScoped_of_listStep admitted.listed.1 admitted.listed.2
        (fun rule member => ((tabular.rules rule).trans Finset.mem_toList.symm).mp member)
        tabular.undefined sourceStep within)
      free width⟩

#print axioms placedHole_keeps
#print axioms applicationContext_keeps
#print axioms binderContext_keeps
#print axioms sealedShapeContextAt
#print axioms act_sealedShapeContextAt
#print axioms sealedScopedMap
#print axioms sealedScopedMap_hosting
#print axioms sealedPart_hostOf_scopedTabularAt

end Mettapedia.Logic.HostingStyles.SpacesAndRegions
