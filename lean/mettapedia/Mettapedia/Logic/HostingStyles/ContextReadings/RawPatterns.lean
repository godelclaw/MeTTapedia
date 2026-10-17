import Mettapedia.Logic.HostingStyles.ContextReadings.PresentedReadings

/-!
# The existing cartesian construction, and what it does not sort

`HoleSyntax.theory` builds a theory with one interface from a syntax with
named holes in which a hole may occur any number of times.  The patterns of a
language with their patterns with holes are such a syntax (`patternSyntax`):
the laws it asks for are the existing laws of filling and plugging.  So for
every language and every evaluator of premises there is already a cartesian
theory (`rawPatternTheory`): its terms are all patterns, compared by the
static equivalence of the language on patterns, its contexts are all patterns
with holes, and its steps are the steps of the language up to that
equivalence.  It discards and copies (`rawPatternTheory_discards`,
`rawPatternTheory_copies`).

It is not the cartesian reading of the presented language
(`ContextTheory.cartesianReading` of `Contexts.contextTheory`): it has one
interface and no sorting: every pattern is a term of it, also one that no
declared constructor heads, which is a term of no interface of the presented
language (`undeclared_not_presentedTerm`).  The readings of the presented
language keep its interfaces and its sorting, and map into it by forgetting
them (`forgetSorts`): a context of a reading goes to a pattern with holes that
does the same.  That map preserves transitions
(`forgetSorts_preservesTransitions`).  Whether it reflects the static
equivalence and the transitions is the question whether two sorted terms that
are equal through unsorted patterns are equal through sorted ones; it is not
settled here.

What makes filling respect the static equivalence without any sorting is that
the equivalence on patterns is a congruence for every pattern former
(`equationEquiv_fill_multi`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.ContextReadings

open Mettapedia.GSLT
open Mettapedia.GSLT.Dedukti (HoleSyntax)
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles

/-- **Patterns with their patterns with holes are a syntax with holes.** -/
def patternSyntax : HoleSyntax Pattern where
  Hole := MultiHoleContext
  fill := MultiHoleContext.fill
  bind := MultiHoleContext.bind
  hole := MultiHoleContext.hole
  constant := MultiHoleContext.ofPattern
  fill_bind := fun filling plugged context => MultiHoleContext.fill_bind filling plugged context
  fill_hole := fun _ _ => rfl
  fill_constant := fun filling term => MultiHoleContext.fill_ofPattern filling term

mutual
  /-- **The static equivalence on patterns is a congruence for every pattern
  with holes**, a hole occurring any number of times. -/
  theorem equationEquiv_fill_multi {base : BasePremiseEvaluator} {lang : LanguageDef} {ι : Type}
      {first second : ι → Pattern}
      (related : ∀ index, EquationEquiv base lang (first index) (second index)) :
      ∀ context : MultiHoleContext ι,
        EquationEquiv base lang (context.fill first) (context.fill second)
    | .hole index => related index
    | .bvar _ => Relation.EqvGen.refl _
    | .fvar _ => Relation.EqvGen.refl _
    | .apply label arguments =>
        equationEquiv_apply_of_forall₂ label (forall₂_fillList related arguments)
    | .lambda binder body =>
        equationEquiv_fill (.lambda binder .hole) (equationEquiv_fill_multi related body)
    | .multiLambda arity binders body =>
        equationEquiv_fill (.multiLambda arity binders .hole)
          (equationEquiv_fill_multi related body)
    | .subst body replacement =>
        Relation.EqvGen.trans _ _ _
          (equationEquiv_fill (.substBody .hole (replacement.fill first))
            (equationEquiv_fill_multi related body))
          (equationEquiv_fill (.substReplacement (body.fill second) .hole)
            (equationEquiv_fill_multi related replacement))
    | .collection kind elements rest =>
        equationEquiv_collection_of_forall₂ kind rest (forall₂_fillList related elements)

  /-- The same along a list of patterns with holes. -/
  theorem forall₂_fillList {base : BasePremiseEvaluator} {lang : LanguageDef} {ι : Type}
      {first second : ι → Pattern}
      (related : ∀ index, EquationEquiv base lang (first index) (second index)) :
      ∀ contexts : List (MultiHoleContext ι),
        List.Forall₂ (EquationEquiv base lang) (MultiHoleContext.fillList first contexts)
          (MultiHoleContext.fillList second contexts)
    | [] => .nil
    | context :: contexts =>
        .cons (equationEquiv_fill_multi related context) (forall₂_fillList related contexts)
end

/-- **The cartesian theory of the patterns of a language**, by the existing
construction: every pattern is a term, every pattern with holes a context. -/
def rawPatternTheory (base : BasePremiseEvaluator) (lang : LanguageDef) : ContextTheory.{0} :=
  patternSyntax.theory (equationSetoid base lang) (StepModuloEquations base lang)
    (fun context _ _ related => equationEquiv_fill_multi related context)
    (stepModuloEquations_resp_left base lang) (stepModuloEquations_resp_right base lang)

/-- It discards: the pattern that is its first hole. -/
theorem rawPatternTheory_discards (base : BasePremiseEvaluator) (lang : LanguageDef) :
    (rawPatternTheory base lang).Discards () :=
  ⟨MultiHoleContext.hole false, fun _ => Relation.EqvGen.refl _⟩

/-- It copies: a constructor applied to one hole twice. -/
theorem rawPatternTheory_copies (base : BasePremiseEvaluator) (lang : LanguageDef) :
    (rawPatternTheory base lang).Copies () :=
  ⟨MultiHoleContext.apply "pair" [.hole false, .hole true],
    MultiHoleContext.apply "pair" [.hole (), .hole ()], fun _ => Relation.EqvGen.refl _⟩

/-- **Negative**: it has no linear size. -/
theorem rawPatternTheory_not_linearSize (base : BasePremiseEvaluator) (lang : LanguageDef) :
    IsEmpty (rawPatternTheory base lang).LinearSize :=
  ⟨fun sized => sized.not_discards (interface := ()) (Pattern.bvar 0)
    (rawPatternTheory_discards base lang)⟩

/-- **The presented language sorts what the cartesian theory of patterns
does not**: a pattern headed by no declared constructor of the candidate
presentation is a term of no interface of the presented language. -/
theorem undeclared_not_presentedTerm (interface : Contexts.Interface) :
    ¬ ∃ term : Contexts.Term Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.language
        interface, term.1 = Pattern.apply "undeclared" [] := by
  rintro ⟨term, shape⟩
  have typed := term.2.1
  rw [shape] at typed
  obtain ⟨rule, declared, label, -⟩ := WellSorted.declared_constructor_of_hasType_apply typed
  revert rule
  decide

/-- **A reading of a presented language, forgetting its sorts**: a term is
its pattern, a context a pattern with holes that does the same. -/
noncomputable def forgetSorts (base : BasePremiseEvaluator) (presentation : ValidatedLanguageDef)
    (declared : Contexts.Interface → Prop) :
    ContextMap ((contextTheory base presentation).regionReading declared)
      (rawPatternTheory base presentation.language) where
  interface := fun _ => ()
  term := fun term => term.1
  context := fun {arity} _ _ context =>
    Classical.choose (@exists_shape base presentation declared arity (Classical.decEq arity) _ _
      context)
  term_resp := fun related => equationEquiv_of_termSetoid related
  equivariant := fun {arity} _ _ context filling =>
    ContextMap.equations_of_eq (target := rawPatternTheory base presentation.language)
      (interface := ())
      ((Classical.choose_spec (@exists_shape base presentation declared arity
        (Classical.decEq arity) _ _ context)).1 filling)

/-- **Forgetting the sorts preserves transitions.** -/
theorem forgetSorts_preservesTransitions (base : BasePremiseEvaluator)
    (presentation : ValidatedLanguageDef) (declared : Contexts.Interface → Prop) :
    (forgetSorts base presentation declared).PreservesTransitions := by
  apply ContextMap.preservesTransitions_of_rewrites
  rintro interface term next ⟨redex, contractum, before, fired, after⟩
  exact ⟨redex.1, contractum.1, equationEquiv_of_termSetoid before, fired,
    equationEquiv_of_termSetoid after⟩

#print axioms patternSyntax
#print axioms equationEquiv_fill_multi
#print axioms rawPatternTheory
#print axioms rawPatternTheory_discards
#print axioms rawPatternTheory_copies
#print axioms rawPatternTheory_not_linearSize
#print axioms undeclared_not_presentedTerm
#print axioms forgetSorts
#print axioms forgetSorts_preservesTransitions

end Mettapedia.Logic.HostingStyles.ContextReadings
