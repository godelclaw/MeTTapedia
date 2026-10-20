import Mettapedia.GSLT.Dedukti.PureTypeSystem
import Mettapedia.GSLT.Dedukti.TypeInTypeParadox
import Mettapedia.GSLT.Dedukti.ConstructionsConsistency

/-!
# Hypercube vertices and conversion bubbles are independent axes

A vertex of the lambda cube chooses which products may be formed. A bubble
of Bubble Type Theory chooses which computations count as definitional
equality. This module puts both on one pure type system and shows they are
independent: neither can be simulated by the other, typing grows along each,
and a bubble only matters at vertices whose types contain its redexes.

* `TypedUnder profile conversion`: the sorted pure type system of
  `GSLT.Dedukti.PureTypeSystem` with its conversion relation as a parameter.
  `derives_iff_typedUnder` identifies `Derives profile` with beta conversion.
* `bubbleConv steps`: the conversion a bubble generates, the equivalence
  closure of its declared steps under every term former. Beta conversion is
  the bubble of the beta steps (`bubbleConv_betaRoot`); the weak core declares
  none and converts nothing (`bubbleConv_noSteps_iff`).
* `Kernel products steps`: the kernel at a vertex with a bubble. It grows in
  both (`Kernel.mono`).

**Polymorphism is a vertex.** The type of the polymorphic identity is not a
type at the simply typed vertex, under any bubble
(`polymorphism_needs_vertex`), and it is typed at the top vertex in the weak
core (`polymorphism_in_weak_core`). No bubble added to the simply typed vertex
reaches the weak core at the top (`no_bubble_simulates_polymorphism`).

**Direct value indexing is a vertex.** A well-formed context
`A : Type, P : A → Type`, together with the direct Curry--Howard proposition
`Π x : A, P x`, exists exactly when the ordinary function rule and the
value-to-type product rule are licensed
(`directValueIndexedForall_iff_contains_dependentProducts`).
This characterization holds under every conversion bubble. The dependent
vertex supplies it in the weak core; the simple, polymorphic and type-operator
vertices do not (`directValueIndexedForall_at_dependent`,
`directValueIndexedForall_absent_off_dependent_face`). The statement is about
using the same term-level values as indices; it does not rule out encodings
that first reify values at another level.

**Least bases depend on the interface.** Adding the polymorphic identity type
and the kind `Type → Type` to that direct interface requires exactly the four
CoC formation rules (`directFormationInterfaces_iff_contains_constructionProducts`).
The result is uniform in the conversion bubble; it does not identify arbitrary
bubbles with CoC, characterize all encodings of higher-order logic, or supply
MLTT's universe and inductive rules. Direct abstraction and application retain
the same value in the evidence type (`directForall_abstract`, `directForall_apply`).

**Type-level conversion is a bubble.** In the context `A : ∗, a : A`, the
judgment `a : (λ X : ∗. X) A` holds at the top vertex with the type-level beta
bubble (`redex_typed_with_typeBeta`) and holds at no vertex in the weak core
(`redex_not_in_weak_core`). No vertex reaches it without the bubble
(`no_vertex_simulates_conversion`).

**Where a bubble is visible.** Any derivation of that judgment, under any
bubble, needs a product rule over kinds (`redex_needs_kind_products`): at the
simply typed vertex and at the dependent vertex `λP` no bubble changes it
(`redex_invisible_without_kind_products`), while at `λω̲` the type-level beta
bubble does (`typeBeta_visible_at_typeOperators`). The term-level beta bubble behaves the same
way on the dependent face: `t : P ((λ x : A. x) a)` needs a product into
kinds under any bubble, so no bubble changes it at `λ→` or `λ2`
(`familyRedex_invisible_without_families`), while at `λP` the bubble does
(`termBeta_visible_at_dependent`). In general a bubble is invisible at a vertex
whose weak-core types avoid its steps (`invisible_of_rigid`).

**The top vertex is consistent, a universal sort is not.** At every vertex
and under every bubble whose steps are beta steps, no closed term has the type
`Π p : ∗. p` (`vertex_consistent`); the proof is the proof-irrelevant model of
the calculus of constructions (`ConstructionsModel.constructions_consistent`).
Replacing `∗ : □` by `∗ : ∗` makes that type inhabited under every bubble
containing beta (`universalTop_inconsistent`).

So the hypercube is not a family of bubbles: its vertices differ in formation,
bubbles in conversion. A kernel is a pair, and the weakness order of bubbles
(fewer conversions, more models) acts within each vertex.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.HypercubeBubbles

open Mettapedia.GSLT.Dedukti
open Mettapedia.GSLT.LanguageDef.LF (Srt)
open Mettapedia.GSLT.LanguageDef.LFProfile (Profile ProductRule)

/-! ## Typing with a conversion parameter -/

/-- The sorted pure type system with its conversion relation as a parameter. -/
inductive TypedUnder (profile : Profile) (conversion : PTerm → PTerm → Prop) :
    SortedCtx → Judgment → Prop where
  | sort {context : SortedCtx} {source target : Srt} :
      profile.sortAxiom source = some target →
      TypedUnder profile conversion context (.type (.sort source) target)
  | pi {context : SortedCtx} {domain body : PTerm} {domainSort codomainSort resultSort : Srt} :
      TypedUnder profile conversion context (.type domain domainSort) →
      TypedUnder profile conversion ((domain, domainSort) :: context) (.type body codomainSort) →
      (⟨domainSort, codomainSort, resultSort⟩ : ProductRule) ∈ profile.products →
      TypedUnder profile conversion context
        (.type (.pi ⟨domainSort, codomainSort, resultSort⟩ domain body) resultSort)
  | ofTerm {context : SortedCtx} {subject : PTerm} {sort above : Srt} :
      TypedUnder profile conversion context (.term subject (.sort sort) above) →
      profile.sortAxiom sort = some above →
      TypedUnder profile conversion context (.type subject sort)
  | toTerm {context : SortedCtx} {subject : PTerm} {sort above : Srt} :
      TypedUnder profile conversion context (.type subject sort) →
      profile.sortAxiom sort = some above →
      TypedUnder profile conversion context (.term subject (.sort sort) above)
  | var {context : SortedCtx} {index : Nat} {type : PTerm} {sort : Srt} :
      lookupSorted context index = some (type, sort) →
      TypedUnder profile conversion context (.term (.var index) type sort)
  | lam {context : SortedCtx} {domain body bodyType : PTerm}
      {domainSort codomainSort resultSort : Srt} :
      TypedUnder profile conversion context (.type domain domainSort) →
      TypedUnder profile conversion ((domain, domainSort) :: context) (.type bodyType codomainSort) →
      (⟨domainSort, codomainSort, resultSort⟩ : ProductRule) ∈ profile.products →
      TypedUnder profile conversion ((domain, domainSort) :: context)
        (.term body bodyType codomainSort) →
      TypedUnder profile conversion context
        (.term (.lam domainSort domain body)
          (.pi ⟨domainSort, codomainSort, resultSort⟩ domain bodyType) resultSort)
  | app {context : SortedCtx} {function argument domain bodyType : PTerm}
      {domainSort codomainSort resultSort : Srt} :
      TypedUnder profile conversion context (.type domain domainSort) →
      TypedUnder profile conversion ((domain, domainSort) :: context) (.type bodyType codomainSort) →
      (⟨domainSort, codomainSort, resultSort⟩ : ProductRule) ∈ profile.products →
      TypedUnder profile conversion context
        (.term function (.pi ⟨domainSort, codomainSort, resultSort⟩ domain bodyType) resultSort) →
      TypedUnder profile conversion context (.term argument domain domainSort) →
      TypedUnder profile conversion context
        (.term (.app function argument) (PTerm.subst0 argument bodyType) codomainSort)
  | conv {context : SortedCtx} {subject source target : PTerm} {sort : Srt} :
      TypedUnder profile conversion context (.term subject source sort) →
      conversion source target →
      TypedUnder profile conversion context (.type target sort) →
      TypedUnder profile conversion context (.term subject target sort)

/-- The pure type system is the conversion-parametric one at beta conversion. -/
theorem derives_iff_typedUnder {profile : Profile} {context : SortedCtx} {judgment : Judgment} :
    Derives profile context judgment ↔ TypedUnder profile PTerm.Conv context judgment := by
  constructor
  · intro derivation
    induction derivation with
    | sort axiomHolds => exact .sort axiomHolds
    | pi _ _ member ihDomain ihBody => exact .pi ihDomain ihBody member
    | ofTerm _ axiomHolds ih => exact .ofTerm ih axiomHolds
    | toTerm _ axiomHolds ih => exact .toTerm ih axiomHolds
    | var found => exact .var found
    | lam _ _ member _ ihDomain ihBodyType ihBody => exact .lam ihDomain ihBodyType member ihBody
    | app _ _ member _ _ ihDomain ihBodyType ihFunction ihArgument =>
        exact .app ihDomain ihBodyType member ihFunction ihArgument
    | conv _ convertible _ ihTerm ihTarget => exact .conv ihTerm convertible ihTarget
  · intro derivation
    induction derivation with
    | sort axiomHolds => exact .sort axiomHolds
    | pi _ _ member ihDomain ihBody => exact .pi ihDomain ihBody member
    | ofTerm _ axiomHolds ih => exact .ofTerm ih axiomHolds
    | toTerm _ axiomHolds ih => exact .toTerm ih axiomHolds
    | var found => exact .var found
    | lam _ _ member _ ihDomain ihBodyType ihBody => exact .lam ihDomain ihBodyType member ihBody
    | app _ _ member _ _ ihDomain ihBodyType ihFunction ihArgument =>
        exact .app ihDomain ihBodyType member ihFunction ihArgument
    | conv _ convertible _ ihTerm ihTarget => exact .conv ihTerm convertible ihTarget

/-- More product rules and more conversion derive more. -/
theorem TypedUnder.mono {small large : Profile} {conversion conversion' : PTerm → PTerm → Prop}
    (sameAxiom : small.sortAxiom = large.sortAxiom) (products : small.products ⊆ large.products)
    (convs : ∀ {source target : PTerm}, conversion source target → conversion' source target)
    {context : SortedCtx} {judgment : Judgment}
    (derivation : TypedUnder small conversion context judgment) :
    TypedUnder large conversion' context judgment := by
  induction derivation with
  | sort axiomHolds => exact .sort (sameAxiom ▸ axiomHolds)
  | pi _ _ member ihDomain ihBody => exact .pi ihDomain ihBody (products member)
  | ofTerm _ axiomHolds ih => exact .ofTerm ih (sameAxiom ▸ axiomHolds)
  | toTerm _ axiomHolds ih => exact .toTerm ih (sameAxiom ▸ axiomHolds)
  | var found => exact .var found
  | lam _ _ member _ ihDomain ihBodyType ihBody =>
      exact .lam ihDomain ihBodyType (products member) ihBody
  | app _ _ member _ _ ihDomain ihBodyType ihFunction ihArgument =>
      exact .app ihDomain ihBodyType (products member) ihFunction ihArgument
  | conv _ convertible _ ihTerm ihTarget => exact .conv ihTerm (convs convertible) ihTarget

/-- A context is well formed for a conversion-parametric profile when every
entry is a type over the preceding context.  Keeping this judgment beside
`TypedUnder` lets profile and bubble comparisons retain the same context
discipline. -/
inductive ContextFormedUnder
    (profile : Profile) (conversion : PTerm → PTerm → Prop) : SortedCtx → Prop where
  | nil : ContextFormedUnder profile conversion []
  | cons {context : SortedCtx} {type : PTerm} {sort : Srt} :
      ContextFormedUnder profile conversion context →
      TypedUnder profile conversion context (.type type sort) →
      ContextFormedUnder profile conversion ((type, sort) :: context)

/-- Context formation is monotone in both the product profile and the
conversion bubble. -/
theorem ContextFormedUnder.mono
    {small large : Profile} {conversion conversion' : PTerm → PTerm → Prop}
    (sameAxiom : small.sortAxiom = large.sortAxiom)
    (products : small.products ⊆ large.products)
    (conversions : ∀ {source target : PTerm}, conversion source target → conversion' source target)
    {context : SortedCtx}
    (formed : ContextFormedUnder small conversion context) :
    ContextFormedUnder large conversion' context := by
  induction formed with
  | nil => exact .nil
  | cons _ entryTyped ih =>
      exact .cons ih (entryTyped.mono sameAxiom products conversions)

/-- A product annotation that is a derivation's subject is a rule of the
system, under any conversion. -/
theorem TypedUnder.pi_rule_mem {profile : Profile} {conversion : PTerm → PTerm → Prop}
    {context : SortedCtx} {judgment : Judgment}
    (derivation : TypedUnder profile conversion context judgment) :
    ∀ {rule : ProductRule} {domain body : PTerm}, judgment.subject = .pi rule domain body →
      rule ∈ profile.products := by
  induction derivation with
  | sort _ => intro rule domain body same; cases same
  | pi _ _ member _ _ => intro rule domain body same; cases same; exact member
  | ofTerm _ _ ih => exact ih
  | toTerm _ _ ih => exact ih
  | var _ => intro rule domain body same; cases same
  | lam _ _ _ _ _ _ _ => intro rule domain body same; cases same
  | app _ _ _ _ _ _ _ _ _ => intro rule domain body same; cases same
  | conv _ _ _ ihTerm _ => exact ihTerm

/-- An abstraction that is a derivation's subject has a product rule over its
domain sort, under any conversion. -/
theorem TypedUnder.lam_rule_mem {profile : Profile} {conversion : PTerm → PTerm → Prop}
    {context : SortedCtx} {judgment : Judgment}
    (derivation : TypedUnder profile conversion context judgment) :
    ∀ {level : Srt} {domain body : PTerm}, judgment.subject = .lam level domain body →
      ∃ codomain result, (⟨level, codomain, result⟩ : ProductRule) ∈ profile.products := by
  induction derivation with
  | sort _ => intro level domain body same; cases same
  | pi _ _ _ _ _ => intro level domain body same; cases same
  | ofTerm _ _ ih => exact ih
  | toTerm _ _ ih => exact ih
  | var _ => intro level domain body same; cases same
  | lam _ _ member _ _ _ _ => intro level domain body same; cases same; exact ⟨_, _, member⟩
  | app _ _ _ _ _ _ _ _ _ => intro level domain body same; cases same
  | conv _ _ _ ihTerm _ => exact ihTerm

/-- An application that is a derivation's subject has its function typed. -/
theorem TypedUnder.app_function {profile : Profile} {conversion : PTerm → PTerm → Prop}
    {context : SortedCtx} {judgment : Judgment}
    (derivation : TypedUnder profile conversion context judgment) :
    ∀ {function argument : PTerm}, judgment.subject = .app function argument →
      ∃ context' judgment', TypedUnder profile conversion context' judgment' ∧
        judgment'.subject = function := by
  induction derivation with
  | sort _ => intro function argument same; cases same
  | pi _ _ _ _ _ => intro function argument same; cases same
  | ofTerm _ _ ih => exact ih
  | toTerm _ _ ih => exact ih
  | var _ => intro function argument same; cases same
  | lam _ _ _ _ _ _ _ => intro function argument same; cases same
  | app _ _ _ functionTyped _ _ _ _ _ =>
      intro function argument same
      cases same
      exact ⟨_, _, functionTyped, rfl⟩
  | conv _ _ _ ihTerm _ => exact ihTerm

/-! ## Bubbles on annotated terms -/

/-- Declared steps, closed under every term former. -/
inductive Congruence (steps : PTerm → PTerm → Prop) : PTerm → PTerm → Prop where
  | root {source target : PTerm} : steps source target → Congruence steps source target
  | piDomain {rule : ProductRule} {domain domain' body : PTerm} :
      Congruence steps domain domain' → Congruence steps (.pi rule domain body) (.pi rule domain' body)
  | piBody {rule : ProductRule} {domain body body' : PTerm} :
      Congruence steps body body' → Congruence steps (.pi rule domain body) (.pi rule domain body')
  | lamDomain {level : Srt} {domain domain' body : PTerm} :
      Congruence steps domain domain' → Congruence steps (.lam level domain body) (.lam level domain' body)
  | lamBody {level : Srt} {domain body body' : PTerm} :
      Congruence steps body body' → Congruence steps (.lam level domain body) (.lam level domain body')
  | appFunction {function function' argument : PTerm} :
      Congruence steps function function' →
        Congruence steps (.app function argument) (.app function' argument)
  | appArgument {function argument argument' : PTerm} :
      Congruence steps argument argument' →
        Congruence steps (.app function argument) (.app function argument')

/-- The definitional equality of a bubble. -/
def bubbleConv (steps : PTerm → PTerm → Prop) : PTerm → PTerm → Prop :=
  Relation.EqvGen (Congruence steps)

/-- Beta steps at the root. -/
def betaRoot (source target : PTerm) : Prop :=
  ∃ level domain body argument,
    source = .app (.lam level domain body) argument ∧ target = PTerm.subst0 argument body

theorem congruence_betaRoot_iff {source target : PTerm} :
    Congruence betaRoot source target ↔ PTerm.Step source target := by
  constructor
  · intro step
    induction step with
    | root holds =>
        obtain ⟨level, domain, body, argument, rfl, rfl⟩ := holds
        exact .beta level domain body argument
    | piDomain _ ih => exact .piDomain ih
    | piBody _ ih => exact .piBody ih
    | lamDomain _ ih => exact .lamDomain ih
    | lamBody _ ih => exact .lamBody ih
    | appFunction _ ih => exact .appFunction ih
    | appArgument _ ih => exact .appArgument ih
  · intro step
    induction step with
    | beta level domain body argument => exact .root ⟨level, domain, body, argument, rfl, rfl⟩
    | piDomain _ ih => exact .piDomain ih
    | piBody _ ih => exact .piBody ih
    | lamDomain _ ih => exact .lamDomain ih
    | lamBody _ ih => exact .lamBody ih
    | appFunction _ ih => exact .appFunction ih
    | appArgument _ ih => exact .appArgument ih

/-- **Beta conversion is the bubble of the beta steps.** -/
theorem bubbleConv_betaRoot : bubbleConv betaRoot = PTerm.Conv := by
  funext source target
  apply propext
  constructor
  · intro converted
    induction converted with
    | rel _ _ step => exact .rel _ _ (congruence_betaRoot_iff.mp step)
    | refl => exact .refl _
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ ihFirst ihSecond => exact .trans _ _ _ ihFirst ihSecond
  · intro converted
    induction converted with
    | rel _ _ step => exact .rel _ _ (congruence_betaRoot_iff.mpr step)
    | refl => exact .refl _
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ ihFirst ihSecond => exact .trans _ _ _ ihFirst ihSecond

/-- The weak core declares no step. -/
def noSteps (_ _ : PTerm) : Prop := False

theorem congruence_noSteps {source target : PTerm} : ¬ Congruence noSteps source target := by
  intro step
  induction step with
  | root holds => exact holds
  | piDomain _ ih => exact ih
  | piBody _ ih => exact ih
  | lamDomain _ ih => exact ih
  | lamBody _ ih => exact ih
  | appFunction _ ih => exact ih
  | appArgument _ ih => exact ih

/-- The weak core converts nothing. -/
theorem bubbleConv_noSteps_iff {source target : PTerm} : bubbleConv noSteps source target ↔ source = target := by
  constructor
  · intro converted
    induction converted with
    | rel _ _ step => exact absurd step congruence_noSteps
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond
  · rintro rfl
    exact .refl _

theorem congruence_mono {small large : PTerm → PTerm → Prop}
    (steps : ∀ {source target : PTerm}, small source target → large source target)
    {source target : PTerm} (step : Congruence small source target) : Congruence large source target := by
  induction step with
  | root holds => exact .root (steps holds)
  | piDomain _ ih => exact .piDomain ih
  | piBody _ ih => exact .piBody ih
  | lamDomain _ ih => exact .lamDomain ih
  | lamBody _ ih => exact .lamBody ih
  | appFunction _ ih => exact .appFunction ih
  | appArgument _ ih => exact .appArgument ih

theorem bubbleConv_mono {small large : PTerm → PTerm → Prop}
    (steps : ∀ {source target : PTerm}, small source target → large source target)
    {source target : PTerm} (converted : bubbleConv small source target) :
    bubbleConv large source target := by
  induction converted with
  | rel _ _ step => exact .rel _ _ (congruence_mono steps step)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ihFirst ihSecond => exact .trans _ _ _ ihFirst ihSecond

/-- Beta at a type-level abstraction: the domain is a kind. -/
def typeBeta (source target : PTerm) : Prop :=
  ∃ domain body argument,
    source = .app (.lam .kind domain body) argument ∧ target = PTerm.subst0 argument body

theorem typeBeta_le_betaRoot {source target : PTerm} (step : typeBeta source target) :
    betaRoot source target := by
  obtain ⟨domain, body, argument, rfl, rfl⟩ := step
  exact ⟨.kind, domain, body, argument, rfl, rfl⟩

/-- Beta at a term-level abstraction: the domain is a type. -/
def termBeta (source target : PTerm) : Prop :=
  ∃ domain body argument,
    source = .app (.lam .type domain body) argument ∧ target = PTerm.subst0 argument body

theorem termBeta_le_betaRoot {source target : PTerm} (step : termBeta source target) :
    betaRoot source target := by
  obtain ⟨domain, body, argument, rfl, rfl⟩ := step
  exact ⟨.type, domain, body, argument, rfl, rfl⟩

/-! ## The kernel at a vertex with a bubble -/

/-- The profile of a vertex: the products it licenses. -/
def vertex (products : List ProductRule) : Profile := ⟨Mettapedia.GSLT.LanguageDef.LFProfile.typeAxiom, products⟩

/-- The kernel at a vertex with a bubble. -/
abbrev Kernel (products : List ProductRule) (steps : PTerm → PTerm → Prop) :
    SortedCtx → Judgment → Prop :=
  TypedUnder (vertex products) (bubbleConv steps)

/-- The kernel grows with the vertex and with the bubble. -/
theorem Kernel.mono {products products' : List ProductRule} {steps steps' : PTerm → PTerm → Prop}
    (moreProducts : products ⊆ products')
    (moreSteps : ∀ {source target : PTerm}, steps source target → steps' source target)
    {context : SortedCtx} {judgment : Judgment} (derivation : Kernel products steps context judgment) :
    Kernel products' steps' context judgment :=
  TypedUnder.mono (small := vertex products) (large := vertex products') rfl moreProducts
    (fun converted => bubbleConv_mono moreSteps converted) derivation

/-- The pure type system at a vertex is the kernel with the beta bubble. -/
theorem derives_iff_kernel_beta (products : List ProductRule) {context : SortedCtx}
    {judgment : Judgment} :
    Derives (vertex products) context judgment ↔ Kernel products betaRoot context judgment := by
  rw [derives_iff_typedUnder, Kernel, bubbleConv_betaRoot]

/-- The simply typed vertex. -/
def simplyTypedProducts : List ProductRule := [Mettapedia.GSLT.LanguageDef.LFProfile.typeTypeType]

/-- The dependent vertex `λP`. -/
def dependentProducts : List ProductRule :=
  [Mettapedia.GSLT.LanguageDef.LFProfile.typeTypeType, Mettapedia.GSLT.LanguageDef.LFProfile.typeKindKind]

/-- The polymorphic vertex `λ2`. -/
def polymorphicProducts : List ProductRule :=
  [Mettapedia.GSLT.LanguageDef.LFProfile.typeTypeType, kindTypeType]

/-- The type-operator vertex `λω̲`. -/
def operatorProducts : List ProductRule :=
  [Mettapedia.GSLT.LanguageDef.LFProfile.typeTypeType, Mettapedia.GSLT.LanguageDef.LFProfile.kindKindKind]

/-- The top vertex, the calculus of constructions. -/
def constructionProducts : List ProductRule := constructions.products

/-! ## Direct value-indexed Curry--Howard needs the dependent vertex

The context below uses one and the same term-level carrier `A` both for
ordinary values and as the domain of the type family `P`.  It therefore
captures direct value indexing: there is no reified copy of values at another
level.  The exact characterization is independent of the conversion bubble.
-/

/-- `A : Type, P : A → Type`.  Context entries are written innermost first. -/
def directPredicateContext : SortedCtx :=
  [(.pi Mettapedia.GSLT.LanguageDef.LFProfile.typeKindKind
      (.var 0) (.sort .type), .kind),
    (.sort .type, .kind)]

/-- The direct Curry--Howard proposition `Π x : A, P x`. -/
def directForall : PTerm :=
  .pi Mettapedia.GSLT.LanguageDef.LFProfile.typeTypeType
    (.var 1) (.app (.var 1) (.var 0))

/-- The direct value-indexed universal is available when both its context and
its proposition type are well formed. -/
def DirectValueIndexedForall
    (products : List ProductRule) (steps : PTerm → PTerm → Prop) : Prop :=
  ContextFormedUnder (vertex products) (bubbleConv steps) directPredicateContext ∧
    Kernel products steps directPredicateContext (.type directForall .type)

/-- The predicate context is well formed whenever the value-to-type product
rule is licensed. -/
theorem directPredicateContext_formed (products : List ProductRule)
    (steps : PTerm → PTerm → Prop)
    (dependent : Mettapedia.GSLT.LanguageDef.LFProfile.typeKindKind ∈ products) :
    ContextFormedUnder (vertex products) (bubbleConv steps) directPredicateContext := by
  apply ContextFormedUnder.cons
  · exact .cons .nil (.sort rfl)
  · exact .pi (.ofTerm (.var rfl) rfl) (.sort rfl) dependent

/-- Conversely, no conversion policy can make the direct predicate context
well formed without licensing the value-to-type product rule. -/
theorem directPredicateContext_needs_dependency
    (products : List ProductRule) (steps : PTerm → PTerm → Prop)
    (formed : ContextFormedUnder (vertex products) (bubbleConv steps)
      directPredicateContext) :
    Mettapedia.GSLT.LanguageDef.LFProfile.typeKindKind ∈ products := by
  cases formed with
  | cons _ predicateType =>
      exact predicateType.pi_rule_mem rfl

/-- Exact syntactic boundary: direct value-indexed predicates are available
exactly at profiles containing the dependent product rule, independently of
their conversion bubble. -/
theorem directPredicateContext_formed_iff
    (products : List ProductRule) (steps : PTerm → PTerm → Prop) :
    ContextFormedUnder (vertex products) (bubbleConv steps) directPredicateContext ↔
      Mettapedia.GSLT.LanguageDef.LFProfile.typeKindKind ∈ products :=
  ⟨directPredicateContext_needs_dependency products steps,
    directPredicateContext_formed products steps⟩

/-- The body `P x` is a type over the actual value `x : A`. -/
theorem directPredicateBody_formed (products : List ProductRule)
    (steps : PTerm → PTerm → Prop)
    (dependent : Mettapedia.GSLT.LanguageDef.LFProfile.typeKindKind ∈ products) :
    Kernel products steps ((.var 1, .type) :: directPredicateContext)
      (.type (.app (.var 1) (.var 0)) .type) := by
  have familyDomainFormed : Kernel products steps
      ((.var 1, .type) :: directPredicateContext) (.type (.var 2) .type) :=
    .ofTerm (.var rfl) rfl
  have familyBodyFormed : Kernel products steps
      ((.var 2, .type) :: (.var 1, .type) :: directPredicateContext)
      (.type (.sort .type) .kind) :=
    .sort rfl
  have family : Kernel products steps
      ((.var 1, .type) :: directPredicateContext)
      (.term (.var 1)
        (.pi Mettapedia.GSLT.LanguageDef.LFProfile.typeKindKind
          (.var 2) (.sort .type)) .kind) :=
    .var rfl
  have argument : Kernel products steps
      ((.var 1, .type) :: directPredicateContext)
      (.term (.var 0) (.var 2) .type) :=
    .var rfl
  have familyApplied : Kernel products steps
      ((.var 1, .type) :: directPredicateContext)
      (.term (.app (.var 1) (.var 0)) (.sort .type) .kind) :=
    .app familyDomainFormed familyBodyFormed dependent family argument
  exact .ofTerm familyApplied rfl

/-- Once ordinary functions and value-indexed families are both licensed,
the direct Curry--Howard universal is a type. -/
theorem directForall_formed (products : List ProductRule)
    (steps : PTerm → PTerm → Prop)
    (simple : Mettapedia.GSLT.LanguageDef.LFProfile.typeTypeType ∈ products)
    (dependent : Mettapedia.GSLT.LanguageDef.LFProfile.typeKindKind ∈ products) :
    Kernel products steps directPredicateContext (.type directForall .type) :=
  .pi (.ofTerm (.var rfl) rfl)
    (directPredicateBody_formed products steps dependent) simple

/-- Abstraction produces the direct universal from evidence over the same
value variable, without a reified index or a conversion step. -/
theorem directForall_abstract (products : List ProductRule)
    (steps : PTerm → PTerm → Prop)
    (simple : Mettapedia.GSLT.LanguageDef.LFProfile.typeTypeType ∈ products)
    (dependent : Mettapedia.GSLT.LanguageDef.LFProfile.typeKindKind ∈ products)
    {body : PTerm}
    (bodyTyped : Kernel products steps ((.var 1, .type) :: directPredicateContext)
      (.term body (.app (.var 1) (.var 0)) .type)) :
    Kernel products steps directPredicateContext
      (.term (.lam .type (.var 1) body) directForall .type) :=
  .lam (.ofTerm (.var rfl) rfl)
    (directPredicateBody_formed products steps dependent) simple bodyTyped

/-- Application substitutes the actual argument into the evidence type.
The conclusion is `P argument`, with the same argument used in execution. -/
theorem directForall_apply (products : List ProductRule)
    (steps : PTerm → PTerm → Prop)
    (simple : Mettapedia.GSLT.LanguageDef.LFProfile.typeTypeType ∈ products)
    (dependent : Mettapedia.GSLT.LanguageDef.LFProfile.typeKindKind ∈ products)
    {function argument : PTerm}
    (functionTyped : Kernel products steps directPredicateContext
      (.term function directForall .type))
    (argumentTyped : Kernel products steps directPredicateContext
      (.term argument (.var 1) .type)) :
    Kernel products steps directPredicateContext
      (.term (.app function argument) (.app (.var 0) argument) .type) :=
  .app (.ofTerm (.var rfl) rfl)
    (directPredicateBody_formed products steps dependent) simple functionTyped argumentTyped

/-- The least formation basis for this direct interface consists of ordinary
functions and value-indexed families. Neither rule is assumed in advance. -/
theorem directValueIndexedForall_iff_contains_dependentProducts
    (products : List ProductRule) (steps : PTerm → PTerm → Prop) :
    DirectValueIndexedForall products steps ↔ dependentProducts ⊆ products := by
  constructor
  · intro available rule required
    rcases List.mem_cons.mp required with rfl | required
    · exact available.2.pi_rule_mem rfl
    · rcases List.mem_cons.mp required with rfl | impossible
      · exact directPredicateContext_needs_dependency products steps available.1
      · cases impossible
  · intro contains
    have simple := contains (by decide :
      Mettapedia.GSLT.LanguageDef.LFProfile.typeTypeType ∈ dependentProducts)
    have dependent := contains (by decide :
      Mettapedia.GSLT.LanguageDef.LFProfile.typeKindKind ∈ dependentProducts)
    exact ⟨directPredicateContext_formed products steps dependent,
      directForall_formed products steps simple dependent⟩

/-- Formation of this interface is unchanged by replacing the conversion
bubble, even when the two bubbles are not comparable. -/
theorem directValueIndexedForall_bubble_iff (products : List ProductRule)
    (first second : PTerm → PTerm → Prop) :
    DirectValueIndexedForall products first ↔ DirectValueIndexedForall products second := by
  rw [directValueIndexedForall_iff_contains_dependentProducts,
    directValueIndexedForall_iff_contains_dependentProducts]

/-- The dependent vertex supplies the interface under every bubble, and
every supplying profile contains its product rules. -/
theorem dependentProducts_least_directInterface (steps : PTerm → PTerm → Prop) :
    DirectValueIndexedForall dependentProducts steps ∧
      ∀ products, DirectValueIndexedForall products steps → dependentProducts ⊆ products :=
  ⟨(directValueIndexedForall_iff_contains_dependentProducts _ _).2 (fun _ member => member),
    fun products => (directValueIndexedForall_iff_contains_dependentProducts products steps).1⟩

/-- Under the ordinary function rule, direct value-indexed Curry--Howard is
available exactly when the dependent product rule is present. -/
theorem directValueIndexedForall_iff
    (products : List ProductRule) (steps : PTerm → PTerm → Prop)
    (simple : Mettapedia.GSLT.LanguageDef.LFProfile.typeTypeType ∈ products) :
    DirectValueIndexedForall products steps ↔
      Mettapedia.GSLT.LanguageDef.LFProfile.typeKindKind ∈ products := by
  constructor
  · exact fun available =>
      directPredicateContext_needs_dependency products steps available.1
  · intro dependent
    exact ⟨directPredicateContext_formed products steps dependent,
      directForall_formed products steps simple dependent⟩

/-- Positive control: the dependent vertex supports direct value-indexed
Curry--Howard even in the weak conversion core. -/
theorem directValueIndexedForall_at_dependent :
    DirectValueIndexedForall dependentProducts noSteps :=
  (directValueIndexedForall_iff dependentProducts noSteps (by decide)).2 (by decide)

/-- Negative controls: neither simple functions, polymorphism nor type
operators substitute for direct value dependency, under any bubble. -/
theorem directValueIndexedForall_absent_off_dependent_face
    (steps : PTerm → PTerm → Prop) :
    ¬ DirectValueIndexedForall simplyTypedProducts steps ∧
      ¬ DirectValueIndexedForall polymorphicProducts steps ∧
      ¬ DirectValueIndexedForall operatorProducts steps := by
  constructor
  · rw [directValueIndexedForall_iff _ _ (by decide)]
    decide
  constructor
  · rw [directValueIndexedForall_iff _ _ (by decide)]
    decide
  · rw [directValueIndexedForall_iff _ _ (by decide)]
    decide

/-! ## Polymorphism is a vertex -/

/-- The polymorphic identity type is formed at every profile that licenses
ordinary functions and polymorphic products. -/
theorem polymorphicIdentityType_formed (products : List ProductRule)
    (steps : PTerm → PTerm → Prop)
    (simple : Mettapedia.GSLT.LanguageDef.LFProfile.typeTypeType ∈ products)
    (polymorphic : kindTypeType ∈ products) :
    Kernel products steps [] (.type Example.polymorphicIdentityType .type) := by
  have variableType : Kernel products steps [(.sort .type, .kind)]
      (.type (.var 0) .type) := .ofTerm (.var rfl) rfl
  have outerType : Kernel products steps [(.var 0, .type), (.sort .type, .kind)]
      (.type (.var 1) .type) := .ofTerm (.var rfl) rfl
  exact .pi (.sort rfl) (.pi variableType outerType simple) polymorphic

/-- The same two product rules type the actual polymorphic identity program;
the formation result is not just an uninhabited interface. -/
theorem polymorphicIdentity_typed (products : List ProductRule)
    (steps : PTerm → PTerm → Prop)
    (simple : Mettapedia.GSLT.LanguageDef.LFProfile.typeTypeType ∈ products)
    (polymorphic : kindTypeType ∈ products) :
    Kernel products steps []
      (.term Example.polymorphicIdentity Example.polymorphicIdentityType .type) := by
  have variableType : Kernel products steps [(.sort .type, .kind)]
      (.type (.var 0) .type) := .ofTerm (.var rfl) rfl
  have outerType : Kernel products steps [(.var 0, .type), (.sort .type, .kind)]
      (.type (.var 1) .type) := .ofTerm (.var rfl) rfl
  exact .lam (.sort rfl) (.pi variableType outerType simple) polymorphic
    (.lam variableType outerType simple (.var rfl))

/-- **No bubble types the polymorphic identity's type at the simply typed vertex.** -/
theorem polymorphism_needs_vertex (steps : PTerm → PTerm → Prop) (context : SortedCtx) (sort : Srt) :
    ¬ Kernel simplyTypedProducts steps context (.type Example.polymorphicIdentityType sort) := by
  intro derivation
  have member := derivation.pi_rule_mem (rule := kindTypeType) rfl
  revert member
  decide

/-- **The weak core at the top vertex types the polymorphic identity.** -/
theorem polymorphism_in_weak_core :
    Kernel constructionProducts noSteps []
      (.term Example.polymorphicIdentity Example.polymorphicIdentityType .type) :=
  polymorphicIdentity_typed _ _ (by decide) (by decide)

/-- **No bubble added to the simply typed vertex reaches the weak core at the top.** -/
theorem no_bubble_simulates_polymorphism (steps : PTerm → PTerm → Prop) :
    ¬ ∀ context judgment, Kernel constructionProducts noSteps context judgment →
      Kernel simplyTypedProducts steps context judgment := by
  intro simulate
  have formed := polymorphicIdentityType_formed constructionProducts noSteps (by decide) (by decide)
  exact polymorphism_needs_vertex steps [] .type (simulate _ _ formed)

/-! ## A least formation basis relative to three direct interfaces

These interfaces require actual typings in the existing annotated syntax.
Their least product set is the four-rule formation profile of the calculus of
constructions. This does not characterize arbitrary encodings of logic or
identify every conversion policy at that vertex with ordinary CoC.
-/

/-- The kind `Type → Type`, using a type as a parameter of a type operator. -/
def typeOperatorKind : PTerm :=
  .pi Mettapedia.GSLT.LanguageDef.LFProfile.kindKindKind (.sort .type) (.sort .type)

theorem typeOperatorKind_formed (products : List ProductRule)
    (steps : PTerm → PTerm → Prop)
    (operators : Mettapedia.GSLT.LanguageDef.LFProfile.kindKindKind ∈ products) :
    Kernel products steps [] (.type typeOperatorKind .kind) :=
  .pi (.sort rfl) (.sort rfl) operators

/-- The direct value-indexed universal, the polymorphic identity type and
the kind of unary type operators, all in their stated contexts. -/
def DirectFormationInterfaces
    (products : List ProductRule) (steps : PTerm → PTerm → Prop) : Prop :=
  DirectValueIndexedForall products steps ∧
    Kernel products steps [] (.type Example.polymorphicIdentityType .type) ∧
    Kernel products steps [] (.type typeOperatorKind .kind)

/-- Exactly the four CoC formation rules are required by these three direct
interfaces, independently of the conversion bubble. -/
theorem directFormationInterfaces_iff_contains_constructionProducts
    (products : List ProductRule) (steps : PTerm → PTerm → Prop) :
    DirectFormationInterfaces products steps ↔ constructionProducts ⊆ products := by
  constructor
  · rintro ⟨direct, polymorphic, operators⟩ rule required
    rcases List.mem_cons.mp required with rfl | required
    · exact direct.2.pi_rule_mem rfl
    · rcases List.mem_cons.mp required with rfl | required
      · exact directPredicateContext_needs_dependency products steps direct.1
      · rcases List.mem_cons.mp required with rfl | required
        · exact polymorphic.pi_rule_mem rfl
        · rcases List.mem_cons.mp required with rfl | impossible
          · exact operators.pi_rule_mem rfl
          · cases impossible
  · intro contains
    have simple := contains (by decide :
      Mettapedia.GSLT.LanguageDef.LFProfile.typeTypeType ∈ constructionProducts)
    have dependent := contains (by decide :
      Mettapedia.GSLT.LanguageDef.LFProfile.typeKindKind ∈ constructionProducts)
    have polymorphic := contains (by decide : kindTypeType ∈ constructionProducts)
    have operators := contains (by decide :
      Mettapedia.GSLT.LanguageDef.LFProfile.kindKindKind ∈ constructionProducts)
    exact ⟨(directValueIndexedForall_iff products steps simple).2 dependent,
      polymorphicIdentityType_formed products steps simple polymorphic,
      typeOperatorKind_formed products steps operators⟩

/-- The four-rule vertex is a least formation basis for the stated
interfaces, rather than a least theory for every representation of them. -/
theorem constructionProducts_least_directInterfaces (steps : PTerm → PTerm → Prop) :
    DirectFormationInterfaces constructionProducts steps ∧
      ∀ products, DirectFormationInterfaces products steps → constructionProducts ⊆ products :=
  ⟨(directFormationInterfaces_iff_contains_constructionProducts _ _).2
      (fun _ member => member),
    fun products => (directFormationInterfaces_iff_contains_constructionProducts products steps).1⟩

/-- Deleting any one of the four formation rules defeats at least one of
the three interfaces, even if arbitrary conversions remain available. -/
theorem directInterfaces_refused_of_missing_rule
    (products : List ProductRule) (steps : PTerm → PTerm → Prop)
    {rule : ProductRule} (required : rule ∈ constructionProducts) (missing : rule ∉ products) :
    ¬ DirectFormationInterfaces products steps := by
  intro interfaces
  exact missing ((directFormationInterfaces_iff_contains_constructionProducts products steps).1
    interfaces required)

/-! ## Type-level conversion is a bubble -/

/-- `A : ∗, a : A`. -/
def redexContext : SortedCtx := [(.var 0, .type), (.sort .type, .kind)]

/-- `(λ X : ∗. X) A`. -/
def typeRedex : PTerm := .app (.lam .kind (.sort .type) (.var 0)) (.var 1)

theorem typeRedex_formed (products : List ProductRule) (steps : PTerm → PTerm → Prop)
    (operators : Mettapedia.GSLT.LanguageDef.LFProfile.kindKindKind ∈ products) :
    Kernel products steps redexContext (.type typeRedex .type) := by
  have universeFormed : Kernel products steps redexContext (.type (.sort .type) .kind) := .sort rfl
  have bodyFormed : Kernel products steps ((.sort .type, .kind) :: redexContext)
      (.type (.sort .type) .kind) := .sort rfl
  have identity : Kernel products steps redexContext
      (.term (.lam .kind (.sort .type) (.var 0))
        (.pi Mettapedia.GSLT.LanguageDef.LFProfile.kindKindKind (.sort .type) (.sort .type)) .kind) :=
    .lam universeFormed bodyFormed operators (.var rfl)
  have argument : Kernel products steps redexContext (.term (.var 1) (.sort .type) .kind) := .var rfl
  have applied : Kernel products steps redexContext (.term typeRedex (.sort .type) .kind) :=
    .app universeFormed bodyFormed operators identity argument
  exact .ofTerm applied rfl

/-- **With the type-level beta bubble, `a : (λ X : ∗. X) A` at any vertex with
type operators.** -/
theorem redex_typed_with_typeBeta (products : List ProductRule)
    (operators : Mettapedia.GSLT.LanguageDef.LFProfile.kindKindKind ∈ products) :
    Kernel products typeBeta redexContext (.term (.var 0) typeRedex .type) := by
  have declaredType : Kernel products typeBeta redexContext (.term (.var 0) (.var 1) .type) := .var rfl
  have converted : bubbleConv typeBeta (.var 1) typeRedex :=
    .symm _ _ (.rel _ _ (.root ⟨.sort .type, .var 0, .var 1, rfl, rfl⟩))
  exact .conv declaredType converted (typeRedex_formed products typeBeta operators)

/-- In the weak core a variable has its declared type, or a sort. -/
theorem weak_core_variable_type {products : List ProductRule} {context : SortedCtx}
    {judgment : Judgment} (derivation : Kernel products noSteps context judgment) :
    ∀ {index : Nat} {type : PTerm} {sort : Srt}, judgment = .term (.var index) type sort →
      (∃ declared, lookupSorted context index = some (type, declared)) ∨ ∃ level, type = .sort level := by
  induction derivation with
  | sort _ => intro index type sort same; cases same
  | pi _ _ _ _ _ => intro index type sort same; cases same
  | ofTerm _ _ _ => intro index type sort same; cases same
  | toTerm _ _ _ => intro index type sort same; cases same; exact Or.inr ⟨_, rfl⟩
  | var found => intro index type sort same; cases same; exact Or.inl ⟨_, found⟩
  | lam _ _ _ _ _ _ _ => intro index type sort same; cases same
  | app _ _ _ _ _ _ _ _ _ => intro index type sort same; cases same
  | conv _ convertible _ ihTerm _ =>
      intro index type sort same
      cases same
      rw [← bubbleConv_noSteps_iff.mp convertible]
      exact ihTerm rfl

/-- **At no vertex does the weak core type `a : (λ X : ∗. X) A`.** -/
theorem redex_not_in_weak_core (products : List ProductRule) :
    ¬ Kernel products noSteps redexContext (.term (.var 0) typeRedex .type) := by
  intro derivation
  rcases weak_core_variable_type derivation rfl with ⟨declared, found⟩ | ⟨level, same⟩
  · simp [lookupSorted, redexContext, PTerm.lift, typeRedex] at found
  · cases same

/-- **No vertex reaches the type-level beta bubble at the top without it.** -/
theorem no_vertex_simulates_conversion (products : List ProductRule) :
    ¬ ∀ context judgment, Kernel constructionProducts typeBeta context judgment →
      Kernel products noSteps context judgment := by
  intro simulate
  exact redex_not_in_weak_core products
    (simulate _ _ (redex_typed_with_typeBeta constructionProducts (by decide)))

/-! ## Where a bubble is visible -/

/-- Under any conversion, a variable has its declared type, a sort, or a type
that is itself formed. -/
theorem variable_type_formed {profile : Profile} {conversion : PTerm → PTerm → Prop}
    {context : SortedCtx} {judgment : Judgment}
    (derivation : TypedUnder profile conversion context judgment) :
    ∀ {index : Nat} {type : PTerm} {sort : Srt}, judgment = .term (.var index) type sort →
      (∃ declared, lookupSorted context index = some (type, declared)) ∨
        (∃ level, type = .sort level) ∨ TypedUnder profile conversion context (.type type sort) := by
  induction derivation with
  | sort _ => intro index type sort same; cases same
  | pi _ _ _ _ _ => intro index type sort same; cases same
  | ofTerm _ _ _ => intro index type sort same; cases same
  | toTerm _ _ _ => intro index type sort same; cases same; exact Or.inr (Or.inl ⟨_, rfl⟩)
  | var found => intro index type sort same; cases same; exact Or.inl ⟨_, found⟩
  | lam _ _ _ _ _ _ _ => intro index type sort same; cases same
  | app _ _ _ _ _ _ _ _ _ => intro index type sort same; cases same
  | conv _ _ targetFormed _ _ =>
      intro index type sort same
      cases same
      exact Or.inr (Or.inr targetFormed)

/-- **Typing `a : (λ X : ∗. X) A` needs a product over kinds**, under any bubble. -/
theorem redex_needs_kind_products (products : List ProductRule) (steps : PTerm → PTerm → Prop)
    (derivation : Kernel products steps redexContext (.term (.var 0) typeRedex .type)) :
    ∃ codomain result, (⟨.kind, codomain, result⟩ : ProductRule) ∈ products := by
  rcases variable_type_formed derivation rfl with ⟨declared, found⟩ | ⟨level, same⟩ | formed
  · simp [lookupSorted, redexContext, PTerm.lift, typeRedex] at found
  · cases same
  · obtain ⟨_, _, functionTyped, subject⟩ := formed.app_function rfl
    exact functionTyped.lam_rule_mem subject

/-- **At `λ→` and `λP` no bubble changes this judgment.** -/
theorem redex_invisible_without_kind_products (steps : PTerm → PTerm → Prop) :
    ¬ Kernel simplyTypedProducts steps redexContext (.term (.var 0) typeRedex .type) ∧
      ¬ Kernel dependentProducts steps redexContext (.term (.var 0) typeRedex .type) := by
  constructor
  · intro derivation
    obtain ⟨codomain, result, member⟩ := redex_needs_kind_products _ steps derivation
    simp [simplyTypedProducts, Mettapedia.GSLT.LanguageDef.LFProfile.typeTypeType] at member
  · intro derivation
    obtain ⟨codomain, result, member⟩ := redex_needs_kind_products _ steps derivation
    simp [dependentProducts, Mettapedia.GSLT.LanguageDef.LFProfile.typeTypeType,
      Mettapedia.GSLT.LanguageDef.LFProfile.typeKindKind] at member

/-- **At `λω̲` the type-level beta bubble changes it.** -/
theorem typeBeta_visible_at_typeOperators :
    Kernel operatorProducts typeBeta redexContext (.term (.var 0) typeRedex .type) ∧
      ¬ Kernel operatorProducts noSteps redexContext (.term (.var 0) typeRedex .type) :=
  ⟨redex_typed_with_typeBeta _ (by decide), redex_not_in_weak_core _⟩

/-! ## Term-level conversion is visible on the dependent face -/

/-- An application that is the subject of a term judgment of sort `s` needs a
product rule into `s`; as the subject of a type judgment of sort `s`, a
product rule into the sort above `s`. Under any conversion. -/
theorem TypedUnder.app_codomain {profile : Profile} {conversion : PTerm → PTerm → Prop}
    {context : SortedCtx} {judgment : Judgment}
    (derivation : TypedUnder profile conversion context judgment) :
    (∀ {function argument type : PTerm} {sort : Srt},
        judgment = .term (.app function argument) type sort →
        ∃ domain result, (⟨domain, sort, result⟩ : ProductRule) ∈ profile.products) ∧
    (∀ {function argument : PTerm} {sort : Srt},
        judgment = .type (.app function argument) sort →
        ∃ above domain result, profile.sortAxiom sort = some above ∧
          (⟨domain, above, result⟩ : ProductRule) ∈ profile.products) := by
  induction derivation with
  | sort _ => exact ⟨fun same => (by cases same), fun same => (by cases same)⟩
  | pi _ _ _ _ _ => exact ⟨fun same => (by cases same), fun same => (by cases same)⟩
  | ofTerm _ axiomHolds ih =>
      refine ⟨fun same => (by cases same), fun same => ?_⟩
      cases same
      obtain ⟨domain, result, member⟩ := ih.1 rfl
      exact ⟨_, domain, result, axiomHolds, member⟩
  | toTerm _ axiomHolds ih =>
      refine ⟨fun same => ?_, fun same => (by cases same)⟩
      cases same
      obtain ⟨above, domain, result, axiomHolds', member⟩ := ih.2 rfl
      rw [axiomHolds] at axiomHolds'
      cases axiomHolds'
      exact ⟨domain, result, member⟩
  | var _ => exact ⟨fun same => (by cases same), fun same => (by cases same)⟩
  | lam _ _ _ _ _ _ _ => exact ⟨fun same => (by cases same), fun same => (by cases same)⟩
  | app _ _ member _ _ _ _ _ _ =>
      refine ⟨fun same => ?_, fun same => (by cases same)⟩
      cases same
      exact ⟨_, _, member⟩
  | conv _ _ _ ihTerm _ =>
      refine ⟨fun same => ?_, fun same => (by cases same)⟩
      cases same
      exact ihTerm.1 rfl

/-- `A : ∗, P : Π x : A. ∗, a : A, t : P a`. -/
def familyContext : SortedCtx :=
  [(.app (.var 1) (.var 0), .type), (.var 1, .type),
    (.pi Mettapedia.GSLT.LanguageDef.LFProfile.typeKindKind (.var 0) (.sort .type), .kind),
    (.sort .type, .kind)]

/-- `P ((λ x : A. x) a)`. -/
def familyRedex : PTerm := .app (.var 2) (.app (.lam .type (.var 3) (.var 0)) (.var 1))

theorem familyRedex_formed (products : List ProductRule) (steps : PTerm → PTerm → Prop)
    (simple : Mettapedia.GSLT.LanguageDef.LFProfile.typeTypeType ∈ products)
    (dependent : Mettapedia.GSLT.LanguageDef.LFProfile.typeKindKind ∈ products) :
    Kernel products steps familyContext (.type familyRedex .type) := by
  have domainFormed : Kernel products steps familyContext (.type (.var 3) .type) :=
    .ofTerm (.var rfl) rfl
  have shiftedDomain : Kernel products steps ((.var 3, .type) :: familyContext) (.type (.var 4) .type) :=
    .ofTerm (.var rfl) rfl
  have identity : Kernel products steps familyContext
      (.term (.lam .type (.var 3) (.var 0))
        (.pi Mettapedia.GSLT.LanguageDef.LFProfile.typeTypeType (.var 3) (.var 4)) .type) :=
    .lam domainFormed shiftedDomain simple (.var rfl)
  have argument : Kernel products steps familyContext
      (.term (.app (.lam .type (.var 3) (.var 0)) (.var 1)) (.var 3) .type) :=
    .app domainFormed shiftedDomain simple identity (.var rfl)
  have family : Kernel products steps familyContext
      (.term (.var 2) (.pi Mettapedia.GSLT.LanguageDef.LFProfile.typeKindKind (.var 3) (.sort .type))
        .kind) := .var rfl
  have universeFormed : Kernel products steps ((.var 3, .type) :: familyContext)
      (.type (.sort .type) .kind) := .sort rfl
  have applied : Kernel products steps familyContext (.term familyRedex (.sort .type) .kind) :=
    .app domainFormed universeFormed dependent family argument
  exact .ofTerm applied rfl

/-- **With the term-level beta bubble, `t : P ((λ x : A. x) a)` at any vertex
with dependent types.** -/
theorem familyRedex_typed_with_termBeta (products : List ProductRule)
    (simple : Mettapedia.GSLT.LanguageDef.LFProfile.typeTypeType ∈ products)
    (dependent : Mettapedia.GSLT.LanguageDef.LFProfile.typeKindKind ∈ products) :
    Kernel products termBeta familyContext (.term (.var 0) familyRedex .type) := by
  have declaredType : Kernel products termBeta familyContext
      (.term (.var 0) (.app (.var 2) (.var 1)) .type) := .var rfl
  have converted : bubbleConv termBeta (.app (.var 2) (.var 1)) familyRedex :=
    .symm _ _ (.rel _ _ (.appArgument (.root ⟨.var 3, .var 0, .var 1, rfl, rfl⟩)))
  exact .conv declaredType converted (familyRedex_formed products termBeta simple dependent)

/-- At no vertex does the weak core type it. -/
theorem familyRedex_not_in_weak_core (products : List ProductRule) :
    ¬ Kernel products noSteps familyContext (.term (.var 0) familyRedex .type) := by
  intro derivation
  rcases weak_core_variable_type derivation rfl with ⟨declared, found⟩ | ⟨level, same⟩
  · simp [lookupSorted, familyContext, PTerm.lift, familyRedex] at found
  · cases same

/-- **Typing `t : P ((λ x : A. x) a)` needs a product into kinds**, under any bubble. -/
theorem familyRedex_needs_kind_codomain (products : List ProductRule) (steps : PTerm → PTerm → Prop)
    (derivation : Kernel products steps familyContext (.term (.var 0) familyRedex .type)) :
    ∃ domain result, (⟨domain, .kind, result⟩ : ProductRule) ∈ products := by
  rcases variable_type_formed derivation rfl with ⟨declared, found⟩ | ⟨level, same⟩ | formed
  · simp [lookupSorted, familyContext, PTerm.lift, familyRedex] at found
  · cases same
  · obtain ⟨above, domain, result, axiomHolds, member⟩ := (formed.app_codomain).2 rfl
    simp only [vertex, Mettapedia.GSLT.LanguageDef.LFProfile.typeAxiom, Option.some.injEq] at axiomHolds
    subst axiomHolds
    exact ⟨domain, result, member⟩

/-- **At `λ→` and `λ2` no bubble changes this judgment.** -/
theorem familyRedex_invisible_without_families (steps : PTerm → PTerm → Prop) :
    ¬ Kernel simplyTypedProducts steps familyContext (.term (.var 0) familyRedex .type) ∧
      ¬ Kernel polymorphicProducts steps familyContext (.term (.var 0) familyRedex .type) := by
  constructor
  · intro derivation
    obtain ⟨domain, result, member⟩ := familyRedex_needs_kind_codomain _ steps derivation
    simp [simplyTypedProducts, Mettapedia.GSLT.LanguageDef.LFProfile.typeTypeType] at member
  · intro derivation
    obtain ⟨domain, result, member⟩ := familyRedex_needs_kind_codomain _ steps derivation
    simp [polymorphicProducts, Mettapedia.GSLT.LanguageDef.LFProfile.typeTypeType,
      kindTypeType] at member

/-- **At `λP` the term-level beta bubble changes it.** -/
theorem termBeta_visible_at_dependent :
    Kernel dependentProducts termBeta familyContext (.term (.var 0) familyRedex .type) ∧
      ¬ Kernel dependentProducts noSteps familyContext (.term (.var 0) familyRedex .type) :=
  ⟨familyRedex_typed_with_termBeta _ (by decide) (by decide), familyRedex_not_in_weak_core _⟩

/-! ## Rigid types make a bubble invisible -/

/-- One term occurs in another. -/
inductive Occurs (inner : PTerm) : PTerm → Prop where
  | here : Occurs inner inner
  | piDomain {rule : ProductRule} {domain body : PTerm} : Occurs inner domain → Occurs inner (.pi rule domain body)
  | piBody {rule : ProductRule} {domain body : PTerm} : Occurs inner body → Occurs inner (.pi rule domain body)
  | lamDomain {level : Srt} {domain body : PTerm} : Occurs inner domain → Occurs inner (.lam level domain body)
  | lamBody {level : Srt} {domain body : PTerm} : Occurs inner body → Occurs inner (.lam level domain body)
  | appFunction {function argument : PTerm} : Occurs inner function → Occurs inner (.app function argument)
  | appArgument {function argument : PTerm} : Occurs inner argument → Occurs inner (.app function argument)

/-- No endpoint of a declared step occurs in the term. -/
def Rigid (steps : PTerm → PTerm → Prop) (term : PTerm) : Prop :=
  ∀ source target, steps source target → ¬ Occurs source term ∧ ¬ Occurs target term

/-- A congruence step has an endpoint of a declared step in each side. -/
theorem congruence_endpoints {steps : PTerm → PTerm → Prop} {source target : PTerm}
    (step : Congruence steps source target) :
    ∃ left right, steps left right ∧ Occurs left source ∧ Occurs right target := by
  induction step with
  | root holds => exact ⟨_, _, holds, .here, .here⟩
  | piDomain _ ih =>
      obtain ⟨left, right, holds, inSource, inTarget⟩ := ih
      exact ⟨left, right, holds, .piDomain inSource, .piDomain inTarget⟩
  | piBody _ ih =>
      obtain ⟨left, right, holds, inSource, inTarget⟩ := ih
      exact ⟨left, right, holds, .piBody inSource, .piBody inTarget⟩
  | lamDomain _ ih =>
      obtain ⟨left, right, holds, inSource, inTarget⟩ := ih
      exact ⟨left, right, holds, .lamDomain inSource, .lamDomain inTarget⟩
  | lamBody _ ih =>
      obtain ⟨left, right, holds, inSource, inTarget⟩ := ih
      exact ⟨left, right, holds, .lamBody inSource, .lamBody inTarget⟩
  | appFunction _ ih =>
      obtain ⟨left, right, holds, inSource, inTarget⟩ := ih
      exact ⟨left, right, holds, .appFunction inSource, .appFunction inTarget⟩
  | appArgument _ ih =>
      obtain ⟨left, right, holds, inSource, inTarget⟩ := ih
      exact ⟨left, right, holds, .appArgument inSource, .appArgument inTarget⟩

/-- A bubble converts a rigid term only to itself. -/
theorem bubbleConv_eq_of_rigid {steps : PTerm → PTerm → Prop} {source target : PTerm}
    (converted : bubbleConv steps source target) :
    (Rigid steps source → source = target) ∧ (Rigid steps target → source = target) := by
  induction converted with
  | rel first second step =>
      obtain ⟨left, right, holds, inFirst, inSecond⟩ := congruence_endpoints step
      exact ⟨fun rigid => absurd inFirst (rigid left right holds).1,
        fun rigid => absurd inSecond (rigid left right holds).2⟩
  | refl => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | symm _ _ _ ih => exact ⟨fun rigid => (ih.2 rigid).symm, fun rigid => (ih.1 rigid).symm⟩
  | trans first middle last _ _ ihFirst ihSecond =>
      constructor
      · intro rigid
        have same := ihFirst.1 rigid
        subst same
        exact ihSecond.1 rigid
      · intro rigid
        have same := ihSecond.2 rigid
        subst same
        exact ihFirst.2 rigid

/-- **A bubble is invisible at a vertex whose weak-core types avoid its steps.** -/
theorem invisible_of_rigid {products : List ProductRule} {steps : PTerm → PTerm → Prop}
    (rigid : ∀ context type sort, Kernel products noSteps context (.type type sort) → Rigid steps type)
    {context : SortedCtx} {judgment : Judgment} (derivation : Kernel products steps context judgment) :
    Kernel products noSteps context judgment := by
  induction derivation with
  | sort axiomHolds => exact .sort axiomHolds
  | pi _ _ member ihDomain ihBody => exact .pi ihDomain ihBody member
  | ofTerm _ axiomHolds ih => exact .ofTerm ih axiomHolds
  | toTerm _ axiomHolds ih => exact .toTerm ih axiomHolds
  | var found => exact .var found
  | lam _ _ member _ ihDomain ihBodyType ihBody => exact .lam ihDomain ihBodyType member ihBody
  | app _ _ member _ _ ihDomain ihBodyType ihFunction ihArgument =>
      exact .app ihDomain ihBodyType member ihFunction ihArgument
  | conv _ convertible _ ihTerm ihTarget =>
      have same := (bubbleConv_eq_of_rigid convertible).2 (rigid _ _ _ ihTarget)
      subst same
      exact ihTerm

/-! ## A consistent top, and no universal top

Every vertex has `∗ : □`. At every vertex, under every bubble whose steps are
beta steps, `Π p : ∗. p` has no closed inhabitant (`vertex_consistent`).
Replacing the axiom by `∗ : ∗` gives a universal sort, and the kernel with any
bubble that contains beta then proves `Π p : ∗. p`
(`universalTop_inconsistent`, Hurkens' paradox through `TypeInTypeParadox`).
A top for the cube therefore exists as the vertex `λC` with its own axiom,
reached by adding products; it is not obtained by letting the sort of types
contain itself. -/

/-- The type `Π p : ∗. p` of the paradox erases to the raw `Π p : ∗. p`. -/
theorem falsumTerm_erase :
    Mettapedia.GSLT.Dedukti.TypeInTypeParadox.falsumTerm.erase =
      Mettapedia.GSLT.Dedukti.ConstructionsModel.falsum := by
  decide

/-- **Every vertex of the cube is consistent under every bubble inside
beta.** -/
theorem vertex_consistent {products : List ProductRule} (inCube : products ⊆ constructionProducts)
    {steps : PTerm → PTerm → Prop}
    (insideBeta : ∀ {source target : PTerm}, steps source target → betaRoot source target)
    (term : PTerm) (sort : Srt) :
    ¬ Kernel products steps [] (.term term Mettapedia.GSLT.Dedukti.TypeInTypeParadox.falsumTerm sort) := by
  intro derivation
  have atTop : Derives constructions [] (.term term Mettapedia.GSLT.Dedukti.TypeInTypeParadox.falsumTerm sort) := by
    rw [derives_iff_typedUnder, ← bubbleConv_betaRoot]
    exact TypedUnder.mono (small := vertex products) (large := constructions) rfl inCube
      (fun converted => bubbleConv_mono insideBeta converted) derivation
  exact Mettapedia.GSLT.Dedukti.ConstructionsModel.derives_consistent
    (Mettapedia.GSLT.LanguageDef.LFProfile.Subsumed.refl _) falsumTerm_erase atTop

/-- **The paradox is not a proof in the calculus of constructions.** -/
theorem paradox_not_constructions (sort : Srt) :
    ¬ Derives constructions []
      (.term Mettapedia.GSLT.Dedukti.TypeInTypeParadox.paradoxTerm
        Mettapedia.GSLT.Dedukti.TypeInTypeParadox.falsumTerm sort) :=
  Mettapedia.GSLT.Dedukti.ConstructionsModel.derives_consistent
    (Mettapedia.GSLT.LanguageDef.LFProfile.Subsumed.refl _) falsumTerm_erase

/-- **A universal sort is inconsistent under every bubble that contains
beta.** -/
theorem universalTop_inconsistent {steps : PTerm → PTerm → Prop}
    (includesBeta : ∀ {source target : PTerm}, betaRoot source target → steps source target) :
    TypedUnder Mettapedia.GSLT.Dedukti.TypeInTypeParadox.typeInType (bubbleConv steps) []
      (.term Mettapedia.GSLT.Dedukti.TypeInTypeParadox.paradoxTerm
        Mettapedia.GSLT.Dedukti.TypeInTypeParadox.falsumTerm .type) := by
  have derived := derives_iff_typedUnder.mp
    Mettapedia.GSLT.Dedukti.TypeInTypeParadox.typeInType_inconsistent
  rw [← bubbleConv_betaRoot] at derived
  exact TypedUnder.mono rfl (fun _ member => member)
    (fun converted => bubbleConv_mono includesBeta converted) derived

/-- The universal sort is not the axiom of any vertex. -/
theorem universalTop_not_vertex (products : List ProductRule) :
    Mettapedia.GSLT.Dedukti.TypeInTypeParadox.typeInType ≠ vertex products := by
  intro same
  have axioms := congrArg (fun profile => profile.sortAxiom .type) same
  simp [Mettapedia.GSLT.Dedukti.TypeInTypeParadox.typeInType, vertex,
    Mettapedia.GSLT.LanguageDef.LFProfile.typeAxiom] at axioms

#print axioms vertex_consistent
#print axioms paradox_not_constructions
#print axioms directPredicateContext_formed_iff
#print axioms directValueIndexedForall_iff
#print axioms directValueIndexedForall_at_dependent
#print axioms directValueIndexedForall_absent_off_dependent_face
#print axioms directForall_abstract
#print axioms directForall_apply
#print axioms directValueIndexedForall_iff_contains_dependentProducts
#print axioms directValueIndexedForall_bubble_iff
#print axioms dependentProducts_least_directInterface
#print axioms polymorphicIdentity_typed
#print axioms typeOperatorKind_formed
#print axioms directFormationInterfaces_iff_contains_constructionProducts
#print axioms constructionProducts_least_directInterfaces
#print axioms directInterfaces_refused_of_missing_rule

end Mettapedia.TypeTheory.HypercubeBubbles
