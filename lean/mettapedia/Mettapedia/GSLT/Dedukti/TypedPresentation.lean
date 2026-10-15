import Mettapedia.GSLT.Core.StepFree
import Mettapedia.GSLT.Contexts.TermFamilies
import Mettapedia.GSLT.Dedukti.ConfluenceApplied

/-!
# The typed presentations, and exhausting as a statement about a map

The theories of `Presentation` have one interface and all raw terms.  Here
the interfaces are types.

* `typedTheory theory`: one interface for each type formed in a context,
  `Γ ⊢ A : s`; its terms are the inhabitants `Γ ⊢ t : A` of the λΠ-calculus
  modulo the theory, compared by the declared conversion.  As
  `conversionTheory`, it has no reduction: it is the theory as its checker
  sees it.
* `typedSystem profile`: the same for a pure type system in the sorted
  presentation of `PureTypeSystem`: one interface for each derivable
  `Γ ⊢ A : s`, its terms the `t` with `Γ ⊢ t : A : s`, compared by beta
  conversion of annotated terms.

The contexts of both are the hole and the terms (`familyTermsAlone`), the
least presentation through contexts, as `GSLT.termsAlone` is for one
interface.  Typed contexts with holes need a typing judgment for terms with
typed holes; it is not built here.

**The embedding as a map between typed theories.**  `cdTypedMap profile`
sends the interface `Γ ⊢ A : s` to `|Γ| ⊢ e_s |A| : Type` and a term to its
translation; its typing is `translate_sound`, its respect of conversion
`translate_conv`.  The map is injective on interfaces
(`translateType_injective`, from `translate_injective`).

* `cdTypedMap_exhausting_iff`: **the map is exhausting, in the sense of
  `ContextMap.Exhausting`, exactly when `ExhaustsTyped profile` holds.**
  `ExhaustsTyped` is the instance of exhausting at the contexts with no hole;
  for these theories the other contexts are the holes, which the map hits.
* `conservative_of_cdTypedMap_exhausting`: exhausting gives conservativity,
  through the existing `conservative_of_exhaustsTyped`.
* `constructions_not_cdTypedMap_exhausting`: the embedding of the calculus of
  constructions is not exhausting, from the existing
  `Unconditional.constructions_not_exhaustsTyped`.
* `simplyTyped_cdTypedMap_hosting`: the embedding of the simply typed
  λ-calculus is hosting between the typed theories: convertible translations
  of typed terms come from convertible annotated terms.
* `forgetTypes_hosting`, `forgetTypes_not_exhausting`: forgetting the types is
  a hosting map from the typed presentation to the untyped one
  (`conversionTheory`), and not an exhausting one as soon as a raw term has no
  type.

`ExhaustsTyped`, `conservative_of_exhaustsTyped` and
`constructions_not_exhaustsTyped` are used as they are.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (lift subst subst0 Ctx)
open Mettapedia.GSLT.LanguageDef.LFProfile (Profile ProductRule)
open Mettapedia.Logic.Relation (IsNormal)

/-! ## The typed presentation of a theory of the λΠ-calculus modulo -/

/-- **A type formed in a context**: the interfaces of the typed presentation. -/
structure FormedType (theory : Theory) where
  context : Ctx
  type : Term
  sort : Srt
  formed : LambdaPiModulo theory context type (.srt sort)

/-- The inhabitants of one formed type, compared by the declared conversion,
with no reduction. -/
def typedMember (theory : Theory) (interface : FormedType theory) : GSLT.{0} :=
  GSLT.equationOnly ({term : Term // LambdaPiModulo theory interface.context term interface.type}) (⟨fun first second => Conv theory first.1 second.1,
        ⟨fun _ => .refl _, fun related => .symm _ _ related,
          fun first second => .trans _ _ _ first second⟩⟩)

/-- **The typed presentation of a theory of the λΠ-calculus modulo**, as its
checker sees it. -/
def typedTheory (theory : Theory) : ContextTheory.{0} := familyTermsAlone (typedMember theory)

/-! ## The typed presentation of a pure type system -/

/-- **A sorted type derivable in a context**: the interfaces of the typed
presentation of a pure type system. -/
structure SortedType (profile : Profile) where
  context : SortedCtx
  type : PTerm
  sort : Srt
  formed : Derives profile context (.type type sort)

/-- The terms of one sorted type, compared by beta conversion of annotated
terms, with no reduction. -/
def sortedMember (profile : Profile) (interface : SortedType profile) : GSLT.{0} :=
  GSLT.equationOnly ({term : PTerm // Derives profile interface.context (.term term interface.type interface.sort)}) (⟨fun first second => PTerm.Conv first.1 second.1,
        ⟨fun _ => .refl _, fun related => .symm _ _ related,
          fun first second => .trans _ _ _ first second⟩⟩)

/-- **The typed presentation of a pure type system**, as its checker sees it. -/
def typedSystem (profile : Profile) : ContextTheory.{0} := familyTermsAlone (sortedMember profile)

/-! ## The translation is injective -/

theorem translate_ne_con_prod (rule : ProductRule) (term : PTerm) :
    translate term ≠ .con (Symbol.prod rule).name := by
  cases term with
  | sort level =>
      intro same
      have names := Term.con.inj same
      exact absurd (Symbol.name_injective names) (by simp)
  | var index => simp [translate]
  | pi rule' domain body => simp [translate, prodCode]
  | lam level domain body => simp [translate]
  | app function argument => simp [translate]

theorem translate_ne_prodHead (rule : ProductRule) (term : PTerm) (domain : Term) :
    translate term ≠ .app (.con (Symbol.prod rule).name) domain := by
  cases term with
  | sort level => simp [translate, sortCode]
  | var index => simp [translate]
  | pi rule' domain' body => simp [translate, prodCode]
  | lam level domain' body => simp [translate]
  | app function argument =>
      intro same
      exact translate_ne_con_prod rule function (Term.app.inj same).1

/-- **The translation of annotated terms is injective.** -/
theorem translate_injective : Function.Injective translate := by
  intro first
  induction first with
  | var index =>
      intro second same
      cases second <;> simp_all [translate, sortCode, prodCode]
  | sort level =>
      intro second same
      cases second with
      | sort level' =>
          have names := Term.con.inj same
          have symbols := Symbol.name_injective names
          cases symbols
          rfl
      | var index => simp [translate, sortCode] at same
      | pi rule domain body => simp [translate, sortCode, prodCode] at same
      | lam level' domain body => simp [translate, sortCode] at same
      | app function argument => simp [translate, sortCode] at same
  | pi rule domain body ihDomain ihBody =>
      intro second same
      cases second with
      | pi rule' domain' body' =>
          simp only [translate, prodCode, El, Term.app.injEq, Term.con.injEq, Term.lam.injEq] at same
          obtain ⟨⟨names, domains⟩, -, bodies⟩ := same
          cases Symbol.name_injective names
          rw [ihDomain domains, ihBody bodies]
      | app function argument =>
          simp only [translate, prodCode, Term.app.injEq] at same
          exact (translate_ne_prodHead rule function _ same.1.symm).elim
      | var index => simp [translate, prodCode] at same
      | sort level => simp [translate, prodCode, sortCode] at same
      | lam level domain' body' => simp [translate, prodCode] at same
  | lam level domain body ihDomain ihBody =>
      intro second same
      cases second with
      | lam level' domain' body' =>
          simp only [translate, El, Term.lam.injEq, Term.app.injEq, Term.con.injEq] at same
          obtain ⟨⟨names, domains⟩, bodies⟩ := same
          cases Symbol.name_injective names
          rw [ihDomain domains, ihBody bodies]
      | var index => simp [translate] at same
      | sort level' => simp [translate, sortCode] at same
      | pi rule domain' body' => simp [translate, prodCode] at same
      | app function argument => simp [translate] at same
  | app function argument ihFunction ihArgument =>
      intro second same
      cases second with
      | app function' argument' =>
          simp only [translate, Term.app.injEq] at same
          rw [ihFunction same.1, ihArgument same.2]
      | pi rule domain body =>
          simp only [translate, prodCode, Term.app.injEq] at same
          exact (translate_ne_prodHead rule function _ same.1).elim
      | var index => simp [translate] at same
      | sort level => simp [translate, sortCode] at same
      | lam level domain body => simp [translate] at same

theorem El_injective {first second : Srt} {firstCode secondCode : Term}
    (same : El first firstCode = El second secondCode) : first = second ∧ firstCode = secondCode := by
  simp only [El, Term.app.injEq, Term.con.injEq] at same
  have symbols := Symbol.name_injective same.1
  cases symbols
  exact ⟨rfl, same.2⟩

theorem translateCtx_injective : Function.Injective translateCtx := by
  intro first second same
  apply List.map_injective_iff.mpr _ same
  intro entry entry' entries
  obtain ⟨sorts, codes⟩ := El_injective entries
  exact Prod.ext (translate_injective codes) sorts

/-! ## The embedding as a map between typed theories -/

variable {profile : Profile}

/-- The image of an interface: `Γ ⊢ A : s` goes to `|Γ| ⊢ e_s |A| : Type`. -/
def translateType (interface : SortedType profile) : FormedType (cdTheory profile) where
  context := translateCtx interface.context
  type := El interface.sort (translate interface.type)
  sort := .type
  formed := type_El (translate_sound interface.formed)

theorem translateType_injective (profile : Profile) :
    Function.Injective (translateType (profile := profile)) := by
  intro first second same
  cases first with
  | mk context type sort formed =>
      cases second with
      | mk context' type' sort' formed' =>
          simp only [translateType, FormedType.mk.injEq] at same
          obtain ⟨contexts, codes, -⟩ := same
          obtain ⟨sorts, types⟩ := El_injective codes
          cases translateCtx_injective contexts
          cases translate_injective types
          cases sorts
          rfl

/-- **The Cousineau–Dowek embedding as a map between typed theories.** -/
def cdTypedMap (profile : Profile) :
    ContextMap (typedSystem profile) (typedTheory (cdTheory profile)) :=
  ContextMap.ofFamilyTerms (family := sortedMember profile) (target := typedTheory (cdTheory profile))
    translateType (fun term => ⟨translate term.1, translate_sound term.2⟩)
    (fun related => translate_conv profile related)

/-- **Exhausting is `ExhaustsTyped`.**  The map between the typed theories is
exhausting exactly when every inhabitant of the translation of a type is
convertible to the translation of an inhabitant. -/
theorem cdTypedMap_exhausting_iff : (cdTypedMap profile).Exhausting ↔ ExhaustsTyped profile := by
  refine (ContextMap.exhausting_iff_of_injective (family := sortedMember profile)
    (family' := typedMember (cdTheory profile)) (cdTypedMap profile)
    (translateType_injective profile)).trans ⟨?_, ?_⟩
  · intro surjective context type level inhabitant formed typed
    obtain ⟨preimage, equivalent⟩ := surjective ⟨context, type, level, formed⟩ ⟨inhabitant, typed⟩
    exact ⟨preimage.1, preimage.2, equivalent⟩
  · intro exhausts origin image
    obtain ⟨source, derivation, equivalent⟩ :=
      exhausts origin.context origin.type origin.sort image.1 origin.formed image.2
    exact ⟨⟨source, derivation⟩, equivalent⟩

/-- **An exhausting embedding is conservative.** -/
theorem conservative_of_cdTypedMap_exhausting (exhausting : (cdTypedMap profile).Exhausting) :
    Conservative profile :=
  conservative_of_exhaustsTyped (cdTypedMap_exhausting_iff.mp exhausting)

/-- **The embedding of the calculus of constructions is not exhausting.** -/
theorem constructions_not_cdTypedMap_exhausting : ¬ (cdTypedMap constructions).Exhausting :=
  fun exhausting => Unconditional.constructions_not_exhaustsTyped
    (cdTypedMap_exhausting_iff.mp exhausting)

/-! ## Positive: the simply typed λ-calculus -/

/-- The subject of a sorted derivation carries only annotations of the
system. -/
theorem Derives.subject_valid {context : SortedCtx} {judgment : Judgment}
    (derivation : Derives profile context judgment) : judgment.subject.Valid profile := by
  induction derivation with
  | sort _ => trivial
  | pi _ _ member ihDomain ihBody => exact ⟨member, ihDomain, ihBody⟩
  | ofTerm _ _ ih => exact ih
  | toTerm _ _ ih => exact ih
  | var _ => trivial
  | lam _ _ member _ ihDomain _ ihBody => exact ⟨⟨_, member, rfl⟩, ihDomain, ihBody⟩
  | app _ _ _ _ _ _ _ ihFunction ihArgument => exact ⟨ihFunction, ihArgument⟩
  | conv _ _ _ ihTerm _ => exact ihTerm

/-- **The embedding of the simply typed λ-calculus is hosting between the
typed theories.** -/
theorem simplyTyped_cdTypedMap_hosting : (cdTypedMap simplyTyped).Hosting := by
  rw [ContextMap.hosting_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro origin first second convertible
    have erased := translate_reflects simplyTyped convertible
    have annotated := annotate_conv erased
    have firstValid : first.1.Valid simplyTyped := Derives.subject_valid first.2
    have secondValid : second.1.Valid simplyTyped := Derives.subject_valid second.2
    rw [annotate_erase firstValid, annotate_erase secondValid] at annotated
    exact annotated
  · intro _ _ _ _ _ step
    exact step.elim
  · intro _ _ _ _ _ step
    exact step.elim

/-! ## Forgetting the types -/

/-- **Forgetting the types**: the typed presentation into the untyped one. -/
def forgetTypes (theory : Theory) : ContextMap (typedTheory theory) (conversionTheory theory) :=
  ContextMap.ofFamilyTerms (family := typedMember theory) (target := conversionTheory theory)
    (fun _ => ()) (fun term => term.1) (fun related => related)

/-- **Forgetting the types is hosting**: the typed terms are compared by the
same conversion. -/
theorem forgetTypes_hosting (theory : Theory) : (forgetTypes theory).Hosting := by
  rw [ContextMap.hosting_iff]
  refine ⟨fun related => related, ?_, ?_⟩
  · intro _ _ _ _ _ step
    exact step.elim
  · intro _ _ _ _ _ step
    exact step.elim

/-- **Forgetting the types is not exhausting**, at an interface whose
untyped theory has a term that is convertible to no inhabitant. -/
theorem forgetTypes_not_exhausting (theory : Theory) (interface : FormedType theory)
    (outside : Term)
    (untyped : ∀ inhabitant : Term, LambdaPiModulo theory interface.context inhabitant interface.type →
      ¬ Conv theory outside inhabitant) :
    ¬ (forgetTypes theory).Exhausting := by
  intro exhausting
  obtain ⟨preimage, equivalent⟩ :=
    ContextMap.Exhausting.term_surjective (forgetTypes theory) exhausting (origin := interface) outside
  exact untyped preimage.1 preimage.2 equivalent

/-! ### An instance: an untyped constant -/

/-- A term mentions a constant. -/
def mentions (name : String) : Term → Prop
  | .con other => other = name
  | .pi domain body => mentions name domain ∨ mentions name body
  | .lam domain body => mentions name domain ∨ mentions name body
  | .app function argument => mentions name function ∨ mentions name argument
  | .var _ => False
  | .srt _ => False

theorem mentions_lift (name : String) (term : Term) :
    ∀ amount cutoff : Nat, mentions name (lift amount cutoff term) ↔ mentions name term := by
  induction term with
  | var index => intro amount cutoff; simp [lift, mentions]
  | srt sort => intro amount cutoff; simp [lift, mentions]
  | con other => intro amount cutoff; simp [lift, mentions]
  | pi domain body ihDomain ihBody =>
      intro amount cutoff; simp [lift, mentions, ihDomain, ihBody]
  | lam domain body ihDomain ihBody =>
      intro amount cutoff; simp [lift, mentions, ihDomain, ihBody]
  | app function argument ihFunction ihArgument =>
      intro amount cutoff; simp [lift, mentions, ihFunction, ihArgument]

theorem mentions_subst (name : String) (term : Term) :
    ∀ (target : Nat) (replacement : Term), mentions name (subst target replacement term) →
      mentions name replacement ∨ mentions name term := by
  induction term with
  | var index =>
      intro target replacement found
      simp only [subst] at found
      split at found
      · exact Or.inl found
      · split at found <;> simp [mentions] at found
  | srt sort => intro target replacement found; simp [subst, mentions] at found
  | con other => intro target replacement found; exact Or.inr found
  | pi domain body ihDomain ihBody =>
      intro target replacement found
      rcases found with inDomain | inBody
      · rcases ihDomain _ _ inDomain with here | there
        · exact Or.inl here
        · exact Or.inr (Or.inl there)
      · rcases ihBody _ _ inBody with here | there
        · exact Or.inl ((mentions_lift name replacement 1 0).mp here)
        · exact Or.inr (Or.inr there)
  | lam domain body ihDomain ihBody =>
      intro target replacement found
      rcases found with inDomain | inBody
      · rcases ihDomain _ _ inDomain with here | there
        · exact Or.inl here
        · exact Or.inr (Or.inl there)
      · rcases ihBody _ _ inBody with here | there
        · exact Or.inl ((mentions_lift name replacement 1 0).mp here)
        · exact Or.inr (Or.inr there)
  | app function argument ihFunction ihArgument =>
      intro target replacement found
      rcases found with inFunction | inArgument
      · rcases ihFunction _ _ inFunction with here | there
        · exact Or.inl here
        · exact Or.inr (Or.inl there)
      · rcases ihArgument _ _ inArgument with here | there
        · exact Or.inl here
        · exact Or.inr (Or.inr there)

/-- **Beta creates no constant.** -/
theorem Step.mentions_empty {name : String} {source target : Term}
    (step : Step Theory.empty source target) (found : mentions name target) :
    mentions name source := by
  cases step with
  | inContext context root =>
      induction context with
      | hole =>
          cases root with
          | beta domain body argument =>
              rcases mentions_subst name body 0 argument found with inArgument | inBody
              · exact Or.inr inArgument
              · exact Or.inl (Or.inr inBody)
          | delta defined => cases defined
          | rule assignment member => exact member.elim
      | piDomain rest body ih =>
          rcases found with here | there
          · exact Or.inl (ih here)
          · exact Or.inr there
      | piBody domain rest ih =>
          rcases found with here | there
          · exact Or.inl here
          · exact Or.inr (ih there)
      | lamDomain rest body ih =>
          rcases found with here | there
          · exact Or.inl (ih here)
          · exact Or.inr there
      | lamBody domain rest ih =>
          rcases found with here | there
          · exact Or.inl here
          · exact Or.inr (ih there)
      | appFunction rest argument ih =>
          rcases found with here | there
          · exact Or.inl (ih here)
          · exact Or.inr there
      | appArgument function rest ih =>
          rcases found with here | there
          · exact Or.inl here
          · exact Or.inr (ih there)

theorem Reduces.mentions_empty {name : String} {source target : Term}
    (reduces : Reduces Theory.empty source target) (found : mentions name target) :
    mentions name source := by
  induction reduces with
  | refl => exact found
  | tail _ step ih => exact ih (step.mentions_empty found)

/-- **A term typed in the pure calculus mentions no constant.** -/
theorem HasType.not_mentions_empty {name : String} {context : Ctx} {term type : Term}
    (typed : LambdaPiModulo Theory.empty context term type) : ¬ mentions name term := by
  induction typed with
  | sort _ => exact fun found => found
  | var _ => exact fun found => found
  | con declared => cases declared
  | pi _ _ _ ihDomain ihBody =>
      rintro (here | there)
      · exact ihDomain here
      · exact ihBody there
  | lam _ _ _ _ ihDomain _ ihBody =>
      rintro (here | there)
      · exact ihDomain here
      · exact ihBody there
  | app _ _ ihFunction ihArgument =>
      rintro (here | there)
      · exact ihFunction here
      · exact ihArgument there
  | conv _ _ _ ihTerm _ => exact ihTerm

/-- **Forgetting the types of the pure calculus is not exhausting**: a
constant is convertible to no inhabitant of `Type` in the empty context. -/
theorem forgetTypes_empty_not_exhausting : ¬ (forgetTypes Theory.empty).Exhausting := by
  refine forgetTypes_not_exhausting Theory.empty ⟨[], .srt .type, .kind, .sort rfl⟩ (.con "c") ?_
  intro inhabitant typed convertible
  obtain ⟨common, constantReduces, inhabitantReduces⟩ :=
    Unconditional.conv_iff_joinable.mp convertible
  have normal : IsNormal (Step Theory.empty) (.con "c") := fun _ step => by
    rcases step.con_inv.con_inv with defined | ⟨_, _, member, _, _⟩
    · cases defined
    · exact member.elim
  have same := normal.reflTransGen_eq constantReduces
  subst same
  exact typed.not_mentions_empty (inhabitantReduces.mentions_empty (name := "c") rfl)

#print axioms translate_injective
#print axioms cdTypedMap_exhausting_iff
#print axioms conservative_of_cdTypedMap_exhausting
#print axioms constructions_not_cdTypedMap_exhausting
#print axioms simplyTyped_cdTypedMap_hosting
#print axioms forgetTypes_hosting
#print axioms forgetTypes_empty_not_exhausting

end Mettapedia.GSLT.Dedukti
