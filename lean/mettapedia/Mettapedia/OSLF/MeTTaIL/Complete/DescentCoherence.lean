import Mettapedia.OSLF.MeTTaIL.Complete.LawCoherence
import Mettapedia.OSLF.MeTTaIL.LawNormalExtended

/-!
# The canonical explorer with reduction inside collections of a flattening kind

A plan may license reduction inside a collection of a flattening kind, as rho does inside a
parallel composition. Normalization then splices nested collections along a site's path. A firing
at any well-sorted presentation is moved, one flattening move at a time, to a presentation whose
path normalization keeps (`CanonicalBags.flatten_site`): the focus stays on a shorter path, or a
nested collection that is the focus is absorbed into its flattened parent, where an extended rule
fires with its rest absorbing the parent's other elements (`CanonicalBags.rootFiring_absorbed`).
The law-normal form does not change along the way, so the firing reaches it
(`primitive_normalize_descent`).

- `firingsNormalize_descent`: firings normalize at every well-sorted presentation;
- `presented_explores_descent`: the canonical explorer is complete for the presented GSLT.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Complete.DescentCoherence

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission CanonicalBags Coherence
open Mettapedia.GSLT.LanguageDef.WellSorted Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence GeneralTypedSites
open GeneralScopedMatch
open Relation (EqvGen)

variable {plan : Plan} {bound : List TypeExpr} {expected : TypeExpr}

variable (plan) in
/-- Rules admissible with reduction inside collections of a flattening kind: no rule's left side is a
bare metavariable or a declared unit, and a rule whose left side is a collection of a flattening
kind is extended for that kind. -/
def DescentRulesAdmissible : Prop :=
  ∀ declaration ordinal, (declaration, ordinal) ∈ plan.rules.zipIdx →
    ∀ rule spec, (GeneralPlanEnvironment.environment plan).language.rewrites[ordinal]? = some rule →
      GeneralPremise.specification? (GeneralPlanEnvironment.environment plan) ordinal = some spec →
      (∀ name, rule.left ≠ .fvar name) ∧
      (∀ kind law label, CollectionLaws.lawFor (Normalized.laws plan) kind = some law → law.unit = some label →
        rule.left ≠ .apply label []) ∧
      (∀ kind law elements rest, rule.left = .collection kind elements rest →
        CollectionLaws.lawFor (Normalized.laws plan) kind = some law →
        ExtendedAt (GeneralPlanEnvironment.environment plan) ordinal kind ∧ kind ≠ .vec)

variable (plan) in
/-- The plan's laws and rules admit reduction inside collections of a flattening kind. -/
structure DescentAdmissible : Prop where
  typed : LawsTypedStrict (Normalized.laws plan) (GeneralPlanEnvironment.environment plan).language plan.snapshot.free
  unique : UniqueBare (Normalized.laws plan) (GeneralPlanEnvironment.environment plan).language
  rules : LawCoherence.LawRulesAdmissible plan
  descent : DescentRulesAdmissible plan

/-- **A firing on a path that normalization keeps has a counterpart at the law-normal form.** -/
theorem primitive_normalize_flat (admissible : DescentAdmissible plan)
    (boundOk : ∀ entry ∈ bound, LawTypeOk (Normalized.laws plan) (GeneralPlanEnvironment.environment plan).language entry)
    (expectedOk : LawTypeOk (Normalized.laws plan) (GeneralPlanEnvironment.environment plan).language expected)
    {source : Pattern} {receipt : GeneralRuleJobs.Receipt}
    (fired : GeneralOccurrenceSemantics.Primitive plan bound expected source receipt)
    (flat : PathFlat (Normalized.laws plan) receipt.job.site.context receipt.job.site.focus) :
    ∃ receipt', GeneralOccurrenceSemantics.Primitive plan bound expected
        (CollectionLaws.normalize (Normalized.laws plan) source) receipt' ∧
      LawSame (Normalized.laws plan) receipt.target receipt'.target := by
  obtain ⟨⟨declared, licensed⟩, rooted, accepts, endpoint, sorted⟩ := fired
  obtain ⟨site', licensed', focus, focusBound, focusType, frames, fill, acceptsSame⟩ :=
    licensed_normalize admissible.typed.toLawsTyped licensed
      (fun entry member => noNested_of_lawTypeOk (boundOk entry member)) (noNested_of_lawTypeOk expectedOk) flat
  obtain ⟨siteTypeOk, siteBoundOk⟩ := _root_.Mettapedia.OSLF.MeTTaIL.CanonicalBags.Licensed.lawTypeOk
    admissible.typed licensed boundOk expectedOk
  obtain ⟨trace', localTarget', rooted', sameLocal⟩ :=
    rootFiring_normalize rooted (admissible.rules _ _ declared) admissible.typed siteBoundOk siteTypeOk
  have sameTarget : LawSame (Normalized.laws plan) receipt.target (site'.context.fill localTarget') := by
    rw [endpoint]; exact fill _ _ sameLocal
  refine ⟨⟨⟨receipt.job.ordinal, receipt.job.declaration, site'⟩, trace',
    mapAssignment (CollectionLaws.normalize (Normalized.laws plan)) receipt.captured,
    mapAssignment (CollectionLaws.normalize (Normalized.laws plan)) receipt.completed, receipt.premiseHistory,
    localTarget', site'.context.fill localTarget'⟩, ⟨⟨declared, licensed'⟩, ?_, ?_, rfl, ?_⟩, sameTarget⟩
  · simp only [focus, focusBound, focusType]
    exact rooted'
  · simp only [GeneralTypedSites.SiteData.acceptsReplacementRepresentation]
    rw [← acceptsSame _ _ _ sameLocal]
    exact accepts
  · exact LawSame.openPatternWellSorted admissible.typed sameTarget boundOk expectedOk sorted

/-- A schema matching a collection is a collection of its kind or a bare metavariable. -/
theorem matches_collection {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat} {site : RulePatternSite}
    {path : List Nat} {depth : Nat} {initial final : ScopedRuleMatching.Assignment} {schema : Pattern} {kind : CollType}
    {elements : List Pattern} (matched : Matches rule spec ambient site path depth initial schema (.collection kind elements none)
      final) : (∃ name, schema = .fvar name) ∨ ∃ schemas rest, schema = .collection kind schemas rest := by
  cases matched with
  | capture => exact .inl ⟨_, rfl⟩
  | bag => exact .inr ⟨_, _, rfl⟩
  | vector => exact .inr ⟨_, _, rfl⟩
  | vectorRest => exact .inr ⟨_, _, rfl⟩

/-- A schema matching a constant is that constant or a bare metavariable. -/
theorem matches_constant {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat} {site : RulePatternSite}
    {path : List Nat} {depth : Nat} {initial final : ScopedRuleMatching.Assignment} {schema : Pattern} {label : String}
    (matched : Matches rule spec ambient site path depth initial schema (.apply label []) final) :
    (∃ name, schema = .fvar name) ∨ schema = .apply label [] := by
  cases matched with
  | capture => exact .inl ⟨_, rfl⟩
  | constructor arguments =>
    have := arguments_length _ arguments
    simp only [List.length_nil, List.length_eq_zero_iff] at this
    subst this
    exact .inr rfl

/-- A collection of a flattening kind typed at a type typed for the laws exhibits a bare
constructor of its kind. -/
theorem lawCollection_witness {language : LanguageDef} {free : FreeTypeContext} {law : CollectionLaws.Laws}
    {kind : CollType} (found : CollectionLaws.lawFor (Normalized.laws plan) kind = some law) {bound' : List TypeExpr}
    {elements : List Pattern} {rest : Option String} {type : TypeExpr}
    (typeOk : LawTypeOk (Normalized.laws plan) language type)
    (typed : HasType language free bound' (.collection kind elements rest) type) :
    ∃ rule ∈ language.terms, ∃ name element, rule.params = [.simple name (.collection kind element)] := by
  rcases hasType_collection_inv typed with ⟨_, rfl, _⟩ | ⟨rule, name, element, declared, parameters, rfl, _⟩
  · obtain ⟨witness, declared, name, parameters, _⟩ := typeOk.lawful found
    exact ⟨witness, declared, name, _, parameters⟩
  · exact ⟨rule, declared, name, element, parameters⟩

/-- **Every firing at a well-sorted presentation has a counterpart at its law-normal form**, with
a law-equal result, also when reduction lies inside collections of a flattening kind. -/
theorem primitive_normalize_descent (admissible : DescentAdmissible plan)
    (boundOk : ∀ entry ∈ bound, LawTypeOk (Normalized.laws plan) (GeneralPlanEnvironment.environment plan).language entry)
    (expectedOk : LawTypeOk (Normalized.laws plan) (GeneralPlanEnvironment.environment plan).language expected)
    {source : Pattern} {receipt : GeneralRuleJobs.Receipt}
    (sorted : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language plan.snapshot.free bound expected source)
    (fired : GeneralOccurrenceSemantics.Primitive plan bound expected source receipt) :
    ∃ receipt', GeneralOccurrenceSemantics.Primitive plan bound expected
        (CollectionLaws.normalize (Normalized.laws plan) source) receipt' ∧
      LawSame (Normalized.laws plan) receipt.target receipt'.target := by
  suffices along : ∀ (depth : Nat) (source : Pattern) (receipt : GeneralRuleJobs.Receipt),
      receipt.job.site.typingFrames.length = depth →
      OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language plan.snapshot.free bound expected source →
      GeneralOccurrenceSemantics.Primitive plan bound expected source receipt →
      ∃ receipt', GeneralOccurrenceSemantics.Primitive plan bound expected
          (CollectionLaws.normalize (Normalized.laws plan) source) receipt' ∧
        LawSame (Normalized.laws plan) receipt.target receipt'.target from
    along _ source receipt rfl sorted fired
  intro depth
  induction depth using Nat.strong_induction_on with
  | _ depth ih =>
  intro source receipt atDepth sorted fired
  by_cases flat : PathFlat (Normalized.laws plan) receipt.job.site.context receipt.job.site.focus
  · exact primitive_normalize_flat admissible boundOk expectedOk fired flat
  obtain ⟨⟨declared, licensed⟩, rooted, accepts, endpoint, targetSorted⟩ := fired
  have siteOk := _root_.Mettapedia.OSLF.MeTTaIL.CanonicalBags.Licensed.lawTypeOk admissible.typed licensed boundOk
    expectedOk
  cases flatten_site admissible.typed licensed boundOk expectedOk flat with
  | shorter source' site' licensed' normal same focus focusBound focusType fill acceptsSame shorter =>
    have source'Sorted := LawSame.openPatternWellSorted admissible.typed same boundOk expectedOk sorted
    have sameTarget : LawSame (Normalized.laws plan) receipt.target (site'.context.fill receipt.localTarget) := by
      rw [endpoint]; exact fill _ _ (.refl _)
    have fired' : GeneralOccurrenceSemantics.Primitive plan bound expected source'
        ⟨⟨receipt.job.ordinal, receipt.job.declaration, site'⟩, receipt.matcherTrace, receipt.captured, receipt.completed,
          receipt.premiseHistory, receipt.localTarget, site'.context.fill receipt.localTarget⟩ := by
      refine ⟨⟨declared, licensed'⟩, ?_, ?_, rfl, ?_⟩
      · simp only [focus, focusBound, focusType]; exact rooted
      · simp only [GeneralTypedSites.SiteData.acceptsReplacementRepresentation]
        rw [← acceptsSame _ _ _ (.refl _)]; exact accepts
      · exact LawSame.openPatternWellSorted admissible.typed sameTarget boundOk expectedOk targetSorted
    obtain ⟨final, firedFinal, sameFinal⟩ := ih _ (by rw [← atDepth]; exact shorter) source' _ rfl source'Sorted fired'
    rw [normal] at firedFinal
    exact ⟨final, firedFinal, .trans _ _ _ sameTarget sameFinal⟩
  | absorbed source' site' law front back elements licensed' normal same found focus focus' focusBound fill acceptsSame
      shorter =>
    have source'Sorted := LawSame.openPatternWellSorted admissible.typed same boundOk expectedOk sorted
    have site'Ok := _root_.Mettapedia.OSLF.MeTTaIL.CanonicalBags.Licensed.lawTypeOk admissible.typed licensed' boundOk
      expectedOk
    have focus'Sorted := _root_.Mettapedia.OSLF.MeTTaIL.CanonicalBags.Licensed.focus_sorted licensed' source'Sorted
    rw [focus'] at focus'Sorted
    rw [focus] at rooted
    -- the rule is extended for the kind
    have extendedFacts : ExtendedAt (GeneralPlanEnvironment.environment plan) receipt.job.ordinal law.kind ∧
        law.kind ≠ .vec ∧ ∃ spec, GeneralPremise.specification? (GeneralPlanEnvironment.environment plan)
          receipt.job.ordinal = some spec := by
      cases rooted with
      | @fire _ _ _ _ _ rule spec _ _ _ _ selected specified _ _ matched _ _ _ _ =>
        obtain ⟨notVariable, _, collectionRule⟩ := admissible.descent _ _ declared rule spec selected specified
        rcases matches_collection (GeneralScopedMatchMachine.traced_iff_matches.mp ⟨_, matched⟩) with
          ⟨name, same⟩ | ⟨schemas, rest, same⟩
        · exact absurd same (notVariable name)
        · obtain ⟨extended, notVector⟩ := collectionRule _ _ _ _ same found
          exact ⟨extended, notVector, spec, specified⟩
    obtain ⟨extended, notVector, spec, specified⟩ := extendedFacts
    obtain ⟨witness, witnessDeclared, witnessName, witnessElement, witnessParameters⟩ :=
      lawCollection_witness found site'Ok.1 focus'Sorted.1
    have focus'Elements := lawCollection_elements admissible.typed admissible.unique found site'Ok.1 focus'Sorted.1
      witnessDeclared witnessParameters
    have siblingsTyped : ∀ item ∈ front ++ back, HasType (GeneralPlanEnvironment.environment plan).language
        plan.snapshot.free site'.focusBound item (.base witness.category) := by
      intro item member
      apply elementsHaveType_iff.mp focus'Elements
      simp only [List.mem_append] at member ⊢; tauto
    obtain ⟨focus'Typed, focus'Metadata, focus'Object, focus'Scope⟩ := focus'Sorted
    have elementsOf : ∀ item ∈ front ++ back, item ∈ front ++ elements ++ back := by
      intro item member; simp only [List.mem_append] at member ⊢; tauto
    have siblingsScoped : ∀ item ∈ front ++ back, item.isWellScopedAt receipt.job.site.focusBound.length = true := by
      intro item member
      unfold ScopeSafeAt at focus'Scope
      simp only [Pattern.isWellScopedAt, isWellScopedListAt_iff] at focus'Scope
      rw [← focusBound]; exact focus'Scope item (elementsOf item member)
    have siblingsObjects : ∀ item ∈ front ++ back, isObjectPattern item = true := by
      intro item member
      simp only [isObjectPattern, Bool.and_eq_true, isObjectPatternList_eq_all, List.all_eq_true] at focus'Object
      exact focus'Object.2 item (elementsOf item member)
    have siblingsMetadata : ∀ item ∈ front ++ back, item.hasCanonicalBinderMetadata = true := by
      intro item member
      simp only [Pattern.hasCanonicalBinderMetadata, hasCanonicalBinderMetadataList_eq_all, List.all_eq_true]
        at focus'Metadata
      exact focus'Metadata item (elementsOf item member)
    have restTyped : ∀ (rule : RewriteRule) (name : String) (sort : TypeExpr) (residual : List Pattern),
        (GeneralPlanEnvironment.environmentWith plan GeneralPremise.DynamicProvider.empty).language.rewrites[receipt.job.ordinal]? =
          some rule → rule.typeContext.lookup name = some sort → (∀ item ∈ residual, item ∈ elements) →
        HasType (GeneralPlanEnvironment.environmentWith plan GeneralPremise.DynamicProvider.empty).language
          (GeneralPlanEnvironment.environmentWith plan GeneralPremise.DynamicProvider.empty).free receipt.job.site.focusBound
          (.collection law.kind residual none) sort →
        HasType (GeneralPlanEnvironment.environmentWith plan GeneralPremise.DynamicProvider.empty).language
          (GeneralPlanEnvironment.environmentWith plan GeneralPremise.DynamicProvider.empty).free receipt.job.site.focusBound
          (.collection law.kind (front ++ residual ++ back) none) sort := by
      intro rule name sort residual selected sortFound _ typedResidual
      have sortOk := (admissible.rules _ _ declared rule spec selected specified).2.2.1 name sort sortFound
      have residualElements := lawCollection_elements admissible.typed admissible.unique found sortOk typedResidual
        witnessDeclared witnessParameters
      apply lawCollection_rebuild admissible.typed admissible.unique found sortOk typedResidual witnessDeclared
        witnessParameters
      apply elementsHaveType_iff.mpr
      intro item member
      simp only [List.mem_append] at member
      rcases member with (inFront | inResidual) | inBack
      · rw [← focusBound]; exact siblingsTyped item (by simp [inFront])
      · exact elementsHaveType_iff.mp residualElements item inResidual
      · rw [← focusBound]; exact siblingsTyped item (by simp [inBack])
    have targetSorted' : ∀ explicit residual : List Pattern, (∀ item ∈ residual, item ∈ elements) →
        OpenPatternWellSorted (GeneralPlanEnvironment.environmentWith plan GeneralPremise.DynamicProvider.empty).language
          (GeneralPlanEnvironment.environmentWith plan GeneralPremise.DynamicProvider.empty).free receipt.job.site.focusBound
          receipt.job.site.focusType (.collection law.kind (explicit ++ residual) none) →
        OpenPatternWellSorted (GeneralPlanEnvironment.environmentWith plan GeneralPremise.DynamicProvider.empty).language
          (GeneralPlanEnvironment.environmentWith plan GeneralPremise.DynamicProvider.empty).free receipt.job.site.focusBound
          site'.focusType (.collection law.kind (explicit ++ front ++ residual ++ back) none) := by
      intro explicit residual _ localSorted
      obtain ⟨localTyped, localMetadata, localObject, localScope⟩ := localSorted
      have localElements := lawCollection_elements admissible.typed admissible.unique found siteOk.1 localTyped
        witnessDeclared witnessParameters
      have inLocal : ∀ item, item ∈ explicit ∨ item ∈ residual → item ∈ explicit ++ residual := by
        intro item member; simp only [List.mem_append]; exact member
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [← focusBound]
        apply lawCollection_rebuild admissible.typed admissible.unique found site'Ok.1 focus'Typed witnessDeclared
          witnessParameters
        apply elementsHaveType_iff.mpr
        intro item member
        simp only [List.mem_append] at member
        rcases member with ((inExplicit | inFront) | inResidual) | inBack
        · rw [focusBound]; exact elementsHaveType_iff.mp localElements item (inLocal item (.inl inExplicit))
        · exact siblingsTyped item (by simp [inFront])
        · rw [focusBound]; exact elementsHaveType_iff.mp localElements item (inLocal item (.inr inResidual))
        · exact siblingsTyped item (by simp [inBack])
      · simp only [Pattern.hasCanonicalBinderMetadata, hasCanonicalBinderMetadataList_eq_all, List.all_eq_true,
          List.mem_append] at localMetadata ⊢
        rintro item (((inExplicit | inFront) | inResidual) | inBack)
        · exact localMetadata item (.inl inExplicit)
        · exact siblingsMetadata item (by simp [inFront])
        · exact localMetadata item (.inr inResidual)
        · exact siblingsMetadata item (by simp [inBack])
      · simp only [isObjectPattern, Bool.and_eq_true, isObjectPatternList_eq_all, List.all_eq_true,
          List.mem_append] at localObject ⊢
        refine ⟨localObject.1, ?_⟩
        rintro item (((inExplicit | inFront) | inResidual) | inBack)
        · exact localObject.2 item (.inl inExplicit)
        · exact siblingsObjects item (by simp [inFront])
        · exact localObject.2 item (.inr inResidual)
        · exact siblingsObjects item (by simp [inBack])
      · unfold ScopeSafeAt at localScope ⊢
        simp only [Pattern.isWellScopedAt, isWellScopedListAt_iff, List.mem_append] at localScope ⊢
        rintro item (((inExplicit | inFront) | inResidual) | inBack)
        · exact localScope item (.inl inExplicit)
        · exact siblingsScoped item (by simp [inFront])
        · exact localScope item (.inr inResidual)
        · exact siblingsScoped item (by simp [inBack])
    have sourceSorted' : OpenPatternWellSorted (GeneralPlanEnvironment.environmentWith plan
        GeneralPremise.DynamicProvider.empty).language
        (GeneralPlanEnvironment.environmentWith plan GeneralPremise.DynamicProvider.empty).free receipt.job.site.focusBound
        site'.focusType (.collection law.kind (front ++ elements ++ back) none) := by
      rw [← focusBound]; exact ⟨focus'Typed, focus'Metadata, focus'Object, focus'Scope⟩
    obtain ⟨trace', captured', explicit, residual, targetEq, rooted'⟩ :=
      rootFiring_absorbed rooted extended notVector siblingsScoped siblingsObjects sourceSorted' restTyped targetSorted'
    have perm : LawSame (Normalized.laws plan) (.collection law.kind (front ++ (explicit ++ residual) ++ back) none)
        (.collection law.kind (explicit ++ front ++ residual ++ back) none) := by
      refine .rel _ _ (.permute (unordered_of_ne_vec notVector) ?_)
      simp only [List.append_assoc]
      exact (List.perm_append_comm_assoc front explicit (residual ++ back))
    have sameTarget : LawSame (Normalized.laws plan) receipt.target
        (site'.context.fill (.collection law.kind (explicit ++ front ++ residual ++ back) none)) := by
      rw [endpoint, targetEq]; exact fill _ _ perm
    have fired' : GeneralOccurrenceSemantics.Primitive plan bound expected source'
        ⟨⟨receipt.job.ordinal, receipt.job.declaration, site'⟩, trace', captured', captured', receipt.premiseHistory,
          .collection law.kind (explicit ++ front ++ residual ++ back) none,
          site'.context.fill (.collection law.kind (explicit ++ front ++ residual ++ back) none)⟩ := by
      refine ⟨⟨declared, licensed'⟩, ?_, ?_, rfl, ?_⟩
      · simp only [focus', focusBound]; exact rooted'
      · simp only [GeneralTypedSites.SiteData.acceptsReplacementRepresentation]
        rw [← acceptsSame _ _ _ perm, ← targetEq]; exact accepts
      · exact LawSame.openPatternWellSorted admissible.typed sameTarget boundOk expectedOk targetSorted
    obtain ⟨final, firedFinal, sameFinal⟩ := ih _ (by rw [← atDepth]; exact shorter) source' _ rfl source'Sorted fired'
    rw [normal] at firedFinal
    exact ⟨final, firedFinal, .trans _ _ _ sameTarget sameFinal⟩
  | unit law label kind found unit focus =>
    rw [focus] at rooted
    cases rooted with
    | @fire _ _ _ _ _ rule spec _ _ _ _ selected specified _ _ matched _ _ _ _ =>
      obtain ⟨notVariable, notUnit, _⟩ := admissible.descent _ _ declared rule spec selected specified
      rcases matches_constant (GeneralScopedMatchMachine.traced_iff_matches.mp ⟨_, matched⟩) with ⟨name, same⟩ | same
      · exact absurd same (notVariable name)
      · exact absurd same (notUnit kind law label found unit)

/-- Sorted law-normal forms of well-sorted terms are well-sorted. -/
theorem lawNormal_sorted (admissible : DescentAdmissible plan)
    (boundOk : ∀ entry ∈ bound, LawTypeOk (Normalized.laws plan) (GeneralPlanEnvironment.environment plan).language entry)
    (expectedOk : LawTypeOk (Normalized.laws plan) (GeneralPlanEnvironment.environment plan).language expected)
    {term : Pattern}
    (sorted : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language plan.snapshot.free bound expected term) :
    OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language plan.snapshot.free bound expected
      (lawNormal (Normalized.laws plan) term) :=
  openPatternWellSorted_canon (LawSame.openPatternWellSorted admissible.typed (to_normalize _ term) boundOk expectedOk sorted)

/-- **Firings normalize at every well-sorted presentation**, also when reduction lies inside
collections of a flattening kind. -/
theorem firingsNormalize_descent (canonical : CanonicalCoherence.RulesAdmissible plan) (admissible : DescentAdmissible plan)
    (boundOk : ∀ entry ∈ bound, LawTypeOk (Normalized.laws plan) (GeneralPlanEnvironment.environment plan).language entry)
    (expectedOk : LawTypeOk (Normalized.laws plan) (GeneralPlanEnvironment.environment plan).language expected) :
    FiringsNormalizeOn (GeneralOccurrenceSemantics.Equation plan bound expected)
      (StandardStep (Normalized.laws plan) (Normalized.extrusions plan)) (lawNormal (Normalized.laws plan))
      (GeneralOccurrenceSemantics.Primitive plan bound expected) GeneralRuleJobs.Receipt.target
      (OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language plan.snapshot.free bound expected) := by
  intro term receipt sorted fired
  obtain ⟨normalized, firedNormal, lawSame⟩ := primitive_normalize_descent admissible boundOk expectedOk sorted fired
  obtain ⟨canonical', firedCanonical, same⟩ := CanonicalCoherence.primitive_canon canonical firedNormal
  exact ⟨canonical', firedCanonical, .trans _ _ _ (LawCoherence.modelEquiv_of_lawSame lawSame)
    (CanonicalCoherence.modelEquiv_of_same same)⟩

/-- **The canonical explorer is complete for the presented GSLT with reduction inside collections
of a flattening kind**: for a plan without equations or declared extrusions whose laws and rules
are admissible, every state reachable from a well-sorted source by finitely many presented steps
is explored, up to equality in the model. -/
theorem presented_explores_descent (checked : Predecessors.equationsChecked plan = true)
    (noEquations : ∀ left right, ¬ GeneralOccurrenceSemantics.Equation plan bound expected left right)
    (noExtrusions : Normalized.extrusions plan = [])
    (canonical : CanonicalCoherence.RulesAdmissible plan) (admissible : DescentAdmissible plan)
    (boundOk : ∀ entry ∈ bound, LawTypeOk (Normalized.laws plan) (GeneralPlanEnvironment.environment plan).language entry)
    (expectedOk : LawTypeOk (Normalized.laws plan) (GeneralPlanEnvironment.environment plan).language expected)
    (source : Pattern)
    (sorted : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language plan.snapshot.free bound expected source)
    {target : Pattern} (reaches : (Presented.gslt plan bound expected).MultiStep source target) :
    ∃ state, Explore.Explored (S := CanonicalCoherence.search plan bound expected)
        (lawNormal (Normalized.laws plan) source) state ∧
      Presented.ModelEquiv plan bound expected state target := by
  refine CanonicalCoherence.presented_explores_canonical_on checked noEquations noExtrusions
    (good := OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language plan.snapshot.free bound expected)
    ?_ ?_ (firingsNormalize_descent canonical admissible boundOk expectedOk) source
    (lawNormal_sorted admissible boundOk expectedOk sorted) reaches
  · intro a b step
    rcases step with equation | moved
    · exact absurd equation (noEquations _ _)
    · rw [noExtrusions] at moved
      exact (lawStep_of_standardStep moved).openPatternWellSorted_iff admissible.typed boundOk expectedOk
  · intro term receipt fired
    exact lawNormal_sorted admissible boundOk expectedOk fired.2.2.2.2

end Mettapedia.OSLF.MeTTaIL.Complete.DescentCoherence
