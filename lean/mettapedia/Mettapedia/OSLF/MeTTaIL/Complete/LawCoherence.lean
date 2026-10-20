import Mettapedia.OSLF.MeTTaIL.Complete.CanonicalCoherence
import Mettapedia.OSLF.MeTTaIL.LawNormalFiring

/-!
# The canonical explorer with collection laws

A plan may declare collection laws: flattening of a nested collection of the same kind and
removal of a unit. The canonical explorer commits `lawNormal`, the sorted normal form of these
laws. It is complete for the presented GSLT whenever:

- the laws are strictly typed (`CanonicalBags.LawsTypedStrict`): a collection of a flattening
  kind is built by a homogeneous bare constructor whose category has the unit, and every declared
  type gives such a collection the category of its constructor as element type
  (`CanonicalBags.LawTypeOk`);
- no reduction context lies inside a collection of a flattening kind (`NoLawDescent`);
- every rule fires at canonical and at law-normal forms (`CanonicalCoherence.RulesAdmissible`,
  `LawRulesAdmissible`);
- the plan has no equations and no declared extrusions.

A firing at any presentation is transported first to the law-normal form
(`primitive_normalize`), then to its canonical form (`CanonicalCoherence.primitive_canon`).

- `firingsNormalize_of_laws`: firings normalize, for the sorted normal form of the laws;
- `presented_explores_of_laws`: every state reachable by finitely many presented steps is
  explored, up to equality in the model.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Complete.LawCoherence

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission CanonicalBags Coherence
open Relation (EqvGen)

variable {plan : Plan} {bound : List TypeExpr} {expected : TypeExpr}

variable (plan) in
/-- Every rule of the plan fires at law-normal forms. -/
def LawRulesAdmissible : Prop :=
  ∀ declaration ordinal, (declaration, ordinal) ∈ plan.rules.zipIdx →
    LawFiringAdmissible (Normalized.laws plan) (GeneralPlanEnvironment.environment plan) ordinal

variable (plan) in
/-- The plan's declared laws are strictly typed and lie outside every reduction context. -/
structure LawsAdmissible : Prop where
  typed : LawsTypedStrict (Normalized.laws plan) (GeneralPlanEnvironment.environment plan).language plan.snapshot.free
  noDescent : NoLawDescent (Normalized.laws plan) plan.permissions.sites
  rules : LawRulesAdmissible plan

/-- **Every firing has a counterpart at the law-normal form**, with a law-equal result. -/
theorem primitive_normalize (admissible : LawsAdmissible plan)
    (boundOk : ∀ entry ∈ bound, LawTypeOk (Normalized.laws plan) (GeneralPlanEnvironment.environment plan).language entry)
    (expectedOk : LawTypeOk (Normalized.laws plan) (GeneralPlanEnvironment.environment plan).language expected) {source : Pattern}
    {receipt : GeneralRuleJobs.Receipt} (fired : GeneralOccurrenceSemantics.Primitive plan bound expected source receipt) :
    ∃ receipt', GeneralOccurrenceSemantics.Primitive plan bound expected
        (CollectionLaws.normalize (Normalized.laws plan) source) receipt' ∧
      LawSame (Normalized.laws plan) receipt.target receipt'.target := by
  obtain ⟨⟨declared, licensed⟩, rooted, accepts, endpoint, sorted⟩ := fired
  obtain ⟨site', licensed', focus, focusBound, focusType, frames, fill, acceptsSame⟩ :=
    licensed_normalize admissible.typed.toLawsTyped licensed
      (fun entry member => noNested_of_lawTypeOk (boundOk entry member)) (noNested_of_lawTypeOk expectedOk)
      (pathFlat_of_noDescent admissible.noDescent licensed)
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

/-- Law-equal terms are equal in the model. -/
theorem modelEquiv_of_lawSame {left right : Pattern} (same : LawSame (Normalized.laws plan) left right) :
    EqvGen (fun a b => GeneralOccurrenceSemantics.Equation plan bound expected a b ∨
      StandardStep (Normalized.laws plan) (Normalized.extrusions plan) a b) left right :=
  Relation.EqvGen.mono (fun _ _ step => .inr (.law step)) _ _ same

/-- **Firings normalize** for the sorted normal form of admissible collection laws. -/
theorem firingsNormalize_of_laws (canonical : CanonicalCoherence.RulesAdmissible plan) (admissible : LawsAdmissible plan)
    (boundOk : ∀ entry ∈ bound, LawTypeOk (Normalized.laws plan) (GeneralPlanEnvironment.environment plan).language entry)
    (expectedOk : LawTypeOk (Normalized.laws plan) (GeneralPlanEnvironment.environment plan).language expected) :
    FiringsNormalize (GeneralOccurrenceSemantics.Equation plan bound expected)
      (StandardStep (Normalized.laws plan) (Normalized.extrusions plan)) (lawNormal (Normalized.laws plan))
      (GeneralOccurrenceSemantics.Primitive plan bound expected) GeneralRuleJobs.Receipt.target := by
  intro term receipt fired
  obtain ⟨normalized, firedNormal, lawSame⟩ := primitive_normalize admissible boundOk expectedOk fired
  obtain ⟨canonical', firedCanonical, same⟩ := CanonicalCoherence.primitive_canon canonical firedNormal
  exact ⟨canonical', firedCanonical, .trans _ _ _ (modelEquiv_of_lawSame lawSame)
    (CanonicalCoherence.modelEquiv_of_same same)⟩

/-- **The canonical explorer is complete for the presented GSLT of every plan with admissible
collection laws**, without equations or declared extrusions, whose rules fire at canonical and at
law-normal forms. -/
theorem presented_explores_of_laws (checked : Predecessors.equationsChecked plan = true)
    (noEquations : ∀ left right, ¬ GeneralOccurrenceSemantics.Equation plan bound expected left right)
    (noExtrusions : Normalized.extrusions plan = [])
    (canonical : CanonicalCoherence.RulesAdmissible plan) (admissible : LawsAdmissible plan)
    (boundOk : ∀ entry ∈ bound, LawTypeOk (Normalized.laws plan) (GeneralPlanEnvironment.environment plan).language entry)
    (expectedOk : LawTypeOk (Normalized.laws plan) (GeneralPlanEnvironment.environment plan).language expected) (source : Pattern) {target : Pattern}
    (reaches : (Presented.gslt plan bound expected).MultiStep source target) :
    ∃ state, Explore.Explored (S := CanonicalCoherence.search plan bound expected)
        (lawNormal (Normalized.laws plan) source) state ∧
      Presented.ModelEquiv plan bound expected state target :=
  CanonicalCoherence.presented_explores_canonical checked noEquations noExtrusions
    (firingsNormalize_of_laws canonical admissible boundOk expectedOk) source reaches

end Mettapedia.OSLF.MeTTaIL.Complete.LawCoherence
