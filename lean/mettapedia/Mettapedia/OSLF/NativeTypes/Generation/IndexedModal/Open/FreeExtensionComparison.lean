import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.Classifying
import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.AuthoredNativeFreeExtensionReadout

/-!
# The whole dependent semantic diagram through the bare logical extension

Every generated mixed context and guarded substitution is realized in the
original authored presheaf category. Its entire realization diagram factors
through the existing bare logical extension's unit. The extension-restriction
comparison recovers this diagram naturally, including arbitrary family total
spaces and complete sections. The comparison does not assert that every base
presheaf has a generated syntactic name, nor identify the dependent contextual
model with the bare closed logical syntax.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.FreeExtensionComparison

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Calculi.NativeDependent Calculi.NativeDependent.Refinement
open Mettapedia.CategoryTheory Mettapedia.GSLT.Core
open Mettapedia.OSLF.NativeTypes.Semantics.Presheaf

variable (installed : Joined.Installed)

abbrev authored := installed.semantic.authored installed.indexed
abbrev source := AuthoredProgramReduction.sourceClass (authored installed)

/-- The semantic target has the original authored presheaf carrier. -/
def nativeContexts : (NativeModel (Interpretation.worlds installed)).toCwf.base.Context ⥤
    (source installed).original.closed.Obj where
  obj context := (AuthoredProgramReduction.up (authored installed)).obj context.val
  map arrow := (AuthoredProgramReduction.up (authored installed)).map arrow
  map_id context := (AuthoredProgramReduction.up (authored installed)).map_id context.val
  map_comp first second := (AuthoredProgramReduction.up (authored installed)).map_comp first second

/-- Every generated context, including arbitrary dependent and assumption
suffixes, is retained as an object; arrows are guarded substitution classes. -/
def contexts : Contextual.quotientContext (SourceModel.signature installed) ⥤
    (source installed).original.closed.Obj :=
  Contextual.Interpretation.quotientFunctor (Classifying.qualified installed) ⋙ nativeContexts installed

def adjoinedContexts : Contextual.quotientContext (SourceModel.signature installed) ⥤
    (RelativeClosedBareLogical.freeObject (source installed)).quantified.programTheory.closed.Obj :=
  contexts installed ⋙ (RelativeClosedBareLogical.unitMap (source installed)).closed.functor

variable (target : QuantifiedImplicativeProgramTheory.{1})
    (original : ProgramReductionTheory.Map (source installed).original target.quantified.programTheory)

def readContexts := adjoinedContexts installed ⋙
  (RelativeClosedBareLogical.extension (source installed) target original).functor

/-- The comparison comes from the proved relative universal construction,
not a supplied whole-diagram preservation assumption. -/
def contextComparison : readContexts installed target original ≅
    contexts installed ⋙ original.closed.functor :=
  (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft (contexts installed)
      (RelativeClosedBareLogical.extensionRestriction (source installed) target original).comparison

/-- The square compares each actual guarded substitution, not only closed
program endpoints or a finite list of generated heads. -/
theorem substitution_square {first second : Contextual.quotientContext (SourceModel.signature installed)}
    (mapping : first ⟶ second) :
    (readContexts installed target original).map mapping ≫
        (contextComparison installed target original).hom.app second =
      (contextComparison installed target original).hom.app first ≫
        (contexts installed ⋙ original.closed.functor).map mapping :=
  (contextComparison installed target original).hom.naturality mapping

/-- Conjugating the extension's reading gives the independently supplied
original-context map exactly. -/
theorem substitution_readout {first second : Contextual.quotientContext (SourceModel.signature installed)}
    (mapping : first ⟶ second) :
    (contextComparison installed target original).inv.app first ≫
        (readContexts installed target original).map mapping ≫
        (contextComparison installed target original).hom.app second =
      original.closed.functor.map ((contexts installed).map mapping) := by
  erw [substitution_square, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  rfl

/-- The full semantic context diagram is a consequence of this earned
factorization square on the original program theory. -/
theorem extension_factorization :
    RelativeClosedBareLogical.unit (source installed) ≫
      QuantifiedImplicativeProgramTheory.forgetProgram.map
        (QuantifiedImplicativeProgramTheory.classOf
          (RelativeClosedBareLogical.extension (source installed) target original)) =
      ProgramReductionTheoryIsoClasses.classOf original := by
  rw [← RelativeClosedBareLogical.restrict_as_base_composition]
  exact Quotient.sound ⟨RelativeClosedBareLogical.extensionRestriction (source installed) target original⟩

/-- Any independently supplied logical map commuting on the original theory
is this extension up to its actual compatible map isomorphism class. -/
theorem extension_unique
    (candidate : RelativeClosedBareLogical.freeObject (source installed) ⟶ target)
    (commutes : RelativeClosedBareLogical.unit (source installed) ≫
      QuantifiedImplicativeProgramTheory.forgetProgram.map candidate =
        ProgramReductionTheoryIsoClasses.classOf original) :
    candidate = QuantifiedImplicativeProgramTheory.classOf
      (RelativeClosedBareLogical.extension (source installed) target original) := by
  apply RelativeClosedBareLogical.restrict_injective (source installed) target
  rw [RelativeClosedBareLogical.restrict_as_base_composition,
    RelativeClosedBareLogical.restrict_as_base_composition, commutes,
    extension_factorization]

/-- The factorization exists uniquely. The generated free object is the
actual nontrivial relative syntax with every named constructor and rule. -/
theorem extension_existsUnique :
    ∃! candidate : RelativeClosedBareLogical.freeObject (source installed) ⟶ target,
      RelativeClosedBareLogical.unit (source installed) ≫
        QuantifiedImplicativeProgramTheory.forgetProgram.map candidate =
          ProgramReductionTheoryIsoClasses.classOf original :=
  ⟨QuantifiedImplicativeProgramTheory.classOf
      (RelativeClosedBareLogical.extension (source installed) target original),
    extension_factorization installed target original,
    fun candidate commutes => extension_unique installed target original candidate commutes⟩

/-- Postcomposing the target interpretation and then extending agrees with
extending first and postcomposing. Both maps are independently constructed. -/
theorem extension_postcompose {later : QuantifiedImplicativeProgramTheory.{1}}
    (after : QuantifiedImplicativeProgramTheory.Map target later) :
    QuantifiedImplicativeProgramTheory.classOf
        (RelativeClosedBareLogical.extension (source installed) target original) ≫
        QuantifiedImplicativeProgramTheory.classOf after =
      QuantifiedImplicativeProgramTheory.classOf
        (RelativeClosedBareLogical.extension (source installed) later
          (ProgramReductionTheory.Map.compose original after.underlying)) := by
  apply extension_unique installed later (ProgramReductionTheory.Map.compose original after.underlying)
  rw [Functor.map_comp, ← Category.assoc, extension_factorization]
  rfl

/-- Read any actual semantic arrow through the unit and logical extension.
This includes display projections and complete dependent sections. -/
def arrowReading {before after : (source installed).original.closed.Obj} (arrow : before ⟶ after) :
    original.closed.functor.obj before ⟶ original.closed.functor.obj after :=
  (RelativeClosedBareLogical.extensionRestriction (source installed) target original).comparison.inv.app before ≫
    (RelativeClosedBareLogical.extension (source installed) target original).functor.map
      ((RelativeClosedBareLogical.unitMap (source installed)).closed.functor.map arrow) ≫
    (RelativeClosedBareLogical.extensionRestriction (source installed) target original).comparison.hom.app after

theorem arrowReading_complete {before after : (source installed).original.closed.Obj}
    (arrow : before ⟶ after) :
    arrowReading installed target original arrow = original.closed.functor.map arrow := by
  unfold arrowReading
  erw [(RelativeClosedBareLogical.extensionRestriction (source installed) target original).comparison.hom.naturality arrow,
    ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

/-- The entire displayed section chosen through an arbitrary classifying map
is recovered; no passage to mere inhabitance or endpoint images is made. -/
theorem section_complete {n : Nat} {context : ContextExpr (Interpretation.symbols installed) n}
    {term : TermExpr (Interpretation.symbols installed) n}
    {type : TypeExpr (Interpretation.symbols installed) n}
    (tree : Derivation (SourceModel.signature installed) (.term context term type))
    (scope : Scope (Interpretation.worlds installed) n)
    (meaning : NativeLocalTypeFormers.NativeType scope.1)
    (contextRead : (Interpretation.model installed).evaluateContext context = some scope)
    (typeRead : (Interpretation.model installed).evaluateType scope type = some meaning)
    (mapping : Abstract.ModelMap (Classifying.generated installed) (Classifying.semantic installed)) :
    arrowReading installed target original
      ((AuthoredProgramReduction.up (authored installed)).map
        (DisplayedPresheafComprehension.sectionLift meaning.decoded
          (Classifying.sectionImage tree scope meaning contextRead typeRead mapping))) =
      original.closed.functor.map
        ((AuthoredProgramReduction.up (authored installed)).map
          (DisplayedPresheafComprehension.sectionLift meaning.decoded
            (tree.termSection (Interpretation.model installed) (Interpretation.realization installed)
              (NativeLocalTypeOperations.products_substitution (Interpretation.worlds installed))
              (NativeLocalTypeOperations.products_beta (Interpretation.worlds installed))
              (NativeLocalPiEta.products_eta (Interpretation.worlds installed)) scope meaning contextRead typeRead))) := by
  rw [arrowReading_complete]
  have generatedRead := Classifying.sectionImage_readout tree scope meaning contextRead typeRead mapping
  have nativeRead := tree.termSection_readout (Interpretation.model installed) (Interpretation.realization installed)
    (NativeLocalTypeOperations.products_substitution (Interpretation.worlds installed))
    (NativeLocalTypeOperations.products_beta (Interpretation.worlds installed))
    (NativeLocalPiEta.products_eta (Interpretation.worlds installed)) scope meaning contextRead typeRead
  have equalValues := Option.some.inj (generatedRead.symm.trans nativeRead)
  have equalSections := eq_of_heq (Sigma.mk.inj equalValues).2
  rw [equalSections]

/-- The transported complete value is still a section of its independently
transported display projection, in every qualified target. -/
theorem section_splits
    {base : (Interpretation.worlds installed)ᵒᵖ ⥤ Type}
    (family : NativeLocalTypeFormers.NativeType base) (value : family.decoded.sections) :
    arrowReading installed target original
        ((AuthoredProgramReduction.up (authored installed)).map
          (DisplayedPresheafComprehension.sectionLift family.decoded value)) ≫
      original.closed.functor.map
        ((AuthoredProgramReduction.up (authored installed)).map
          (DisplayedPresheafComprehension.totalProjection family.decoded)) =
      𝟙 (original.closed.functor.obj
        ((AuthoredProgramReduction.up (authored installed)).obj base)) := by
  rw [arrowReading_complete, ← Functor.map_comp, ← Functor.map_comp,
    DisplayedPresheafComprehension.sectionLift_projection]
  exact (congrArg original.closed.functor.map
    ((AuthoredProgramReduction.up (authored installed)).map_id base)).trans
      (original.closed.functor.map_id _)

/-- Equal original arrows after the unit have equal readings in any
qualified target; the whole-arrow comparison supplies the implication. -/
theorem unit_reading_respects {before after : (source installed).original.closed.Obj}
    {first second : before ⟶ after}
    (same : (RelativeClosedBareLogical.unitMap (source installed)).closed.functor.map first =
      (RelativeClosedBareLogical.unitMap (source installed)).closed.functor.map second) :
    original.closed.functor.map first = original.closed.functor.map second := by
  calc
    original.closed.functor.map first = arrowReading installed target original first :=
      (arrowReading_complete installed target original first).symm
    _ = arrowReading installed target original second := by
      unfold arrowReading
      rw [same]
    _ = original.closed.functor.map second := arrowReading_complete installed target original second

/-- In the actual presheaf interpretation, adjoining the logic identifies
no original semantic arrows. Faithfulness follows from the earned retraction. -/
theorem unit_reflects_arrows {before after : (source installed).original.closed.Obj}
    {first second : before ⟶ after}
    (same : (RelativeClosedBareLogical.unitMap (source installed)).closed.functor.map first =
      (RelativeClosedBareLogical.unitMap (source installed)).closed.functor.map second) :
    first = second :=
  unit_reading_respects installed (AuthoredNativeFreeExtensionReadout.target (authored installed))
    (AuthoredNativeFreeExtensionReadout.original (authored installed)) same

/-- The complete dependent section, not just its source and target carrier,
is reflected by the same unit. Distinct witness functions stay distinct. -/
theorem unit_reflects_sections
    {base : (Interpretation.worlds installed)ᵒᵖ ⥤ Type}
    (family : NativeLocalTypeFormers.NativeType base)
    {first second : family.decoded.sections}
    (same : (RelativeClosedBareLogical.unitMap (source installed)).closed.functor.map
        ((AuthoredProgramReduction.up (authored installed)).map
          (DisplayedPresheafComprehension.sectionLift family.decoded first)) =
      (RelativeClosedBareLogical.unitMap (source installed)).closed.functor.map
        ((AuthoredProgramReduction.up (authored installed)).map
          (DisplayedPresheafComprehension.sectionLift family.decoded second))) :
    first = second :=
  DisplayedPresheafComprehension.sectionLift_injective family.decoded
    ((AuthoredProgramReduction.up (authored installed)).map_injective
      (unit_reflects_arrows installed same))

/-- A negative witness is preserved: unequal native responses do not become
equal merely by moving them into the freely adjoined logical presentation. -/
theorem distinct_sections_remain_distinct
    {base : (Interpretation.worlds installed)ᵒᵖ ⥤ Type}
    (family : NativeLocalTypeFormers.NativeType base)
    {first second : family.decoded.sections} (different : first ≠ second) :
    (RelativeClosedBareLogical.unitMap (source installed)).closed.functor.map
        ((AuthoredProgramReduction.up (authored installed)).map
          (DisplayedPresheafComprehension.sectionLift family.decoded first)) ≠
      (RelativeClosedBareLogical.unitMap (source installed)).closed.functor.map
        ((AuthoredProgramReduction.up (authored installed)).map
          (DisplayedPresheafComprehension.sectionLift family.decoded second)) :=
  fun same => different (unit_reflects_sections installed family same)

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.FreeExtensionComparison
