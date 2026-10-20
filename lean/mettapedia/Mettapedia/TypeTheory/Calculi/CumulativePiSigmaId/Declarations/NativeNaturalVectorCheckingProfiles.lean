import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorRawPreservation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLExtensionalProfile

/-!
# Explicit checking profiles for the admitted natural/vector package

Three concrete nodes share the cumulative tower and the admitted Nat/Vec
schema table.

* The minimal node retains every typed iota receipt but licenses no iota row
  as conversion.
* The natural intensional node licenses exactly the two natural-number rows.
* The scoped logical-extensional node keeps that computation policy and adds
  the existing opaque proposition- and function-extensionality declarations.

The last node is an actual layered rule package.  Its extensional principles
remain object-theory constants; neither is judgmental equality, UIP, or
equality reflection.  No Hofmann translation is claimed here.  The admitted
iota receipts are metatheoretic typed evidence and are not relabelled as
object-theory equality proofs.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies
namespace Programs.CheckingProfiles

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation Presentation.Declaration Presentation.FormationSensitive
open Presentation.TypedEquality.Annotated
open Declaration.IndexedFamily.Checking

abbrev noIota : ComputationProfiles.Selection :=
  ComputationProfiles.NaturalConversion.RawPreservation.Formation.noIota

abbrev Contract := Profile Checking.schemas

def naturalZeroIndex : Fin Checking.table.length := ⟨0, by decide⟩

def vectorNilIndex : Fin Checking.table.length := ⟨2, by decide⟩

/-- The cumulative profile permits elimination into every declared tower
universe and never treats the legacy ground head as a universe. -/
def towerEliminationTarget : Tower.Head → Bool
  | .legacyGround => false
  | .sort _ => true

def noOptionalIdentity : IdentityPrinciple → PrinciplePolicy :=
  fun _ => ⟨false, false⟩

/-- Exactly the two existing logical extensionality declarations are
propositional.  They do not enter conversion. -/
def scopedLogicalIdentity : IdentityPrinciple → PrinciplePolicy
  | .propositionExtensionality => ⟨true, false⟩
  | .functionExtensionality => ⟨true, false⟩
  | _ => ⟨false, false⟩

/-- Every admitted row retains its typed source receipt.  The selected Boolean
controls only judgmental conversion; no object-level equality proof is added. -/
def retainedRow (enabled : ComputationProfiles.Selection)
    (index : Fin Checking.table.length) : EquationPolicy :=
  ⟨true, false, enabled index⟩

def minimal : Contract where
  eliminationTarget := towerEliminationTarget
  identity := noOptionalIdentity
  iota := retainedRow noIota
  judgmentalHasReceipt := by
    intro index _licensed
    rfl

def naturalIntensional : Contract where
  eliminationTarget := towerEliminationTarget
  identity := noOptionalIdentity
  iota := retainedRow ComputationProfiles.naturalOnly
  judgmentalHasReceipt := by
    intro index _licensed
    rfl

def scopedLogicalExtensional : Contract where
  eliminationTarget := towerEliminationTarget
  identity := scopedLogicalIdentity
  iota := retainedRow ComputationProfiles.naturalOnly
  judgmentalHasReceipt := by
    intro index _licensed
    rfl

/-- The original four-row relation as an operational node.  Its vector rows
are not thereby installed in the natural-only annotated checking judgment. -/
def fullRawOperational : Contract where
  eliminationTarget := towerEliminationTarget
  identity := noOptionalIdentity
  iota := retainedRow (fun _ => true)
  judgmentalHasReceipt := by
    intro index _licensed
    rfl

theorem minimal_extends_naturalIntensional :
    minimal.Extends naturalIntensional where
  elimination := fun _ known => known
  identityPropositional := by
    intro principle known
    cases principle <;> simp [minimal, noOptionalIdentity] at known
  identityJudgmental := by
    intro principle known
    cases principle <;> simp [minimal, noOptionalIdentity] at known
  iotaReceipt := fun _ _ => rfl
  iotaPropositional := by
    intro index known
    simp [minimal, retainedRow] at known
  iotaJudgmental := by
    intro index known
    simp [minimal, retainedRow, noIota,
      ComputationProfiles.NaturalConversion.RawPreservation.Formation.noIota] at known

theorem naturalIntensional_extends_scopedLogicalExtensional :
    naturalIntensional.Extends scopedLogicalExtensional where
  elimination := fun _ known => known
  identityPropositional := by
    intro principle known
    cases principle <;> simp [naturalIntensional, noOptionalIdentity] at known
  identityJudgmental := by
    intro principle known
    cases principle <;> simp [naturalIntensional, noOptionalIdentity] at known
  iotaReceipt := fun _ known => known
  iotaPropositional := fun _ known => known
  iotaJudgmental := fun _ known => known

theorem naturalIntensional_extends_fullRawOperational :
    naturalIntensional.Extends fullRawOperational where
  elimination := fun _ known => known
  identityPropositional := fun _ known => known
  identityJudgmental := fun _ known => known
  iotaReceipt := fun _ known => known
  iotaPropositional := fun _ known => known
  iotaJudgmental := fun _ _ => rfl

/-- The natural conversion node is strictly above the minimal node on the
judgmental axis. -/
theorem not_naturalIntensional_extends_minimal :
    ¬ naturalIntensional.Extends minimal := by
  intro extension
  have licensed : (naturalIntensional.iota naturalZeroIndex).judgmental = true := by
    decide
  have impossible := extension.iotaJudgmental naturalZeroIndex licensed
  exact Bool.noConfusion impossible

/-- The logical-extensional node is strictly above the intensional node on
the propositional-principle axis. -/
theorem not_scopedLogicalExtensional_extends_naturalIntensional :
    ¬ scopedLogicalExtensional.Extends naturalIntensional := by
  intro extension
  have available :
      (scopedLogicalExtensional.identity
        .propositionExtensionality).propositional = true := rfl
  have impossible := extension.identityPropositional
    .propositionExtensionality available
  exact Bool.noConfusion impossible

/-- The two richer children of the natural node are incomparable: one adds
logical propositions, while the other adds raw operational conversion. -/
theorem not_scopedLogicalExtensional_extends_fullRawOperational :
    ¬ scopedLogicalExtensional.Extends fullRawOperational := by
  intro extension
  have available :
      (scopedLogicalExtensional.identity
        .propositionExtensionality).propositional = true := rfl
  have impossible := extension.identityPropositional
    .propositionExtensionality available
  exact Bool.noConfusion impossible

theorem not_fullRawOperational_extends_scopedLogicalExtensional :
    ¬ fullRawOperational.Extends scopedLogicalExtensional := by
  intro extension
  have licensed : (fullRawOperational.iota vectorNilIndex).judgmental = true := rfl
  have impossible := extension.iotaJudgmental vectorNilIndex licensed
  exact Bool.noConfusion impossible

theorem natural_profile_fork :
    naturalIntensional.Extends scopedLogicalExtensional ∧
      naturalIntensional.Extends fullRawOperational ∧
      ¬ scopedLogicalExtensional.Extends fullRawOperational ∧
      ¬ fullRawOperational.Extends scopedLogicalExtensional :=
  ⟨naturalIntensional_extends_scopedLogicalExtensional,
    naturalIntensional_extends_fullRawOperational,
    not_scopedLogicalExtensional_extends_fullRawOperational,
    not_fullRawOperational_extends_scopedLogicalExtensional⟩

theorem minimal_enabled_eq : minimal.enabled = noIota := by
  funext index
  rfl

theorem naturalIntensional_enabled_eq :
    naturalIntensional.enabled = ComputationProfiles.naturalOnly := by
  funext index
  rfl

theorem scoped_enabled_eq :
    scopedLogicalExtensional.enabled = ComputationProfiles.naturalOnly := by
  funext index
  rfl

theorem fullRawOperational_enabled_eq :
    fullRawOperational.enabled = (fun _ => true) := by
  funext index
  rfl

/-- The operational child is sound against the natural checking judgment. -/
theorem fullRawOperational_preserves_naturalChecking :
    FormationSensitive.RootPreservationAgainst
      ComputationProfiles.NaturalConversion.Preservation.selectedRules Programs.rules :=
  ComputationProfiles.NaturalConversion.Preservation.operational_preservation_against

/-- The operational child has no unrestricted realization as annotated
schema conversion, because annotation erasure identifies repeated payloads. -/
theorem fullRawOperational_not_unrestrictedAnnotatedLift :
    ¬ ∀ {n : Nat} (left : CTm Tower.Head n) (right : Tower.Tm n),
      (ComputationProfiles.rules (fun _ => true)).computation.step left.erase right →
        ∃ result, (Annotated.church (fun _ => true)).computation.step left result ∧
          result.erase = right :=
  Annotated.RepeatedParameterCanary.unrestricted_lifting_fails

/-! ## The actual layered logical-extensional node -/

abbrev logicalRules := FormationSensitiveHOLExtensionalProfile.rules

/-- Add the selected Nat/Vec declarations above the maintained logical
extensional rules.  Base declarations retain priority. -/
def scopedRules : Rules Tower.Head :=
  extendRules logicalRules
    (ComputationProfiles.signature ComputationProfiles.naturalOnly)

/-- A selected natural declaration never collides with the maintained HOL
logical and extensional declarations. -/
theorem logicalRules_absent_for_natural
    {name : DeclName} {type : Tower.Tm 0}
    (known : (ComputationProfiles.signature
      ComputationProfiles.naturalOnly).typeOf? name = some type) :
    logicalRules.constantType name = none := by
  obtain ⟨level, member⟩ :=
    ComputationProfiles.NaturalConversion.RawPreservation.Formation.lookup_covered known
  simp [ComputationProfiles.NaturalConversion.RawPreservation.Formation.requests] at member
  rcases member with member | member | member | member | member | member | member | member
  all_goals
    rcases member with ⟨rfl, rfl⟩
    decide

/-- The selected natural checker embeds in the layered node.  The proof keeps
the original natural declarations and roots; the logical layer contributes
only inherited computation and fresh declarations. -/
theorem naturalToScopedMorphism :
    (ComputationProfiles.rules ComputationProfiles.naturalOnly).Morphism
      scopedRules (fun head => head) where
  headTyping := fun known => known
  isUniverse := fun known => known
  join := fun known => known
  cumulative := fun known => known
  headEq := fun known => known
  constantType := by
    intro name type known
    simp only [Tm.mapHead_id]
    change combinedType Tower.rules
      (ComputationProfiles.signature ComputationProfiles.naturalOnly) name =
        some type at known
    change combinedType logicalRules
      (ComputationProfiles.signature ComputationProfiles.naturalOnly) name =
        some type
    have towerAbsent : Tower.rules.constantType name = none := rfl
    simp only [combinedType, towerAbsent] at known
    rw [combinedType, logicalRules_absent_for_natural known, known]
  computation := by
    intro n left right step
    simp only [Tm.mapHead_id]
    change RootStep Tower.rules
      (ComputationProfiles.signature ComputationProfiles.naturalOnly) n left right at step
    change RootStep logicalRules
      (ComputationProfiles.signature ComputationProfiles.naturalOnly) n left right
    cases step with
    | inherited inherited =>
        exact .inherited (by
          change (extendRules Tower.rules
            FormationSensitiveHOLExtensionalProfile.declarations).computation.step
              left right
          simpa only [Tm.mapHead_id] using
            (includeMorphism Tower.rules
              FormationSensitiveHOLExtensionalProfile.declarations).computation inherited)
    | delta known => exact .delta known
    | declared known => exact .declared known

/-- The existing extensional declarations embed into the same layered node. -/
theorem logicalToScopedMorphism :
    logicalRules.Morphism scopedRules (fun head => head) :=
  includeMorphism logicalRules
    (ComputationProfiles.signature ComputationProfiles.naturalOnly)

theorem scoped_propositionExtensionality_typed {n : Nat} (context : Tower.Ctx n) :
    Typing scopedRules context
      (.const FormationSensitiveHOLExtensionalProfile.propositionExtensionalityName)
      (liftClosed FormationSensitiveHOLExtensionalProfile.propositionExtensionalityType) := by
  simpa only [Ctx.mapHead_id, Tm.mapHead_id] using
    (FormationSensitiveHOLExtensionalProfile.propositionExtensionality_typed context).mapHead
      logicalToScopedMorphism

theorem scoped_functionExtensionality_typed {n : Nat} (context : Tower.Ctx n) :
    Typing scopedRules context
      (.const FormationSensitiveHOLExtensionalProfile.functionExtensionalityName)
      (liftClosed FormationSensitiveHOLExtensionalProfile.functionExtensionalityType) := by
  simpa only [Ctx.mapHead_id, Tm.mapHead_id] using
    (FormationSensitiveHOLExtensionalProfile.functionExtensionality_typed context).mapHead
      logicalToScopedMorphism

theorem append_typed_naturalIntensional :
    Judgment (ComputationProfiles.rules ComputationProfiles.naturalOnly)
      .nil appendTerm appendType :=
  ComputationProfiles.append_typed_naturalOnly

theorem append_typed_scopedLogicalExtensional :
    Judgment scopedRules .nil appendTerm appendType := by
  simpa only [Ctx.mapHead_id, Tm.mapHead_id] using
    append_typed_naturalIntensional.mapHead naturalToScopedMorphism

/-! ## Positive and negative profile requests -/

theorem motive_universe_permitted :
    naturalIntensional.eliminationTarget (.sort motiveLevel) = true := rfl

theorem legacy_ground_not_elimination_target :
    naturalIntensional.eliminationTarget .legacyGround = false := rfl

theorem no_iota_is_object_propositional (index : Fin Checking.table.length) :
    (scopedLogicalExtensional.iota index).propositional = false := rfl

theorem scoped_extensionality_not_judgmental :
    (scopedLogicalExtensional.identity
        .propositionExtensionality).judgmental = false ∧
      (scopedLogicalExtensional.identity
        .functionExtensionality).judgmental = false :=
  ⟨rfl, rfl⟩

theorem scoped_has_neither_uip_nor_equalityReflection :
    scopedLogicalExtensional.identity .uip = ⟨false, false⟩ ∧
      scopedLogicalExtensional.identity .equalityReflection = ⟨false, false⟩ :=
  ⟨rfl, rfl⟩

def verdicts : List (String × Bool) := [
  ("minimal profile refuses dependent append evidence",
    !(ComputationProfiles.replay noIota)),
  ("natural intensional profile checks dependent append",
    ComputationProfiles.replay ComputationProfiles.naturalOnly),
  ("minimal retains natural zero receipt",
    (minimal.iota naturalZeroIndex).receipt),
  ("minimal does not license natural zero conversion",
    !(minimal.iota naturalZeroIndex).judgmental),
  ("intensional licenses natural zero conversion",
    (naturalIntensional.iota naturalZeroIndex).judgmental),
  ("intensional refuses vector nil conversion",
    !(naturalIntensional.iota vectorNilIndex).judgmental),
  ("full raw operational node licenses vector nil",
    (fullRawOperational.iota vectorNilIndex).judgmental),
  ("scoped node exposes proposition extensionality propositionally",
    (scopedLogicalExtensional.identity
      .propositionExtensionality).propositional),
  ("scoped node keeps proposition extensionality out of conversion",
    !(scopedLogicalExtensional.identity
      .propositionExtensionality).judgmental),
  ("scoped node omits UIP",
    !(scopedLogicalExtensional.identity .uip).propositional),
  ("legacy ground is not an elimination target",
    !(naturalIntensional.eliminationTarget .legacyGround))]

theorem all_verdicts : verdicts.all (·.2) = true := by decide +kernel

#print axioms minimal_extends_naturalIntensional
#print axioms naturalIntensional_extends_scopedLogicalExtensional
#print axioms naturalIntensional_extends_fullRawOperational
#print axioms not_naturalIntensional_extends_minimal
#print axioms not_scopedLogicalExtensional_extends_naturalIntensional
#print axioms not_scopedLogicalExtensional_extends_fullRawOperational
#print axioms not_fullRawOperational_extends_scopedLogicalExtensional
#print axioms natural_profile_fork
#print axioms fullRawOperational_preserves_naturalChecking
#print axioms fullRawOperational_not_unrestrictedAnnotatedLift
#print axioms logicalRules_absent_for_natural
#print axioms naturalToScopedMorphism
#print axioms scoped_propositionExtensionality_typed
#print axioms scoped_functionExtensionality_typed
#print axioms append_typed_naturalIntensional
#print axioms append_typed_scopedLogicalExtensional
#print axioms all_verdicts

end Programs.CheckingProfiles
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies
