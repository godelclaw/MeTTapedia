import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorCheckingProfileInteraction
import Mettapedia.Languages.MeTTa.Bridges.GSLT.FinitePolicyAtomWire

/-!
# Nat/Vec checking profiles as finite MeTTa data

The admitted Nat/Vec package already has one profile contract separating
elimination targets, optional identity principles, retained typed iota
receipts, object-theory propositions and judgmental computation.  This module
gives that contract a finite first-order boundary in the existing MeTTa
`Atom` carrier.

A manifest requests capabilities; it is not a theorem claim. Validation checks
the one generic authority law of the profile record: every judgmental iota row
must retain its typed receipt. The decoder also checks every submitted table
index. Optional identity fields still require a calculus-specific realization
theorem. Successful validation selects the existing schema table and checker;
it does not reconstruct a second Nat/Vec calculus.

The wire does not establish normalization, confluence, conservativity, UIP,
equality reflection, a Hofmann translation or native runtime qualification.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.NatVecCheckingProfileAtomWire

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.Bridges.GSLT.FinitePolicyAtomWire
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Declaration
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Declaration.IndexedFamily.Checking
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies
open AlgebraicSchema ComputationAuthority

namespace Profiles

open Programs Programs.CheckingProfiles

abbrev Contract := Programs.CheckingProfiles.Contract
abbrev RowIndex := Fin Checking.table.length

/-- Finite capabilities of the concrete cumulative Nat/Vec checking profile.
Tower universes share one flag; legacy ground remains separately visible. -/
inductive Feature where
  | eliminateLegacyGround
  | eliminateTowerSorts
  | identityPropositional (principle : IdentityPrinciple)
  | identityJudgmental (principle : IdentityPrinciple)
  | iotaReceipt (index : RowIndex)
  | iotaPropositional (index : RowIndex)
  | iotaJudgmental (index : RowIndex)
  deriving DecidableEq, Repr

abbrev Manifest := List Feature

def enabled (manifest : Manifest) (feature : Feature) : Bool :=
  decide (feature ∈ manifest)

def join (first second : Manifest) : Manifest :=
  (first ++ second).eraseDups

@[simp] theorem enabled_join (first second : Manifest) (feature : Feature) :
    enabled (join first second) feature =
      (enabled first feature || enabled second feature) := by
  simp [enabled, join]

/-- The only generic authority law needed to construct the existing profile:
judgmental use of a row requires its retained typed receipt. -/
def Valid (manifest : Manifest) : Prop :=
  ∀ index,
    enabled manifest (.iotaJudgmental index) = true →
      enabled manifest (.iotaReceipt index) = true

instance validDecidable (manifest : Manifest) : Decidable (Valid manifest) := by
  unfold Valid
  infer_instance

def validCheck (manifest : Manifest) : Bool := decide (Valid manifest)

theorem validCheck_eq_true_iff (manifest : Manifest) :
    validCheck manifest = true ↔ Valid manifest := by
  simp [validCheck]

theorem valid_join {first second : Manifest}
    (firstValid : Valid first) (secondValid : Valid second) :
    Valid (join first second) := by
  intro index judgmental
  simp only [enabled_join, Bool.or_eq_true] at judgmental ⊢
  rcases judgmental with fromFirst | fromSecond
  · exact Or.inl (firstValid index fromFirst)
  · exact Or.inr (secondValid index fromSecond)

def eliminationTarget (manifest : Manifest) : Tower.Head → Bool
  | .legacyGround => enabled manifest .eliminateLegacyGround
  | .sort _ => enabled manifest .eliminateTowerSorts

def identityPolicy (manifest : Manifest)
    (principle : IdentityPrinciple) : PrinciplePolicy :=
  ⟨enabled manifest (.identityPropositional principle),
    enabled manifest (.identityJudgmental principle)⟩

def equationPolicy (manifest : Manifest) (index : RowIndex) : EquationPolicy :=
  ⟨enabled manifest (.iotaReceipt index),
    enabled manifest (.iotaPropositional index),
    enabled manifest (.iotaJudgmental index)⟩

/-- Interpret a validated finite manifest as the existing checking-profile
record over the one admitted Nat/Vec schema table. -/
def denote (manifest : Manifest) (valid : Valid manifest) : Contract where
  eliminationTarget := eliminationTarget manifest
  identity := identityPolicy manifest
  iota := equationPolicy manifest
  judgmentalHasReceipt := valid

/-- Reject an unsafe capability set instead of manufacturing the proof field
required by the checking profile. -/
def validate (manifest : Manifest) : Option Contract :=
  if valid : Valid manifest then some (denote manifest valid) else none

theorem validate_isSome_iff (manifest : Manifest) :
    (validate manifest).isSome = true ↔ Valid manifest := by
  simp [validate]

theorem validate_eq_none_iff (manifest : Manifest) :
    validate manifest = none ↔ ¬ Valid manifest := by
  simp [validate]

/-- Adding capabilities preserves the concrete checking-profile order. -/
theorem denote_extends_join_left {first second : Manifest}
    (firstValid : Valid first) (secondValid : Valid second) :
    (denote first firstValid).Extends
      (denote (join first second) (valid_join firstValid secondValid)) where
  elimination := by
    intro head known
    cases head with
    | legacyGround =>
        change enabled (join first second) .eliminateLegacyGround = true
        change enabled first .eliminateLegacyGround = true at known
        simp [enabled_join, known]
    | sort level =>
        change enabled (join first second) .eliminateTowerSorts = true
        change enabled first .eliminateTowerSorts = true at known
        simp [enabled_join, known]
  identityPropositional := by
    intro principle known
    change enabled (join first second) (.identityPropositional principle) = true
    change enabled first (.identityPropositional principle) = true at known
    simp [enabled_join, known]
  identityJudgmental := by
    intro principle known
    change enabled (join first second) (.identityJudgmental principle) = true
    change enabled first (.identityJudgmental principle) = true at known
    simp [enabled_join, known]
  iotaReceipt := by
    intro index known
    change enabled (join first second) (.iotaReceipt index) = true
    change enabled first (.iotaReceipt index) = true at known
    simp [enabled_join, known]
  iotaPropositional := by
    intro index known
    change enabled (join first second) (.iotaPropositional index) = true
    change enabled first (.iotaPropositional index) = true at known
    simp [enabled_join, known]
  iotaJudgmental := by
    intro index known
    change enabled (join first second) (.iotaJudgmental index) = true
    change enabled first (.iotaJudgmental index) = true at known
    simp [enabled_join, known]

theorem denote_extends_join_right {first second : Manifest}
    (firstValid : Valid first) (secondValid : Valid second) :
    (denote second secondValid).Extends
      (denote (join first second) (valid_join firstValid secondValid)) where
  elimination := by
    intro head known
    cases head with
    | legacyGround =>
        change enabled (join first second) .eliminateLegacyGround = true
        change enabled second .eliminateLegacyGround = true at known
        simp [enabled_join, known]
    | sort level =>
        change enabled (join first second) .eliminateTowerSorts = true
        change enabled second .eliminateTowerSorts = true at known
        simp [enabled_join, known]
  identityPropositional := by
    intro principle known
    change enabled (join first second) (.identityPropositional principle) = true
    change enabled second (.identityPropositional principle) = true at known
    simp [enabled_join, known]
  identityJudgmental := by
    intro principle known
    change enabled (join first second) (.identityJudgmental principle) = true
    change enabled second (.identityJudgmental principle) = true at known
    simp [enabled_join, known]
  iotaReceipt := by
    intro index known
    change enabled (join first second) (.iotaReceipt index) = true
    change enabled second (.iotaReceipt index) = true at known
    simp [enabled_join, known]
  iotaPropositional := by
    intro index known
    change enabled (join first second) (.iotaPropositional index) = true
    change enabled second (.iotaPropositional index) = true at known
    simp [enabled_join, known]
  iotaJudgmental := by
    intro index known
    change enabled (join first second) (.iotaJudgmental index) = true
    change enabled second (.iotaJudgmental index) = true at known
    simp [enabled_join, known]

/-! ## Lossless atom wire -/

def encodeIdentityPrinciple : IdentityPrinciple → Atom
  | .elimination => .symbol "natvec-identity-elimination-v1"
  | .propositionExtensionality => .symbol "natvec-identity-propext-v1"
  | .functionExtensionality => .symbol "natvec-identity-funext-v1"
  | .uip => .symbol "natvec-identity-uip-v1"
  | .equalityReflection => .symbol "natvec-identity-reflection-v1"

def decodeIdentityPrinciple : Atom → Option IdentityPrinciple
  | .symbol "natvec-identity-elimination-v1" => some .elimination
  | .symbol "natvec-identity-propext-v1" => some .propositionExtensionality
  | .symbol "natvec-identity-funext-v1" => some .functionExtensionality
  | .symbol "natvec-identity-uip-v1" => some .uip
  | .symbol "natvec-identity-reflection-v1" => some .equalityReflection
  | _ => none

@[simp] theorem decodeIdentityPrinciple_encodeIdentityPrinciple
    (principle : IdentityPrinciple) :
    decodeIdentityPrinciple (encodeIdentityPrinciple principle) = some principle := by
  cases principle <;> rfl

def encodeFeature : Feature → Atom
  | .eliminateLegacyGround => .symbol "natvec-eliminate-legacy-ground-v1"
  | .eliminateTowerSorts => .symbol "natvec-eliminate-tower-sorts-v1"
  | .identityPropositional principle =>
      .expression [.symbol "natvec-identity-propositional-v1",
        encodeIdentityPrinciple principle]
  | .identityJudgmental principle =>
      .expression [.symbol "natvec-identity-judgmental-v1",
        encodeIdentityPrinciple principle]
  | .iotaReceipt index =>
      .expression [.symbol "natvec-iota-receipt-v1", encodeFin index]
  | .iotaPropositional index =>
      .expression [.symbol "natvec-iota-propositional-v1", encodeFin index]
  | .iotaJudgmental index =>
      .expression [.symbol "natvec-iota-judgmental-v1", encodeFin index]

def decodeFeature : Atom → Option Feature
  | .symbol "natvec-eliminate-legacy-ground-v1" => some .eliminateLegacyGround
  | .symbol "natvec-eliminate-tower-sorts-v1" => some .eliminateTowerSorts
  | .expression [.symbol "natvec-identity-propositional-v1", principle] =>
      .identityPropositional <$> decodeIdentityPrinciple principle
  | .expression [.symbol "natvec-identity-judgmental-v1", principle] =>
      .identityJudgmental <$> decodeIdentityPrinciple principle
  | .expression [.symbol "natvec-iota-receipt-v1", index] =>
      .iotaReceipt <$> decodeFin Checking.table.length index
  | .expression [.symbol "natvec-iota-propositional-v1", index] =>
      .iotaPropositional <$> decodeFin Checking.table.length index
  | .expression [.symbol "natvec-iota-judgmental-v1", index] =>
      .iotaJudgmental <$> decodeFin Checking.table.length index
  | _ => none

@[simp] theorem decodeFeature_encodeFeature (feature : Feature) :
    decodeFeature (encodeFeature feature) = some feature := by
  cases feature <;> simp [encodeFeature, decodeFeature]

def encode (manifest : Manifest) : Atom :=
  .expression (.symbol "natvec-checking-profile-v1" :: manifest.map encodeFeature)

def decode : Atom → Option Manifest
  | .expression (.symbol "natvec-checking-profile-v1" :: features) =>
      features.mapM decodeFeature
  | _ => none

private theorem mapM_decodeFeature_encodeFeature (manifest : Manifest) :
    (manifest.map encodeFeature).mapM decodeFeature = some manifest := by
  induction manifest with
  | nil => rfl
  | cons feature manifest ih => simp [ih]

@[simp] theorem decode_encode (manifest : Manifest) :
    decode (encode manifest) = some manifest :=
  mapM_decodeFeature_encodeFeature manifest

theorem encode_injective : Function.Injective encode := by
  intro first second same
  have decoded := congrArg decode same
  simpa only [decode_encode, Option.some.injEq] using decoded

def decodeValidated (atom : Atom) : Option Contract := do
  validate (← decode atom)

@[simp] theorem decodeValidated_encode (manifest : Manifest) :
    decodeValidated (encode manifest) = validate manifest := by
  simp [decodeValidated]

/-- Join only two decodable, individually valid manifests.  Their union is
valid by the checked feature-inclusion theorem above. -/
def joinEncoded (first second : Atom) : Option Atom := do
  let firstManifest ← decode first
  let secondManifest ← decode second
  if Valid firstManifest ∧ Valid secondManifest then
    some (encode (join firstManifest secondManifest))
  else none

theorem joinEncoded_encode {first second : Manifest}
    (firstValid : Valid first) (secondValid : Valid second) :
    joinEncoded (encode first) (encode second) =
      some (encode (join first second)) := by
  simp [joinEncoded, firstValid, secondValid]

theorem joinEncoded_sound {firstCode secondCode output : Atom}
    (accepted : joinEncoded firstCode secondCode = some output) :
    ∃ first second : Manifest,
      decode firstCode = some first ∧
      decode secondCode = some second ∧
      Valid first ∧ Valid second ∧
      output = encode (join first second) := by
  unfold joinEncoded at accepted
  cases firstDecoded : decode firstCode with
  | none => simp [firstDecoded] at accepted
  | some first =>
      cases secondDecoded : decode secondCode with
      | none => simp [firstDecoded, secondDecoded] at accepted
      | some second =>
          by_cases valid : Valid first ∧ Valid second
          · simp [firstDecoded, secondDecoded, valid] at accepted
            exact ⟨first, second, rfl, rfl, valid.1, valid.2, accepted.symm⟩
          · simp [firstDecoded, secondDecoded, valid] at accepted

/-! ## The four maintained profile nodes -/

def naturalZeroIndex : RowIndex := ⟨0, by decide⟩
def naturalSuccIndex : RowIndex := ⟨1, by decide⟩
def vectorNilIndex : RowIndex := ⟨2, by decide⟩
def vectorConsIndex : RowIndex := ⟨3, by decide⟩

/-- The least package retains all four admitted typed receipts and permits
elimination into tower universes.  It grants no judgmental iota step. -/
def minimalManifest : Manifest := [
  .eliminateTowerSorts,
  .iotaReceipt naturalZeroIndex,
  .iotaReceipt naturalSuccIndex,
  .iotaReceipt vectorNilIndex,
  .iotaReceipt vectorConsIndex]

/-- A self-contained feature package for the two natural computation rows. -/
def naturalIotaPackage : Manifest := [
  .iotaReceipt naturalZeroIndex,
  .iotaReceipt naturalSuccIndex,
  .iotaJudgmental naturalZeroIndex,
  .iotaJudgmental naturalSuccIndex]

/-- The existing scoped extensional principles are propositions only. -/
def logicalExtensionalPackage : Manifest := [
  .identityPropositional .propositionExtensionality,
  .identityPropositional .functionExtensionality]

/-- A self-contained feature package for the two vector computation rows. -/
def vectorIotaPackage : Manifest := [
  .iotaReceipt vectorNilIndex,
  .iotaReceipt vectorConsIndex,
  .iotaJudgmental vectorNilIndex,
  .iotaJudgmental vectorConsIndex]

def naturalIntensionalManifest : Manifest :=
  join minimalManifest naturalIotaPackage

def scopedLogicalExtensionalManifest : Manifest :=
  join naturalIntensionalManifest logicalExtensionalPackage

def fullRawOperationalManifest : Manifest :=
  join naturalIntensionalManifest vectorIotaPackage

theorem minimalManifest_valid : Valid minimalManifest := by decide
theorem naturalIotaPackage_valid : Valid naturalIotaPackage := by decide
theorem logicalExtensionalPackage_valid : Valid logicalExtensionalPackage := by decide
theorem vectorIotaPackage_valid : Valid vectorIotaPackage := by decide

theorem naturalIntensionalManifest_valid : Valid naturalIntensionalManifest :=
  valid_join minimalManifest_valid naturalIotaPackage_valid

theorem scopedLogicalExtensionalManifest_valid :
    Valid scopedLogicalExtensionalManifest :=
  valid_join naturalIntensionalManifest_valid logicalExtensionalPackage_valid

theorem fullRawOperationalManifest_valid : Valid fullRawOperationalManifest :=
  valid_join naturalIntensionalManifest_valid vectorIotaPackage_valid

/-- Profiles with the same observable fields are equal; their authority law
is proof-irrelevant. -/
theorem contract_ext {first second : Contract}
    (elimination : first.eliminationTarget = second.eliminationTarget)
    (identity : first.identity = second.identity)
    (iota : first.iota = second.iota) : first = second := by
  cases first
  cases second
  cases elimination
  cases identity
  cases iota
  rfl

theorem denote_minimal_eq :
    denote minimalManifest minimalManifest_valid =
      Programs.CheckingProfiles.minimal := by
  apply contract_ext
  · funext head
    cases head <;>
      simp [denote, eliminationTarget, minimalManifest,
        Programs.CheckingProfiles.minimal,
        Programs.CheckingProfiles.towerEliminationTarget, enabled]
  · funext principle
    cases principle <;>
      decide
  · funext index
    fin_cases index <;>
      decide

theorem denote_naturalIntensional_eq :
    denote naturalIntensionalManifest naturalIntensionalManifest_valid =
      Programs.CheckingProfiles.naturalIntensional := by
  apply contract_ext
  · funext head
    cases head <;>
      simp [denote, eliminationTarget, naturalIntensionalManifest,
        minimalManifest, naturalIotaPackage, join,
        Programs.CheckingProfiles.naturalIntensional,
        Programs.CheckingProfiles.towerEliminationTarget, enabled]
  · funext principle
    cases principle <;>
      decide
  · funext index
    fin_cases index <;>
      decide

theorem denote_scopedLogicalExtensional_eq :
    denote scopedLogicalExtensionalManifest
        scopedLogicalExtensionalManifest_valid =
      Programs.CheckingProfiles.scopedLogicalExtensional := by
  apply contract_ext
  · funext head
    cases head <;>
      simp [denote, eliminationTarget, scopedLogicalExtensionalManifest,
        naturalIntensionalManifest, minimalManifest, naturalIotaPackage,
        logicalExtensionalPackage, join,
        Programs.CheckingProfiles.scopedLogicalExtensional,
        Programs.CheckingProfiles.towerEliminationTarget, enabled]
  · funext principle
    cases principle <;>
      decide
  · funext index
    fin_cases index <;>
      decide

theorem denote_fullRawOperational_eq :
    denote fullRawOperationalManifest fullRawOperationalManifest_valid =
      Programs.CheckingProfiles.fullRawOperational := by
  apply contract_ext
  · funext head
    cases head <;>
      simp [denote, eliminationTarget, fullRawOperationalManifest,
        naturalIntensionalManifest, minimalManifest, naturalIotaPackage,
        vectorIotaPackage, join,
        Programs.CheckingProfiles.fullRawOperational,
        Programs.CheckingProfiles.towerEliminationTarget, enabled]
  · funext principle
    cases principle <;>
      decide
  · funext index
    fin_cases index <;>
      decide

theorem minimal_encoded_validated :
    decodeValidated (encode minimalManifest) =
      some Programs.CheckingProfiles.minimal := by
  rw [decodeValidated_encode]
  simp only [validate, minimalManifest_valid, dite_true]
  rw [denote_minimal_eq]

theorem naturalIntensional_encoded_validated :
    decodeValidated (encode naturalIntensionalManifest) =
      some Programs.CheckingProfiles.naturalIntensional := by
  rw [decodeValidated_encode]
  simp only [validate, naturalIntensionalManifest_valid, dite_true]
  rw [denote_naturalIntensional_eq]

theorem scopedLogicalExtensional_encoded_validated :
    decodeValidated (encode scopedLogicalExtensionalManifest) =
      some Programs.CheckingProfiles.scopedLogicalExtensional := by
  rw [decodeValidated_encode]
  simp only [validate, scopedLogicalExtensionalManifest_valid, dite_true]
  rw [denote_scopedLogicalExtensional_eq]

theorem fullRawOperational_encoded_validated :
    decodeValidated (encode fullRawOperationalManifest) =
      some Programs.CheckingProfiles.fullRawOperational := by
  rw [decodeValidated_encode]
  simp only [validate, fullRawOperationalManifest_valid, dite_true]
  rw [denote_fullRawOperational_eq]

/-- A validated wire profile together with the separate interaction theorem
for the actual declaration-aware calculus it selects. -/
structure InteractionQualified (atom : Atom) where
  profile : Contract
  validated : decodeValidated atom = some profile
  interaction : Programs.CheckingProfiles.Interaction.Certificate profile

/-- The encoded natural-intensional node carries the existing exact
beta/projection/iota Church--Rosser and preservation certificate. -/
def naturalIntensional_encoded_qualified :
    InteractionQualified (encode naturalIntensionalManifest) :=
  ⟨Programs.CheckingProfiles.naturalIntensional,
    naturalIntensional_encoded_validated,
    Programs.CheckingProfiles.Interaction.naturalIntensionalCertificate⟩

/-! ## Retained typed receipts and executable controls -/

abbrev TypedReceiptAt (index : RowIndex) :=
  Σ context : Tower.Ctx ((Checking.table.get index).1),
    Σ type : Tower.Tm ((Checking.table.get index).1),
      ProofRelevantStepReceipt Tower.rules rawSignature
        proofRelevantIotaComputation context
        (Checking.table.get index).2.1 (Checking.table.get index).2.2 type

/-- Judgmental authority exposes the retained evidence from the admitted
schema row, including its source and target typing derivations. -/
structure LicensedReceipt (profile : Contract) (index : RowIndex) where
  retained : (profile.iota index).receipt = true
  typed : TypedReceiptAt index

def licensedReceipt (profile : Contract) (index : RowIndex)
    (licensed : profile.enabled index = true) : LicensedReceipt profile index where
  retained := profile.judgmental_receipt index licensed
  typed := receiptAt Checking.schemas index

@[simp] theorem naturalZero_typedReceipt_exact :
    (receiptAt Checking.schemas naturalZeroIndex).2.2 = natZeroIotaReceipt := rfl

@[simp] theorem naturalSucc_typedReceipt_exact :
    (receiptAt Checking.schemas naturalSuccIndex).2.2 = natSuccIotaReceipt := rfl

@[simp] theorem vectorNil_typedReceipt_exact :
    (receiptAt Checking.schemas vectorNilIndex).2.2 = vecNilIotaReceipt := rfl

@[simp] theorem vectorCons_typedReceipt_exact :
    (receiptAt Checking.schemas vectorConsIndex).2.2 = vecConsIotaReceipt := rfl

def naturalZeroLicensedReceipt :
    LicensedReceipt Programs.CheckingProfiles.naturalIntensional
      naturalZeroIndex :=
  licensedReceipt _ _ (by rfl)

def naturalSuccLicensedReceipt :
    LicensedReceipt Programs.CheckingProfiles.naturalIntensional
      naturalSuccIndex :=
  licensedReceipt _ _ (by rfl)

@[simp] theorem naturalZeroLicensedReceipt_exact :
    naturalZeroLicensedReceipt.typed.2.2 = natZeroIotaReceipt := rfl

@[simp] theorem naturalSuccLicensedReceipt_exact :
    naturalSuccLicensedReceipt.typed.2.2 = natSuccIotaReceipt := rfl

/-- The same validated profile retains the vector receipt but does not grant
the vector row judgmental authority. -/
theorem naturalIntensional_vectorNil_not_judgmental :
    Programs.CheckingProfiles.naturalIntensional.enabled vectorNilIndex = false := rfl

/-- One concrete wire consumer: decode and validate a profile, then replay the
existing append certificate under precisely its judgmental iota selection. -/
def checkAppendEncoded (atom : Atom) : Bool :=
  match decodeValidated atom with
  | none => false
  | some profile => Programs.ComputationProfiles.replay profile.enabled

theorem naturalIntensional_encoded_checks_append :
    checkAppendEncoded (encode naturalIntensionalManifest) = true := by
  unfold checkAppendEncoded
  rw [naturalIntensional_encoded_validated]
  change Programs.ComputationProfiles.replay
    Programs.CheckingProfiles.naturalIntensional.enabled = true
  rw [Programs.CheckingProfiles.naturalIntensional_enabled_eq]
  exact Programs.ComputationProfiles.append_checked_naturalOnly

theorem minimal_encoded_refuses_append :
    checkAppendEncoded (encode minimalManifest) = false := by
  decide +kernel

/-- Negative authority control: a judgmental permission without its receipt
is rejected before it can select conversion. -/
def missingReceiptManifest : Manifest := [
  .eliminateTowerSorts,
  .iotaJudgmental naturalZeroIndex]

theorem missingReceiptManifest_invalid : ¬ Valid missingReceiptManifest := by
  decide

theorem missingReceipt_encoded_refused :
    decodeValidated (encode missingReceiptManifest) = none := by
  rw [decodeValidated_encode]
  exact (validate_eq_none_iff _).2 missingReceiptManifest_invalid

theorem out_of_range_iota_refused :
    decodeFeature (.expression [
      .symbol "natvec-iota-judgmental-v1",
      encodeNat Checking.table.length]) = none := by
  simp [decodeFeature, decodeFin]

theorem malformed_profile_refused :
    decodeValidated (.symbol "natvec-checking-profile-v1") = none := by
  rfl

theorem natural_package_encoded_join :
    joinEncoded (encode minimalManifest) (encode naturalIotaPackage) =
      some (encode naturalIntensionalManifest) :=
  joinEncoded_encode minimalManifest_valid naturalIotaPackage_valid

def verdicts : List (String × Bool) := [
  ("minimal manifest validates", validCheck minimalManifest),
  ("natural intensional manifest validates", validCheck naturalIntensionalManifest),
  ("scoped logical-extensional manifest validates",
    validCheck scopedLogicalExtensionalManifest),
  ("full raw operational manifest validates", validCheck fullRawOperationalManifest),
  ("encoded natural profile checks append",
    checkAppendEncoded (encode naturalIntensionalManifest)),
  ("encoded minimal profile refuses append",
    !(checkAppendEncoded (encode minimalManifest))),
  ("missing receipt manifest refuses validation",
    (decodeValidated (encode missingReceiptManifest)).isNone),
  ("out-of-range iota selector refuses decoding",
    (decodeFeature (.expression [
      .symbol "natvec-iota-judgmental-v1",
      encodeNat Checking.table.length])).isNone),
  ("malformed profile refuses decoding",
    (decodeValidated (.symbol "natvec-checking-profile-v1")).isNone)]

theorem all_verdicts : verdicts.all (·.2) = true := by decide +kernel

#print axioms validCheck_eq_true_iff
#print axioms valid_join
#print axioms validate_isSome_iff
#print axioms denote_extends_join_left
#print axioms denote_extends_join_right
#print axioms decodeIdentityPrinciple_encodeIdentityPrinciple
#print axioms decodeFeature_encodeFeature
#print axioms decode_encode
#print axioms encode_injective
#print axioms joinEncoded_encode
#print axioms joinEncoded_sound
#print axioms denote_minimal_eq
#print axioms denote_naturalIntensional_eq
#print axioms denote_scopedLogicalExtensional_eq
#print axioms denote_fullRawOperational_eq
#print axioms naturalIntensional_encoded_validated
#print axioms naturalIntensional_encoded_qualified
#print axioms naturalZero_typedReceipt_exact
#print axioms naturalSucc_typedReceipt_exact
#print axioms vectorNil_typedReceipt_exact
#print axioms vectorCons_typedReceipt_exact
#print axioms naturalZeroLicensedReceipt_exact
#print axioms naturalSuccLicensedReceipt_exact
#print axioms naturalIntensional_vectorNil_not_judgmental
#print axioms naturalIntensional_encoded_checks_append
#print axioms minimal_encoded_refuses_append
#print axioms missingReceipt_encoded_refused
#print axioms out_of_range_iota_refused
#print axioms malformed_profile_refused
#print axioms all_verdicts

end Profiles
end Mettapedia.Languages.MeTTa.Bridges.GSLT.NatVecCheckingProfileAtomWire
