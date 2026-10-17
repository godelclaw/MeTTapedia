import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.PatternCodec
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.UniverseProfiles

/-!
# Cumulative-tower specialization of the scoped Pattern codec

Explicit levels and cumulative heads specialize the single parameterized
syntax codec. Round trips, scope refusals and checker-side admission retain
the original fixed wire format. This is one specified calculus representation;
it selects no MeTTa language or universal proof-checking foundation.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.PatternCodec
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.PatternCodec
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker
open Mettapedia.OSLF.MeTTaIL.Syntax

namespace WithScalars
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.PatternCodec.WithScalars

abbrev encodeLevel (scalars : ScalarCodecs) : LevelExpr Nat → Pattern
  | .const value => .apply "prime-level-const" [scalars.natural.encode value]
  | .param index => .apply "prime-level-param" [scalars.natural.encode index]
  | .succ level => .apply "prime-level-succ" [encodeLevel scalars level]
  | .max left right =>
      .apply "prime-level-max" [encodeLevel scalars left, encodeLevel scalars right]

@[simp] def decodeLevel? (scalars : ScalarCodecs) : Pattern → Option (LevelExpr Nat)
  | .apply "prime-level-const" [value] => do
      pure (.const (← scalars.natural.decode value))
  | .apply "prime-level-param" [index] => do
      pure (.param (← scalars.natural.decode index))
  | .apply "prime-level-succ" [level] => do
      pure (.succ (← decodeLevel? scalars level))
  | .apply "prime-level-max" [left, right] => do
      pure (.max (← decodeLevel? scalars left) (← decodeLevel? scalars right))
  | _ => none

@[simp] theorem decodeLevel?_encodeLevel (scalars : ScalarCodecs) (level : LevelExpr Nat) :
    decodeLevel? scalars (encodeLevel scalars level) = some level := by
  induction level with
  | const value => simp [encodeLevel, decodeLevel?, scalars.natural.decode_encode]
  | param index => simp [encodeLevel, decodeLevel?, scalars.natural.decode_encode]
  | succ level ih => simp [encodeLevel, decodeLevel?, ih]
  | max left right leftIH rightIH =>
      simp [encodeLevel, decodeLevel?, leftIH, rightIH]

abbrev encodeTowerHead (scalars : ScalarCodecs) : Tower.Head → Pattern
  | .legacyGround => .apply "prime-head-legacy-ground" []
  | .sort level => .apply "prime-head-sort" [encodeLevel scalars level]

theorem encodeTowerHead_legacyGround (scalars : ScalarCodecs) :
    encodeTowerHead scalars .legacyGround = .apply "prime-head-legacy-ground" [] := rfl

theorem encodeTowerHead_sort (scalars : ScalarCodecs) (level : LevelExpr Nat) :
    encodeTowerHead scalars (.sort level) = .apply "prime-head-sort" [encodeLevel scalars level] := rfl

abbrev decodeTowerHead? (scalars : ScalarCodecs) : Pattern → Option Tower.Head
  | .apply "prime-head-legacy-ground" [] => some .legacyGround
  | .apply "prime-head-sort" [level] => do
      pure (.sort (← decodeLevel? scalars level))
  | _ => none

@[simp] theorem decodeTowerHead?_encodeTowerHead (scalars : ScalarCodecs) (head : Tower.Head) :
    decodeTowerHead? scalars (encodeTowerHead scalars head) = some head := by
  cases head with
  | legacyGround => rfl
  | sort level => simp [encodeTowerHead, decodeTowerHead?]

abbrev towerHeadCodec (scalars : ScalarCodecs) : PartialCodec Tower.Head Pattern where
  encode := encodeTowerHead scalars
  decode := decodeTowerHead? scalars
  decode_encode := decodeTowerHead?_encodeTowerHead scalars

abbrev towerTypingClaimCodec (scalars : ScalarCodecs) : PartialCodec (TypingClaim Tower.Head) Pattern :=
  typingClaimCodec scalars (towerHeadCodec scalars)

end WithScalars

abbrev encodeLevel : LevelExpr Nat → Pattern := WithScalars.encodeLevel existingScalars

abbrev decodeLevel? : Pattern → Option (LevelExpr Nat) := WithScalars.decodeLevel? existingScalars

@[simp] theorem decodeLevel?_encodeLevel (level : LevelExpr Nat) :
    decodeLevel? (encodeLevel level) = some level :=
  WithScalars.decodeLevel?_encodeLevel existingScalars level

abbrev encodeTowerHead : Tower.Head → Pattern := WithScalars.encodeTowerHead existingScalars

abbrev decodeTowerHead? : Pattern → Option Tower.Head := WithScalars.decodeTowerHead? existingScalars

@[simp] theorem decodeTowerHead?_encodeTowerHead (head : Tower.Head) :
    decodeTowerHead? (encodeTowerHead head) = some head :=
  WithScalars.decodeTowerHead?_encodeTowerHead existingScalars head

def towerHeadCodec : PartialCodec Tower.Head Pattern := WithScalars.towerHeadCodec existingScalars

def towerTypingClaimCodec : PartialCodec (TypingClaim Tower.Head) Pattern :=
  typingClaimCodec towerHeadCodec

namespace WithScalars

theorem encodeLevel_ground (scalars : ScalarCodecs) (admissible : ScalarAdmissible scalars) (level : LevelExpr Nat) :
    (encodeLevel scalars level).isGroundAt 0 = true := by
  induction level with
  | const value =>
      simp [Pattern.isGroundAt, Pattern.isGroundListAt,
        admissible.naturalGround]
  | param index =>
      simp [Pattern.isGroundAt, Pattern.isGroundListAt,
        admissible.naturalGround]
  | succ level ih =>
      simp [Pattern.isGroundAt, Pattern.isGroundListAt, ih]
  | max left right leftIH rightIH =>
      simp [Pattern.isGroundAt, Pattern.isGroundListAt,
        leftIH, rightIH]

theorem encodeLevel_canonical (scalars : ScalarCodecs) (admissible : ScalarAdmissible scalars) (level : LevelExpr Nat) :
    (encodeLevel scalars level).hasCanonicalBinderMetadata = true := by
  induction level with
  | const value =>
      simp [Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, admissible.naturalCanonical]
  | param index =>
      simp [Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, admissible.naturalCanonical]
  | succ level ih =>
      simp [Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, ih]
  | max left right leftIH rightIH =>
      simp [Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, leftIH, rightIH]

theorem encodeTowerHead_ground (scalars : ScalarCodecs) (admissible : ScalarAdmissible scalars) (head : Tower.Head) :
    (encodeTowerHead scalars head).isGroundAt 0 = true := by
  cases head with
  | legacyGround =>
      simp [Pattern.isGroundAt, Pattern.isGroundListAt]
  | sort level =>
      simp [Pattern.isGroundAt, Pattern.isGroundListAt,
        encodeLevel_ground scalars admissible]

theorem encodeTowerHead_canonical (scalars : ScalarCodecs) (admissible : ScalarAdmissible scalars) (head : Tower.Head) :
    (encodeTowerHead scalars head).hasCanonicalBinderMetadata = true := by
  cases head with
  | legacyGround =>
      simp [Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList]
  | sort level =>
      simp [Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, encodeLevel_canonical scalars admissible]

end WithScalars

theorem encodeLevel_ground (level : LevelExpr Nat) :
    (encodeLevel level).isGroundAt 0 = true :=
  WithScalars.encodeLevel_ground existingScalars existingScalarsAdmissible level

theorem encodeLevel_canonical (level : LevelExpr Nat) :
    (encodeLevel level).hasCanonicalBinderMetadata = true :=
  WithScalars.encodeLevel_canonical existingScalars existingScalarsAdmissible level

theorem encodeTowerHead_ground (head : Tower.Head) :
    (encodeTowerHead head).isGroundAt 0 = true :=
  WithScalars.encodeTowerHead_ground existingScalars existingScalarsAdmissible head

theorem encodeTowerHead_canonical (head : Tower.Head) :
    (encodeTowerHead head).hasCanonicalBinderMetadata = true :=
  WithScalars.encodeTowerHead_canonical existingScalars existingScalarsAdmissible head

theorem encodeLevel_argumentValid (level : LevelExpr Nat) :
    argumentValidAt 0 (encodeLevel level) = true := by
  simp [argumentValidAt, encodeLevel_ground, encodeLevel_canonical]

theorem encodeTowerHead_argumentValid (head : Tower.Head) :
    argumentValidAt 0 (encodeTowerHead head) = true := by
  simp [argumentValidAt, encodeTowerHead_ground,
    encodeTowerHead_canonical]

theorem encodeTowerTm_argumentValid (term : Tower.Tm n) :
    argumentValidAt 0 (encodeTm towerHeadCodec term) = true := by
  simp [argumentValidAt,
    encodeTm_ground towerHeadCodec encodeTowerHead_ground,
    encodeTm_canonical towerHeadCodec encodeTowerHead_canonical]

theorem encodeTowerCtx_argumentValid (context : Tower.Ctx n) :
    argumentValidAt 0 (encodeCtx towerHeadCodec context) = true := by
  simp [argumentValidAt,
    encodeCtx_ground towerHeadCodec encodeTowerHead_ground,
    encodeCtx_canonical towerHeadCodec encodeTowerHead_canonical]

theorem encodeTowerTypingClaim_argumentValid
    (claim : TypingClaim Tower.Head) :
    argumentValidAt 0 (encodeTypingClaim towerHeadCodec claim) = true := by
  cases claim with
  | mk arity context subject type =>
      change argumentValidAt 0 (.apply "prime-has-type"
        [encodeNat arity, encodeCtx towerHeadCodec context,
          encodeTm towerHeadCodec subject, encodeTm towerHeadCodec type]) = true
      simp [argumentValidAt, Pattern.isGroundAt, Pattern.isGroundListAt,
        Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList,
        encodeNat_ground, encodeNat_canonical,
        encodeCtx_ground towerHeadCodec encodeTowerHead_ground,
        encodeCtx_canonical towerHeadCodec encodeTowerHead_canonical,
        encodeTm_ground towerHeadCodec encodeTowerHead_ground,
        encodeTm_canonical towerHeadCodec encodeTowerHead_canonical]

/-! ## Positive and negative controls -/

def legacyGroundClaim : TypingClaim Tower.Head where
  arity := 0
  context := .nil
  subject := .head .legacyGround
  type := .head (.sort Tower.zero)

theorem legacyGroundClaim_round_trip :
    decodeTypingClaim? towerHeadCodec
        (encodeTypingClaim towerHeadCodec legacyGroundClaim) =
      some legacyGroundClaim := by
  exact decodeTypingClaim?_encodeTypingClaim towerHeadCodec legacyGroundClaim

/-- A variable encoded from a one-variable term cannot be decoded at arity
zero.  Scope is checked by construction rather than trusted metadata. -/
theorem outOfScopeVariable_rejected :
    decodeTm? towerHeadCodec 0
        (encodeTm towerHeadCodec
          (Tm.var (Head := Tower.Head) (0 : Fin 1))) = none := by
  rfl

/-- A one-entry context cannot be relabeled as an empty context. -/
theorem mismatchedContextArity_rejected :
    decodeCtx? towerHeadCodec 0
        (encodeCtx towerHeadCodec
          (Ctx.snoc Ctx.nil
            (Tm.head (Head := Tower.Head) .legacyGround))) = none := by
  rfl

/-- Exact decoding makes the full dependent claim encoder injective. -/
theorem encodeTowerTypingClaim_injective :
    Function.Injective (encodeTypingClaim towerHeadCodec) :=
  towerTypingClaimCodec.encode_injective

#print axioms legacyGroundClaim_round_trip
#print axioms mismatchedContextArity_rejected
#print axioms encodeTowerTypingClaim_injective

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.PatternCodec
