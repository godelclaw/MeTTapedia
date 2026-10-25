import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorAllResultErasureControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.FormationSensitiveLevelInstantiation

/-!
# Actual universe instances of the base Vector result identity

Universe substitution changes every declared type, the input context and the
proof/specification terms. The target keeps the existing Nat/Vector/List/J
root families, with explicit maps of their informative iota evidence. These
instances preserve judgments; they do not assume reflection of a possibly
non-injective level substitution.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllResultComparison.LevelTransport
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation Declaration RussellTarski
open NativeVectorAll.ResultView
open NativeVectorAllTypedMaps (Direction)

private theorem natural_map (theta : Nat → LevelExpr Nat) {n : Nat} {left right : Tower.Tm n}
    (step : NativeNaturalVectorFamilies.iotaComputation.step left right) :
    NativeNaturalVectorFamilies.iotaComputation.step (substLevelsTm theta left) (substLevelsTm theta right) := by
  obtain ⟨evidence⟩ := step
  exact ⟨NativeNaturalVectorFamilies.Programs.mapIota (substLevelsHead theta) evidence⟩

private theorem output_map (theta : Nat → LevelExpr Nat) {n : Nat} {left right : Tower.Tm n}
    (step : NativeVectorAllCommonRecursorProfile.output.computation.step left right) :
    NativeVectorAllCommonRecursorProfile.output.computation.step
      (substLevelsTm theta left) (substLevelsTm theta right) := by
  have mapped := natural_map theta step
  change NativeNaturalVectorFamilies.iotaComputation.step
    ((substLevelsTm theta left).mapConst OriginalInputUniverses.names.symm)
    ((substLevelsTm theta right).mapConst OriginalInputUniverses.names.symm)
  simpa only [substLevelsTm, Tm.mapConst_mapHead] using mapped

private theorem identity_map (theta : Nat → LevelExpr Nat) {n : Nat} {left right : Tower.Tm n}
    (step : NativeVectorIdentityComparison.identitySignature.computation.step left right) :
    NativeVectorIdentityComparison.identitySignature.computation.step
      (substLevelsTm theta left) (substLevelsTm theta right) := by
  obtain ⟨evidence⟩ := step
  exact ⟨NativeIndexedFamilies.IntrinsicMaps.mapIotaEvidence (substLevelsHead theta) evidence⟩

def instanceAt (theta : Nat → LevelExpr Nat) : LevelInstance NativeVectorAllResultComparison.signature theta where
  computation := NativeVectorAllResultComparison.signature.computation
  computationMap := by
    intro n left right step
    rcases step with common | identity
    · rcases common with lower | output
      · exact Or.inl (Or.inl (natural_map theta lower))
      · exact Or.inl (Or.inr (output_map theta output))
    · exact Or.inr (identity_map theta identity)

theorem signature_formed (theta : Nat → LevelExpr Nat) :
    (instanceAt theta).signature.Formed Tower.rules :=
  (instanceAt theta).formed NativeVectorAllResultComparison.signature_formed

theorem identity_typed (theta : Nat → LevelExpr Nat) (direction : Direction) :
    FormationSensitive.Judgment (instanceAt theta).rules
      (substLevelsCtx theta (Named.Assembly.inputContext direction))
      (substLevelsTm theta (ConstantExpansion.expand Named.Erasure.bodies (Named.Assembly.neutralProof direction)))
      (substLevelsTm theta
        (Named.Erasure.Controls.referenceGoal direction (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))) :=
  (instanceAt theta).refinedJudgment (Named.Erasure.Controls.neutral_identity direction)

/-- Callers are checked in the instantiated profile itself; they need not
be images of source-profile assignments. -/
theorem target_caller_identity (theta : Nat → LevelExpr Nat) (direction : Direction)
    {n : Nat} {targetContext : Tower.Ctx n}
    (targetFormation : FormationSensitive.ContextFormation (instanceAt theta).rules targetContext)
    {sigma : Sub Tower.Head 5 n}
    (typed : FormationSensitive.CtxMor (instanceAt theta).rules
      (substLevelsCtx theta (Named.Assembly.inputContext direction)) targetContext sigma) :
    FormationSensitive.Judgment (instanceAt theta).rules targetContext
      (subst sigma (substLevelsTm theta (ConstantExpansion.expand Named.Erasure.bodies
        (Named.Assembly.neutralProof direction))))
      (subst sigma (substLevelsTm theta
        (Named.Erasure.Controls.referenceGoal direction (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)))) :=
  ⟨targetFormation, (identity_typed theta direction).typing.substitute typed⟩

theorem substitution_square (theta : Nat → LevelExpr Nat) (direction : Direction)
    {n : Nat} (sigma : Sub Tower.Head 5 n) :
    substLevelsTm theta (subst sigma (ConstantExpansion.expand Named.Erasure.bodies
      (Named.Assembly.neutralProof direction))) =
    subst (fun index => substLevelsTm theta (sigma index))
      (substLevelsTm theta (ConstantExpansion.expand Named.Erasure.bodies
        (Named.Assembly.neutralProof direction))) :=
  Tm.mapHead_subst (substLevelsHead theta) sigma _

namespace Controls

def mixedLevels (parameter : Nat) : LevelExpr Nat :=
  if parameter = 0 then Tower.zero
  else if parameter = 2 then .succ Tower.zero
  else if parameter = 3 then .succ (.succ Tower.zero)
  else .param parameter

theorem mixed_identity : FormationSensitive.Judgment (instanceAt mixedLevels).rules
    (substLevelsCtx mixedLevels (Named.Assembly.inputContext .forward))
    (substLevelsTm mixedLevels (ConstantExpansion.expand Named.Erasure.bodies (Named.Assembly.neutralProof .forward)))
    (substLevelsTm mixedLevels
      (Named.Erasure.Controls.referenceGoal .forward (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))) :=
  identity_typed mixedLevels .forward

theorem mixed_caller_identity : FormationSensitive.Judgment (instanceAt mixedLevels).rules
    (substLevelsCtx mixedLevels (Named.Assembly.inputContext .forward))
    (subst ids (substLevelsTm mixedLevels (ConstantExpansion.expand Named.Erasure.bodies
      (Named.Assembly.neutralProof .forward))))
    (subst ids (substLevelsTm mixedLevels
      (Named.Erasure.Controls.referenceGoal .forward (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)))) := by
  apply target_caller_identity mixedLevels .forward mixed_identity.context
  intro index
  simpa only [subst_ids, ids] using
    (FormationSensitive.Typing.var (R := (instanceAt mixedLevels).rules)
      (Γ := substLevelsCtx mixedLevels (Named.Assembly.inputContext .forward)) index)

theorem weakening_square :
    substLevelsTm mixedLevels (subst (renSub wk : Sub Tower.Head 5 6)
      (ConstantExpansion.expand Named.Erasure.bodies (Named.Assembly.neutralProof .forward))) =
    subst (fun index => substLevelsTm mixedLevels ((renSub wk : Sub Tower.Head 5 6) index))
      (substLevelsTm mixedLevels (ConstantExpansion.expand Named.Erasure.bodies
        (Named.Assembly.neutralProof .forward))) :=
  substitution_square mixedLevels .forward (renSub wk)

def collapseLevels (_ : Nat) : LevelExpr Nat := Tower.zero

theorem distinct_parameters : NativeVectorAllCommonRecursorProfile.dataLevel ≠
    NativeVectorAllCommonRecursorProfile.resultLevel := by decide +kernel

theorem collapsed_parameters :
    LevelExpr.subst collapseLevels NativeVectorAllCommonRecursorProfile.dataLevel =
      LevelExpr.subst collapseLevels NativeVectorAllCommonRecursorProfile.resultLevel := rfl

theorem mixed_recursor_bound :
    LevelExpr.subst mixedLevels NativeVectorAllCommonRecursorProfile.recursorLevel =
      .succ (.max (.max Tower.zero (.succ Tower.zero)) (.succ (.succ Tower.zero))) := rfl

end Controls

#print axioms instanceAt
#print axioms identity_typed
#print axioms Controls.mixed_identity
#print axioms target_caller_identity
#print axioms Controls.mixed_caller_identity
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllResultComparison.LevelTransport
