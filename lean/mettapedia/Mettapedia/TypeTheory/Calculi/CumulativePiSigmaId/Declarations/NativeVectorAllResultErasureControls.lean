import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorAllResultErasure
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorAllResultMethodChecking

/-!
# Base-profile instances of the erased Vector result proof

The actual closed programs and neutral-input identities are interpreted into
the preceding base. Their specifications use applications of the original
projection and evidence-map bodies. No fresh definition name occurs in the
translated proof. A fresh source name remains unavailable in the base unless
it is expanded.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllResultComparison.Named.Erasure.Controls
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Declaration
open TypedEquality.Normalization
open NativeVectorAll.ResultView
open NativeVectorAllTypedMaps (Direction source target)

theorem first_natural_row_fixed :
    ConstantExpansion.expand (naturalBodies false)
      (NativeNaturalVectorFamilies.Checking.table.get ⟨0, by decide +kernel⟩).2.1 =
      (NativeNaturalVectorFamilies.Checking.table.get ⟨0, by decide +kernel⟩).2.1 ∧
    ConstantExpansion.expand (naturalBodies false)
      (NativeNaturalVectorFamilies.Checking.table.get ⟨0, by decide +kernel⟩).2.2 =
      (NativeNaturalVectorFamilies.Checking.table.get ⟨0, by decide +kernel⟩).2.2 :=
  natural_rows_fixed false ⟨0, by decide +kernel⟩

theorem forward_programme : FormationSensitive.Judgment base .nil
    (ConstantExpansion.expand bodies (Comparison.programme .forward))
    (ConstantExpansion.expand bodies (Comparison.programmeType .forward)) :=
  erase_judgment Assembly.Controls.forward_programme

theorem backward_programme : FormationSensitive.Judgment base .nil
    (ConstantExpansion.expand bodies (Comparison.programme .backward))
    (ConstantExpansion.expand bodies (Comparison.programmeType .backward)) :=
  erase_judgment Assembly.Controls.backward_programme

theorem input_context_fixed (direction : Direction) :
    ConstantExpansion.expandCtx bodies (Assembly.inputContext direction) = Assembly.inputContext direction := by
  cases direction
  · exact context_fixed NativeVectorAllResultComparison.lower_context_formed
  · exact context_fixed NativeVectorAllResultComparison.upper_context_formed

def referenceRead {n : Nat} (level : Mettapedia.TypeTheory.UniverseLevel.LevelExpr Nat)
    (element result length vector evidence : Tower.Tm n) : Tower.Tm n :=
  appSpine (liftClosed (NativeVectorAllCommonRecursorProfile.Projection.programme level))
    [element, result, length, vector, evidence]

def referenceMapBody (direction : Direction) : Tower.Tm 0 :=
  TelescopeAbstraction.closeTerm NativeVectorAll.Universes.context
    (match direction with
    | .forward => NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.forward
    | .backward => NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.backward)

def referenceMap {n : Nat} (direction : Direction)
    (element result length vector evidence : Tower.Tm n) : Tower.Tm n :=
  appSpine (liftClosed (referenceMapBody direction)) [element, predicate result, length, vector, evidence]

def referenceGoal {n : Nat} (direction : Direction)
    (element result length vector evidence : Tower.Tm n) : Tower.Tm n :=
  .id (OriginalInputUniverses.upperVec result length)
    (referenceRead (target direction) element result length vector
      (referenceMap direction element result length vector evidence))
    (referenceRead (source direction) element result length vector evidence)

theorem goal_readback (direction : Direction) :
    ConstantExpansion.expand bodies
      (Comparison.goal direction (.var 4 : Tower.Tm 5) (.var 3) (.var 2) (.var 1) (.var 0)) =
    referenceGoal direction (.var 4) (.var 3) (.var 2) (.var 1) (.var 0) := by
  cases direction <;> decide +kernel

theorem neutral_identity (direction : Direction) : FormationSensitive.Judgment base (Assembly.inputContext direction)
    (ConstantExpansion.expand bodies (Assembly.neutralProof direction))
    (referenceGoal direction (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)) := by
  have translated := erase_judgment (Assembly.neutral_identity direction)
  rw [input_context_fixed, goal_readback] at translated
  exact translated

theorem translated_proof_has_no_definition_names (direction : Direction) (operation : Operation) :
    Named.name operation ∉ ConstantExpansion.constantNames
      (ConstantExpansion.expand bodies (Assembly.neutralProof direction)) := by
  intro present
  have known := (neutral_identity direction).typing.constants_declared (Named.name operation) present
  exact known (Named.fresh operation)

theorem zero_conservative :
    FormationSensitive.Judgment Named.rules .nil NativeNaturalVectorFamilies.zeroTm NativeNaturalVectorFamilies.natTm ↔
    FormationSensitive.Judgment base .nil NativeNaturalVectorFamilies.zeroTm NativeNaturalVectorFamilies.natTm :=
  conservative_on_fixed rfl rfl rfl

theorem fresh_constant_refused (operation : Operation) {n : Nat} (context : Tower.Ctx n) (displayed : Tower.Tm n) :
    ¬ FormationSensitive.Judgment base context (.const (Named.name operation)) displayed := by
  intro checked
  have known := checked.typing.constants_declared (Named.name operation) (by simp [ConstantExpansion.constantNames])
  exact known (Named.fresh operation)

#print axioms forward_programme
#print axioms neutral_identity
#print axioms translated_proof_has_no_definition_names
#print axioms zero_conservative
#print axioms fresh_constant_refused
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllResultComparison.Named.Erasure.Controls
