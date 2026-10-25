import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorAllNamedResultComparison
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorAllResultPrimitiveFormation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ConversionCoherence

/-!
# Formation-sensitive assembly of the Vector result comparison

Motive, method and result-family judgments form independent input contracts.
The native eliminator applications, type conversions and telescope closure
construct the complete comparison program's judgment. No complete program
judgment or general subject-reduction principle is an input.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllResultComparison.Named.Assembly
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Declaration
open TypedEquality.Normalization
open NativeNaturalVectorFamilies
open NativeVectorAllTypedMaps (Direction motiveTypeAt nilTypeAt consTypeAt resultTypeAt afterMotiveTypeAt)
abbrev rules := Named.rules
abbrev ambient := NativeVectorAllResultComparison.parameterContext
abbrev decoder := Comparison.decoder
abbrev choices := Comparison.choices

def currentMotive (direction : Direction) : Tower.Tm 4 := Comparison.motive direction (.var 3) (.var 2)
def nilInterface (direction : Direction) : Tower.Tm 4 :=
  Comparison.typeView 256 (nilTypeAt (.var 3) (currentMotive direction))
def consInterface (direction : Direction) : Tower.Tm 4 :=
  Comparison.typeView 256 (consTypeAt (.var 3) (currentMotive direction))
def goalFamily (direction : Direction) : Tower.Tm 4 :=
  .pi (NativeVectorAllCommonRecursorProfile.Projection.inputType (NativeVectorAllTypedMaps.source direction)
    (.var 3) (.var 2) (.var 1) (.var 0))
    (Comparison.goal direction (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))

theorem universe_regularity : FormationSensitive.UniverseRegularity rules :=
  Named.universe_regularity.includeSignature Named.signature

private theorem eliminator_closed : FormationSensitive.Typing rules .nil
    (.const vecEliminateName) NativeVectorAllTypedMaps.eliminatorType :=
  (PrimitiveBase.primitive_typed (actual := vecEliminateName)
    (by simp [PrimitiveBase.primitiveNames]) rfl).typing.includeSignature Named.signature

private theorem parameter_application : FormationSensitive.Typing rules
    NativeVectorAllTypedMaps.parameterContext
    (.app (.app (.const vecEliminateName) (.var 1)) (.var 0))
    (afterMotiveTypeAt (.var 1) (.var 0)) := by
  have operation : FormationSensitive.Typing rules NativeVectorAllTypedMaps.parameterContext
      (.const vecEliminateName) (liftClosed NativeVectorAllTypedMaps.eliminatorType) :=
    FormationCheckedTelescopePrograms.liftClosed_typing eliminator_closed _
  rw [← NativeVectorAllTypedMaps.parameter_result_readback]
  exact .appElim (.appElim operation (.var 1)) (.var 0)

theorem after_motive {n : Nat} {context : Tower.Ctx n} {element motive : Tower.Tm n}
    (elementTyped : FormationSensitive.Typing rules context element
      (sortTm NativeVectorAll.Universes.dataLevel))
    (motiveTyped : FormationSensitive.Typing rules context motive (motiveTypeAt element)) :
    FormationSensitive.Typing rules context (.app (.app (.const vecEliminateName) element) motive)
      (afterMotiveTypeAt element motive) := by
  let sigma : Sub Tower.Head 2 n := consSub motive (consSub element Fin.elim0)
  have assignment : FormationSensitive.CtxMor rules NativeVectorAllTypedMaps.parameterContext context sigma := by
    intro index
    fin_cases index
    · exact motiveTyped
    · exact elementTyped
  have linked := parameter_application.substitute assignment
  rw [NativeVectorAllTypedMaps.substitute_afterMotiveTypeAt] at linked
  have firstImage : sigma 1 = element := by
    change consSub motive (consSub element Fin.elim0) (Fin.succ 0) = element
    simp only [consSub_succ, consSub_zero]
  simpa only [subst, sigma, consSub_zero, firstImage] using linked

theorem result_apply {n : Nat} {context : Tower.Ctx n}
    {element motive function number vector : Tower.Tm n}
    (functionTyped : FormationSensitive.Typing rules context function (resultTypeAt element motive))
    (numberTyped : FormationSensitive.Typing rules context number natTm)
    (vectorTyped : FormationSensitive.Typing rules context vector (vecApp element number)) :
    FormationSensitive.Typing rules context (.app (.app function number) vector)
      (.app (.app motive number) vector) := by
  have openingWeakening {k : Nat} (value body : Tower.Tm k) :
      subst (subst0 value) (rename wk body) = body := inst0_rename_wk value body
  have atNumber := FormationSensitive.Typing.appElim functionTyped numberTyped
  simp only [inst0, subst, openingWeakening, subst_liftSub_wk,
    liftSub_zero, liftSub_succ, subst0_zero, NativeNaturalVectorFamilies.subst_vecApp] at atNumber
  have atVector := FormationSensitive.Typing.appElim atNumber vectorTyped
  simpa only [inst0, subst, openingWeakening, subst0_zero] using atVector

def motiveResultRecipe (direction : Direction) : StructuralConversionCode.Code Tower.Head decoder.Code 4 :=
  (StructuralWeakHeadSearch.produce decoder.decode Comparison.searchRoot 64
    (.app (.app (currentMotive direction) (.var 1)) (.var 0))).recipe

local instance : DecidableRel rules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

theorem motive_result_checked (direction : Direction) :
    (motiveResultRecipe direction).check rules.headEq decoder.decode
      (.app (.app (currentMotive direction) (.var 1)) (.var 0)) (goalFamily direction) = true := by
  cases direction <;> decide +kernel

theorem motive_result_conversion (direction : Direction) :
    Conv rules.headEq (.app (.app (currentMotive direction) (.var 1)) (.var 0))
      (goalFamily direction) rules.computation :=
  StructuralConversionCode.Code.check_sound decoder (motive_result_checked direction)

def appliedEliminator (direction : Direction) : Tower.Tm 4 :=
  vecEliminateApp (.var 3) (currentMotive direction)
    (Comparison.nilCase (.var 2)) (Comparison.consCase direction (.var 3) (.var 2)) (.var 1) (.var 0)

theorem close_term_readback (direction : Direction) :
    TelescopeAbstraction.closeTerm ambient (.lam (.app (rename wk (appliedEliminator direction)) (.var 0))) =
      Comparison.programme direction := by
  cases direction <;> decide +kernel

theorem close_type_readback (direction : Direction) :
    TelescopeAbstraction.closeType ambient (goalFamily direction) = Comparison.programmeType direction := rfl

theorem programme_typed (direction : Direction)
    (motiveChecked : FormationSensitive.Judgment rules ambient (currentMotive direction)
      (motiveTypeAt (.var 3)))
    (nilChecked : FormationSensitive.Judgment rules ambient (Comparison.nilCase (.var 2))
      (nilInterface direction))
    (consChecked : FormationSensitive.Judgment rules ambient
      (Comparison.consCase direction (.var 3) (.var 2)) (consInterface direction))
    (familyChecked : FormationSensitive.Judgment rules ambient (goalFamily direction)
      (sortTm evidenceUpperLevel)) :
    FormationSensitive.Judgment rules .nil (Comparison.programme direction) (Comparison.programmeType direction) := by
  have afterMotive := after_motive (.var 3) motiveChecked.typing
  obtain ⟨_, _, afterMotiveFormation⟩ := afterMotive.regularity universe_regularity motiveChecked.context
  obtain ⟨_, _, _, nilFormed, nilUniverse, _, _, _⟩ := afterMotiveFormation.piFormation
  have nilTyped : FormationSensitive.Typing rules ambient (Comparison.nilCase (.var 2))
      (nilTypeAt (.var 3) (currentMotive direction)) :=
    .conv nilChecked.typing nilFormed nilUniverse
      (.symm _ _ (ConversionCoherence.stepStar_implies_conv (Comparison.typeView_reduces 256 _)))
  have afterNil : FormationSensitive.Typing rules ambient
      (.app (.app (.app (.const vecEliminateName) (.var 3)) (currentMotive direction))
        (Comparison.nilCase (.var 2)))
      (.pi (consTypeAt (.var 3) (currentMotive direction))
        (rename wk (resultTypeAt (.var 3) (currentMotive direction)))) := by
    have applied := FormationSensitive.Typing.appElim afterMotive nilTyped
    simpa only [afterMotiveTypeAt, inst0_rename_wk] using applied
  obtain ⟨_, _, afterNilFormation⟩ := afterNil.regularity universe_regularity motiveChecked.context
  obtain ⟨_, _, _, consFormed, consUniverse, _, _, _⟩ := afterNilFormation.piFormation
  have consTyped : FormationSensitive.Typing rules ambient
      (Comparison.consCase direction (.var 3) (.var 2)) (consTypeAt (.var 3) (currentMotive direction)) :=
    .conv consChecked.typing consFormed consUniverse
      (.symm _ _ (ConversionCoherence.stepStar_implies_conv (Comparison.typeView_reduces 256 _)))
  have afterCons : FormationSensitive.Typing rules ambient
      (.app (.app (.app (.app (.const vecEliminateName) (.var 3)) (currentMotive direction))
        (Comparison.nilCase (.var 2))) (Comparison.consCase direction (.var 3) (.var 2)))
      (resultTypeAt (.var 3) (currentMotive direction)) := by
    have applied := FormationSensitive.Typing.appElim afterNil consTyped
    simpa only [inst0_rename_wk] using applied
  have functionTyped : FormationSensitive.Typing rules ambient (appliedEliminator direction)
      (goalFamily direction) :=
    .conv (result_apply afterCons (.var 1) (.var 0)) familyChecked.typing (.sort _)
      (motive_result_conversion direction)
  have bodyTyped : FormationSensitive.Typing rules
      (.snoc ambient (NativeVectorAllCommonRecursorProfile.Projection.inputType
        (NativeVectorAllTypedMaps.source direction) (.var 3) (.var 2) (.var 1) (.var 0)))
      (.app (rename wk (appliedEliminator direction)) (.var 0))
      (Comparison.goal direction (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)) := by
    have argumentTyped : FormationSensitive.Typing rules
        (.snoc ambient (NativeVectorAllCommonRecursorProfile.Projection.inputType
          (NativeVectorAllTypedMaps.source direction) (.var 3) (.var 2) (.var 1) (.var 0)))
        (.var 0) (rename wk (NativeVectorAllCommonRecursorProfile.Projection.inputType
          (NativeVectorAllTypedMaps.source direction) (.var 3) (.var 2) (.var 1) (.var 0))) := .var 0
    have applied := FormationSensitive.Typing.appElim functionTyped.weaken argumentTyped
    convert applied using 1
    cases direction <;> decide +kernel
  have lambdaTyped : FormationSensitive.Typing rules ambient
      (.lam (.app (rename wk (appliedEliminator direction)) (.var 0))) (goalFamily direction) :=
    .lamIntro familyChecked.typing (.sort _) bodyTyped
  have closed := FormationCheckedTelescopePrograms.close_typed universe_regularity
    (fun first second => FormationCheckedTelescopePrograms.tower_joins first second)
      motiveChecked.context lambdaTyped
  rw [close_term_readback, close_type_readback] at closed
  exact ⟨.nil, closed⟩

#print axioms programme_typed
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllResultComparison.Named.Assembly
