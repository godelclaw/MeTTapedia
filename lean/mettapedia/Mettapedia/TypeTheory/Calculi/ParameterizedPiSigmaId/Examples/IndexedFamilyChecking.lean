import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorChecking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.TowerChecking

/-!
# Schema replay and dependent instantiation controls

The controls distinguish selected occurrences, binder-safe substitution,
raw conversion and independently checked argument typing. The positive iota
request uses the actual natural eliminator's open dependent telescope.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace IndexedFamilyCheckingControls

open Declaration Declaration.IndexedFamily.Checking
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

abbrev nativeSchemas := NativeNaturalVectorFamilies.Checking.schemas
abbrev nativeTable := NativeNaturalVectorFamilies.Checking.table
abbrev nativeDecoder := NativeNaturalVectorFamilies.Checking.decoder
abbrev allRows := NativeNaturalVectorFamilies.Checking.enabled

def duplicateTable : AlgebraicSchema.SchemaTable Unit :=
  [⟨1, .app (.const `f) (.var 0), .var 0⟩,
   ⟨1, .app (.const `f) (.var 0), .var 0⟩]

def duplicateCode (row : Nat) : SchemaTableConversionCode.Code Unit 1 := ⟨row, [.var 0]⟩

def secondOnly : Fin duplicateTable.length → Bool := fun index => index.val == 1

def binderTable : AlgebraicSchema.SchemaTable Unit :=
  [⟨1, .lam (.app (.const `f) (.var 1)), .lam (.var 1)⟩]

def binderCode : SchemaTableConversionCode.Code Unit 1 := ⟨0, [.var 0]⟩

def binderExpected : Tm Unit 1 × Tm Unit 1 :=
  (.lam (.app (.const `f) (.var 1)), .lam (.var 1))

def binderWrongCapture : Tm Unit 1 × Tm Unit 1 :=
  (.lam (.app (.const `f) (.var 0)), .lam (.var 0))

abbrev depContext := Tower.Checking.Controls.dependentContext
abbrev depContextCode := Tower.Checking.Controls.dependentContextCode
abbrev ground {n : Nat} : Tower.Tm n := .head .legacyGround
abbrev u0 : Tower.Head := Tower.Checking.Controls.u0

def identitySubstitution : FormationSensitiveChecking.SubstitutionRequest
    Tower.Checking.decoder depContext depContext ids :=
  ⟨depContextCode, fun _ => .var⟩

def swappedSubstitution : Sub Tower.Head 2 2 := ![.var 1, .var 0]

def wrongDependentSubstitution : FormationSensitiveChecking.SubstitutionRequest
    Tower.Checking.decoder depContext depContext swappedSubstitution :=
  ⟨depContextCode, fun _ => .var⟩

def unformedEmptySubstitution : FormationSensitiveChecking.SubstitutionRequest
    Tower.Checking.decoder (.nil : Tower.Ctx 0) Tower.Checking.Controls.badContext Fin.elim0 :=
  ⟨.snoc .nil u0 .headType, Fin.elim0⟩

abbrev NativeTypingCode (n : Nat) := StructuralTypingReplay.Code Tower.Head
  (NativeNaturalVectorFamilies.Checking.ConversionCode) n

open NativeNaturalVectorFamilies

def natCode {n : Nat} : NativeTypingCode n :=
  .const (.sort (.succ natLevel)) .headType

def zeroCode {n : Nat} : NativeTypingCode n := .const (.sort natLevel) natCode

def succCode {n : Nat} : NativeTypingCode n :=
  .const (.sort (.max natLevel natLevel))
    (.piForm (.sort natLevel) (.sort natLevel) natCode natCode)

def motiveTypeCode : NativeTypingCode 0 :=
  .piForm (.sort natLevel) (.sort (.succ motiveLevel)) natCode .headType

def zeroCaseTypeCode : NativeTypingCode 1 :=
  .appElim natTm (sortTm motiveLevel) .var zeroCode

def succCaseTypeCode : NativeTypingCode 2 :=
  .piForm (.sort natLevel) (.sort (.max motiveLevel motiveLevel)) natCode
    (.piForm (.sort motiveLevel) (.sort motiveLevel)
      (.appElim natTm (sortTm motiveLevel) .var .var)
      (.appElim natTm (sortTm motiveLevel) .var
        (.appElim natTm natTm succCode .var)))

def natContextCode : FormationSensitiveChecking.ContextCode nativeDecoder natContextPZS :=
  .snoc
    (.snoc
      (.snoc .nil (.sort natMotiveTypeLevel) motiveTypeCode)
      (.sort motiveLevel) zeroCaseTypeCode)
    (.sort (.max natLevel (.max motiveLevel motiveLevel))) succCaseTypeCode

def zeroRequest : InstanceRequest nativeSchemas nativeDecoder natContextPZS where
  index := ⟨0, by decide⟩
  substitution := ids
  arguments := ⟨natContextCode, fun _ => .var⟩

def weakContext : Tower.Ctx 4 := .snoc natContextPZS natTm

def weakRequest : InstanceRequest nativeSchemas nativeDecoder weakContext where
  index := ⟨0, by decide⟩
  substitution := fun index => .var index.succ
  arguments := ⟨.snoc natContextCode (.sort natLevel) natCode, fun _ => .var⟩

def unknownArguments : Sub Tower.Head 3 0 :=
  ![.const `unknownSucc, .const `unknownZero, .const `unknownMotive]

def untypedRequest : InstanceRequest nativeSchemas nativeDecoder (.nil : Tower.Ctx 0) where
  index := ⟨0, by decide⟩
  substitution := unknownArguments
  arguments := ⟨.nil, fun _ => .const (.sort natLevel) .headType⟩

def natOnly : Fin nativeTable.length → Bool := fun index => decide (index.val < 2)

def rawNatZero : SchemaTableConversionCode.Code Tower.Head 0 :=
  ⟨0, [.const `s, .const `z, .const `p]⟩

def rawNatSucc : SchemaTableConversionCode.Code Tower.Head 0 :=
  ⟨1, [.const `n, .const `s, .const `z, .const `p]⟩

def rawVecNil : SchemaTableConversionCode.Code Tower.Head 0 :=
  ⟨2, [.const `s, .const `z, .const `p, .const `a]⟩

def rawVecCons : SchemaTableConversionCode.Code Tower.Head 0 :=
  ⟨3, [.const `v, .const `h, .const `n, .const `s, .const `z, .const `p, .const `a]⟩

def verdicts : List (String × Bool) := [
  ("schema duplicate keeps original row zero",
    ((SchemaTableConversionCode.decodeInstance duplicateTable (fun _ => true)
      (duplicateCode 0)).map fun parsed => parsed.index.val) == some 0),
  ("schema duplicate keeps original row one",
    ((SchemaTableConversionCode.decodeInstance duplicateTable (fun _ => true)
      (duplicateCode 1)).map fun parsed => parsed.index.val) == some 1),
  ("another duplicate cannot rescue a disabled citation",
    (SchemaTableConversionCode.decode duplicateTable secondOnly (duplicateCode 0)).isNone),
  ("selected duplicate is accepted",
    (SchemaTableConversionCode.decode duplicateTable secondOnly (duplicateCode 1)).isSome),
  ("schema out of range row refuses",
    (SchemaTableConversionCode.decode duplicateTable (fun _ => true) (duplicateCode 2)).isNone),
  ("schema wrong argument count refuses",
    (SchemaTableConversionCode.decode duplicateTable (fun _ => true)
      (⟨0, []⟩ : SchemaTableConversionCode.Code Unit 1)).isNone),
  ("schema substitution preserves binder scope",
    SchemaTableConversionCode.decode binderTable (fun _ => true) binderCode == some binderExpected),
  ("schema substitution rejects captured endpoints",
    SchemaTableConversionCode.decode binderTable (fun _ => true) binderCode != some binderWrongCapture),
  ("formed dependent identity substitution",
    identitySubstitution.check Tower.Checking.decoder),
  ("dependent argument exchange refuses",
    !(wrongDependentSubstitution.check Tower.Checking.decoder)),
  ("empty substitution still checks target formation",
    !(unformedEmptySubstitution.check Tower.Checking.decoder)),
  ("actual Nat zero root",
    Checking.iotaDecoder.decode rawNatZero ==
      some (natEliminateApp (.const `p) (.const `z) (.const `s) zeroTm, .const `z)),
  ("actual Nat successor root", (Checking.iotaDecoder.decode rawNatSucc).isSome),
  ("actual Vec nil root", (Checking.iotaDecoder.decode rawVecNil).isSome),
  ("actual Vec cons root", (Checking.iotaDecoder.decode rawVecCons).isSome),
  ("selected Nat profile refuses Vec computation",
    (SchemaTableConversionCode.decode nativeTable natOnly rawVecNil).isNone),
  ("actual typed Nat iota request",
    zeroRequest.check nativeSchemas nativeDecoder allRows
      natZeroIotaLeft natZeroIotaRight natZeroIotaType),
  ("typed Nat iota keeps displayed type",
    !(zeroRequest.check nativeSchemas nativeDecoder allRows
      natZeroIotaLeft natZeroIotaRight natTm)),
  ("typed Nat iota checks the selected policy",
    !(zeroRequest.check nativeSchemas nativeDecoder (fun _ => false)
      natZeroIotaLeft natZeroIotaRight natZeroIotaType)),
  ("typed Nat iota under context weakening",
    weakRequest.check nativeSchemas nativeDecoder allRows
      (rename wk natZeroIotaLeft) (rename wk natZeroIotaRight) (rename wk natZeroIotaType)),
  ("raw iota with unknown arguments still has raw evidence",
    (Checking.iotaDecoder.decode ⟨0, List.ofFn unknownArguments⟩).isSome),
  ("raw iota does not authorize untyped arguments",
    !(untypedRequest.check nativeSchemas nativeDecoder allRows
      (subst unknownArguments natZeroIotaLeft) (subst unknownArguments natZeroIotaRight)
      (subst unknownArguments natZeroIotaType)))]

theorem all_verdicts : verdicts.all Prod.snd = true := by decide +kernel

/-- This is the actual retained rule evidence reconstructed by finite replay. -/
def checkedZeroReceipt : ComputationAuthority.ProofRelevantStepReceipt
    Tower.rules rawSignature proofRelevantIotaComputation natContextPZS
    natZeroIotaLeft natZeroIotaRight natZeroIotaType :=
  zeroRequest.replay nativeSchemas nativeDecoder allRows
    natZeroIotaLeft natZeroIotaRight natZeroIotaType (by decide +kernel)

end IndexedFamilyCheckingControls
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
