import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationCheckedTelescopePrograms
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionSubstitution
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ConstantExpansion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionPaths

/-!
# Computed interpretation of retained conversion certificates

The original step and proof-tree grammars are retained. Constant bodies replace
only term payloads; primitive root-code translation must agree with their actual
decoders. The existing context map then transports every accepted composition.
Original endpoint admission is retained because constant interpretation can merge
different source terms. Selected-step counts are separate from payload size and
execution time.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace StructuralConversionCode

variable {Head : Type} {RootCode : Nat → Type}

/-- Interpret constants inside the retained step data. Root codes use the
selected local translator; constructor and binder positions are unchanged. -/
def StepCode.expandConstants (bodies : ConstantExpansion.Bodies Head)
    (mapRoot : {n : Nat} → RootCode n → RootCode n) :
    {n : Nat} → StepCode Head RootCode n → StepCode Head RootCode n
  | _, .betaPi body argument => .betaPi (ConstantExpansion.expand bodies body) (ConstantExpansion.expand bodies argument)
  | _, .betaSigmaFst first second => .betaSigmaFst (ConstantExpansion.expand bodies first) (ConstantExpansion.expand bodies second)
  | _, .betaSigmaSnd first second => .betaSigmaSnd (ConstantExpansion.expand bodies first) (ConstantExpansion.expand bodies second)
  | _, .head first second => .head first second
  | _, .root code => .root (mapRoot code)
  | _, .congPiDom code codomain => .congPiDom (expandConstants bodies mapRoot code) (ConstantExpansion.expand bodies codomain)
  | _, .congPiCod domain code => .congPiCod (ConstantExpansion.expand bodies domain) (expandConstants bodies mapRoot code)
  | _, .congSigmaDom code codomain => .congSigmaDom (expandConstants bodies mapRoot code) (ConstantExpansion.expand bodies codomain)
  | _, .congSigmaCod domain code => .congSigmaCod (ConstantExpansion.expand bodies domain) (expandConstants bodies mapRoot code)
  | _, .congIdTy code left right => .congIdTy (expandConstants bodies mapRoot code)
      (ConstantExpansion.expand bodies left) (ConstantExpansion.expand bodies right)
  | _, .congIdLeft type code right => .congIdLeft (ConstantExpansion.expand bodies type)
      (expandConstants bodies mapRoot code) (ConstantExpansion.expand bodies right)
  | _, .congIdRight type left code => .congIdRight (ConstantExpansion.expand bodies type)
      (ConstantExpansion.expand bodies left) (expandConstants bodies mapRoot code)
  | _, .congLam code => .congLam (expandConstants bodies mapRoot code)
  | _, .congAppFun code argument => .congAppFun (expandConstants bodies mapRoot code) (ConstantExpansion.expand bodies argument)
  | _, .congAppArg function code => .congAppArg (ConstantExpansion.expand bodies function) (expandConstants bodies mapRoot code)
  | _, .congPairFst code second => .congPairFst (expandConstants bodies mapRoot code) (ConstantExpansion.expand bodies second)
  | _, .congPairSnd first code => .congPairSnd (ConstantExpansion.expand bodies first) (expandConstants bodies mapRoot code)
  | _, .congFst code => .congFst (expandConstants bodies mapRoot code)
  | _, .congSnd code => .congSnd (expandConstants bodies mapRoot code)
  | _, .congRefl code => .congRefl (expandConstants bodies mapRoot code)

variable (bodies : ConstantExpansion.Bodies Head)
variable (mapRoot : {n : Nat} → RootCode n → RootCode n)
variable (headEq : Head → Head → Prop) [DecidableRel headEq]
variable (sourceRoot targetRoot : {n : Nat} → RootCode n → Option (Tm Head n × Tm Head n))

/-- Primitive root data must preserve the decoded endpoints. All compound
step correctness, including beta substitution below binders, is derived. -/
theorem StepCode.decode_expandConstants
    (roots : ∀ {n : Nat} (code : RootCode n), targetRoot (mapRoot code) =
      mapEndpoints (ConstantExpansion.expand bodies) (sourceRoot code))
    {n : Nat} (code : StepCode Head RootCode n) :
    (code.expandConstants bodies mapRoot).decode headEq targetRoot =
      mapEndpoints (ConstantExpansion.expand bodies) (code.decode headEq sourceRoot) := by
  induction code <;>
    simp_all [StepCode.expandConstants, StepCode.decode, ConstantExpansion.expand,
      ConstantExpansion.expand_inst0, mapEndpoints, Option.map_map, Function.comp_def]

/-- Reuse the existing proof-tree context map; no second certificate grammar
or composition checker is introduced. -/
def Code.expandConstants {n : Nat} (code : Code Head RootCode n) : Code Head RootCode n :=
  code.mapContext (ConstantExpansion.expand bodies) (StepCode.expandConstants bodies mapRoot)

variable [DecidableEq Head]

theorem Code.decode_expandConstants
    (roots : ∀ {n : Nat} (code : RootCode n), targetRoot (mapRoot code) =
      mapEndpoints (ConstantExpansion.expand bodies) (sourceRoot code))
    {n : Nat} {code : Code Head RootCode n} {left right : Tm Head n}
    (accepted : code.decode headEq sourceRoot = some (left, right)) :
    (code.expandConstants bodies mapRoot).decode headEq targetRoot =
      some (ConstantExpansion.expand bodies left, ConstantExpansion.expand bodies right) := by
  exact Code.decode_mapContext_between headEq headEq sourceRoot targetRoot
    (ConstantExpansion.expand bodies) (StepCode.expandConstants bodies mapRoot)
    (StepCode.decode_expandConstants bodies mapRoot headEq sourceRoot targetRoot roots) code accepted

theorem Code.check_expandConstants
    (roots : ∀ {n : Nat} (code : RootCode n), targetRoot (mapRoot code) =
      mapEndpoints (ConstantExpansion.expand bodies) (sourceRoot code))
    {n : Nat} {code : Code Head RootCode n} {left right : Tm Head n}
    (accepted : code.check headEq sourceRoot left right = true) :
    (code.expandConstants bodies mapRoot).check headEq targetRoot
      (ConstantExpansion.expand bodies left) (ConstantExpansion.expand bodies right) = true :=
  decide_eq_true (Code.decode_expandConstants bodies mapRoot headEq sourceRoot targetRoot roots
    (of_decide_eq_true accepted))

omit [DecidableEq Head] in
/-- Expansion preserves selected-step occurrences, while replacing their
actual term payloads. This is not a statement about bytes or machine time. -/
theorem Code.expandConstants_stepCount {n : Nat} (code : Code Head RootCode n) :
    (code.expandConstants bodies mapRoot).stepCount = code.stepCount :=
  Code.stepCount_mapContext (ConstantExpansion.expand bodies) (StepCode.expandConstants bodies mapRoot) code

/-- Original endpoint admission precedes compilation. Constant interpretation
can identify different source terms; the requested source endpoints therefore
remain part of this executable compiler's check. -/
def Code.expandFor? {n : Nat} (code : Code Head RootCode n) (left right : Tm Head n) :
    Option (Code Head RootCode n) :=
  if code.check headEq sourceRoot left right then some (code.expandConstants bodies mapRoot) else none

theorem Code.expandFor?_eq_none_iff {n : Nat} (code : Code Head RootCode n) (left right : Tm Head n) :
    code.expandFor? bodies mapRoot headEq sourceRoot left right = none ↔
      code.check headEq sourceRoot left right = false := by
  cases checked : code.check headEq sourceRoot left right <;> simp [expandFor?, checked]

theorem Code.expandFor?_eq_some_iff {n : Nat} (code : Code Head RootCode n)
    (left right : Tm Head n) (compiled : Code Head RootCode n) :
    code.expandFor? bodies mapRoot headEq sourceRoot left right = some compiled ↔
      code.check headEq sourceRoot left right = true ∧ compiled = code.expandConstants bodies mapRoot := by
  cases checked : code.check headEq sourceRoot left right <;>
    simp [expandFor?, checked, eq_comm]

theorem Code.expandFor?_checked
    (roots : ∀ {n : Nat} (code : RootCode n), targetRoot (mapRoot code) =
      mapEndpoints (ConstantExpansion.expand bodies) (sourceRoot code))
    {n : Nat} {code compiled : Code Head RootCode n} {left right : Tm Head n}
    (returned : code.expandFor? bodies mapRoot headEq sourceRoot left right = some compiled) :
    compiled.check headEq targetRoot (ConstantExpansion.expand bodies left)
      (ConstantExpansion.expand bodies right) = true := by
  obtain ⟨admitted, rfl⟩ := (Code.expandFor?_eq_some_iff bodies mapRoot headEq sourceRoot
    code left right compiled).1 returned
  exact Code.check_expandConstants bodies mapRoot headEq sourceRoot targetRoot roots admitted

end StructuralConversionCode
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace StructuralConversionCode

open ConstantSubstitution

variable {Head : Type}

/-- Interpret retained no-root step data by actual open native values. Binder
positions use the same lifted assignments as the term interpreter. -/
def StepCode.interpretParameters : {n m : Nat} → Values Head m → Sub Head n m →
    StepCode Head (fun _ => Empty) n → StepCode Head (fun _ => Empty) m
  | _, _, values, variables, .betaPi body argument =>
      .betaPi (interpret (liftValues values) (liftSub variables) body) (interpret values variables argument)
  | _, _, values, variables, .betaSigmaFst first second =>
      .betaSigmaFst (interpret values variables first) (interpret values variables second)
  | _, _, values, variables, .betaSigmaSnd first second =>
      .betaSigmaSnd (interpret values variables first) (interpret values variables second)
  | _, _, _, _, .head first second => .head first second
  | _, _, _, _, .root empty => nomatch empty
  | _, _, values, variables, .congPiDom code codomain =>
      .congPiDom (interpretParameters values variables code)
        (interpret (liftValues values) (liftSub variables) codomain)
  | _, _, values, variables, .congPiCod domain code =>
      .congPiCod (interpret values variables domain)
        (interpretParameters (liftValues values) (liftSub variables) code)
  | _, _, values, variables, .congSigmaDom code codomain =>
      .congSigmaDom (interpretParameters values variables code)
        (interpret (liftValues values) (liftSub variables) codomain)
  | _, _, values, variables, .congSigmaCod domain code =>
      .congSigmaCod (interpret values variables domain)
        (interpretParameters (liftValues values) (liftSub variables) code)
  | _, _, values, variables, .congIdTy code left right =>
      .congIdTy (interpretParameters values variables code)
        (interpret values variables left) (interpret values variables right)
  | _, _, values, variables, .congIdLeft type code right =>
      .congIdLeft (interpret values variables type)
        (interpretParameters values variables code) (interpret values variables right)
  | _, _, values, variables, .congIdRight type left code =>
      .congIdRight (interpret values variables type) (interpret values variables left)
        (interpretParameters values variables code)
  | _, _, values, variables, .congLam code =>
      .congLam (interpretParameters (liftValues values) (liftSub variables) code)
  | _, _, values, variables, .congAppFun code argument =>
      .congAppFun (interpretParameters values variables code) (interpret values variables argument)
  | _, _, values, variables, .congAppArg function code =>
      .congAppArg (interpret values variables function) (interpretParameters values variables code)
  | _, _, values, variables, .congPairFst code second =>
      .congPairFst (interpretParameters values variables code) (interpret values variables second)
  | _, _, values, variables, .congPairSnd first code =>
      .congPairSnd (interpret values variables first) (interpretParameters values variables code)
  | _, _, values, variables, .congFst code => .congFst (interpretParameters values variables code)
  | _, _, values, variables, .congSnd code => .congSnd (interpretParameters values variables code)
  | _, _, values, variables, .congRefl code => .congRefl (interpretParameters values variables code)

variable (headEq : Head → Head → Prop) [DecidableRel headEq]

/-- Original primitive endpoints commute with the actual code transformer.
No conversion search or source-body enumeration is inserted. -/
theorem StepCode.decode_interpretParameters {n m : Nat}
    (values : Values Head m) (variables : Sub Head n m)
    (code : StepCode Head (fun _ => Empty) n) :
    (code.interpretParameters values variables).decode headEq FormationCheckedTelescopePrograms.noRoot =
      mapEndpoints (interpret values variables) (code.decode headEq FormationCheckedTelescopePrograms.noRoot) := by
  induction code generalizing m with
  | root empty => exact nomatch empty
  | _ =>
      simp_all [StepCode.interpretParameters, StepCode.decode, interpret, interpret_inst0,
        mapEndpoints, Option.map_map, Function.comp_def]

/-- Retain the original proof composition tree through its existing context map. -/
def Code.interpretParameters {n m : Nat} (code : Code Head (fun _ => Empty) n)
    (values : Values Head m) (variables : Sub Head n m) : Code Head (fun _ => Empty) m :=
  code.mapContext (interpret values variables) (StepCode.interpretParameters values variables)

variable [DecidableEq Head]

theorem Code.interpretParameters_checked {n m : Nat}
    {code : Code Head (fun _ => Empty) n} {first last : Tm Head n}
    (accepted : code.check headEq FormationCheckedTelescopePrograms.noRoot first last = true)
    (values : Values Head m) (variables : Sub Head n m) :
    (code.interpretParameters values variables).check headEq FormationCheckedTelescopePrograms.noRoot
      (interpret values variables first) (interpret values variables last) = true :=
  Code.check_mapContext headEq FormationCheckedTelescopePrograms.noRoot
    (interpret values variables) (StepCode.interpretParameters values variables)
    (StepCode.decode_interpretParameters headEq values variables) accepted

omit [DecidableEq Head] in
/-- Count retained selected inference occurrences separately from payloads. -/
theorem Code.interpretParameters_stepCount {n m : Nat} (code : Code Head (fun _ => Empty) n)
    (values : Values Head m) (variables : Sub Head n m) :
    (code.interpretParameters values variables).stepCount = code.stepCount :=
  Code.stepCount_mapContext (interpret values variables) (StepCode.interpretParameters values variables) code

/-- Preserve original admission before any primitive value can merge source
terms or repair a rejected composition. -/
def Code.interpretFor? {n m : Nat} (code : Code Head (fun _ => Empty) n)
    (first last : Tm Head n) (values : Values Head m) (variables : Sub Head n m) :
    Option (Code Head (fun _ => Empty) m) :=
  if code.check headEq FormationCheckedTelescopePrograms.noRoot first last then
    some (code.interpretParameters values variables) else none

theorem Code.interpretFor?_eq_none_iff {n m : Nat} (code : Code Head (fun _ => Empty) n)
    (first last : Tm Head n) (values : Values Head m) (variables : Sub Head n m) :
    code.interpretFor? headEq first last values variables = none ↔
      code.check headEq FormationCheckedTelescopePrograms.noRoot first last = false := by
  cases checked : code.check headEq FormationCheckedTelescopePrograms.noRoot first last <;>
    simp [Code.interpretFor?, checked]


theorem Code.interpretFor?_eq_some_iff {n m : Nat} (code : Code Head (fun _ => Empty) n)
    (first last : Tm Head n) (values : Values Head m) (variables : Sub Head n m)
    (compiled : Code Head (fun _ => Empty) m) :
    code.interpretFor? headEq first last values variables = some compiled ↔
      code.check headEq FormationCheckedTelescopePrograms.noRoot first last = true ∧
        compiled = code.interpretParameters values variables := by
  cases checked : code.check headEq FormationCheckedTelescopePrograms.noRoot first last <;>
    simp [Code.interpretFor?, checked, eq_comm]

theorem Code.interpretFor?_checked {n m : Nat}
    {code : Code Head (fun _ => Empty) n} {first last : Tm Head n}
    {values : Values Head m} {variables : Sub Head n m}
    {compiled : Code Head (fun _ => Empty) m}
    (returned : code.interpretFor? headEq first last values variables = some compiled) :
    compiled.check headEq FormationCheckedTelescopePrograms.noRoot
      (interpret values variables first) (interpret values variables last) = true := by
  obtain ⟨accepted, rfl⟩ := (Code.interpretFor?_eq_some_iff headEq code first last values variables compiled).1 returned
  exact Code.interpretParameters_checked headEq accepted values variables

private def emptyRootSubstitution {n m : Nat} (_ : Sub Head n m) (code : Empty) : Empty := nomatch code

/-- Abstract selected source constants once, then use the original code
substitution operation to supply actual native parameter values. -/
def Code.specializeParameters {k m : Nat} (code : Code Head (fun _ => Empty) 0)
    (positions : DeclName → Option (Fin k)) (arguments : Sub Head k m) :
    Code Head (fun _ => Empty) m :=
  (code.interpretParameters (parameterValues positions) Fin.elim0).substitute emptyRootSubstitution arguments

theorem Code.specializeParameters_checked {k m : Nat}
    {code : Code Head (fun _ => Empty) 0} {first last : Tm Head 0}
    (accepted : code.check headEq FormationCheckedTelescopePrograms.noRoot first last = true)
    (positions : DeclName → Option (Fin k)) (arguments : Sub Head k m) :
    (code.specializeParameters positions arguments).check headEq FormationCheckedTelescopePrograms.noRoot
      (interpret (specializedValues positions arguments) Fin.elim0 first)
      (interpret (specializedValues positions arguments) Fin.elim0 last) = true := by
  have opened := Code.interpretParameters_checked headEq accepted (parameterValues positions) Fin.elim0
  have specialized := Code.check_substitute emptyRootSubstitution headEq FormationCheckedTelescopePrograms.noRoot
    (fun _ empty => nomatch empty) arguments _ opened
  change Code.check headEq FormationCheckedTelescopePrograms.noRoot _
    (subst arguments (parameterTerm positions first)) (subst arguments (parameterTerm positions last)) = true at specialized
  rw [parameterTerm_specialize, parameterTerm_specialize] at specialized
  exact specialized

omit [DecidableEq Head] [DecidableRel headEq] in
theorem Code.specializeParameters_stepCount {k m : Nat}
    (code : Code Head (fun _ => Empty) 0) (positions : DeclName → Option (Fin k))
    (arguments : Sub Head k m) :
    (code.specializeParameters positions arguments).stepCount = code.stepCount :=
  (Code.substitute_stepCount emptyRootSubstitution _ _).trans (Code.interpretParameters_stepCount _ _ _)

/-- Apply one retained closed template to its actual native parameters, then
replay its specialized evidence. The original composition and every selected
inference occurrence remain explicit in the returned code. -/
def Code.applyParameters {k m : Nat} (code : Code Head (fun _ => Empty) 0)
    (context : Ctx Head k) (positions : DeclName → Option (Fin k))
    (arguments : Sub Head k m) (first : Tm Head 0) : Code Head (fun _ => Empty) m :=
  .trans
    (FormationCheckedTelescopePrograms.applicationCode context arguments (parameterTerm positions first))
    (code.specializeParameters positions arguments)

omit [DecidableRel headEq] in
theorem Code.applyParameters_checked {k m : Nat}
    {code : Code Head (fun _ => Empty) 0} {first last : Tm Head 0}
    (accepted : code.check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot first last = true)
    (context : Ctx Head k) (positions : DeclName → Option (Fin k)) (arguments : Sub Head k m) :
    (code.applyParameters context positions arguments first).check (fun _ _ => False)
      FormationCheckedTelescopePrograms.noRoot
      (TelescopeAbstraction.applyClosed context arguments
        (liftClosed (TelescopeAbstraction.closeTerm context (parameterTerm positions first))))
      (interpret (specializedValues positions arguments) Fin.elim0 last) = true := by
  have application := FormationCheckedTelescopePrograms.applicationCode_checked
    context arguments (parameterTerm positions first)
  rw [parameterTerm_specialize] at application
  exact Code.check_trans (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot
    application (Code.specializeParameters_checked (fun _ _ => False) accepted positions arguments)

omit [DecidableEq Head] [DecidableRel headEq] in
/-- Count parameter-application beta steps and retained proof steps together.
This does not charge the term payloads, comparisons or executed instructions. -/
theorem Code.applyParameters_stepCount {k m : Nat}
    (code : Code Head (fun _ => Empty) 0) (context : Ctx Head k)
    (positions : DeclName → Option (Fin k)) (arguments : Sub Head k m) (first : Tm Head 0) :
    (code.applyParameters context positions arguments first).stepCount = k + code.stepCount := by
  simp only [Code.applyParameters, Code.stepCount,
    FormationCheckedTelescopePrograms.applicationCode_stepCount, Code.specializeParameters_stepCount]

/-- Admission of the original requested endpoints is checked before compiling
or applying the template, so parameter values cannot repair an invalid source. -/
def Code.applyParametersFor? {k m : Nat} (code : Code Head (fun _ => Empty) 0)
    (context : Ctx Head k) (positions : DeclName → Option (Fin k))
    (arguments : Sub Head k m) (first last : Tm Head 0) : Option (Code Head (fun _ => Empty) m) :=
  if code.check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot first last then
    some (code.applyParameters context positions arguments first) else none

omit [DecidableRel headEq] in
theorem Code.applyParametersFor?_eq_none_iff {k m : Nat}
    (code : Code Head (fun _ => Empty) 0) (context : Ctx Head k)
    (positions : DeclName → Option (Fin k)) (arguments : Sub Head k m) (first last : Tm Head 0) :
    code.applyParametersFor? context positions arguments first last = none ↔
      code.check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot first last = false := by
  cases checked : code.check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot first last <;>
    simp [Code.applyParametersFor?, checked]

omit [DecidableRel headEq] in
theorem Code.applyParametersFor?_eq_some_iff {k m : Nat}
    (code : Code Head (fun _ => Empty) 0) (context : Ctx Head k)
    (positions : DeclName → Option (Fin k)) (arguments : Sub Head k m)
    (first last : Tm Head 0) (compiled : Code Head (fun _ => Empty) m) :
    code.applyParametersFor? context positions arguments first last = some compiled ↔
      code.check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot first last = true ∧
        compiled = code.applyParameters context positions arguments first := by
  cases checked : code.check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot first last <;>
    simp [Code.applyParametersFor?, checked, eq_comm]

omit [DecidableRel headEq] in
theorem Code.applyParametersFor?_checked {k m : Nat}
    {code : Code Head (fun _ => Empty) 0} {context : Ctx Head k}
    {positions : DeclName → Option (Fin k)} {arguments : Sub Head k m}
    {first last : Tm Head 0} {compiled : Code Head (fun _ => Empty) m}
    (returned : code.applyParametersFor? context positions arguments first last = some compiled) :
    compiled.check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot
      (TelescopeAbstraction.applyClosed context arguments
        (liftClosed (TelescopeAbstraction.closeTerm context (parameterTerm positions first))))
      (interpret (specializedValues positions arguments) Fin.elim0 last) = true := by
  obtain ⟨accepted, rfl⟩ := (Code.applyParametersFor?_eq_some_iff code context positions
    arguments first last compiled).1 returned
  exact Code.applyParameters_checked accepted context positions arguments

end StructuralConversionCode
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
