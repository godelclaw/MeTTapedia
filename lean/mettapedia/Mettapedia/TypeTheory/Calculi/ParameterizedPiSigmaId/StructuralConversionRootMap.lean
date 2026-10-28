import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionCode

/-!
# Re-encoding local root evidence in structural conversion programs

Only root payloads change. Terms, binder scopes, composition order and exact
endpoints are retained. Agreement of the local root readers derives equality
of the complete decoder, including failed reads; no whole-program soundness
condition is supplied.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.StructuralConversionCode

variable {Head : Type} {Source Target : Nat → Type}

def StepCode.mapRoot (map : {n : Nat} → Source n → Target n) :
    {n : Nat} → StepCode Head Source n → StepCode Head Target n
  | _, .betaPi body argument => .betaPi body argument
  | _, .betaSigmaFst first second => .betaSigmaFst first second
  | _, .betaSigmaSnd first second => .betaSigmaSnd first second
  | _, .head first second => .head first second
  | _, .root code => .root (map code)
  | _, .congPiDom code body => .congPiDom (code.mapRoot map) body
  | _, .congPiCod domain code => .congPiCod domain (code.mapRoot map)
  | _, .congSigmaDom code body => .congSigmaDom (code.mapRoot map) body
  | _, .congSigmaCod domain code => .congSigmaCod domain (code.mapRoot map)
  | _, .congIdTy code first second => .congIdTy (code.mapRoot map) first second
  | _, .congIdLeft type code second => .congIdLeft type (code.mapRoot map) second
  | _, .congIdRight type first code => .congIdRight type first (code.mapRoot map)
  | _, .congLam code => .congLam (code.mapRoot map)
  | _, .congAppFun code argument => .congAppFun (code.mapRoot map) argument
  | _, .congAppArg function code => .congAppArg function (code.mapRoot map)
  | _, .congPairFst code second => .congPairFst (code.mapRoot map) second
  | _, .congPairSnd first code => .congPairSnd first (code.mapRoot map)
  | _, .congFst code => .congFst (code.mapRoot map)
  | _, .congSnd code => .congSnd (code.mapRoot map)
  | _, .congRefl code => .congRefl (code.mapRoot map)

def Code.mapRoot (map : {n : Nat} → Source n → Target n) :
    {n : Nat} → Code Head Source n → Code Head Target n
  | _, .single step => .single (step.mapRoot map)
  | _, .refl term => .refl term
  | _, .symm code => .symm (code.mapRoot map)
  | _, .trans first second => .trans (first.mapRoot map) (second.mapRoot map)

variable (headEq : Head → Head → Prop) [DecidableRel headEq]
    (source : {n : Nat} → Source n → Option (Tm Head n × Tm Head n))
    (target : {n : Nat} → Target n → Option (Tm Head n × Tm Head n))
    (map : {n : Nat} → Source n → Target n)
    (roots : ∀ {n : Nat} (code : Source n), target (map code) = source code)

include roots in
theorem StepCode.decode_mapRoot {n : Nat} (code : StepCode Head Source n) :
    (code.mapRoot map).decode headEq target = code.decode headEq source := by
  induction code <;> simp_all only [mapRoot, decode]

include roots in
theorem Code.decode_mapRoot [DecidableEq Head] {n : Nat} (code : Code Head Source n) :
    (code.mapRoot map).decode headEq target = code.decode headEq source := by
  induction code with
  | single step =>
      simpa only [mapRoot, decode] using StepCode.decode_mapRoot headEq source target map roots step
  | refl term => simp only [mapRoot, decode]
  | symm code ih => simp only [mapRoot, decode, ih]
  | trans first second firstIH secondIH => simp only [mapRoot, decode, firstIH, secondIH]

include roots in
theorem Code.check_mapRoot [DecidableEq Head] {n : Nat} (code : Code Head Source n)
    (first second : Tm Head n) :
    (code.mapRoot map).check headEq target first second = code.check headEq source first second := by
  simp only [check, Code.decode_mapRoot headEq source target map roots]

theorem StepCode.mapRoot_comp {Final : Nat → Type}
    (first : {n : Nat} → Source n → Target n) (second : {n : Nat} → Target n → Final n)
    {n : Nat} (code : StepCode Head Source n) :
    (code.mapRoot first).mapRoot second = code.mapRoot (fun root => second (first root)) := by
  induction code <;> simp_all only [mapRoot]

theorem Code.mapRoot_comp {Final : Nat → Type}
    (first : {n : Nat} → Source n → Target n) (second : {n : Nat} → Target n → Final n)
    {n : Nat} (code : Code Head Source n) :
    (code.mapRoot first).mapRoot second = code.mapRoot (fun root => second (first root)) := by
  induction code <;> simp_all only [mapRoot, StepCode.mapRoot_comp]

#print axioms StepCode.decode_mapRoot
#print axioms Code.check_mapRoot
#print axioms Code.mapRoot_comp

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.StructuralConversionCode
