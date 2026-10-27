import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionCertificate
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionSubstitution
import Mettapedia.TypeTheory.BubbleReindexing

/-!
# Conversion trees elaborated into the maintained structural certificates

A scoped source-term readout and checked certificates for the generators
determine a certificate for the entire conversion tree. The same construction
serves typed declaration instances and interpreted annotated terms. A second
decoder may check the emitted code when it checks every emitted generator.

The substitution law compares full finite codes, including cited rules and
their arguments. It does not infer typing, interpretation or normalization
from a bare code.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.StructuralConversionCode
namespace Elaboration

open Mettapedia.TypeTheory

universe uIndex uState uBubble uStep
variable {Index : Type uIndex} {Head : Type} {RootCode : Nat → Type}
    [DecidableEq Head] (B : BubbleConversion.Bubbles.{uIndex, uState, uBubble, uStep} Index)
    (arity : Index → Nat) (readout : {index : Index} → B.State index → Tm Head (arity index))
    (headEq : Head → Head → Prop) [DecidableRel headEq]
    (decodeRoot : {n : Nat} → RootCode n → Option (Tm Head n × Tm Head n))

def equality : B.GlobalEquality where
  Eq source target := Certificate headEq decodeRoot (readout source) (readout target)
  refl source := .refl (readout source)
  symm proof := proof.symm
  trans first second := first.trans second

variable {B arity readout headEq decodeRoot} {enabled : B.Bubble}
    (justify : {index : Index} → {source target : B.State index} → B.Step enabled source target →
      Certificate headEq decodeRoot (readout source) (readout target))

def emit {index : Index} {source target : B.State index} (path : B.Conv enabled source target) :
    Certificate headEq decodeRoot (readout source) (readout target) :=
  B.sound (equality B arity readout headEq decodeRoot) justify path

theorem code_step {index : Index} {source target : B.State index} (step : B.Step enabled source target) :
    (emit justify (.step step)).code = (justify step).code := by
  exact congrArg (fun certificate : Certificate headEq decodeRoot (readout source) (readout target) => certificate.code)
    (BubbleElaboration.sound_step B (equality B arity readout headEq decodeRoot) justify step)

theorem code_refl {index : Index} (state : B.State index) :
    (emit justify (.refl (computation := FreeConversion.computation B.State (B.Step enabled)) state)).code =
      .refl (readout state) := by
  simp [emit, equality, Certificate.refl]

theorem code_symm {index : Index} {source target : B.State index} (path : B.Conv enabled source target) :
    (emit justify (.symm path)).code = .symm (emit justify path).code := by
  simp [emit, equality, Certificate.symm]

theorem code_trans {index : Index} {source middle target : B.State index}
    (first : B.Conv enabled source middle) (second : B.Conv enabled middle target) :
    (emit justify (.trans first second)).code = .trans (emit justify first).code (emit justify second).code := by
  simp [emit, equality, Certificate.trans]

/-- Checking each emitted generator with another decoder suffices for the
whole emitted certificate. This includes restriction to a selected rule policy. -/
theorem checkWith (headEq' : Head → Head → Prop) [DecidableRel headEq']
    (decodeRoot' : {n : Nat} → RootCode n → Option (Tm Head n × Tm Head n))
    (generators : ∀ {index : Index} {source target : B.State index} (step : B.Step enabled source target),
      (justify step).code.check headEq' decodeRoot' (readout source) (readout target) = true)
    {index : Index} {source target : B.State index} (path : B.Conv enabled source target) :
    (emit justify path).code.check headEq' decodeRoot' (readout source) (readout target) = true := by
  induction path using @JudgmentalEquality.ConversionEvidence.rec Index
      (FreeConversion.computation B.State (B.Step enabled)) index with
  | step step => simpa only [code_step] using generators step
  | refl state => simpa only [code_refl] using Code.check_refl headEq' decodeRoot' (readout state)
  | symm path ih => simpa only [code_symm] using Code.check_symm headEq' decodeRoot' ih
  | trans first second ihFirst ihSecond =>
      simpa only [code_trans] using Code.check_trans headEq' decodeRoot' ihFirst ihSecond

theorem stepCount
    (generators : ∀ {index : Index} {source target : B.State index} (step : B.Step enabled source target),
      (justify step).code.stepCount = 1)
    {index : Index} {source target : B.State index} (path : B.Conv enabled source target) :
    (emit justify path).code.stepCount = BubbleElaboration.stepCount path := by
  induction path using @JudgmentalEquality.ConversionEvidence.rec Index
      (FreeConversion.computation B.State (B.Step enabled)) index with
  | step step => simpa only [code_step, BubbleElaboration.stepCount_step] using generators step
  | refl state => simp only [code_refl, Code.stepCount, BubbleElaboration.stepCount_refl]
  | symm path ih => simpa only [code_symm, Code.stepCount, BubbleElaboration.stepCount_symm] using ih
  | trans first second ihFirst ihSecond =>
      simp only [code_trans, Code.stepCount, BubbleElaboration.stepCount_trans, ihFirst, ihSecond]

/-- The existing finite-code substitution commutes with any concrete fibre
map whose readout and generator codes have the stated substitution laws. -/
theorem substitute (substituteRoot : {n m : Nat} → Sub Head n m → RootCode n → RootCode m)
    {i j : Index} (map : BubbleReindexing.FibreMap B enabled i j)
    (substitution : Sub Head (arity i) (arity j))
    (terms : ∀ source : B.State i, readout (map.state source) = subst substitution (readout source))
    (generators : ∀ {source target : B.State i} (step : B.Step enabled source target),
      (justify (map.step step)).code = (justify step).code.substitute substituteRoot substitution)
    {source target : B.State i} (path : B.Conv enabled source target) :
    (emit justify (map.mapConv path)).code = (emit justify path).code.substitute substituteRoot substitution := by
  induction path using @JudgmentalEquality.ConversionEvidence.rec Index
      (FreeConversion.computation B.State (B.Step enabled)) i with
  | step step =>
      simpa only [BubbleReindexing.FibreMap.mapConv, code_step] using generators step
  | refl source =>
      simp only [BubbleReindexing.FibreMap.mapConv, code_refl, Code.substitute, terms]
  | symm path ih =>
      simp only [BubbleReindexing.FibreMap.mapConv, code_symm, Code.substitute, ih]
  | trans first second ihFirst ihSecond =>
      simp only [BubbleReindexing.FibreMap.mapConv, code_trans, Code.substitute, ihFirst, ihSecond]

#print axioms emit
#print axioms checkWith
#print axioms stepCount
#print axioms substitute

end Elaboration
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.StructuralConversionCode
