import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedFamilyConversionBubbles

/-!
# Substitution of typed declaration conversion trees and their emitted codes

Typed context maps act on the existing schema instances, keeping their row
addresses and composing their actual assignments. Elaborating the resulting
tree gives exactly the finite certificate obtained by the existing structural
certificate substitution program. Both routes retain the binary tree and all
selected inference occurrences, including reverse steps and repeated uses.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace Declaration.IndexedFamily.ConversionBubbles

open Mettapedia.TypeTheory
open BubbleConversion BubbleElaboration ComputationAuthority

variable {Head : Type} {base : Rules Head} {signature : Signature Head}
    {computation : ProofRelevantRootComputation Head}
    {schemas : Checking.Schemas base signature computation}
    {index : TypingIndex Head} {m : Nat}

def substitutedIndex (index : TypingIndex Head) (context : Ctx Head m)
    (sigma : Sub Head index.arity m) : TypingIndex Head :=
  ⟨m, context, subst sigma index.type⟩

def substituteState (context : Ctx Head m) (sigma : Sub Head index.arity m)
    (typed : CtxMor (extendRules base signature) index.context context sigma)
    (state : State base signature index) :
    State base signature (substitutedIndex index context sigma) :=
  ⟨subst sigma state.1, ⟨state.2.down.substitute typed⟩⟩

def Step.substitute {enabled : Fin (Checking.table schemas).length → Bool}
    (context : Ctx Head m) (sigma : Sub Head index.arity m)
    (typed : CtxMor (extendRules base signature) index.context context sigma)
    {source target : State base signature index}
    (step : Step schemas enabled source target) :
    Step schemas enabled (substituteState context sigma typed source)
      (substituteState context sigma typed target) where
  row := step.row
  permitted := step.permitted
  occurrence := {
    substitution := subComp sigma step.occurrence.substitution
    typed := step.occurrence.typed.comp typed
    sourceEquation := by rw [← subst_subComp, step.occurrence.sourceEquation]; rfl
    targetEquation := by rw [← subst_subComp, step.occurrence.targetEquation]; rfl
    typeEquation := by rw [← subst_subComp, step.occurrence.typeEquation]; rfl }

theorem Step.rootCode_substitute {enabled : Fin (Checking.table schemas).length → Bool}
    (context : Ctx Head m) (sigma : Sub Head index.arity m)
    (typed : CtxMor (extendRules base signature) index.context context sigma)
    {source target : State base signature index}
    (step : Step schemas enabled source target) :
    (step.substitute context sigma typed).rootCode = step.rootCode.substitute sigma := by
  simp [Step.rootCode, Step.substitute, SchemaTableConversionCode.encode,
    SchemaTableConversionCode.Code.substitute, SchemaTableConversionCode.Code.mapArguments,
    subComp, List.map_ofFn, Function.comp_def]

def substitutionMap {enabled : Fin (Checking.table schemas).length → Bool}
    (context : Ctx Head m) (sigma : Sub Head index.arity m)
    (typed : CtxMor (extendRules base signature) index.context context sigma) :
    BubbleReindexing.FibreMap (bubbles schemas) enabled index (substitutedIndex index context sigma) where
  state := substituteState context sigma typed
  step := Step.substitute context sigma typed

def substitute {enabled : Fin (Checking.table schemas).length → Bool}
    (context : Ctx Head m) (sigma : Sub Head index.arity m)
    (typed : CtxMor (extendRules base signature) index.context context sigma)
    {source target : State base signature index}
    (path : (bubbles schemas).Conv enabled source target) :
    (bubbles schemas).Conv enabled (substituteState context sigma typed source)
      (substituteState context sigma typed target) :=
  (substitutionMap context sigma typed).mapConv path

variable (schemas)
variable [DecidableEq Head] [DecidableRel base.headEq]

/-- The two programs agree on the full emitted syntax, not just its decoded
endpoints. The root-code substitution is the existing table program. -/
theorem elaborate_substitute {enabled : Fin (Checking.table schemas).length → Bool}
    (context : Ctx Head m) (sigma : Sub Head index.arity m)
    (typed : CtxMor (extendRules base signature) index.context context sigma)
    {source target : State base signature index}
    (path : (bubbles schemas).Conv enabled source target) :
    (elaborate schemas (substitute context sigma typed path)).code =
      (elaborate schemas path).code.substitute SchemaTableConversionCode.Code.substitute sigma := by
  apply StructuralConversionCode.Elaboration.substitute (B := bubbles schemas)
    (arity := TypingIndex.arity) (readout := fun state => state.1) (justify schemas)
    SchemaTableConversionCode.Code.substitute (substitutionMap context sigma typed) sigma (fun _ => rfl) ?_ path
  intro source target step
  simp only [substitutionMap, justify, StructuralConversionCode.Certificate.single, Step.rootCode_substitute,
    StructuralConversionCode.Code.substitute, StructuralConversionCode.StepCode.substitute]

theorem substituted_code_accepted {enabled : Fin (Checking.table schemas).length → Bool}
    (context : Ctx Head m) (sigma : Sub Head index.arity m)
    (typed : CtxMor (extendRules base signature) index.context context sigma)
    {source target : State base signature index}
    (path : (bubbles schemas).Conv enabled source target) :
    ((elaborate schemas path).code.substitute SchemaTableConversionCode.Code.substitute sigma).check
      base.headEq (SchemaTableConversionCode.decode (Checking.table schemas) enabled)
      (subst sigma source.1) (subst sigma target.1) = true := by
  rw [← elaborate_substitute schemas context sigma typed path]
  exact elaborate_selected schemas (substitute context sigma typed path)

theorem substituted_work {enabled : Fin (Checking.table schemas).length → Bool}
    (context : Ctx Head m) (sigma : Sub Head index.arity m)
    (typed : CtxMor (extendRules base signature) index.context context sigma)
    {source target : State base signature index}
    (path : (bubbles schemas).Conv enabled source target) :
    (elaborate schemas (substitute context sigma typed path)).code.stepCount =
      BubbleElaboration.stepCount path := by
  rw [elaborate_substitute, StructuralConversionCode.Code.substitute_stepCount, elaborate_work]

#print axioms Step.rootCode_substitute
#print axioms elaborate_substitute
#print axioms substituted_code_accepted
#print axioms substituted_work

end Declaration.IndexedFamily.ConversionBubbles
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
