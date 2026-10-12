import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierClosureRecoveryComputation
import Mettapedia.CategoryTheory.RelativeClosedSyntaxRegularity

/-!
# Every complete closure derivation comes from a finite stage

The actual forty-rule recursion reconstructs formation and equations from
their individual premises. Its bound includes every declaration occurring
in the proof, even when absent from the conclusion. The resulting finite
stage retains the whole raw endpoints, arrows and derivation, so the merged
category introduces no context-identification shortcut.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Closure

open _root_.CategoryTheory
open RelativeClosedSyntax GeneratedCategory Iteration

universe k
variable {C : Type k} [Category.{k} C] (initial : Stage C)

def recover : {judgment : Judgment C (symbols initial)} →
    (tree : Derivation (signature initial) judgment) → (depth : Nat) →
    proofBound initial tree ≤ depth → Recovery initial depth judgment
  | _, .baseObject object, depth, _ => ObjectRecovery.base initial depth object
  | _, .objectName origin, depth, _ => ObjectRecovery.name initial depth origin
  | _, .terminalObject, depth, _ => ObjectRecovery.terminal initial depth
  | _, .productObject first second, depth, admitted => by
      simp only [proofBound] at admitted
      exact ObjectRecovery.product initial depth (recover first depth (by omega)) (recover second depth (by omega))
  | _, .exponentialObject argument result, depth, admitted => by
      simp only [proofBound] at admitted
      exact ObjectRecovery.exponential initial depth (recover argument depth (by omega)) (recover result depth (by omega))
  | _, .equalizerObject source target first second, depth, admitted => by
      simp only [proofBound] at admitted
      exact ObjectRecovery.equalizer initial depth
        (recover source depth (by omega)) (recover target depth (by omega))
        (recover first depth (by omega)) (recover second depth (by omega))
  | _, .baseArrow arrow, depth, _ => ArrowRecovery.base initial depth arrow
  | _, .arrowName origin source target, depth, admitted => by
      simp only [proofBound] at admitted
      exact ArrowRecovery.name initial depth origin (by omega)
        (recover source depth (by omega)) (recover target depth (by omega))
  | _, .identity formed, depth, admitted => ArrowRecovery.identity initial depth (recover formed depth admitted)
  | _, .compose before after, depth, admitted => by
      simp only [proofBound] at admitted
      exact ArrowRecovery.compose initial depth (recover before depth (by omega)) (recover after depth (by omega))
  | _, .terminalArrow formed, depth, admitted => ArrowRecovery.terminal initial depth (recover formed depth admitted)
  | _, .first left right, depth, admitted => by
      simp only [proofBound] at admitted
      exact ArrowRecovery.first initial depth (recover left depth (by omega)) (recover right depth (by omega))
  | _, .second left right, depth, admitted => by
      simp only [proofBound] at admitted
      exact ArrowRecovery.second initial depth (recover left depth (by omega)) (recover right depth (by omega))
  | _, .pair first second, depth, admitted => by
      simp only [proofBound] at admitted
      exact ArrowRecovery.pair initial depth (recover first depth (by omega)) (recover second depth (by omega))
  | _, .evaluation argument result, depth, admitted => by
      simp only [proofBound] at admitted
      exact ArrowRecovery.evaluation initial depth (recover argument depth (by omega)) (recover result depth (by omega))
  | _, .curry context argument result body, depth, admitted => by
      simp only [proofBound] at admitted
      exact ArrowRecovery.curry initial depth
        (recover context depth (by omega)) (recover argument depth (by omega))
        (recover result depth (by omega)) (recover body depth (by omega))
  | _, .equalizerArrow source target first second, depth, admitted => by
      simp only [proofBound] at admitted
      exact ArrowRecovery.equalizerArrow initial depth
        (recover source depth (by omega)) (recover target depth (by omega))
        (recover first depth (by omega)) (recover second depth (by omega))
  | _, .equalizerLift source target context first second candidate commutes, depth, admitted => by
      simp only [proofBound] at admitted
      exact ArrowRecovery.equalizerLift initial depth
        (recover source depth (by omega)) (recover target depth (by omega)) (recover context depth (by omega))
        (recover first depth (by omega)) (recover second depth (by omega))
        (recover candidate depth (by omega)) (recover commutes depth (by omega))
  | _, .reflexivity typed, depth, admitted => EquationRecovery.reflexivity initial depth (recover typed depth admitted)
  | _, .symmetry same, depth, admitted => EquationRecovery.symmetry initial depth (recover same depth admitted)
  | _, .transitivity before after, depth, admitted => by
      simp only [proofBound] at admitted
      exact EquationRecovery.transitivity initial depth (recover before depth (by omega)) (recover after depth (by omega))
  | _, .compositionCongruence before after, depth, admitted => by
      simp only [proofBound] at admitted
      exact EquationRecovery.compositionCongruence initial depth (recover before depth (by omega)) (recover after depth (by omega))
  | _, .pairCongruence before after, depth, admitted => by
      simp only [proofBound] at admitted
      exact EquationRecovery.pairCongruence initial depth (recover before depth (by omega)) (recover after depth (by omega))
  | _, .curryCongruence context argument result same, depth, admitted => by
      simp only [proofBound] at admitted
      exact EquationRecovery.curryCongruence initial depth
        (recover context depth (by omega)) (recover argument depth (by omega))
        (recover result depth (by omega)) (recover same depth (by omega))
  | _, .leftIdentity source typed, depth, admitted => by
      simp only [proofBound] at admitted
      exact EquationRecovery.leftIdentity initial depth (recover source depth (by omega)) (recover typed depth (by omega))
  | _, .rightIdentity target typed, depth, admitted => by
      simp only [proofBound] at admitted
      exact EquationRecovery.rightIdentity initial depth (recover target depth (by omega)) (recover typed depth (by omega))
  | _, .associativity before middle after, depth, admitted => by
      simp only [proofBound] at admitted
      exact EquationRecovery.associativity initial depth
        (recover before depth (by omega)) (recover middle depth (by omega)) (recover after depth (by omega))
  | _, .terminalUniqueness before after, depth, admitted => by
      simp only [proofBound] at admitted
      exact EquationRecovery.terminalUniqueness initial depth (recover before depth (by omega)) (recover after depth (by omega))
  | _, .firstBeta left right before after, depth, admitted => by
      simp only [proofBound] at admitted
      exact EquationRecovery.firstBeta initial depth
        (recover left depth (by omega)) (recover right depth (by omega))
        (recover before depth (by omega)) (recover after depth (by omega))
  | _, .secondBeta left right before after, depth, admitted => by
      simp only [proofBound] at admitted
      exact EquationRecovery.secondBeta initial depth
        (recover left depth (by omega)) (recover right depth (by omega))
        (recover before depth (by omega)) (recover after depth (by omega))
  | _, .productEta left right typed, depth, admitted => by
      simp only [proofBound] at admitted
      exact EquationRecovery.productEta initial depth
        (recover left depth (by omega)) (recover right depth (by omega)) (recover typed depth (by omega))
  | _, .exponentialBeta context argument result body, depth, admitted => by
      simp only [proofBound] at admitted
      exact EquationRecovery.exponentialBeta initial depth
        (recover context depth (by omega)) (recover argument depth (by omega))
        (recover result depth (by omega)) (recover body depth (by omega))
  | _, .exponentialEta context argument result typed, depth, admitted => by
      simp only [proofBound] at admitted
      exact EquationRecovery.exponentialEta initial depth
        (recover context depth (by omega)) (recover argument depth (by omega))
        (recover result depth (by omega)) (recover typed depth (by omega))
  | _, .equalizerCondition source target before after, depth, admitted => by
      simp only [proofBound] at admitted
      exact EquationRecovery.equalizerCondition initial depth
        (recover source depth (by omega)) (recover target depth (by omega))
        (recover before depth (by omega)) (recover after depth (by omega))
  | _, .equalizerBeta source target context before after candidate commutes, depth, admitted => by
      simp only [proofBound] at admitted
      exact EquationRecovery.equalizerBeta initial depth
        (recover source depth (by omega)) (recover target depth (by omega)) (recover context depth (by omega))
        (recover before depth (by omega)) (recover after depth (by omega))
        (recover candidate depth (by omega)) (recover commutes depth (by omega))
  | _, .equalizerUniqueness before after same, depth, admitted => by
      simp only [proofBound] at admitted
      exact EquationRecovery.equalizerUniqueness initial depth
        (recover before depth (by omega)) (recover after depth (by omega)) (recover same depth (by omega))
  | _, .baseIdentity object, depth, _ => EquationRecovery.baseIdentity initial depth object
  | _, .baseComposition before after, depth, _ => EquationRecovery.baseComposition initial depth before after
  | _, .baseEquality same, depth, _ => EquationRecovery.baseEquality initial depth same
  | _, .declaredEquation origin before after, depth, admitted => by
      simp only [proofBound] at admitted
      exact EquationRecovery.declaredEquation initial depth origin (by omega)
        (recover before depth (by omega)) (recover after depth (by omega))

theorem judgment_finite {judgment : Judgment C (symbols initial)}
    (tree : Derivation (signature initial) judgment) :
    ∃ depth, Nonempty (Recovery initial depth judgment) :=
  ⟨proofBound initial tree, ⟨recover initial tree _ (Nat.le_refl _)⟩⟩

theorem object_formation_finite {code : ObjectCode C (symbols initial)}
    (tree : Derivation (signature initial) (.object code)) :
    ∃ depth, ∃ previous : ObjectCode C (stages initial depth).symbols,
      Nonempty (Derivation (stages initial depth).presentation (.object previous)) ∧
      objectCode initial depth previous = code := by
  let recovered := recover initial tree (proofBound initial tree) (Nat.le_refl _)
  exact ⟨_, recovered.code, ⟨recovered.formed⟩, recovered.read⟩

theorem arrow_formation_finite {source target : ObjectCode C (symbols initial)}
    {code : ArrowCode C (symbols initial)} (tree : Derivation (signature initial) (.arrow source target code)) :
    ∃ depth, ∃ previousSource previousTarget : ObjectCode C (stages initial depth).symbols,
      ∃ previous : ArrowCode C (stages initial depth).symbols,
        Nonempty (Derivation (stages initial depth).presentation (.arrow previousSource previousTarget previous)) ∧
        objectCode initial depth previousSource = source ∧
        objectCode initial depth previousTarget = target ∧ arrowCode initial depth previous = code := by
  let recovered := recover initial tree (proofBound initial tree) (Nat.le_refl _)
  exact ⟨_, recovered.source, recovered.target, recovered.code, ⟨recovered.admitted⟩,
    recovered.source_read, recovered.target_read, recovered.read⟩

theorem equation_finite {source target : ObjectCode C (symbols initial)}
    {first second : ArrowCode C (symbols initial)}
    (tree : Derivation (signature initial) (.equation source target first second)) :
    ∃ depth, ∃ previousSource previousTarget : ObjectCode C (stages initial depth).symbols,
      ∃ previousFirst previousSecond : ArrowCode C (stages initial depth).symbols,
        Nonempty (Derivation (stages initial depth).presentation
          (.equation previousSource previousTarget previousFirst previousSecond)) ∧
        objectCode initial depth previousSource = source ∧ objectCode initial depth previousTarget = target ∧
        arrowCode initial depth previousFirst = first ∧ arrowCode initial depth previousSecond = second := by
  let recovered := recover initial tree (proofBound initial tree) (Nat.le_refl _)
  exact ⟨_, recovered.source, recovered.target, recovered.first, recovered.second, ⟨recovered.admitted⟩,
    recovered.source_read, recovered.target_read, recovered.first_read, recovered.second_read⟩

theorem whole_object_finite (object : Object (signature initial)) :
    ∃ depth, ∃ previous : Object (stages initial depth).presentation,
      (stageMap initial depth).object previous = object := by
  let recovered := recover initial object.formed.some (proofBound initial object.formed.some) (Nat.le_refl _)
  refine ⟨_, ⟨recovered.code, ⟨recovered.formed⟩⟩, ?_⟩
  exact Object.ext recovered.read

theorem whole_arrow_finite {source target : Object (signature initial)} (arrow : RawHom source target) :
    ∃ depth, ∃ previousSource previousTarget : Object (stages initial depth).presentation,
      ∃ previous : RawHom previousSource previousTarget,
        (stageMap initial depth).object previousSource = source ∧
        (stageMap initial depth).object previousTarget = target ∧
        ((stageMap initial depth).rawArrow previous).code = arrow.code := by
  let recovered := recover initial arrow.admitted.some (proofBound initial arrow.admitted.some) (Nat.le_refl _)
  have formed := Regularity.arrow_endpoints (⟨recovered.admitted⟩)
  refine ⟨_, ⟨recovered.source, formed.1⟩, ⟨recovered.target, formed.2⟩,
    ⟨recovered.code, ⟨recovered.admitted⟩⟩, ?_, ?_, recovered.read⟩
  · exact Object.ext recovered.source_read
  · exact Object.ext recovered.target_read

end Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Closure
