import Mettapedia.Languages.Megalodon.HOLEqualityProofTemplates
import Mettapedia.Languages.Megalodon.HOLProofSpecialization

/-!
# Native equality inference for typed HOL arguments

The source equality rules instantiate the existing binary-relation equality
proofs. The programs, canonical conclusions, ordered contexts and argument
formation conditions remain explicit. Extensionality is handled separately
from these axiom-free equality combinators.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.HOLEqualityProofInference

open Mettapedia.Logic.HOL
open MathdataKernel HenkinTermInterpretation HOLTermEncoding HOLNormalForms HOLProofInference

variable {environment : Environment} {gamma : Ctx Base} {type domain result : Ty Base}
variable {depth : Nat} {assumptions : List (Formula (Constant environment) gamma)}

theorem eqRefl (value : Term (Constant environment) gamma type)
    (typeFormed : (reifyType type).plainWellFormed depth = true)
    (formed : plainAnnotations depth (native value) = true)
    (unfoldingAbsent : DeltaNormalInvariant.Normal environment (native value))
    (contextNormal : DeltaNormalInvariant.ContextNormal environment (context depth assumptions)) :
    Infers depth assumptions
      (.termApp (RelationEqualityProofs.reflexivity (reifyType type)) (native value)) (.eq value value) := by
  have inferred := HOLProofInference.allE value formed unfoldingAbsent contextNormal
    (HOLEqualityProofTemplates.reflexivity_infers depth type typeFormed assumptions)
  simpa only [instantiate, subst, Subst.single] using inferred

theorem eqSymm {program : Pf} {left right : Term (Constant environment) gamma type}
    (typeFormed : (reifyType type).plainWellFormed depth = true)
    (leftFormed : plainAnnotations depth (native left) = true)
    (rightFormed : plainAnnotations depth (native right) = true)
    (leftNormal : DeltaNormalInvariant.Normal environment (native left))
    (rightNormal : DeltaNormalInvariant.Normal environment (native right))
    (contextNormal : DeltaNormalInvariant.ContextNormal environment (context depth assumptions))
    (inferred : Infers depth assumptions program (.eq left right)) :
    Infers depth assumptions
      (.proofApp (.termApp (.termApp (RelationEqualityProofs.symmetry (reifyType type))
        (native left)) (native right)) program) (.eq right left) := by
  have specialized := HOLProofSpecialization.allE2 left right leftFormed rightFormed
    leftNormal rightNormal contextNormal
    (HOLEqualityProofTemplates.symmetry_infers depth type typeFormed assumptions)
  have function : Infers depth assumptions
      (.termApp (.termApp (RelationEqualityProofs.symmetry (reifyType type))
        (native left)) (native right)) (.imp (.eq left right) (.eq right left)) := by
    simpa only [subst, Subst.cons, Subst.single] using specialized
  exact HOLProofInference.impE function inferred

theorem eqTrans {firstProgram secondProgram : Pf}
    {first second third : Term (Constant environment) gamma type}
    (typeFormed : (reifyType type).plainWellFormed depth = true)
    (firstFormed : plainAnnotations depth (native first) = true)
    (secondFormed : plainAnnotations depth (native second) = true)
    (thirdFormed : plainAnnotations depth (native third) = true)
    (firstNormal : DeltaNormalInvariant.Normal environment (native first))
    (secondNormal : DeltaNormalInvariant.Normal environment (native second))
    (thirdNormal : DeltaNormalInvariant.Normal environment (native third))
    (contextNormal : DeltaNormalInvariant.ContextNormal environment (context depth assumptions))
    (one : Infers depth assumptions firstProgram (.eq first second))
    (two : Infers depth assumptions secondProgram (.eq second third)) :
    Infers depth assumptions
      (.proofApp (.proofApp (.termApp (.termApp (.termApp
        (RelationEqualityProofs.transitivity (reifyType type)) (native first)) (native second))
        (native third)) firstProgram) secondProgram) (.eq first third) := by
  have specialized := HOLProofSpecialization.allE3 first second third
    firstFormed secondFormed thirdFormed firstNormal secondNormal thirdNormal contextNormal
    (HOLEqualityProofTemplates.transitivity_infers depth type typeFormed assumptions)
  have function : Infers depth assumptions
      (.termApp (.termApp (.termApp (RelationEqualityProofs.transitivity (reifyType type))
        (native first)) (native second)) (native third))
      (.imp (.eq first second) (.imp (.eq second third) (.eq first third))) := by
    simpa only [subst, Subst.cons, Subst.single] using specialized
  exact HOLProofInference.impE (HOLProofInference.impE function one) two

theorem eqApp {program : Pf}
    {left right : Term (Constant environment) gamma (domain ⇒ result)}
    (argument : Term (Constant environment) gamma domain)
    (domainFormed : (reifyType domain).plainWellFormed depth = true)
    (resultFormed : (reifyType result).plainWellFormed depth = true)
    (leftFormed : plainAnnotations depth (native left) = true)
    (rightFormed : plainAnnotations depth (native right) = true)
    (argumentFormed : plainAnnotations depth (native argument) = true)
    (leftNormal : DeltaNormalInvariant.Normal environment (native left))
    (rightNormal : DeltaNormalInvariant.Normal environment (native right))
    (argumentNormal : DeltaNormalInvariant.Normal environment (native argument))
    (contextNormal : DeltaNormalInvariant.ContextNormal environment (context depth assumptions))
    (inferred : Infers depth assumptions program (.eq left right)) :
    Infers depth assumptions
      (.proofApp (.termApp (.termApp (.termApp
        (RelationEqualityProofs.functionCongruence (reifyType domain) (reifyType result))
        (native left)) (native right)) (native argument)) program)
      (.eq (.app left argument) (.app right argument)) := by
  have specialized := HOLProofSpecialization.allE3 left right argument
    leftFormed rightFormed argumentFormed leftNormal rightNormal argumentNormal contextNormal
    (HOLEqualityProofTemplates.functionCongruence_infers depth domain result
      domainFormed resultFormed assumptions)
  have function : Infers depth assumptions
      (.termApp (.termApp (.termApp
        (RelationEqualityProofs.functionCongruence (reifyType domain) (reifyType result))
        (native left)) (native right)) (native argument))
      (.imp (.eq left right) (.eq (.app left argument) (.app right argument))) := by
    simpa only [subst, Subst.cons, Subst.single] using specialized
  exact HOLProofInference.impE function inferred

theorem eqAppArg {program : Pf}
    (function : Term (Constant environment) gamma (domain ⇒ result))
    {left right : Term (Constant environment) gamma domain}
    (domainFormed : (reifyType domain).plainWellFormed depth = true)
    (resultFormed : (reifyType result).plainWellFormed depth = true)
    (functionFormed : plainAnnotations depth (native function) = true)
    (leftFormed : plainAnnotations depth (native left) = true)
    (rightFormed : plainAnnotations depth (native right) = true)
    (functionNormal : DeltaNormalInvariant.Normal environment (native function))
    (leftNormal : DeltaNormalInvariant.Normal environment (native left))
    (rightNormal : DeltaNormalInvariant.Normal environment (native right))
    (contextNormal : DeltaNormalInvariant.ContextNormal environment (context depth assumptions))
    (inferred : Infers depth assumptions program (.eq left right)) :
    Infers depth assumptions
      (.proofApp (.termApp (.termApp (.termApp
        (RelationEqualityProofs.argumentCongruence (reifyType domain) (reifyType result))
        (native function)) (native left)) (native right)) program)
      (.eq (.app function left) (.app function right)) := by
  have specialized := HOLProofSpecialization.allE3 function left right
    functionFormed leftFormed rightFormed functionNormal leftNormal rightNormal contextNormal
    (HOLEqualityProofTemplates.argumentCongruence_infers depth domain result
      domainFormed resultFormed assumptions)
  have implication : Infers depth assumptions
      (.termApp (.termApp (.termApp
        (RelationEqualityProofs.argumentCongruence (reifyType domain) (reifyType result))
        (native function)) (native left)) (native right))
      (.imp (.eq left right) (.eq (.app function left) (.app function right))) := by
    simpa only [subst, Subst.cons, Subst.single] using specialized
  exact HOLProofInference.impE implication inferred

theorem eqPropEL {program : Pf} {left right : Formula (Constant environment) gamma}
    (leftFormed : plainAnnotations depth (native left) = true)
    (rightFormed : plainAnnotations depth (native right) = true)
    (leftNormal : DeltaNormalInvariant.Normal environment (native left))
    (rightNormal : DeltaNormalInvariant.Normal environment (native right))
    (contextNormal : DeltaNormalInvariant.ContextNormal environment (context depth assumptions))
    (inferred : Infers depth assumptions program (.eq left right)) :
    Infers depth assumptions
      (.proofApp (.termApp (.termApp RelationEqualityProofs.propositionElimination
        (native left)) (native right)) program) (.imp left right) := by
  have specialized := HOLProofSpecialization.allE2 left right leftFormed rightFormed
    leftNormal rightNormal contextNormal
    (HOLEqualityProofTemplates.propositionElimination_infers depth assumptions)
  have function : Infers depth assumptions
      (.termApp (.termApp RelationEqualityProofs.propositionElimination (native left)) (native right))
      (.imp (.eq left right) (.imp left right)) := by
    simpa only [subst, Subst.cons, Subst.single] using specialized
  exact HOLProofInference.impE function inferred

theorem eqPropER {program : Pf} {left right : Formula (Constant environment) gamma}
    (leftFormed : plainAnnotations depth (native left) = true)
    (rightFormed : plainAnnotations depth (native right) = true)
    (leftNormal : DeltaNormalInvariant.Normal environment (native left))
    (rightNormal : DeltaNormalInvariant.Normal environment (native right))
    (contextNormal : DeltaNormalInvariant.ContextNormal environment (context depth assumptions))
    (inferred : Infers depth assumptions program (.eq left right)) :
    Infers depth assumptions
      (.proofApp (.termApp (.termApp RelationEqualityProofs.propositionEliminationReverse
        (native left)) (native right)) program) (.imp right left) := by
  have specialized := HOLProofSpecialization.allE2 left right leftFormed rightFormed
    leftNormal rightNormal contextNormal
    (HOLEqualityProofTemplates.propositionEliminationReverse_infers depth assumptions)
  have function : Infers depth assumptions
      (.termApp (.termApp RelationEqualityProofs.propositionEliminationReverse
        (native left)) (native right)) (.imp (.eq left right) (.imp right left)) := by
    simpa only [subst, Subst.cons, Subst.single] using specialized
  exact HOLProofInference.impE function inferred

theorem beta (body : Term (Constant environment) (domain :: gamma) result)
    (argument : Term (Constant environment) gamma domain)
    (resultFormed : (reifyType result).plainWellFormed depth = true)
    (formed : plainAnnotations depth (native (instantiate argument body)) = true)
    (unfoldingAbsent : DeltaNormalInvariant.Normal environment (native (instantiate argument body)))
    (contextNormal : DeltaNormalInvariant.ContextNormal environment (context depth assumptions)) :
    Infers depth assumptions
      (.termApp (RelationEqualityProofs.reflexivity (reifyType result))
        (native (instantiate argument body))) (.eq (.app (.lam body) argument) (instantiate argument body)) := by
  apply HOLProofInference.of_conversion (eqRefl _ resultFormed formed unfoldingAbsent contextNormal)
  exact BetaEtaSubstitution.eq_congr (.symm _ _ (BetaEtaSubstitution.beta body argument)) (.refl _)

theorem eta (function : Term (Constant environment) gamma (domain ⇒ result))
    (typeFormed : (reifyType (domain ⇒ result)).plainWellFormed depth = true)
    (formed : plainAnnotations depth (native function) = true)
    (unfoldingAbsent : DeltaNormalInvariant.Normal environment (native function))
    (contextNormal : DeltaNormalInvariant.ContextNormal environment (context depth assumptions)) :
    Infers depth assumptions
      (.termApp (RelationEqualityProofs.reflexivity (reifyType (domain ⇒ result))) (native function))
      (.eq (.lam (.app (weaken function) (.var .vz))) function) := by
  apply HOLProofInference.of_conversion (eqRefl _ typeFormed formed unfoldingAbsent contextNormal)
  exact BetaEtaSubstitution.eq_congr
    (.symm _ _ (.rel _ _ (.inr (.eta function)))) (.refl _)

#print axioms eqRefl
#print axioms eqSymm
#print axioms eqTrans
#print axioms eqApp
#print axioms eqAppArg
#print axioms eqPropEL
#print axioms eqPropER
#print axioms beta
#print axioms eta

end Mettapedia.Languages.Megalodon.HOLEqualityProofInference
