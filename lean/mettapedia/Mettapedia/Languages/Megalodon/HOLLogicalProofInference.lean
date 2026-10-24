import Mettapedia.Languages.Megalodon.HOLProofTemplates

/-!
# Instantiating the native logical proof programs

The existing primitive proof schemas are instantiated through the typed
universal-elimination theorem and composed through native proof application.
Every statement retains the actual emitted program and ordered source
assumptions. Annotation formation and definition support are explicit.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.HOLLogicalProofInference

open Mettapedia.Logic.HOL
open MathdataKernel HenkinTermInterpretation HOLTermEncoding HOLNormalForms HOLProofInference

variable {environment : Environment} {gamma : Ctx Base}
variable {depth : Nat} {assumptions : List (Formula (Constant environment) gamma)}

theorem botE {program : Pf} (conclusion : Formula (Constant environment) gamma)
    (formed : plainAnnotations depth (native conclusion) = true)
    (unfoldingAbsent : DeltaNormalInvariant.Normal environment (native conclusion))
    (contextNormal : DeltaNormalInvariant.ContextNormal environment (context depth assumptions))
    (inferred : Infers depth assumptions program .bot) :
    Infers depth assumptions
      (.proofApp (.termApp ImpredicativeLogicalProofs.falsityElimination (native conclusion)) program)
      conclusion := by
  have instantiated := HOLProofInference.allE conclusion formed unfoldingAbsent contextNormal
    (HOLProofTemplates.falsityElimination_infers depth assumptions)
  have function : Infers depth assumptions
      (.termApp ImpredicativeLogicalProofs.falsityElimination (native conclusion))
      (.imp .bot conclusion) := by
    simpa only [HOLProofTemplates.falsityEliminationFormula, instantiate, subst, Subst.single]
      using instantiated
  exact HOLProofInference.impE function inferred

theorem andI {leftProgram rightProgram : Pf}
    {left right : Formula (Constant environment) gamma}
    (leftFormed : plainAnnotations depth (native left) = true)
    (rightFormed : plainAnnotations depth (native right) = true)
    (leftNormal : DeltaNormalInvariant.Normal environment (native left))
    (rightNormal : DeltaNormalInvariant.Normal environment (native right))
    (contextNormal : DeltaNormalInvariant.ContextNormal environment (context depth assumptions))
    (one : Infers depth assumptions leftProgram left)
    (two : Infers depth assumptions rightProgram right) :
    Infers depth assumptions
      (.proofApp (.proofApp
        (.termApp (.termApp ImpredicativeLogicalProofs.conjunctionIntroduction (native left))
          (native right)) leftProgram) rightProgram) (.and left right) := by
  have first := HOLProofInference.allE left leftFormed leftNormal contextNormal
    (HOLProofTemplates.conjunctionIntroduction_infers depth assumptions)
  simp only [instantiate, subst, Subst.single, Subst.lift] at first
  have second := HOLProofInference.allE right rightFormed rightNormal contextNormal first
  have function : Infers depth assumptions
      (.termApp (.termApp ImpredicativeLogicalProofs.conjunctionIntroduction (native left)) (native right))
      (.imp left (.imp right (.and left right))) := by
    have lowered : subst (Subst.single right) (rename Rename.weaken left) = left :=
      instantiate_weaken right left
    simpa only [instantiate, subst, Subst.single, lowered] using second
  exact HOLProofInference.impE (HOLProofInference.impE function one) two

#print axioms botE
#print axioms andI


theorem andEL {program : Pf} {left right : Formula (Constant environment) gamma}
    (leftFormed : plainAnnotations depth (native left) = true)
    (rightFormed : plainAnnotations depth (native right) = true)
    (leftNormal : DeltaNormalInvariant.Normal environment (native left))
    (rightNormal : DeltaNormalInvariant.Normal environment (native right))
    (contextNormal : DeltaNormalInvariant.ContextNormal environment (context depth assumptions))
    (inferred : Infers depth assumptions program (.and left right)) :
    Infers depth assumptions
      (.proofApp (.termApp (.termApp ImpredicativeLogicalProofs.conjunctionLeft (native left))
        (native right)) program) (left) := by
  have first := HOLProofInference.allE left leftFormed leftNormal contextNormal
    (HOLProofTemplates.conjunctionLeft_infers depth assumptions)
  simp only [instantiate, subst, Subst.single, Subst.lift] at first
  have second := HOLProofInference.allE right rightFormed rightNormal contextNormal first
  have function : Infers depth assumptions
      (.termApp (.termApp ImpredicativeLogicalProofs.conjunctionLeft (native left)) (native right))
      (.imp (.and left right) (left)) := by
    have lowered : subst (Subst.single right) (rename Rename.weaken left) = left :=
      instantiate_weaken right left
    simpa only [instantiate, subst, Subst.single, lowered] using second
  exact HOLProofInference.impE function inferred

#print axioms andEL

theorem andER {program : Pf} {left right : Formula (Constant environment) gamma}
    (leftFormed : plainAnnotations depth (native left) = true)
    (rightFormed : plainAnnotations depth (native right) = true)
    (leftNormal : DeltaNormalInvariant.Normal environment (native left))
    (rightNormal : DeltaNormalInvariant.Normal environment (native right))
    (contextNormal : DeltaNormalInvariant.ContextNormal environment (context depth assumptions))
    (inferred : Infers depth assumptions program (.and left right)) :
    Infers depth assumptions
      (.proofApp (.termApp (.termApp ImpredicativeLogicalProofs.conjunctionRight (native left))
        (native right)) program) (right) := by
  have first := HOLProofInference.allE left leftFormed leftNormal contextNormal
    (HOLProofTemplates.conjunctionRight_infers depth assumptions)
  simp only [instantiate, subst, Subst.single, Subst.lift] at first
  have second := HOLProofInference.allE right rightFormed rightNormal contextNormal first
  have function : Infers depth assumptions
      (.termApp (.termApp ImpredicativeLogicalProofs.conjunctionRight (native left)) (native right))
      (.imp (.and left right) (right)) := by
    have lowered : subst (Subst.single right) (rename Rename.weaken left) = left :=
      instantiate_weaken right left
    simpa only [instantiate, subst, Subst.single, lowered] using second
  exact HOLProofInference.impE function inferred

#print axioms andER

theorem orIL {program : Pf} {left right : Formula (Constant environment) gamma}
    (leftFormed : plainAnnotations depth (native left) = true)
    (rightFormed : plainAnnotations depth (native right) = true)
    (leftNormal : DeltaNormalInvariant.Normal environment (native left))
    (rightNormal : DeltaNormalInvariant.Normal environment (native right))
    (contextNormal : DeltaNormalInvariant.ContextNormal environment (context depth assumptions))
    (inferred : Infers depth assumptions program (left)) :
    Infers depth assumptions
      (.proofApp (.termApp (.termApp ImpredicativeLogicalProofs.disjunctionLeft (native left))
        (native right)) program) (.or left right) := by
  have first := HOLProofInference.allE left leftFormed leftNormal contextNormal
    (HOLProofTemplates.disjunctionLeft_infers depth assumptions)
  simp only [instantiate, subst, Subst.single, Subst.lift] at first
  have second := HOLProofInference.allE right rightFormed rightNormal contextNormal first
  have function : Infers depth assumptions
      (.termApp (.termApp ImpredicativeLogicalProofs.disjunctionLeft (native left)) (native right))
      (.imp (left) (.or left right)) := by
    have lowered : subst (Subst.single right) (rename Rename.weaken left) = left :=
      instantiate_weaken right left
    simpa only [instantiate, subst, Subst.single, lowered] using second
  exact HOLProofInference.impE function inferred

#print axioms orIL

theorem orIR {program : Pf} {left right : Formula (Constant environment) gamma}
    (leftFormed : plainAnnotations depth (native left) = true)
    (rightFormed : plainAnnotations depth (native right) = true)
    (leftNormal : DeltaNormalInvariant.Normal environment (native left))
    (rightNormal : DeltaNormalInvariant.Normal environment (native right))
    (contextNormal : DeltaNormalInvariant.ContextNormal environment (context depth assumptions))
    (inferred : Infers depth assumptions program (right)) :
    Infers depth assumptions
      (.proofApp (.termApp (.termApp ImpredicativeLogicalProofs.disjunctionRight (native left))
        (native right)) program) (.or left right) := by
  have first := HOLProofInference.allE left leftFormed leftNormal contextNormal
    (HOLProofTemplates.disjunctionRight_infers depth assumptions)
  simp only [instantiate, subst, Subst.single, Subst.lift] at first
  have second := HOLProofInference.allE right rightFormed rightNormal contextNormal first
  have function : Infers depth assumptions
      (.termApp (.termApp ImpredicativeLogicalProofs.disjunctionRight (native left)) (native right))
      (.imp (right) (.or left right)) := by
    have lowered : subst (Subst.single right) (rename Rename.weaken left) = left :=
      instantiate_weaken right left
    simpa only [instantiate, subst, Subst.single, lowered] using second
  exact HOLProofInference.impE function inferred

#print axioms orIR

theorem notI {program : Pf} {premise : Formula (Constant environment) gamma}
    (formed : plainAnnotations depth (native premise) = true)
    (unfoldingAbsent : DeltaNormalInvariant.Normal environment (native premise))
    (inferred : Infers depth (premise :: assumptions) program .bot) :
    Infers depth assumptions (.proofLam (native premise) program) (.not premise) := by
  obtain ⟨fuel, derived⟩ := HOLProofInference.impI formed unfoldingAbsent inferred
  rw [normalFormCode_imp] at derived
  refine ⟨fuel, ?_⟩
  rw [normalFormCode_not]
  exact derived

theorem notE {negative positive : Pf} {premise : Formula (Constant environment) gamma}
    (one : Infers depth assumptions negative (.not premise))
    (two : Infers depth assumptions positive premise) :
    Infers depth assumptions (.proofApp negative positive) .bot := by
  obtain ⟨first, negativeDerived⟩ := one
  obtain ⟨second, positiveDerived⟩ := two
  rw [normalFormCode_not] at negativeDerived
  exact ⟨max first second, TypedProofApplication.proof_application negativeDerived positiveDerived⟩

#print axioms notI
#print axioms notE

theorem orE {casesProgram leftProgram rightProgram : Pf}
    {left right conclusion : Formula (Constant environment) gamma}
    (leftFormed : plainAnnotations depth (native left) = true)
    (rightFormed : plainAnnotations depth (native right) = true)
    (conclusionFormed : plainAnnotations depth (native conclusion) = true)
    (leftNormal : DeltaNormalInvariant.Normal environment (native left))
    (rightNormal : DeltaNormalInvariant.Normal environment (native right))
    (conclusionNormal : DeltaNormalInvariant.Normal environment (native conclusion))
    (contextNormal : DeltaNormalInvariant.ContextNormal environment (context depth assumptions))
    (casesInferred : Infers depth assumptions casesProgram (.or left right))
    (leftInferred : Infers depth (left :: assumptions) leftProgram conclusion)
    (rightInferred : Infers depth (right :: assumptions) rightProgram conclusion) :
    Infers depth assumptions
      (.proofApp (.proofApp (.proofApp
        (.termApp (.termApp (.termApp ImpredicativeLogicalProofs.disjunctionElimination
          (native left)) (native right)) (native conclusion)) casesProgram)
        (.proofLam (native left) leftProgram)) (.proofLam (native right) rightProgram)) conclusion := by
  have first := HOLProofInference.allE left leftFormed leftNormal contextNormal
    (HOLProofTemplates.disjunctionElimination_infers depth assumptions)
  simp only [instantiate, subst, Subst.single, Subst.lift] at first
  have second := HOLProofInference.allE right rightFormed rightNormal contextNormal first
  have lowered : subst (Subst.single right) (rename Rename.weaken left) = left :=
    instantiate_weaken right left
  have liftedLeft : subst (Subst.lift (σ := .prop) (Subst.single right))
      (rename (Rename.weaken (σ := .prop)) (rename (Rename.weaken (σ := .prop)) left)) =
      rename (Rename.weaken (σ := .prop)) left := by
    change subst (Subst.lift (Subst.single right)) (weaken (weaken left)) = weaken left
    rw [subst_weaken]
    exact congrArg (weaken (σ := .prop)) lowered
  have liftedRight : subst (Subst.lift (σ := .prop) (Subst.single right))
      (rename (Rename.weaken (σ := .prop)) (Term.var .vz)) =
      rename (Rename.weaken (σ := .prop)) right := by
    change subst (Subst.lift (Subst.single right)) (weaken (Term.var .vz)) = weaken right
    rw [subst_weaken]
    rfl
  simp only [instantiate, subst, Subst.lift, liftedLeft, liftedRight] at second
  have third := HOLProofInference.allE conclusion conclusionFormed conclusionNormal contextNormal second
  have function : Infers depth assumptions
      (.termApp (.termApp (.termApp ImpredicativeLogicalProofs.disjunctionElimination
        (native left)) (native right)) (native conclusion))
      (.imp (.or left right) (.imp (.imp left conclusion) (.imp (.imp right conclusion) conclusion))) := by
    have loweredLeft : subst (Subst.single conclusion) (rename Rename.weaken left) = left :=
      instantiate_weaken conclusion left
    have loweredRight : subst (Subst.single conclusion) (rename Rename.weaken right) = right :=
      instantiate_weaken conclusion right
    simpa only [instantiate, subst, Subst.single, loweredLeft, loweredRight] using third
  exact HOLProofInference.impE
    (HOLProofInference.impE (HOLProofInference.impE function casesInferred)
      (HOLProofInference.impI leftFormed leftNormal leftInferred))
    (HOLProofInference.impI rightFormed rightNormal rightInferred)

#print axioms orE

end Mettapedia.Languages.Megalodon.HOLLogicalProofInference
