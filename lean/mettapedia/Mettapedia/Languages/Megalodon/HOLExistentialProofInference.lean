import Mettapedia.Languages.Megalodon.HOLProofTemplates

/-!
# Existential proof inference with retained witnesses and binders

The existing native existential combinators are instantiated with a typed HOL
predicate. Beta conversion relates their applications to the source body's
simultaneous substitution. The programs retain the chosen witness and the
elimination branch's term and proof binders.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.HOLExistentialProofInference

open Mettapedia.Logic.HOL
open MathdataKernel HenkinTermInterpretation HOLTermEncoding HOLNormalForms HOLProofInference

variable {environment : Environment} {gamma : Ctx Base} {domain : Ty Base}
variable {depth : Nat} {assumptions : List (Formula (Constant environment) gamma)}

theorem exI {program : Pf} {predicate : Formula (Constant environment) (domain :: gamma)}
    (argument : Term (Constant environment) gamma domain)
    (domainFormed : (reifyType domain).plainWellFormed depth = true)
    (predicateFormed : plainAnnotations depth (native (.lam predicate)) = true)
    (argumentFormed : plainAnnotations depth (native argument) = true)
    (predicateNormal : DeltaNormalInvariant.Normal environment (native (.lam predicate)))
    (argumentNormal : DeltaNormalInvariant.Normal environment (native argument))
    (contextNormal : DeltaNormalInvariant.ContextNormal environment (context depth assumptions))
    (inferred : Infers depth assumptions program (instantiate argument predicate)) :
    Infers depth assumptions
      (.proofApp (.termApp (.termApp
        (ImpredicativeLogicalProofs.existentialIntroduction (reifyType domain))
        (native (.lam predicate))) (native argument)) program) (.ex predicate) := by
  have first := HOLProofInference.allE (.lam predicate) predicateFormed predicateNormal contextNormal
    (HOLProofTemplates.existentialIntroduction_infers depth domain domainFormed assumptions)
  simp only [instantiate, subst, Subst.single, Subst.lift] at first
  have second := HOLProofInference.allE argument argumentFormed argumentNormal contextNormal first
  have lowered : subst (Subst.single argument) (rename Rename.weaken (.lam predicate)) =
      Term.lam predicate := instantiate_weaken argument (.lam predicate)
  have lifted : subst (Subst.lift (σ := domain) (Subst.single argument))
      (rename (Rename.weaken (σ := domain)) (rename (Rename.weaken (σ := domain))
        (.lam predicate))) = rename Rename.weaken (.lam predicate) := by
    change subst (Subst.lift (Subst.single argument)) (weaken (weaken (.lam predicate))) =
      weaken (.lam predicate)
    rw [subst_weaken]
    exact congrArg (weaken (σ := domain)) lowered
  have function : Infers depth assumptions
      (.termApp (.termApp (ImpredicativeLogicalProofs.existentialIntroduction (reifyType domain))
        (native (.lam predicate))) (native argument))
      (.imp (.app (.lam predicate) argument)
        (.ex (.app (weaken (.lam predicate)) (.var .vz)))) := by
    simpa only [instantiate, subst, Subst.single, Subst.lift, lowered, lifted, weaken] using second
  have converted : EtaConversion.BetaEtaConv
      (.imp (.app (.lam predicate) argument)
        (.ex (.app (weaken (.lam predicate)) (.var .vz))))
      (.imp (instantiate argument predicate) (.ex predicate)) := by
    exact BetaEtaSubstitution.imp_congr (BetaEtaSubstitution.beta predicate argument)
      (BetaEtaSubstitution.ex_congr (BetaEtaSubstitution.apply_weakened_abstraction predicate))
  exact HOLProofInference.impE (HOLProofInference.of_conversion function converted) inferred

#print axioms exI

theorem exE {witnessProgram bodyProgram : Pf}
    {predicate : Formula (Constant environment) (domain :: gamma)}
    {conclusion : Formula (Constant environment) gamma}
    (domainFormed : (reifyType domain).plainWellFormed depth = true)
    (predicateFormed : plainAnnotations depth (native (.lam predicate)) = true)
    (bodyFormed : plainAnnotations depth (native predicate) = true)
    (conclusionFormed : plainAnnotations depth (native conclusion) = true)
    (predicateNormal : DeltaNormalInvariant.Normal environment (native (.lam predicate)))
    (bodyNormal : DeltaNormalInvariant.Normal environment (native predicate))
    (conclusionNormal : DeltaNormalInvariant.Normal environment (native conclusion))
    (contextNormal : DeltaNormalInvariant.ContextNormal environment (context depth assumptions))
    (witnessInferred : Infers depth assumptions witnessProgram (.ex predicate))
    (bodyInferred : Infers depth (predicate :: weakenHyps assumptions) bodyProgram (weaken conclusion)) :
    Infers depth assumptions
      (.proofApp (.proofApp
        (.termApp (.termApp (ImpredicativeLogicalProofs.existentialElimination (reifyType domain))
          (native (.lam predicate))) (native conclusion)) witnessProgram)
        (.termLam (reifyType domain) (.proofLam (native predicate) bodyProgram))) conclusion := by
  have first := HOLProofInference.allE (.lam predicate) predicateFormed predicateNormal contextNormal
    (HOLProofTemplates.existentialElimination_infers depth domain domainFormed assumptions)
  simp only [instantiate, subst, Subst.single, Subst.lift] at first
  have second := HOLProofInference.allE conclusion conclusionFormed conclusionNormal contextNormal first
  have lowered : subst (Subst.single conclusion) (rename (Rename.weaken (σ := .prop))
      (.lam predicate)) = Term.lam predicate := instantiate_weaken conclusion (.lam predicate)
  have lifted : subst (Subst.lift (σ := domain) (Subst.single conclusion))
      (rename (Rename.weaken (σ := domain)) (rename (Rename.weaken (σ := .prop))
        (.lam predicate))) = rename Rename.weaken (.lam predicate) := by
    change subst (Subst.lift (Subst.single conclusion)) (weaken (weaken (.lam predicate))) =
      weaken (.lam predicate)
    rw [subst_weaken]
    exact congrArg (weaken (σ := domain)) lowered
  have liftedConclusion : subst (Subst.lift (σ := domain) (Subst.single conclusion))
      (rename (Rename.weaken (σ := domain)) (Term.var .vz)) = weaken conclusion := rfl
  have function : Infers depth assumptions
      (.termApp (.termApp (ImpredicativeLogicalProofs.existentialElimination (reifyType domain))
        (native (.lam predicate))) (native conclusion))
      (.imp (.ex (.app (weaken (.lam predicate)) (.var .vz)))
        (.imp (.all (.imp (.app (weaken (.lam predicate)) (.var .vz)) (weaken conclusion)))
          conclusion)) := by
    simpa only [instantiate, subst, Subst.single, Subst.lift, lifted, liftedConclusion, weaken]
      using second
  have converted : EtaConversion.BetaEtaConv
      (.imp (.ex (.app (weaken (.lam predicate)) (.var .vz)))
        (.imp (.all (.imp (.app (weaken (.lam predicate)) (.var .vz)) (weaken conclusion)))
          conclusion))
      (.imp (.ex predicate) (.imp (.all (.imp predicate (weaken conclusion))) conclusion)) := by
    have applied := BetaEtaSubstitution.apply_weakened_abstraction predicate
    exact BetaEtaSubstitution.imp_congr (BetaEtaSubstitution.ex_congr applied)
      (BetaEtaSubstitution.imp_congr
        (BetaEtaSubstitution.all_congr (BetaEtaSubstitution.imp_congr applied (.refl _))) (.refl _))
  have branch := HOLProofInference.allI domainFormed
    (HOLProofInference.impI bodyFormed bodyNormal bodyInferred)
  exact HOLProofInference.impE
    (HOLProofInference.impE (HOLProofInference.of_conversion function converted) witnessInferred) branch

#print axioms exE

end Mettapedia.Languages.Megalodon.HOLExistentialProofInference
