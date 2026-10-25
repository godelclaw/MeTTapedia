import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Structural
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.ContextualSubstitutionEquality

/-!
# Typed beta application under dependent binders

Applying a checked two-argument abstraction yields simultaneous substitution
of its two typed arguments. The proof is two primitive typed beta equations,
application congruence and the existing substitution composition law. It
requires neither normalization nor an untyped conversion-to-equality theorem.
The three-argument law extends the same checked substitution by one component.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality

theorem betaPi_two_substitute {Head : Type} {R : Rules Head} {n m : Nat}
    {context : Ctx Head n} {ambient : Ctx Head m} {sigma : Sub Head n m}
    {domain : Tm Head n} {secondDomain : Tm Head (n + 1)}
    {body resultType : Tm Head (n + 2)} {outerLevel innerLevel : Head}
    (outerFormed : Typed R context (.pi domain (.pi secondDomain resultType)) (.head outerLevel))
    (outerUniverse : R.isUniverse outerLevel)
    (innerFormed : Typed R (.snoc context domain) (.pi secondDomain resultType) (.head innerLevel))
    (innerUniverse : R.isUniverse innerLevel)
    (bodyTyped : Typed R (.snoc (.snoc context domain) secondDomain) body resultType)
    (parameters : SubstMor R context ambient sigma)
    {first second : Tm Head m} (firstTyped : Typed R ambient first (subst sigma domain))
    (secondTyped : Typed R ambient second (subst (consSub first sigma) secondDomain)) :
    Equal R ambient (.app (.app (subst sigma (.lam (.lam body))) first) second)
      (subst (consSub second (consSub first sigma)) body)
      (subst (consSub second (consSub first sigma)) resultType) := by
  have innerLambda := Derivable.lamIntro innerFormed innerUniverse bodyTyped
  have firstBeta := Derivable.betaPi (outerFormed.substitute parameters) outerUniverse
    (Typed.substitute innerLambda (parameters.lift domain)) firstTyped
  simp only [← subst_consSub] at firstBeta
  have firstParameters := SubstMor.cons parameters domain firstTyped
  have secondBeta := Derivable.betaPi (innerFormed.substitute firstParameters) innerUniverse
    (bodyTyped.substitute (firstParameters.lift secondDomain)) secondTyped
  simp only [← subst_consSub] at secondBeta
  have applied := Derivable.appCong firstBeta (Derivable.refl secondTyped)
  simp only [← subst_consSub] at applied
  exact Derivable.trans applied secondBeta

#print axioms betaPi_two_substitute

theorem betaPi_two {Head : Type} {R : Rules Head} {n : Nat} {context : Ctx Head n}
    {domain : Tm Head n} {secondDomain : Tm Head (n + 1)}
    {body resultType : Tm Head (n + 2)} {outerLevel innerLevel : Head}
    (outerFormed : Typed R context (.pi domain (.pi secondDomain resultType)) (.head outerLevel))
    (outerUniverse : R.isUniverse outerLevel)
    (innerFormed : Typed R (.snoc context domain) (.pi secondDomain resultType) (.head innerLevel))
    (innerUniverse : R.isUniverse innerLevel)
    (bodyTyped : Typed R (.snoc (.snoc context domain) secondDomain) body resultType)
    {first second : Tm Head n} (firstTyped : Typed R context first domain)
    (secondTyped : Typed R context second (inst0 first secondDomain)) :
    Equal R context (.app (.app (.lam (.lam body)) first) second)
      (subst (consSub second (consSub first ids)) body)
      (subst (consSub second (consSub first ids)) resultType) := by
  have firstAt : Typed R context first (subst ids domain) := by
    simpa only [subst_ids] using firstTyped
  have secondAt : Typed R context second (subst (consSub first ids) secondDomain) := by
    simpa only [subst_consSub, liftSub_ids, subst_ids] using secondTyped
  have equation := betaPi_two_substitute outerFormed outerUniverse innerFormed innerUniverse
    bodyTyped (SubstMor.identity context) firstAt secondAt
  simpa only [subst_ids] using equation

#print axioms betaPi_two

/-- An identity abstraction also checks between two typed-equal carriers. -/
theorem betaPi_identity {Head : Type} {R : Rules Head} {n : Nat} {context : Ctx Head n}
    {domain codomain argument : Tm Head n} {functionLevel equalityLevel : Head}
    (functionFormed : Typed R context (.pi domain (rename wk codomain)) (.head functionLevel))
    (functionUniverse : R.isUniverse functionLevel)
    (carriersEqual : Equal R context domain codomain (.head equalityLevel))
    (equalityUniverse : R.isUniverse equalityLevel)
    (argumentTyped : Typed R context argument domain) :
    Equal R context (.app (.lam (.var 0)) argument) argument codomain := by
  have body : Typed R (.snoc context domain) (.var 0) (rename wk codomain) :=
    .conv (.var 0) carriersEqual.weaken equalityUniverse
  have beta := Derivable.betaPi functionFormed functionUniverse body argumentTyped
  rw [inst0_rename_wk] at beta
  simpa only [inst0, subst, subst0_zero] using beta

#print axioms betaPi_identity

theorem betaPi_three_substitute {Head : Type} {R : Rules Head} {n m : Nat}
    {context : Ctx Head n} {ambient : Ctx Head m} {sigma : Sub Head n m}
    {domain : Tm Head n} {secondDomain : Tm Head (n + 1)} {thirdDomain : Tm Head (n + 2)}
    {body resultType : Tm Head (n + 3)} {outerLevel middleLevel innerLevel : Head}
    (outerFormed : Typed R context (.pi domain (.pi secondDomain (.pi thirdDomain resultType))) (.head outerLevel))
    (outerUniverse : R.isUniverse outerLevel)
    (middleFormed : Typed R (.snoc context domain) (.pi secondDomain (.pi thirdDomain resultType)) (.head middleLevel))
    (middleUniverse : R.isUniverse middleLevel)
    (innerFormed : Typed R (.snoc (.snoc context domain) secondDomain) (.pi thirdDomain resultType) (.head innerLevel))
    (innerUniverse : R.isUniverse innerLevel)
    (bodyTyped : Typed R (.snoc (.snoc (.snoc context domain) secondDomain) thirdDomain) body resultType)
    (parameters : SubstMor R context ambient sigma)
    {first second third : Tm Head m}
    (firstTyped : Typed R ambient first (subst sigma domain))
    (secondTyped : Typed R ambient second (subst (consSub first sigma) secondDomain))
    (thirdTyped : Typed R ambient third (subst (consSub second (consSub first sigma)) thirdDomain)) :
    Equal R ambient (.app (.app (.app (subst sigma (.lam (.lam (.lam body)))) first) second) third)
      (subst (consSub third (consSub second (consSub first sigma))) body)
      (subst (consSub third (consSub second (consSub first sigma))) resultType) := by
  have firstParameters := SubstMor.cons parameters domain firstTyped
  have secondParameters := SubstMor.cons firstParameters secondDomain secondTyped
  have firstTwo := betaPi_two_substitute outerFormed outerUniverse middleFormed middleUniverse
    (Derivable.lamIntro innerFormed innerUniverse bodyTyped) parameters firstTyped secondTyped
  have thirdBeta := Derivable.betaPi (innerFormed.substitute secondParameters) innerUniverse
    (bodyTyped.substitute (secondParameters.lift thirdDomain)) thirdTyped
  simp only [← subst_consSub] at thirdBeta
  have applied := Derivable.appCong firstTwo (Derivable.refl thirdTyped)
  simp only [← subst_consSub] at applied
  exact Derivable.trans applied thirdBeta

#print axioms betaPi_three_substitute

theorem betaPi_three {Head : Type} {R : Rules Head} {n : Nat} {context : Ctx Head n}
    {domain : Tm Head n} {secondDomain : Tm Head (n + 1)} {thirdDomain : Tm Head (n + 2)}
    {body resultType : Tm Head (n + 3)} {outerLevel middleLevel innerLevel : Head}
    (outerFormed : Typed R context (.pi domain (.pi secondDomain (.pi thirdDomain resultType))) (.head outerLevel))
    (outerUniverse : R.isUniverse outerLevel)
    (middleFormed : Typed R (.snoc context domain) (.pi secondDomain (.pi thirdDomain resultType)) (.head middleLevel))
    (middleUniverse : R.isUniverse middleLevel)
    (innerFormed : Typed R (.snoc (.snoc context domain) secondDomain) (.pi thirdDomain resultType) (.head innerLevel))
    (innerUniverse : R.isUniverse innerLevel)
    (bodyTyped : Typed R (.snoc (.snoc (.snoc context domain) secondDomain) thirdDomain) body resultType)
    {first second third : Tm Head n} (firstTyped : Typed R context first domain)
    (secondTyped : Typed R context second (inst0 first secondDomain))
    (thirdTyped : Typed R context third (subst (consSub second (consSub first ids)) thirdDomain)) :
    Equal R context (.app (.app (.app (.lam (.lam (.lam body))) first) second) third)
      (subst (consSub third (consSub second (consSub first ids))) body)
      (subst (consSub third (consSub second (consSub first ids))) resultType) := by
  have firstAt : Typed R context first (subst ids domain) := by
    simpa only [subst_ids] using firstTyped
  have secondAt : Typed R context second (subst (consSub first ids) secondDomain) := by
    simpa only [subst_consSub, liftSub_ids, subst_ids] using secondTyped
  have equation := betaPi_three_substitute outerFormed outerUniverse middleFormed middleUniverse
    innerFormed innerUniverse bodyTyped (SubstMor.identity context) firstAt secondAt thirdTyped
  simpa only [subst_ids] using equation

#print axioms betaPi_three

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality
