import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.SetOperationExtensionalProfile

/-!
# Explicit applications of the material-signature extensionality constants

The two declaration spines consume every premise as a native proof argument.
The function spine takes its native domain and codomain codes explicitly.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.SetOperationExtensionalApplications
open Presentation Presentation.FormationSensitive
open SetOperationExtensionalProfile
variable {n : Nat}

def propositionExtensionalityApp {n : Nat}
    (p q forward backward : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.app (.app (.const propositionExtensionalityName) p) q)
    forward) backward

def functionExtensionalityApp {n : Nat}
    (domain codomain function other pointwise : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.app (.app (.app (.const functionExtensionalityName) domain)
    codomain) function) other) pointwise

/-- Propositional extensionality is a fully explicit four-argument native
application. -/
theorem propositionExtensionalityApp_typed {context : Tower.Ctx n}
    {p q forward backward : Tower.Tm n}
    (pTyped : Typing rules context p (liftClosed proposition))
    (qTyped : Typing rules context q (liftClosed proposition))
    (forwardTyped : Typing rules context forward (proof (rawImp p q)))
    (backwardTyped : Typing rules context backward (proof (rawImp q p))) :
    Typing rules context (propositionExtensionalityApp p q forward backward)
      (proof (rawEqualityAt (liftClosed proposition) p q)) := by
  have appliedP := Typing.appElim
    (propositionExtensionality_typed context) pTyped
  rw [inst0_rename_liftRen_elim0] at appliedP
  have appliedQ := Typing.appElim appliedP qTyped
  rw [← subst_consSub] at appliedQ
  have appliedForward := Typing.appElim appliedQ (by
    simpa [subst, rawImp, FormationSensitiveHOLGenericProofFamily.rawImp, consSub, Fin.cases, Fin.induction, Fin.induction.go, Fin.ofNat] using forwardTyped)
  rw [← subst_consSub] at appliedForward
  have appliedBackward := Typing.appElim appliedForward (by
    simpa [subst, rawImp, FormationSensitiveHOLGenericProofFamily.rawImp, consSub, Fin.cases, Fin.induction, Fin.induction.go, Fin.ofNat] using backwardTyped)
  rw [← subst_consSub] at appliedBackward
  simpa [propositionExtensionalityApp, subst,
    rawEqualityAt_subst, consSub, Fin.cases, Fin.induction, Fin.induction.go, Fin.ofNat] using appliedBackward

/-- Function extensionality remains universe-polymorphic at the object level:
the domain and codomain codes are the first two explicit arguments. -/
theorem functionExtensionalityApp_typed {context : Tower.Ctx n}
    {domain codomain function other pointwise : Tower.Tm n}
    (domainTyped : Typing rules context domain (sortTm Tower.zero))
    (codomainTyped : Typing rules context codomain (sortTm Tower.zero))
    (functionTyped : Typing rules context function (arrow domain codomain))
    (otherTyped : Typing rules context other (arrow domain codomain))
    (pointwiseTyped : Typing rules context pointwise
      (pointwiseEquality domain codomain function other)) :
    Typing rules context
      (functionExtensionalityApp domain codomain function other pointwise)
      (proof (rawEqualityAt (arrow domain codomain) function other)) := by
  have appliedDomain := Typing.appElim
    (functionExtensionality_typed context) domainTyped
  rw [inst0_rename_liftRen_elim0] at appliedDomain
  have appliedCodomain := Typing.appElim appliedDomain codomainTyped
  rw [← subst_consSub] at appliedCodomain
  have appliedFunction := Typing.appElim appliedCodomain (by
    simpa [subst, arrow, consSub, Fin.cases, Fin.induction, Fin.induction.go, Fin.ofNat] using functionTyped)
  rw [← subst_consSub] at appliedFunction
  have appliedOther := Typing.appElim appliedFunction (by
    simpa [subst, arrow, consSub, Fin.cases, Fin.induction, Fin.induction.go, Fin.ofNat] using otherTyped)
  rw [← subst_consSub] at appliedOther
  have appliedOtherNormalized : Typing rules context
      (.app (.app (.app (.app (.const functionExtensionalityName) domain)
        codomain) function) other)
      (functionExtensionalityBody domain codomain function other) := by
    simpa [functionExtensionalityBody, subst, pointwiseEquality,
      rawEqualityAt_subst, arrow,
      proof_subst,
      proof_rename, consSub, liftSub, Fin.cases, Fin.induction, Fin.induction.go, Fin.ofNat] using appliedOther
  have bodyShape : functionExtensionalityBody domain codomain function other =
      .pi (pointwiseEquality domain codomain function other)
        (rename wk (proof
          (rawEqualityAt (arrow domain codomain) function other))) := by
    simp only [functionExtensionalityBody]
  rw [bodyShape] at appliedOtherNormalized
  have appliedPointwise := Typing.appElim
    (g := .app (.app (.app (.app (.const functionExtensionalityName) domain)
      codomain) function) other)
    (a := pointwise)
    (A := pointwiseEquality domain codomain function other)
    (B := rename wk
      (proof (rawEqualityAt (arrow domain codomain) function other)))
    appliedOtherNormalized (by
    simpa [subst, pointwiseEquality, rawEqualityAt_subst,
      proof_subst, consSub, liftSub, Fin.cases, Fin.induction, Fin.induction.go, Fin.ofNat] using pointwiseTyped)
  simpa only [functionExtensionalityApp, inst0_rename_wk] using appliedPointwise

#print axioms propositionExtensionalityApp_typed
#print axioms functionExtensionalityApp_typed
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.SetOperationExtensionalApplications
