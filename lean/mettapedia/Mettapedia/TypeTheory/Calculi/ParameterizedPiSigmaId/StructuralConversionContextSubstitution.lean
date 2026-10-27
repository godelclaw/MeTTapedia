import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionSubstitution

/-!
# Substitution commutes with structural context codes

The equalities compare the complete finite code. Binder contexts use the
existing lifted substitution, retaining the same contextual constructors and
the same order of the two components of application and product congruence.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.StructuralConversionCode.Code

variable {Head : Type} {RootCode : Nat → Type}
    (substituteRoot : {n m : Nat} → Sub Head n m → RootCode n → RootCode m)

theorem substitute_mapContext {n m n' m' : Nat}
    (wrap : Tm Head n → Tm Head m) (wrapStep : StepCode Head RootCode n → StepCode Head RootCode m)
    (wrap' : Tm Head n' → Tm Head m') (wrapStep' : StepCode Head RootCode n' → StepCode Head RootCode m')
    (outer : Sub Head m m') (inner : Sub Head n n')
    (terms : ∀ term, subst outer (wrap term) = wrap' (subst inner term))
    (steps : ∀ step, (wrapStep step).substitute substituteRoot outer =
      wrapStep' (step.substitute substituteRoot inner))
    (code : Code Head RootCode n) :
    (mapContext wrap wrapStep code).substitute substituteRoot outer =
      mapContext wrap' wrapStep' (code.substitute substituteRoot inner) := by
  induction code with
  | single step => simp only [mapContext, substitute, steps]
  | refl term => simp only [mapContext, substitute, terms]
  | symm code ih => simp only [mapContext, substitute, ih]
  | trans first second ihFirst ihSecond => simp only [mapContext, substitute, ihFirst, ihSecond]

theorem substitute_congApp {n m : Nat} (substitution : Sub Head n m)
    (function argument : Tm Head n) (first second : Code Head RootCode n) :
    (congApp function argument first second).substitute substituteRoot substitution =
      congApp (subst substitution function) (subst substitution argument)
        (first.substitute substituteRoot substitution) (second.substitute substituteRoot substitution) := by
  simp only [congApp, substitute]
  rw [substitute_mapContext substituteRoot _ _ (fun term => .app term (subst substitution argument))
      (fun step => .congAppFun step (subst substitution argument)) substitution substitution (fun _ => rfl) (fun _ => rfl),
    substitute_mapContext substituteRoot _ _ (.app (subst substitution function))
      (.congAppArg (subst substitution function)) substitution substitution (fun _ => rfl) (fun _ => rfl)]

theorem substitute_congPi {n m : Nat} (substitution : Sub Head n m)
    (domain : Tm Head n) (family : Tm Head (n + 1))
    (first : Code Head RootCode n) (second : Code Head RootCode (n + 1)) :
    (congPi domain family first second).substitute substituteRoot substitution =
      congPi (subst substitution domain) (subst (liftSub substitution) family)
        (first.substitute substituteRoot substitution) (second.substitute substituteRoot (liftSub substitution)) := by
  simp only [congPi, substitute]
  rw [substitute_mapContext substituteRoot _ _ (fun term => .pi term (subst (liftSub substitution) family))
      (fun step => .congPiDom step (subst (liftSub substitution) family)) substitution substitution (fun _ => rfl) (fun _ => rfl),
    substitute_mapContext substituteRoot _ _ (.pi (subst substitution domain))
      (.congPiCod (subst substitution domain)) substitution (liftSub substitution) (fun _ => rfl) (fun _ => rfl)]

theorem substitute_congLam {n m : Nat} (substitution : Sub Head n m)
    (body : Code Head RootCode (n + 1)) :
    (congLam body).substitute substituteRoot substitution =
      congLam (body.substitute substituteRoot (liftSub substitution)) :=
  substitute_mapContext substituteRoot _ _ _ _ substitution (liftSub substitution) (fun _ => rfl) (fun _ => rfl) body

#print axioms substitute_mapContext
#print axioms substitute_congApp
#print axioms substitute_congPi
#print axioms substitute_congLam

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.StructuralConversionCode.Code
