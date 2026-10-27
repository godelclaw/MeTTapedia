import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.DeclarationConversionCode

/-!
# Substitution of declaration-root certificates

Inherited and declared certificates use their own substitution operations.
A delta certificate retains the definition name; the checker still reads its
closed body from the signature. Thus substitution neither supplies a replacement
definition nor changes its declaration address.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.DeclarationConversionCode

variable {Head : Type} {BaseCode DeclaredCode : Nat → Type}
    (substituteBase : {n m : Nat} → Sub Head n m → BaseCode n → BaseCode m)
    (substituteDeclared : {n m : Nat} → Sub Head n m → DeclaredCode n → DeclaredCode m)

def RootCode.substitute {n m : Nat} (substitution : Sub Head n m) :
    RootCode BaseCode DeclaredCode n → RootCode BaseCode DeclaredCode m
  | .inherited code => .inherited (substituteBase substitution code)
  | .delta name => .delta name
  | .declared code => .declared (substituteDeclared substitution code)

theorem decode_substitute (signature : Declaration.Signature Head)
    (decodeBase : {n : Nat} → BaseCode n → Option (Tm Head n × Tm Head n))
    (decodeDeclared : {n : Nat} → DeclaredCode n → Option (Tm Head n × Tm Head n))
    (baseLaw : ∀ {n m : Nat} (substitution : Sub Head n m) (code : BaseCode n),
      decodeBase (substituteBase substitution code) =
        (decodeBase code).map (fun endpoints => (subst substitution endpoints.1, subst substitution endpoints.2)))
    (declaredLaw : ∀ {n m : Nat} (substitution : Sub Head n m) (code : DeclaredCode n),
      decodeDeclared (substituteDeclared substitution code) =
        (decodeDeclared code).map (fun endpoints => (subst substitution endpoints.1, subst substitution endpoints.2)))
    {n m : Nat} (substitution : Sub Head n m) (code : RootCode BaseCode DeclaredCode n) :
    decode signature decodeBase decodeDeclared (code.substitute substituteBase substituteDeclared substitution) =
      (decode signature decodeBase decodeDeclared code).map
        (fun endpoints => (subst substitution endpoints.1, subst substitution endpoints.2)) := by
  cases code with
  | inherited code => exact baseLaw substitution code
  | declared code => exact declaredLaw substitution code
  | delta name =>
      cases found : signature.valueOf? name <;>
        simp [RootCode.substitute, decode, found, subst_liftClosed, subst]

theorem RootCode.substitute_ids
    (baseId : ∀ {n : Nat} (code : BaseCode n), substituteBase ids code = code)
    (declaredId : ∀ {n : Nat} (code : DeclaredCode n), substituteDeclared ids code = code)
    {n : Nat} (code : RootCode BaseCode DeclaredCode n) :
    code.substitute substituteBase substituteDeclared ids = code := by
  cases code <;> simp only [substitute, baseId, declaredId]

theorem RootCode.substitute_comp
    (baseComp : ∀ {n m k : Nat} (first : Sub Head n m) (second : Sub Head m k) (code : BaseCode n),
      substituteBase second (substituteBase first code) = substituteBase (subComp second first) code)
    (declaredComp : ∀ {n m k : Nat} (first : Sub Head n m) (second : Sub Head m k) (code : DeclaredCode n),
      substituteDeclared second (substituteDeclared first code) = substituteDeclared (subComp second first) code)
    {n m k : Nat} (first : Sub Head n m) (second : Sub Head m k) (code : RootCode BaseCode DeclaredCode n) :
    (code.substitute substituteBase substituteDeclared first).substitute substituteBase substituteDeclared second =
      code.substitute substituteBase substituteDeclared (subComp second first) := by
  cases code <;> simp only [substitute, baseComp, declaredComp]

#print axioms decode_substitute
#print axioms RootCode.substitute_ids
#print axioms RootCode.substitute_comp

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.DeclarationConversionCode
