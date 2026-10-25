import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.SetOperationSignature
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLPredicateEqualityOperations
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.DeclarationInsertionCoherence

/-!
# An extensional proof profile for the common material signature

The existing six operations retain their declarations and native terms. Two
opaque proof constants express propositional and functional extensionality.
Their types use the same predicate-equality formula and the same proof-family
name as the constructive reading. The proof family is then installed through
the existing parameterized implication and universal decoders.

Global declaration lookup is independent of declaration order. The formation
proofs below use only the logical operations and proof family, so neither
extensionality constant is used to form its own type. The constants are
object-theory commitments, separate from native identity and conversion.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.SetOperationExtensionalProfile
open Presentation Presentation.Declaration Presentation.FormationSensitive
open FormationSensitiveHOLInterface
open Mettapedia.Logic HOL.Embedding.ZFSetHenkinInterpretation
open SetOperationSignature (proofName)

def proposition : Tower.Tm 0 := SetOperationSignature.types.proposition

def arrow {n : Nat} (domain codomain : Tower.Tm n) : Tower.Tm n :=
  .pi domain (rename wk codomain)

def nativeAll {n : Nat} (domain predicate : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.const `SetOperationHOL.universal) domain) predicate

def rawImp {n : Nat} (left right : Tower.Tm n) : Tower.Tm n :=
  FormationSensitiveHOLGenericProofFamily.rawImp SetOperationSignature.signature left right

def proof {n : Nat} (formula : Tower.Tm n) : Tower.Tm n :=
  FormationSensitiveHOLGenericProofFamily.proof proofName formula

def predicateType {n : Nat} (type : Tower.Tm n) : Tower.Tm n :=
  arrow type (liftClosed proposition)

def rawEqualityAt {n : Nat} (type left right : Tower.Tm n) : Tower.Tm n :=
  nativeAll (predicateType type)
    (.lam (rawImp (.app (.var 0) (rename wk left))
      (.app (.var 0) (rename wk right))))

def propositionExtensionalityName : DeclName := `SetOperationHOL.Extensional.proposition
def functionExtensionalityName : DeclName := `SetOperationHOL.Extensional.function

def propositionExtensionalityType : Tower.Tm 0 :=
  .pi proposition (.pi (liftClosed proposition)
    (.pi (proof (rawImp (.var 1) (.var 0)))
      (.pi (proof (rawImp (.var 1) (.var 2)))
        (proof (rawEqualityAt (liftClosed proposition) (.var 3) (.var 2))))))

def pointwiseEquality {n : Nat}
    (domain codomain function other : Tower.Tm n) : Tower.Tm n :=
  .pi domain (proof (rawEqualityAt (rename wk codomain)
    (.app (rename wk function) (.var 0)) (.app (rename wk other) (.var 0))))

def functionExtensionalityBody {n : Nat}
    (domain codomain function other : Tower.Tm n) : Tower.Tm n :=
  .pi (pointwiseEquality domain codomain function other)
    (rename wk (proof (rawEqualityAt (arrow domain codomain) function other)))

def functionExtensionalityType : Tower.Tm 0 :=
  .pi (sortTm Tower.zero) (.pi (sortTm Tower.zero)
    (.pi (arrow (.var 1) (.var 0)) (.pi (arrow (.var 2) (.var 1))
      (functionExtensionalityBody (.var 3) (.var 2) (.var 1) (.var 0)))))

def declarations : Signature Tower.Head :=
  (SetOperationSignature.declarations.insert propositionExtensionalityName
    ⟨propositionExtensionalityType, none⟩).insert functionExtensionalityName
      ⟨functionExtensionalityType, none⟩

theorem extendsSource : SetOperationSignature.declarations.Extends declarations :=
  (Signature.extends_insert_of_absent _ propositionExtensionalityName
    ⟨propositionExtensionalityType, none⟩ (by decide)).trans
    (Signature.extends_insert_of_absent _ functionExtensionalityName
      ⟨functionExtensionalityType, none⟩ (by decide))

/-- The source interface still exposes exactly the original six operations. -/
def signature : LogicalSignature Unit Symbol where
  declarations := declarations
  types := SetOperationSignature.types
  proposition_formed := SetOperationSignature.signature.proposition_formed.monoSignature extendsSource
  base_formed := fun base => (SetOperationSignature.signature.base_formed base).monoSignature extendsSource
  constant := SetOperationSignature.signature.constant
  constant_typed := fun symbol =>
    (SetOperationSignature.signature.constant_typed symbol).monoSignature extendsSource
  implication := SetOperationSignature.signature.implication
  implication_typed := SetOperationSignature.signature.implication_typed.monoSignature extendsSource
  universal := SetOperationSignature.signature.universal
  universal_typed := fun type =>
    (SetOperationSignature.signature.universal_typed type).monoSignature extendsSource
  equality := SetOperationSignature.signature.equality
  equality_typed := fun type =>
    (SetOperationSignature.signature.equality_typed type).monoSignature extendsSource

def reading : LogicalSignature Unit Symbol := HOLPredicateEqualitySignature.signature signature

@[simp] theorem reading_types : reading.types = SetOperationSignature.types := rfl

@[simp] theorem typeAt_prop {n : Nat} :
    typeAt SetOperationSignature.types n .prop = liftClosed proposition := rfl

abbrev rules : Rules Tower.Head := HOLPredicateEqualityRules.rules signature proofName

theorem fresh : signature.rules.constantType proofName = none := by decide

@[simp] theorem rawImp_reading {n : Nat} (left right : Tower.Tm n) :
    FormationSensitiveHOLGenericProofFamily.rawImp reading left right = rawImp left right := rfl

@[simp] theorem proof_rename {n m : Nat} (rho : Ren n m) (formula : Tower.Tm n) :
    rename rho (proof formula) = proof (rename rho formula) := rfl

@[simp] theorem proof_subst {n m : Nat} (sigma : Sub Tower.Head n m) (formula : Tower.Tm n) :
    subst sigma (proof formula) = proof (subst sigma formula) := rfl

theorem includeSourceTyping {n : Nat} {context : Tower.Ctx n} {term type : Tower.Tm n}
    (typed : Typing SetOperationSignature.rules context term type) :
    Typing rules context term type :=
  HOLPredicateEqualityOperations.includeSourceTyping signature proofName (typed.monoSignature extendsSource)

theorem proof_formed {n : Nat} {context : Tower.Ctx n} {formula : Tower.Tm n}
    (typed : Typing rules context formula (liftClosed proposition)) :
    Typing rules context (proof formula) (sortTm Tower.zero) :=
  FormationSensitiveHOLGenericProofFamily.proof_formed reading proofName fresh typed

theorem pi_zero {n : Nat} {context : Tower.Ctx n} {domain : Tower.Tm n} {codomain : Tower.Tm (n + 1)}
    (domainTyped : Typing rules context domain (sortTm Tower.zero))
    (codomainTyped : Typing rules (.snoc context domain) codomain (sortTm Tower.zero)) :
    Typing rules context (.pi domain codomain) (sortTm Tower.zero) :=
  FormationSensitiveHOLGenericProofFamily.pi_zero reading proofName domainTyped codomainTyped

theorem proposition_formed {n : Nat} (context : Tower.Ctx n) :
    Typing rules context (liftClosed proposition) (sortTm Tower.zero) :=
  includeSourceTyping (SetOperationSignature.proposition_formed context)

@[simp] theorem arrow_rename {n m : Nat} (rho : Ren n m) (domain codomain : Tower.Tm n) :
    rename rho (arrow domain codomain) = arrow (rename rho domain) (rename rho codomain) := by
  simp [arrow, rename, rename_comp, liftRen, wk]

@[simp] theorem arrow_subst {n m : Nat} (sigma : Sub Tower.Head n m) (domain codomain : Tower.Tm n) :
    subst sigma (arrow domain codomain) = arrow (subst sigma domain) (subst sigma codomain) := by
  simp [arrow, subst, subst_rename, rename_subst, liftSub, wk]

theorem arrow_typeAt {n : Nat} (domain codomain : HOL.Ty Unit) :
    arrow (typeAt SetOperationSignature.types n domain) (typeAt SetOperationSignature.types n codomain) =
      typeAt SetOperationSignature.types n (.arr domain codomain) := by
  simp only [arrow, typeAt_rename, typeAt]

@[simp] theorem nativeAll_rename {n m : Nat} (rho : Ren n m) (domain predicate : Tower.Tm n) :
    rename rho (nativeAll domain predicate) = nativeAll (rename rho domain) (rename rho predicate) := rfl

@[simp] theorem nativeAll_subst {n m : Nat} (sigma : Sub Tower.Head n m) (domain predicate : Tower.Tm n) :
    subst sigma (nativeAll domain predicate) = nativeAll (subst sigma domain) (subst sigma predicate) := rfl

@[simp] theorem rawImp_rename {n m : Nat} (rho : Ren n m) (left right : Tower.Tm n) :
    rename rho (rawImp left right) = rawImp (rename rho left) (rename rho right) :=
  FormationSensitiveHOLGenericProofFamily.rawImp_rename _ _ _ _

@[simp] theorem rawImp_subst {n m : Nat} (sigma : Sub Tower.Head n m) (left right : Tower.Tm n) :
    subst sigma (rawImp left right) = rawImp (subst sigma left) (subst sigma right) :=
  FormationSensitiveHOLGenericProofFamily.rawImp_subst _ _ _ _

@[simp] theorem rawEqualityAt_rename {n m : Nat} (rho : Ren n m) (type left right : Tower.Tm n) :
    rename rho (rawEqualityAt type left right) =
      rawEqualityAt (rename rho type) (rename rho left) (rename rho right) := by
  simp [rawEqualityAt, predicateType, arrow, rename, rename_comp, liftRen, wk]

@[simp] theorem rawEqualityAt_subst {n m : Nat} (sigma : Sub Tower.Head n m) (type left right : Tower.Tm n) :
    subst sigma (rawEqualityAt type left right) =
      rawEqualityAt (subst sigma type) (subst sigma left) (subst sigma right) := by
  simp [rawEqualityAt, predicateType, arrow, subst, subst_rename, rename_subst, liftSub, wk]

theorem nativeAll_typeAt {n : Nat} (type : HOL.Ty Unit) (predicate : Tower.Tm n) :
    nativeAll (typeAt SetOperationSignature.types n type) predicate =
      FormationSensitiveHOLGenericProofFamily.universalProposition signature type predicate := by
  change nativeAll (typeAt SetOperationSignature.types n type) predicate =
    Tm.app (liftClosed (SetOperationSignature.universal type)) predicate
  simp only [nativeAll, SetOperationSignature.universal, liftClosed, rename, typeAt_rename]

theorem rawEqualityAt_typeAt {n : Nat} (type : HOL.Ty Unit) (left right : Tower.Tm n) :
    rawEqualityAt (typeAt SetOperationSignature.types n type) left right =
      HOLPredicateEqualitySignature.raw signature type left right := by
  change nativeAll (typeAt SetOperationSignature.types n (.arr type .prop))
      (.lam (rawImp (.app (.var 0) (rename wk left)) (.app (.var 0) (rename wk right)))) = _
  exact nativeAll_typeAt _ _

theorem arrow_formed {n : Nat} {context : Tower.Ctx n} {domain codomain : Tower.Tm n}
    (domainTyped : Typing rules context domain (sortTm Tower.zero))
    (codomainTyped : Typing rules context codomain (sortTm Tower.zero)) :
    Typing rules context (arrow domain codomain) (sortTm Tower.zero) := by
  apply pi_zero domainTyped
  simpa only [sortTm, rename] using codomainTyped.weaken (extension := domain)

theorem application_typed {n : Nat} {context : Tower.Ctx n} {domain codomain function argument : Tower.Tm n}
    (functionTyped : Typing rules context function (arrow domain codomain))
    (argumentTyped : Typing rules context argument domain) :
    Typing rules context (.app function argument) codomain := by
  simpa only [arrow, inst0_rename_wk] using Typing.appElim functionTyped argumentTyped

theorem nativeUniversal_typed {n : Nat} (context : Tower.Ctx n) :
    Typing rules context (.const `SetOperationHOL.universal) (liftClosed SetOperationSignature.universalType) := by
  have declared : Typing SetOperationSignature.rules .nil (.const `SetOperationHOL.universal)
      SetOperationSignature.universalType :=
    .const (by decide) SetOperationSignature.universal_type_formed
      (.sort (.max (.succ Tower.zero) Tower.zero))
  exact includeSourceTyping (closed_typed declared context)

theorem nativeAll_typed {n : Nat} {context : Tower.Ctx n} {type predicate : Tower.Tm n}
    (typeTyped : Typing rules context type (sortTm Tower.zero))
    (predicateTyped : Typing rules context predicate (predicateType type)) :
    Typing rules context (nativeAll type predicate) (liftClosed proposition) := by
  have first := Typing.appElim (nativeUniversal_typed context) typeTyped
  change Typing rules context (.app (.const `SetOperationHOL.universal) type)
    (.pi (predicateType type) (liftClosed proposition)) at first
  simpa only [nativeAll, inst0, subst, proposition, SetOperationSignature.types, liftClosed, rename]
    using Typing.appElim first predicateTyped

theorem nativeAll_lambda_typed {n : Nat} {context : Tower.Ctx n} {type : Tower.Tm n}
    {body : Tower.Tm (n + 1)}
    (typeTyped : Typing rules context type (sortTm Tower.zero))
    (bodyTyped : Typing rules (.snoc context type) body (liftClosed proposition)) :
    Typing rules context (nativeAll type (.lam body)) (liftClosed proposition) := by
  apply nativeAll_typed typeTyped
  exact .lamIntro (arrow_formed typeTyped (proposition_formed context)) (.sort Tower.zero)
    (by simpa only [rename_liftClosed] using bodyTyped)

theorem rawEqualityAt_typed {n : Nat} {context : Tower.Ctx n} {type left right : Tower.Tm n}
    (typeTyped : Typing rules context type (sortTm Tower.zero))
    (leftTyped : Typing rules context left type) (rightTyped : Typing rules context right type) :
    Typing rules context (rawEqualityAt type left right) (liftClosed proposition) := by
  let predicates := predicateType type
  have predicatesTyped : Typing rules context predicates (sortTm Tower.zero) :=
    arrow_formed typeTyped (proposition_formed context)
  have predicateVariable : Typing rules (.snoc context predicates) (.var 0)
      (rename wk predicates) := .var 0
  have predicateShape : rename wk predicates = arrow (rename wk type) (liftClosed proposition) := by
    simp only [predicates, predicateType, arrow_rename, rename_liftClosed]
  rw [predicateShape] at predicateVariable
  have leftProposition := application_typed predicateVariable (leftTyped.weaken (extension := predicates))
  have rightProposition := application_typed predicateVariable (rightTyped.weaken (extension := predicates))
  exact nativeAll_lambda_typed predicatesTyped
    (FormationSensitiveHOLGenericProofFamily.implication_proposition reading proofName
      leftProposition rightProposition)

theorem propositionExtensionalityType_formed :
    Typing rules .nil propositionExtensionalityType (sortTm Tower.zero) := by
  let two := (.snoc (.snoc (.nil) proposition) (liftClosed proposition) : Tower.Ctx 2)
  have pTwo : Typing rules two (.var 1) (liftClosed proposition) := by
    have lookup : two.lookup 1 = liftClosed proposition := by decide
    simpa only [lookup] using
      (Typing.var (R := rules) (Γ := two) 1)
  have qTwo : Typing rules two (.var 0) (liftClosed proposition) := by
    simpa only [two, Ctx.lookup_snoc_zero, rename_liftClosed] using
      (Typing.var (R := rules) (Γ := two) 0)
  have forwardProp := FormationSensitiveHOLGenericProofFamily.implication_proposition reading proofName pTwo qTwo
  let withForward := two.snoc (proof (rawImp (.var 1) (.var 0)))
  have pForward : Typing rules withForward (.var 2) (liftClosed proposition) := by
    have lookup : withForward.lookup 2 = liftClosed proposition := by decide
    simpa only [lookup] using
      (Typing.var (R := rules) (Γ := withForward) 2)
  have qForward : Typing rules withForward (.var 1) (liftClosed proposition) := by
    have lookup : withForward.lookup 1 = liftClosed proposition := by decide
    simpa only [lookup] using
      (Typing.var (R := rules) (Γ := withForward) 1)
  have backwardProp := FormationSensitiveHOLGenericProofFamily.implication_proposition reading proofName qForward pForward
  let withBackward := withForward.snoc (proof (rawImp (.var 1) (.var 2)))
  have pBackward : Typing rules withBackward (.var 3) (liftClosed proposition) := by
    have lookup : withBackward.lookup 3 = liftClosed proposition := by decide
    simpa only [lookup] using
      (Typing.var (R := rules) (Γ := withBackward) 3)
  have qBackward : Typing rules withBackward (.var 2) (liftClosed proposition) := by
    have lookup : withBackward.lookup 2 = liftClosed proposition := by decide
    simpa only [lookup] using
      (Typing.var (R := rules) (Γ := withBackward) 2)
  have equalityProp := rawEqualityAt_typed
    (proposition_formed withBackward) pBackward qBackward
  have result := pi_zero (proposition_formed .nil)
    (pi_zero (proposition_formed (.snoc .nil proposition))
      (pi_zero (proof_formed forwardProp)
        (pi_zero (proof_formed backwardProp)
          (proof_formed equalityProp))))
  simpa only [propositionExtensionalityType, two, withForward, withBackward,
    proposition, SetOperationSignature.types, liftClosed, rename, rawImp_reading] using result

theorem pointwiseEquality_formed {n : Nat} {context : Tower.Ctx n}
    {domain codomain function other : Tower.Tm n}
    (domainTyped : Typing rules context domain (sortTm Tower.zero))
    (codomainTyped : Typing rules context codomain (sortTm Tower.zero))
    (functionTyped : Typing rules context function (arrow domain codomain))
    (otherTyped : Typing rules context other (arrow domain codomain)) :
    Typing rules context (pointwiseEquality domain codomain function other)
      (sortTm Tower.zero) := by
  have argumentTyped : Typing rules (.snoc context domain) (.var 0)
      (rename wk domain) := by
    simpa only [Ctx.lookup_snoc_zero] using
      (Typing.var (R := rules) (Γ := .snoc context domain) 0)
  have functionWeakened := functionTyped.weaken (extension := domain)
  have otherWeakened := otherTyped.weaken (extension := domain)
  rw [arrow_rename] at functionWeakened otherWeakened
  have leftApplied := application_typed functionWeakened argumentTyped
  have rightApplied := application_typed otherWeakened argumentTyped
  have equalityProp := rawEqualityAt_typed codomainTyped.weaken
    leftApplied rightApplied
  exact pi_zero domainTyped (proof_formed equalityProp)

theorem functionExtensionalityBody_formed {n : Nat} {context : Tower.Ctx n}
    {domain codomain function other : Tower.Tm n}
    (domainTyped : Typing rules context domain (sortTm Tower.zero))
    (codomainTyped : Typing rules context codomain (sortTm Tower.zero))
    (functionTyped : Typing rules context function (arrow domain codomain))
    (otherTyped : Typing rules context other (arrow domain codomain)) :
    Typing rules context
      (functionExtensionalityBody domain codomain function other)
      (sortTm Tower.zero) := by
  have pointwise := pointwiseEquality_formed domainTyped codomainTyped
    functionTyped otherTyped
  have equalityProp := rawEqualityAt_typed
    (arrow_formed domainTyped codomainTyped) functionTyped otherTyped
  have weakened := (proof_formed equalityProp).weaken
    (extension := pointwiseEquality domain codomain function other)
  exact pi_zero pointwise (by
    simpa [proof, FormationSensitiveHOLGenericProofFamily.proof_rename, sortTm, rename] using weakened)

theorem functionExtensionalityType_formed :
    Typing rules .nil functionExtensionalityType
      (sortTm (.succ Tower.zero)) := by
  let withDomain := (.snoc (.nil) (sortTm Tower.zero) : Tower.Ctx 1)
  let withTypes := (withDomain.snoc (sortTm Tower.zero) : Tower.Ctx 2)
  have domainType : Typing rules withTypes (.var 1) (sortTm Tower.zero) := by
    have lookup : withTypes.lookup 1 = sortTm Tower.zero := by decide
    simpa only [lookup] using
      (Typing.var (R := rules) (Γ := withTypes) 1)
  have codomainType : Typing rules withTypes (.var 0) (sortTm Tower.zero) := by
    have lookup : withTypes.lookup 0 = sortTm Tower.zero := by decide
    simpa only [lookup] using
      (Typing.var (R := rules) (Γ := withTypes) 0)
  let functionType : Tower.Tm 2 := arrow (.var 1) (.var 0)
  have functionTypeFormed : Typing rules withTypes functionType
      (sortTm Tower.zero) := arrow_formed domainType codomainType
  let withFunction := withTypes.snoc functionType
  let otherType : Tower.Tm 3 := arrow (.var 2) (.var 1)
  have functionTyped : Typing rules withFunction (.var 0) otherType := by
    have lookup : withFunction.lookup 0 = otherType := by decide
    simpa only [lookup] using (Typing.var (R := rules) (Γ := withFunction) 0)
  have domainFunction : Typing rules withFunction (.var 2) (sortTm Tower.zero) := by
    have lookup : withFunction.lookup 2 = sortTm Tower.zero := by decide
    simpa only [lookup] using (Typing.var (R := rules) (Γ := withFunction) 2)
  have codomainFunction : Typing rules withFunction (.var 1)
      (sortTm Tower.zero) := by
    have lookup : withFunction.lookup 1 = sortTm Tower.zero := by decide
    simpa only [lookup] using (Typing.var (R := rules) (Γ := withFunction) 1)
  have otherTypeFormed : Typing rules withFunction otherType
      (sortTm Tower.zero) := arrow_formed domainFunction codomainFunction
  let withOther := withFunction.snoc otherType
  have domainOther : Typing rules withOther (.var 3) (sortTm Tower.zero) := by
    have lookup : withOther.lookup 3 = sortTm Tower.zero := by decide
    simpa only [lookup] using
      (Typing.var (R := rules) (Γ := withOther) 3)
  have codomainOther : Typing rules withOther (.var 2)
      (sortTm Tower.zero) := by
    have lookup : withOther.lookup 2 = sortTm Tower.zero := by decide
    simpa only [lookup] using (Typing.var (R := rules) (Γ := withOther) 2)
  have firstFunction : Typing rules withOther (.var 1)
      (arrow (.var 3) (.var 2)) := by
    have lookup : withOther.lookup 1 = arrow (.var 3) (.var 2) := by decide
    simpa only [lookup] using
      (Typing.var (R := rules) (Γ := withOther) 1)
  have secondFunction : Typing rules withOther (.var 0)
      (arrow (.var 3) (.var 2)) := by
    have lookup : withOther.lookup 0 = arrow (.var 3) (.var 2) := by decide
    simpa only [lookup] using
      (Typing.var (R := rules) (Γ := withOther) 0)
  have bodyFormed := functionExtensionalityBody_formed domainOther codomainOther
    firstFunction secondFunction
  have functionsFormed := pi_zero functionTypeFormed
    (pi_zero otherTypeFormed bodyFormed)
  have overCodomain : Typing rules withDomain
      (.pi (sortTm Tower.zero)
        (.pi functionType
          (.pi otherType
            (functionExtensionalityBody (.var 3) (.var 2) (.var 1) (.var 0)))))
      (sortTm (.succ Tower.zero)) := by
    apply Typing.cumul
      (Typing.piForm (R := rules)
        (.headType (.sort Tower.zero)) (.sort (.succ Tower.zero))
        functionsFormed (.sort Tower.zero)
        (.sorts (.succ Tower.zero) Tower.zero))
    intro valuation
    simp [LevelExpr.eval, LevelTower.zero]
  have complete : Typing rules .nil
      (.pi (sortTm Tower.zero)
        (.pi (sortTm Tower.zero)
          (.pi functionType
            (.pi otherType
              (functionExtensionalityBody (.var 3) (.var 2) (.var 1) (.var 0))))))
      (sortTm (.succ Tower.zero)) := by
    apply Typing.cumul
      (Typing.piForm (R := rules)
        (.headType (.sort Tower.zero)) (.sort (.succ Tower.zero))
        overCodomain (.sort (.succ Tower.zero))
        (.sorts (.succ Tower.zero) (.succ Tower.zero)))
    intro valuation
    simp [LevelExpr.eval, LevelTower.zero]
  simpa only [functionExtensionalityType, withDomain, withTypes, functionType,
    withFunction, otherType, withOther] using complete

theorem propositionExtensionality_typed {n : Nat} (context : Tower.Ctx n) :
    Typing rules context (.const propositionExtensionalityName)
      (liftClosed propositionExtensionalityType) :=
  .const (by decide) propositionExtensionalityType_formed (.sort Tower.zero)

theorem functionExtensionality_typed {n : Nat} (context : Tower.Ctx n) :
    Typing rules context (.const functionExtensionalityName)
      (liftClosed functionExtensionalityType) :=
  .const (by decide) functionExtensionalityType_formed (.sort (.succ Tower.zero))

#print axioms propositionExtensionality_typed
#print axioms functionExtensionality_typed

#print axioms extendsSource
#print axioms signature
#print axioms fresh
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.SetOperationExtensionalProfile
