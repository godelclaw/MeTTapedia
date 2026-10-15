import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneGeneration

/-!
# Generated native least and greatest predicate terms

The complete fixed-point predicates are ordinary native lambdas quoting
the generated membership formulas at their generic dependent argument.
Finite typing certificates are constructed from the original native rules.
Generation checks the context, carrier, full operator and its quantified
monotonicity premise before returning both predicate terms and evidence.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotonePredicates

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.NativeTypes.Generation
open FixedPointSyntax (predicateType)

universe v
variable {S : Symbols.{v}} {signature : Signature S} {n : Nat}

def leastPredicate (domain : TypeExpr S n) (operator : TermExpr S n) : TermExpr S n :=
  .lam domain .propositions (.quote
    (NativeMonotoneSyntax.least (domain.rename Fin.succ) (operator.rename Fin.succ) (.var 0)))

def greatestPredicate (domain : TypeExpr S n) (operator : TermExpr S n) : TermExpr S n :=
  .lam domain .propositions (.quote
    (NativeMonotoneSyntax.greatest (domain.rename Fin.succ) (operator.rename Fin.succ) (.var 0)))

theorem leastPredicate_substitution {m : Nat} (domain : TypeExpr S n) (operator : TermExpr S n)
    (substitution : Substitution S n m) :
    (leastPredicate domain operator).substitute substitution =
      leastPredicate (domain.substitute substitution) (operator.substitute substitution) := by
  simp only [leastPredicate, TermExpr.substitute, TypeExpr.substitute,
    NativeMonotoneSyntaxTransport.least_substitution, TypeExpr.substitute_weaken,
    TermExpr.substitute_weaken, liftSubstitution_zero]

theorem greatestPredicate_substitution {m : Nat} (domain : TypeExpr S n) (operator : TermExpr S n)
    (substitution : Substitution S n m) :
    (greatestPredicate domain operator).substitute substitution =
      greatestPredicate (domain.substitute substitution) (operator.substitute substitution) := by
  simp only [greatestPredicate, TermExpr.substitute, TypeExpr.substitute,
    NativeMonotoneSyntaxTransport.greatest_substitution, TypeExpr.substitute_weaken,
    TermExpr.substitute_weaken, liftSubstitution_zero]

theorem leastPredicate_rename {m : Nat} (domain : TypeExpr S n) (operator : TermExpr S n)
    (mapping : Renaming n m) :
    (leastPredicate domain operator).rename mapping = leastPredicate (domain.rename mapping) (operator.rename mapping) := by
  simpa only [TypeExpr.substitute_variables, TermExpr.substitute_variables] using
    leastPredicate_substitution domain operator (fun index => .var (mapping index))

theorem greatestPredicate_rename {m : Nat} (domain : TypeExpr S n) (operator : TermExpr S n)
    (mapping : Renaming n m) :
    (greatestPredicate domain operator).rename mapping = greatestPredicate (domain.rename mapping) (operator.rename mapping) := by
  simpa only [TypeExpr.substitute_variables, TermExpr.substitute_variables] using
    greatestPredicate_substitution domain operator (fun index => .var (mapping index))

def quoteLambdaTyping (context : ContextExpr S n) (domain : TypeExpr S n) (body : PropExpr S (n + 1))
    (formed : Derivation signature (.context context))
    (domainFormed : Derivation signature (.type context domain))
    (bodyFormed : Derivation signature (.predicate (.snoc context domain) body)) :
    Derivation signature (.term context (.lam domain .propositions (.quote body)) (predicateType domain)) :=
  deriveList (.lambda context domain .propositions (.quote body))
    (.cons domainFormed (.cons
      (deriveList (.propositionType (.snoc context domain))
        (.cons (NativeMonotoneFormation.extendContext context domain formed domainFormed) .nil))
      (.cons (deriveList (.quote (.snoc context domain) body) (.cons bodyFormed .nil)) .nil)))

def leastPredicateTyping (context : ContextExpr S n) (domain : TypeExpr S n) (operator : TermExpr S n)
    (formed : Derivation signature (.context context))
    (domainFormed : Derivation signature (.type context domain))
    (operatorTyped : Derivation signature (.term context operator (NativeMonotoneSyntax.operatorType domain))) :
    Derivation signature (.term context (leastPredicate domain operator) (predicateType domain)) := by
  let extended := NativeMonotoneFormation.extendContext context domain formed domainFormed
  have genericTyped : Derivation signature (.term (.snoc context domain) (.var 0) (domain.rename Fin.succ)) := by
    simpa only [RuleCode.conclusion, ContextExpr.lookup_zero] using
      deriveList (.variable (.snoc context domain) 0) (.cons extended .nil)
  exact quoteLambdaTyping context domain _ formed domainFormed
    (NativeMonotoneFormation.leastFormation (.snoc context domain) (domain.rename Fin.succ)
      (operator.rename Fin.succ) (.var 0) extended
      (NativeEquality.weakenType context domain domain domainFormed domainFormed)
      (NativeMonotoneFormation.operatorWeaken context domain domain operator domainFormed operatorTyped) genericTyped)

def greatestPredicateTyping (context : ContextExpr S n) (domain : TypeExpr S n) (operator : TermExpr S n)
    (formed : Derivation signature (.context context))
    (domainFormed : Derivation signature (.type context domain))
    (operatorTyped : Derivation signature (.term context operator (NativeMonotoneSyntax.operatorType domain))) :
    Derivation signature (.term context (greatestPredicate domain operator) (predicateType domain)) := by
  let extended := NativeMonotoneFormation.extendContext context domain formed domainFormed
  have genericTyped : Derivation signature (.term (.snoc context domain) (.var 0) (domain.rename Fin.succ)) := by
    simpa only [RuleCode.conclusion, ContextExpr.lookup_zero] using
      deriveList (.variable (.snoc context domain) 0) (.cons extended .nil)
  exact quoteLambdaTyping context domain _ formed domainFormed
    (NativeMonotoneFormation.greatestFormation (.snoc context domain) (domain.rename Fin.succ)
      (operator.rename Fin.succ) (.var 0) extended
      (NativeEquality.weakenType context domain domain domainFormed domainFormed)
      (NativeMonotoneFormation.operatorWeaken context domain domain operator domainFormed operatorTyped) genericTyped)

variable [DecidableEq S.TypeSymbol] [DecidableEq S.TermSymbol] [DecidableEq S.PredicateSymbol]

def checkInputs (context : ContextExpr S n) (domain : TypeExpr S n) (operator : TermExpr S n)
    (contextCertificate domainCertificate operatorCertificate monotonicityCertificate : Certificates.Refinement.Certificate signature) : Bool :=
  Certificates.Refinement.check contextCertificate (.context context) &&
    (Certificates.Refinement.check domainCertificate (.type context domain) &&
      (Certificates.Refinement.check operatorCertificate (.term context operator (NativeMonotoneSyntax.operatorType domain)) &&
        Certificates.Refinement.check monotonicityCertificate (.entails context (NativeMonotoneSyntax.monotonicity domain operator))))

theorem checkInputs_exact (context : ContextExpr S n) (domain : TypeExpr S n) (operator : TermExpr S n)
    (contextCertificate domainCertificate operatorCertificate monotonicityCertificate : Certificates.Refinement.Certificate signature) :
    checkInputs context domain operator contextCertificate domainCertificate operatorCertificate monotonicityCertificate = true ↔
      Certificates.Refinement.check contextCertificate (.context context) = true ∧
      Certificates.Refinement.check domainCertificate (.type context domain) = true ∧
      Certificates.Refinement.check operatorCertificate (.term context operator (NativeMonotoneSyntax.operatorType domain)) = true ∧
      Certificates.Refinement.check monotonicityCertificate (.entails context (NativeMonotoneSyntax.monotonicity domain operator)) = true := by
  simp only [checkInputs, Bool.and_eq_true]

structure GeneratedPredicates (signature : Signature S) (n : Nat) where
  leastCode : TermExpr S n
  greatestCode : TermExpr S n
  leastCertificate : Certificates.Refinement.Certificate signature
  greatestCertificate : Certificates.Refinement.Certificate signature

def certifiedGenerate (context : ContextExpr S n) (domain : TypeExpr S n) (operator : TermExpr S n)
    (contextCertificate domainCertificate operatorCertificate monotonicityCertificate : Certificates.Refinement.Certificate signature) :
    Option (GeneratedPredicates signature n) :=
  if accepted : checkInputs context domain operator contextCertificate domainCertificate operatorCertificate monotonicityCertificate = true then
    let checked := (checkInputs_exact context domain operator _ _ _ _).mp accepted
    let formed := Certificates.Refinement.reconstruct contextCertificate _ checked.1
    let domainFormed := Certificates.Refinement.reconstruct domainCertificate _ checked.2.1
    let operatorTyped := Certificates.Refinement.reconstruct operatorCertificate _ checked.2.2.1
    some {
      leastCode := leastPredicate domain operator
      greatestCode := greatestPredicate domain operator
      leastCertificate := Certificates.Refinement.erase (leastPredicateTyping context domain operator formed domainFormed operatorTyped)
      greatestCertificate := Certificates.Refinement.erase (greatestPredicateTyping context domain operator formed domainFormed operatorTyped) }
  else none

theorem certifiedGenerate_checked (context : ContextExpr S n) (domain : TypeExpr S n) (operator : TermExpr S n)
    (contextCertificate domainCertificate operatorCertificate monotonicityCertificate : Certificates.Refinement.Certificate signature)
    (generated : GeneratedPredicates signature n)
    (result : certifiedGenerate context domain operator contextCertificate domainCertificate operatorCertificate monotonicityCertificate = some generated) :
    generated.leastCode = leastPredicate domain operator ∧ generated.greatestCode = greatestPredicate domain operator ∧
      Certificates.Refinement.check generated.leastCertificate (.term context generated.leastCode (predicateType domain)) = true ∧
      Certificates.Refinement.check generated.greatestCertificate (.term context generated.greatestCode (predicateType domain)) = true := by
  unfold certifiedGenerate at result
  split at result
  · cases Option.some.inj result
    exact ⟨rfl,rfl,Certificates.Refinement.check_erase _,Certificates.Refinement.check_erase _⟩
  · contradiction

theorem certifiedGenerate_isSome (context : ContextExpr S n) (domain : TypeExpr S n) (operator : TermExpr S n)
    (contextCertificate domainCertificate operatorCertificate monotonicityCertificate : Certificates.Refinement.Certificate signature) :
    (certifiedGenerate context domain operator contextCertificate domainCertificate operatorCertificate monotonicityCertificate).isSome = true ↔
      checkInputs context domain operator contextCertificate domainCertificate operatorCertificate monotonicityCertificate = true := by
  unfold certifiedGenerate
  split <;> simp_all

theorem finite_generation_complete (context : ContextExpr S n) (domain : TypeExpr S n) (operator : TermExpr S n)
    (formed : Derivation signature (.context context))
    (domainFormed : Derivation signature (.type context domain))
    (operatorTyped : Derivation signature (.term context operator (NativeMonotoneSyntax.operatorType domain)))
    (monotonicityProved : Derivation signature (.entails context (NativeMonotoneSyntax.monotonicity domain operator))) :
    (certifiedGenerate context domain operator (Certificates.Refinement.erase formed)
      (Certificates.Refinement.erase domainFormed) (Certificates.Refinement.erase operatorTyped)
      (Certificates.Refinement.erase monotonicityProved)).isSome = true := by
  apply (certifiedGenerate_isSome context domain operator _ _ _ _).mpr
  simp only [checkInputs, Certificates.Refinement.check_erase, Bool.and_self]

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotonePredicates
