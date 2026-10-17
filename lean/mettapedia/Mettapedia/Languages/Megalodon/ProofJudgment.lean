import Mettapedia.Languages.Megalodon.MathdataKernel

/-!
# Context-indexed native Megalodon proof judgments

The rules below give a relational reading of every ordinary Mathdata proof
constructor. The two-way theorem relates this independently structured
derivation to the existing recursive checker, including its exact context
changes and its bounded normalization operations. Proposition formation and
admission of the selected environment remain separate checks.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.ProofJudgment

open MathdataKernel

structure Context where
  typeDepth : Nat
  terms : List Tp
  hypotheses : List Tm
  deriving DecidableEq, Repr

def Context.termBinder (context : Context) (type : Tp) : Context :=
  ⟨context.typeDepth, type :: context.terms, context.hypotheses.map (Tm.shift 0 1)⟩

def Context.proofBinder (context : Context) (proposition : Tm) : Context :=
  { context with hypotheses := proposition :: context.hypotheses }

def Context.typeBinder (context : Context) : Context :=
  ⟨context.typeDepth + 1, [], []⟩

inductive Proves (environment : Environment) (fuel : Nat) : Context → Pf → Tm → Prop where
  | hyp {context : Context} {index : Nat} {proposition : Tm} :
      context.hypotheses[index]? = some proposition →
      Proves environment fuel context (.hyp index) proposition
  | known {context : Context} {name : Name} {source proposition : Tm} :
      environment.lookupKnown? name = some source →
      normalize environment fuel source = some proposition →
      Proves environment fuel context (.known name) proposition
  | termApp {context : Context} {proof : Pf} {argument body normalized proposition : Tm}
      {domain : Tp} :
      Proves environment fuel context proof (.all domain body) →
      inferTerm environment context.typeDepth context.terms argument = some domain →
      deltaNormalize environment fuel argument = some normalized →
      normalize environment fuel (Tm.instantiate normalized body) = some proposition →
      Proves environment fuel context (.termApp proof argument) proposition
  | proofApp {context : Context} {function argument : Pf} {domain codomain : Tm} :
      Proves environment fuel context function (.imp domain codomain) →
      Proves environment fuel context argument domain →
      Proves environment fuel context (.proofApp function argument) codomain
  | termLam {context : Context} {type : Tp} {proof : Pf} {body : Tm} :
      type.plainWellFormed context.typeDepth = true →
      Proves environment fuel (context.termBinder type) proof body →
      Proves environment fuel context (.termLam type proof) (.all type body)
  | proofLam {context : Context} {proposition normalized body : Tm} {proof : Pf} :
      inferTerm environment context.typeDepth context.terms proposition = some .prop →
      normalize environment fuel proposition = some normalized →
      Proves environment fuel (context.proofBinder normalized) proof body →
      Proves environment fuel context (.proofLam proposition proof) (.imp normalized body)
  | typeApp {context : Context} {proof : Pf} {type : Tp} {body : Tm} :
      Proves environment fuel context proof (.typeAll body) →
      Proves environment fuel context (.typeApp proof type) (Tm.typeInstantiate type body)
  | typeLam {context : Context} {proof : Pf} {body : Tm} :
      context.terms = [] → context.hypotheses = [] →
      Proves environment fuel context.typeBinder proof body →
      Proves environment fuel context (.typeLam proof) (.typeAll body)

theorem Proves.infer {environment : Environment} {fuel : Nat} {context : Context}
    {proof : Pf} {proposition : Tm} (derivation : Proves environment fuel context proof proposition) :
    inferProof environment fuel context.typeDepth context.terms context.hypotheses proof =
      some proposition := by
  induction derivation with
  | hyp found => exact found
  | known found normalized => simp [inferProof, found, normalized]
  | termApp _ typed unfolded normalized ih =>
      simp [inferProof, ih, typed, unfolded, normalized]
  | proofApp _ _ ihf iha => simp [inferProof, ihf, iha]
  | termLam formed _ ih =>
      simp only [Context.termBinder] at ih
      simp [inferProof, formed, ih]
  | proofLam typed normalized _ ih =>
      simp only [Context.proofBinder] at ih
      simp [inferProof, typed, normalized, ih]
  | typeApp _ ih => simp [inferProof, ih]
  | typeLam terms hypotheses _ ih =>
      simp only [Context.typeBinder] at ih
      simp [inferProof, terms, hypotheses, ih]

theorem proves_of_infer {environment : Environment} {fuel : Nat} {context : Context}
    {proof : Pf} {proposition : Tm}
    (accepted : inferProof environment fuel context.typeDepth context.terms context.hypotheses proof =
      some proposition) : Proves environment fuel context proof proposition := by
  induction proof generalizing context proposition with
  | gpa name => simp [inferProof] at accepted
  | hyp index => exact .hyp accepted
  | known name =>
      cases found : environment.lookupKnown? name with
      | none => simp [inferProof, found] at accepted
      | some source =>
          exact .known found (by simpa [inferProof, found] using accepted)
  | termApp function argument ih =>
      cases functionResult : inferProof environment fuel context.typeDepth context.terms
          context.hypotheses function with
      | none => simp [inferProof, functionResult] at accepted
      | some result =>
          cases result <;> simp only [inferProof, functionResult] at accepted
          all_goals try contradiction
          rename_i domain body
          cases typed : inferTerm environment context.typeDepth context.terms argument with
          | none => simp [typed] at accepted
          | some actual =>
              by_cases same : actual = domain
              · subst actual
                cases unfolded : deltaNormalize environment fuel argument with
                | none => simp [typed, unfolded] at accepted
                | some normalized =>
                    exact .termApp (ih functionResult) typed unfolded
                      (by simpa [typed, unfolded] using accepted)
              · simp [typed, same] at accepted
  | proofApp function argument ihf iha =>
      cases functionResult : inferProof environment fuel context.typeDepth context.terms
          context.hypotheses function with
      | none => simp [inferProof, functionResult] at accepted
      | some result =>
          cases result <;> simp only [inferProof, functionResult] at accepted
          all_goals try contradiction
          rename_i domain codomain
          cases argumentResult : inferProof environment fuel context.typeDepth context.terms
              context.hypotheses argument with
          | none => simp [argumentResult] at accepted
          | some actual =>
              by_cases same : actual = domain
              · subst actual
                have equal : codomain = proposition := by simpa [argumentResult] using accepted
                subst proposition
                exact .proofApp (ihf functionResult) (iha argumentResult)
              · simp [argumentResult, same] at accepted
  | termLam type proof ih =>
      by_cases formed : type.plainWellFormed context.typeDepth = true
      · cases bodyResult : inferProof environment fuel context.typeDepth (type :: context.terms)
            (context.hypotheses.map (Tm.shift 0 1)) proof with
        | none => simp [inferProof, formed, bodyResult] at accepted
        | some body =>
            have equal : Tm.all type body = proposition := by
              simpa [inferProof, formed, bodyResult] using accepted
            subst proposition
            exact .termLam formed (ih (context := context.termBinder type) bodyResult)
      · simp [inferProof, formed] at accepted
  | proofLam source proof ih =>
      cases typed : inferTerm environment context.typeDepth context.terms source with
      | none => simp [inferProof, typed] at accepted
      | some type =>
          by_cases same : type = .prop
          · subst type
            cases normalized : normalize environment fuel source with
            | none => simp [inferProof, typed, normalized] at accepted
            | some normal =>
                cases bodyResult : inferProof environment fuel context.typeDepth context.terms
                    (normal :: context.hypotheses) proof with
                | none => simp [inferProof, typed, normalized, bodyResult] at accepted
                | some body =>
                    have equal : Tm.imp normal body = proposition := by
                      simpa [inferProof, typed, normalized, bodyResult] using accepted
                    subst proposition
                    exact .proofLam typed normalized
                      (ih (context := context.proofBinder normal) bodyResult)
          · simp [inferProof, typed, same] at accepted
  | typeApp function type ih =>
      cases functionResult : inferProof environment fuel context.typeDepth context.terms
          context.hypotheses function with
      | none => simp [inferProof, functionResult] at accepted
      | some result =>
          cases result <;> simp only [inferProof, functionResult] at accepted
          all_goals try contradiction
          rename_i body
          have equal : Tm.typeInstantiate type body = proposition := Option.some.inj accepted
          subst proposition
          exact .typeApp (ih functionResult)
  | typeLam proof ih =>
      by_cases empty : context.terms = [] ∧ context.hypotheses = []
      · obtain ⟨terms, hypotheses⟩ := empty
        cases bodyResult : inferProof environment fuel (context.typeDepth + 1) [] [] proof with
        | none => simp [inferProof, terms, hypotheses, bodyResult] at accepted
        | some body =>
            have equal : Tm.typeAll body = proposition := by
              simpa [inferProof, terms, hypotheses, bodyResult] using accepted
            subst proposition
            exact .typeLam terms hypotheses (ih (context := context.typeBinder) bodyResult)
      · simp [inferProof, List.isEmpty_iff, empty] at accepted

theorem infer_iff (environment : Environment) (fuel : Nat) (context : Context)
    (proof : Pf) (proposition : Tm) :
    inferProof environment fuel context.typeDepth context.terms context.hypotheses proof =
      some proposition ↔ Proves environment fuel context proof proposition :=
  ⟨proves_of_infer, Proves.infer⟩

theorem check_iff (environment : Environment) (fuel : Nat) (context : Context)
    (proof : Pf) (proposition : Tm) :
    checkProof environment fuel context.typeDepth context.terms context.hypotheses proof proposition =
      true ↔ ∃ normal, normalize environment fuel proposition = some normal ∧
        Proves environment fuel context proof normal := by
  cases normalized : normalize environment fuel proposition <;>
    simp [checkProof, checkNormalizedProof, normalized, infer_iff]

end Mettapedia.Languages.Megalodon.ProofJudgment
