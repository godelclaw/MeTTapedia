import Mettapedia.Logic.HOL.ProofSyntaxStructural

/-!
# Retained HOL proofs for guarded retractions

A left inverse on the valid source values gives injectivity on that same
guarded domain. The construction returns an actual object-HOL proof tree.
It uses quantifier instantiation, implication and equality congruence; no
semantic datatype law, choice or function-extensionality rule is inserted.

The guards remain explicit. A datatype client must separately produce its
actual retraction law and the representation of its valid source values.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.GuardedRetraction
universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
variable {Γ : Ctx Base} {σ τ : Ty Base}

def law (encode : Term Const Γ (σ ⇒ τ)) (decode : Term Const Γ (τ ⇒ σ))
    (valid : Term Const Γ (σ ⇒ .prop)) : Formula Const Γ :=
  .all (.imp (.app (weaken valid) (.var .vz))
    (.eq (.app (weaken decode) (.app (weaken encode) (.var .vz))) (.var .vz)))

def consequence (encode : Term Const Γ (σ ⇒ τ)) (decode : Term Const Γ (τ ⇒ σ))
    (valid : Term Const Γ (σ ⇒ .prop)) (first second : Term Const Γ σ) : Formula Const Γ :=
  .imp (law encode decode valid)
    (.imp (.app valid first) (.imp (.app valid second)
      (.imp (.eq (.app encode first) (.app encode second)) (.eq first second))))

def unguardedConsequence (encode : Term Const Γ (σ ⇒ τ)) (decode : Term Const Γ (τ ⇒ σ))
    (valid : Term Const Γ (σ ⇒ .prop)) (first second : Term Const Γ σ) : Formula Const Γ :=
  .imp (law encode decode valid)
    (.imp (.eq (.app encode first) (.app encode second)) (.eq first second))

theorem instantiate_law (encode : Term Const Γ (σ ⇒ τ)) (decode : Term Const Γ (τ ⇒ σ))
    (valid : Term Const Γ (σ ⇒ .prop)) (value : Term Const Γ σ) :
    instantiate value
      (.imp (.app (weaken valid) (.var .vz))
        (.eq (.app (weaken decode) (.app (weaken encode) (.var .vz))) (.var .vz))) =
      .imp (.app valid value) (.eq (.app decode (.app encode value)) value) := by
  simp only [instantiate, subst, Subst.single]
  rw [show subst (Subst.single value) (weaken valid) = valid from instantiate_weaken value valid,
    show subst (Subst.single value) (weaken decode) = decode from instantiate_weaken value decode,
    show subst (Subst.single value) (weaken encode) = encode from instantiate_weaken value encode]

/-- This transforms four retained proofs through genuine logical inference;
the conclusion is not among its input propositions. -/
def reflectEquality {Δ : List (Formula Const Γ)}
    (encode : Term Const Γ (σ ⇒ τ)) (decode : Term Const Γ (τ ⇒ σ))
    (valid : Term Const Γ (σ ⇒ .prop)) (first second : Term Const Γ σ)
    (retraction : ProofSyntax Const Δ (law encode decode valid))
    (firstValid : ProofSyntax Const Δ (.app valid first))
    (secondValid : ProofSyntax Const Δ (.app valid second))
    (same : ProofSyntax Const Δ (.eq (.app encode first) (.app encode second))) :
    ProofSyntax Const Δ (.eq first second) := by
  have firstLaw : ProofSyntax Const Δ
      (.imp (.app valid first) (.eq (.app decode (.app encode first)) first)) := by
    simpa only [law, instantiate_law] using ProofSyntax.allE first retraction
  have secondLaw : ProofSyntax Const Δ
      (.imp (.app valid second) (.eq (.app decode (.app encode second)) second)) := by
    simpa only [law, instantiate_law] using ProofSyntax.allE second retraction
  exact .eqTrans (.eqSymm (.impE firstLaw firstValid))
    (.eqTrans (.eqAppArg decode same) (.impE secondLaw secondValid))

def pointProof (encode : Term Const Γ (σ ⇒ τ)) (decode : Term Const Γ (τ ⇒ σ))
    (valid : Term Const Γ (σ ⇒ .prop)) (first second : Term Const Γ σ) :
    ProofSyntax Const [] (consequence encode decode valid first second) := by
  refine .impI (.impI (.impI (.impI ?_)))
  exact reflectEquality encode decode valid first second
    (.hyp ⟨3, by simp⟩) (.hyp ⟨2, by simp⟩) (.hyp ⟨1, by simp⟩) (.hyp ⟨0, by simp⟩)

/-- Functions, the source guard and both compared values are all quantified
in the object language. The statement is closed and contains no constants. -/
def rule (σ τ : Ty Base) : ClosedFormula Const :=
  .all (σ := σ ⇒ τ) (.all (σ := τ ⇒ σ) (.all (σ := σ ⇒ .prop)
    (.all (σ := σ) (.all (σ := σ)
      (consequence (.var (.vs (.vs (.vs (.vs .vz))))) (.var (.vs (.vs (.vs .vz))))
        (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))))))

def ruleProof (σ τ : Ty Base) : ProofSyntax Const [] (rule σ τ) :=
  .allI (.allI (.allI (.allI (.allI
    (pointProof (.var (.vs (.vs (.vs (.vs .vz))))) (.var (.vs (.vs (.vs .vz))))
      (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))))))

/-- A source value is stored as a constant Boolean-indexed function. -/
def constantEmbedding : Term Const Γ (σ ⇒ (.prop ⇒ σ)) :=
  .lam (.lam (.var (.vs .vz)))

def evaluateTrue : Term Const Γ ((.prop ⇒ σ) ⇒ σ) :=
  .lam (.app (.var .vz) .top)

def allValid : Term Const Γ (σ ⇒ .prop) := .lam .top

def functionalRoundtrip {Δ : List (Formula Const Γ)} (value : Term Const Γ σ) :
    ProofSyntax Const Δ
      (.eq (.app evaluateTrue (.app constantEmbedding value)) value) := by
  have decodeBeta : ProofSyntax Const Δ
      (.eq (.app evaluateTrue (.app constantEmbedding value))
        (.app (.app constantEmbedding value) .top)) := by
    simpa only [evaluateTrue, instantiate, subst, Subst.single] using
      (ProofSyntax.beta (Δ := Δ) (.app constantEmbedding value) (.app (.var .vz) .top))
  have encodeBeta : ProofSyntax Const Δ
      (.eq (.app constantEmbedding value) (.lam (weaken value))) := by
    simpa only [constantEmbedding, instantiate, subst, Subst.single, Subst.lift, weaken] using
      (ProofSyntax.beta (Δ := Δ) value (.lam (.var (.vs .vz))))
  have readBeta : ProofSyntax Const Δ (.eq (.app (.lam (weaken value)) .top) value) := by
    simpa only [instantiate_weaken] using ProofSyntax.beta (Δ := Δ) .top (weaken value)
  exact .eqTrans decodeBeta (.eqTrans (.eqApp .top encodeBeta) readBeta)

def functionalLaw {Δ : List (Formula Const Γ)} :
    ProofSyntax Const Δ (law (constantEmbedding (σ := σ)) evaluateTrue allValid) := by
  refine .allI (.impI ?_)
  exact functionalRoundtrip (.var .vz)

def allValidProof {Δ : List (Formula Const Γ)} (value : Term Const Γ σ) :
    ProofSyntax Const Δ (.app allValid value) := by
  have beta : ProofSyntax Const Δ (.eq (.app allValid value) .top) := by
    simpa only [allValid, instantiate, subst] using ProofSyntax.beta (Δ := Δ) value .top
  exact .impE (.eqPropER beta) .topI

/-- The two Boolean values stay distinct after the higher-order encoding.
The proof uses the proved beta retraction, not an injectivity assumption. -/
def functionalSeparation : ProofSyntax Const []
    (.not (.eq (.app (constantEmbedding (Γ := Γ) (σ := .prop)) .top) (.app constantEmbedding .bot))) := by
  refine .notI ?_
  have same : ProofSyntax Const
      [.eq (.app (constantEmbedding (Γ := Γ)) .top) (.app constantEmbedding .bot)]
      (.eq (.top : Term Const Γ .prop) .bot) :=
    reflectEquality constantEmbedding evaluateTrue allValid
      .top .bot functionalLaw (allValidProof .top) (allValidProof .bot) (.hyp ⟨0, by simp⟩)
  exact .impE (.eqPropEL same) .topI

#print axioms instantiate_law
#print axioms reflectEquality
#print axioms ruleProof
#print axioms functionalRoundtrip
#print axioms functionalLaw
#print axioms functionalSeparation
end Mettapedia.Logic.HOL.GuardedRetraction
