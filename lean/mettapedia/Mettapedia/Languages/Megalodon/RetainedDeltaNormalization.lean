import Mettapedia.Languages.Megalodon.HenkinDeltaInterpretation
import Mettapedia.Languages.Megalodon.RetainedNormalization
import Mettapedia.Logic.HOL.ConstantExpansionProofs
import Mettapedia.Logic.HOL.ProofSyntaxHypothesisSubstitution

/-!
# Retained equality evidence for checked definition unfolding

The definition checker establishes the type of each body. Its defining
equation is a separate, explicit source premise. Finite delta expansion
composes those equations through the actual syntax, including binders, and
then joins the existing beta/eta proof-producing normalization.

Cycles are not ruled out by this interface. The native fuel test remains the
success condition; no termination or consistency conclusion is obtained from
body typing alone. The returned evidence is ordinary retained HOL proof data.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.Megalodon.RetainedDeltaNormalization
open MathdataKernel HenkinTermInterpretation
open Mettapedia.Logic.HOL
open ConstantExpansionProofs

variable {environment : Environment}

/-- Equality evidence for the authored defining equations, at their actual
closed types. It does not assert the equation of a normalized whole term. -/
def DefinitionEquations (checked : CheckedPlainDefinitions environment)
    (theory : List (ClosedFormula (Constant environment))) :=
  ∀ {type : Ty Base} (name : Name) (declaration : TermDecl)
    (lookup : environment.lookupTerm? name = some declaration)
    (typed : declaration.type = reifyType type) (body : Tm)
    (defined : declaration.definition = some body),
    ProofSyntax (Constant environment) theory
      (.eq (.const (.named name declaration lookup typed))
        (checked.interpretBody name declaration lookup typed body defined))

/-- Compute the equality of a recursively unfolded constant from its own
one-step equation and the equations used inside its body. -/
def constant (checked : CheckedPlainDefinitions environment)
    (theory : List (ClosedFormula (Constant environment)))
    (equations : DefinitionEquations checked theory) :
    (fuel : Nat) → {type : Ty Base} → (symbol : Constant environment type) →
    {result : ClosedTerm (Constant environment) type} →
    deltaConstants checked fuel symbol = some result →
    ProofSyntax (Constant environment) theory (.eq (.const symbol) result)
  | fuel, _, .primitive index lookup, result, success => by
      cases fuel <;> simp only [deltaConstants, Option.some.injEq] at success <;>
        subst result <;> exact .eqRefl _
  | 0, _, .named name declaration lookup typed, result, success => by
      rcases declaration with ⟨declName, declType, definition⟩
      cases definition with
      | none =>
          cases Option.some.inj success
          exact .eqRefl _
      | some body => simp [deltaConstants] at success
  | fuel + 1, _, .named name declaration lookup typed, result, success => by
      rcases declaration with ⟨declName, declType, definition⟩
      cases definition with
      | none =>
          cases Option.some.inj success
          exact .eqRefl _
      | some body =>
          have expanded : substConst? (deltaConstants checked fuel)
              (checked.interpretBody name _ lookup typed body rfl) = some result := success
          let bodyProof := expand theory (deltaConstants checked fuel)
            (fun symbol target computed => constant checked theory equations fuel symbol computed)
            (checked.interpretBody name _ lookup typed body rfl) expanded
          have targetProof : ProofSyntax (Constant environment) theory
              (.eq (checked.interpretBody name _ lookup typed body rfl) result) :=
            ProofSyntax.castIndices (by change theory.map id = theory; simp) rfl bodyProof
          exact .eqTrans (equations name _ lookup typed body rfl) targetProof

structure Result (theory : List (ClosedFormula (Constant environment)))
    {Γ : Ctx Base} {type : Ty Base} (source : Term (Constant environment) Γ type) (rawTarget : Tm) where
  target : Term (Constant environment) Γ type
  erased : erase target = some rawTarget
  proof : ProofSyntax (Constant environment) (assumptionsAt theory Γ) (.eq source target)

/-- Success of the actual native delta evaluator supplies the exact target
of the retained equality. Failed or exhausted runs produce no evidence. -/
def delta (checked : CheckedPlainDefinitions environment)
    (theory : List (ClosedFormula (Constant environment)))
    (equations : DefinitionEquations checked theory) (fuel : Nat)
    {Γ : Ctx Base} {type : Ty Base} (source : Term (Constant environment) Γ type)
    {rawSource rawTarget : Tm} (erased : erase source = some rawSource)
    (accepted : deltaNormalize environment fuel rawSource = some rawTarget) :
    Result theory source rawTarget := by
  if same : rawSource = rawTarget then
    exact ⟨source, erased.trans (congrArg some same), .eqRefl source⟩
  else
    have comparison := erase_deltaInterpretation checked fuel source
    rw [erased, Option.bind_some, accepted] at comparison
    cases computed : deltaInterpretation checked fuel source with
    | none => simp [computed] at comparison
    | some target =>
        exact ⟨target, by simpa [computed] using comparison,
          expand theory (deltaConstants checked fuel)
            (fun symbol body success => constant checked theory equations fuel symbol success)
            source computed⟩

/-- The complete monomorphic native conversion policy: checked definitions,
then finite beta/eta normalization, with all defining premises retained. -/
def normalize (checked : CheckedPlainDefinitions environment)
    (theory : List (ClosedFormula (Constant environment)))
    (equations : DefinitionEquations checked theory) (fuel : Nat)
    {Γ : Ctx Base} {type : Ty Base} (source : Term (Constant environment) Γ type)
    {rawSource rawTarget : Tm} (erased : erase source = some rawSource)
    (accepted : MathdataKernel.normalize environment fuel rawSource = some rawTarget) :
    Result theory source rawTarget := by
  cases unfolded : deltaNormalize environment fuel rawSource with
  | none => simp [MathdataKernel.normalize, unfolded] at accepted
  | some middle =>
      let first := delta checked theory equations fuel source erased unfolded
      have normalized : Tm.normalize fuel middle = some rawTarget := by
        simpa [MathdataKernel.normalize, unfolded] using accepted
      let second := RetainedNormalization.readback fuel first.target first.erased normalized
      exact ⟨second.val.target, second.property,
        .eqTrans first.proof
          (second.val.proof.mono (ProofSyntax.emptyOccurrenceMap _))⟩

end Mettapedia.Languages.Megalodon.RetainedDeltaNormalization
