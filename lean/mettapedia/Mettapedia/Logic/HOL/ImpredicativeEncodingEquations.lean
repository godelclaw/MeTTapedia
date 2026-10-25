import Mettapedia.Logic.HOL.ProofSyntaxCongruence
import Mettapedia.Logic.HOL.ImpredicativeProofTranslation
import Mettapedia.Logic.HOL.ImpredicativeProofModulo
import Mettapedia.Logic.HOL.ProofSyntaxHypothesisSubstitution

/-!
# Retained equations for the impredicative connective interpretation

Every source term is equated with its inline connective expansion by a proof
in the existing extensional HOL calculus. The comparison traverses all term
constructors and constructs the local connective equations. Proof transport
substitutes actual evidence for each ordered hypothesis occurrence.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.ImpredicativeEncodingEquations
open ImpredicativeConnectives ContextualTrinity
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {gamma : Ctx Base}
variable {assumptions : List (Formula Const gamma)}

def truthEquation : ProofSyntax Const assumptions (.eq .top truth) :=
  .eqPropI (.impI truthIntro) (.impI .topI)

def falsityEquation : ProofSyntax Const assumptions (.eq .bot falsity) :=
  .eqPropI (.impI (.botE (.hyp 0))) (.impI (falsityElim .bot (.hyp 0)))

def conjunctionEquation (first second : Formula Const gamma) :
    ProofSyntax Const assumptions (.eq (.and first second) (conjunctionFormula first second)) := by
  apply ProofSyntax.eqPropI
  · apply ProofSyntax.impI
    exact .impE (.eqPropEL (conjunctionBeta first second)) (conjunctionIntro (.andEL (.hyp 0)) (.andER (.hyp 0)))
  · apply ProofSyntax.impI
    let supplied := ProofSyntax.impE (ProofSyntax.eqPropER (conjunctionBeta first second))
      (ProofSyntax.hyp (Const := Const) (Δ := conjunctionFormula first second :: assumptions) 0)
    exact .andI (conjunctionLeft supplied) (conjunctionRight supplied)

def disjunctionEquation (first second : Formula Const gamma) :
    ProofSyntax Const assumptions (.eq (.or first second) (disjunctionFormula first second)) := by
  apply ProofSyntax.eqPropI
  · apply ProofSyntax.impI
    apply ProofSyntax.impE (ProofSyntax.eqPropEL (disjunctionBeta first second))
    exact .orE (.hyp 0) (disjunctionLeft (.hyp 0)) (disjunctionRight (.hyp 0))
  · apply ProofSyntax.impI
    let supplied := ProofSyntax.impE (ProofSyntax.eqPropER (disjunctionBeta first second))
      (ProofSyntax.hyp (Const := Const) (Δ := disjunctionFormula first second :: assumptions) 0)
    exact disjunctionElim supplied (.orIL (.hyp 0)) (.orIR (.hyp 0))

def negationEquation (formula : Formula Const gamma) :
    ProofSyntax Const assumptions (.eq (.not formula) (.imp formula falsity)) :=
  .eqPropI (.impI (.impI (.botE (.notE (.hyp 1) (.hyp 0)))))
    (.impI (.notI (falsityElim .bot (.impE (.hyp 1) (.hyp 0)))))

def inlineExistentialIntro {domain : Ty Base} {body : Formula Const (domain :: gamma)}
    (witness : Term Const gamma domain) (proof : ProofSyntax Const assumptions (instantiate witness body)) :
    ProofSyntax Const assumptions (existentialInline body) := by
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  let continuation : Formula Const (.prop :: gamma) :=
    .all (.imp (rename (Rename.lift Rename.weaken) body) (.var (.vs .vz)))
  have selected := ProofSyntax.allE (weaken (σ := .prop) witness)
    (ProofSyntax.hyp (Const := Const) (Δ := continuation :: weakenHyps (σ := .prop) assumptions) 0)
  have specialized : ProofSyntax Const (continuation :: weakenHyps (σ := .prop) assumptions)
      (.imp (weaken (σ := .prop) (instantiate witness body)) (.var .vz)) :=
    ProofSyntax.castIndices rfl (Modulo.instantiate_existentialInstance witness body) selected
  exact .impE specialized ((proof.rename Rename.weaken).prepend _)

def inlineExistentialElim {domain : Ty Base} {body : Formula Const (domain :: gamma)}
    {result : Formula Const gamma} (major : ProofSyntax Const assumptions (existentialInline body))
    (branch : ProofSyntax Const (body :: weakenHyps (σ := domain) assumptions) (weaken result)) :
    ProofSyntax Const assumptions result :=
  .impE (ProofSyntax.castIndices rfl (Modulo.instantiate_existentialBody result body) (.allE result major))
    (.allI (.impI branch))

def existentialEquation {domain : Ty Base} (body : Formula Const (domain :: gamma)) :
    ProofSyntax Const assumptions (.eq (.ex body) (existentialInline body)) := by
  let lifted := rename (Rename.lift (Rename.weaken (σ := domain))) body
  have instanceEquation : instantiate (.var .vz) lifted = body := instantiate_vz_rename_lift_weaken body
  apply ProofSyntax.eqPropI
  · apply ProofSyntax.impI
    apply ProofSyntax.exE (.hyp 0)
    have supplied : ProofSyntax Const (body :: weakenHyps (σ := domain) (.ex body :: assumptions))
        (instantiate (.var .vz) lifted) := ProofSyntax.castIndices rfl instanceEquation.symm (.hyp 0)
    have packed := inlineExistentialIntro (.var .vz) supplied
    exact ProofSyntax.castIndices rfl (rename_existentialInline Rename.weaken body).symm packed
  · apply ProofSyntax.impI
    apply inlineExistentialElim (ProofSyntax.hyp 0)
    have supplied : ProofSyntax Const (body :: weakenHyps (σ := domain) (existentialInline body :: assumptions))
        (instantiate (.var .vz) lifted) := ProofSyntax.castIndices rfl instanceEquation.symm (.hyp 0)
    exact .exI (.var .vz) supplied

/-- All constructors, including equality and object binders, retain actual
source equality evidence at the requested assumption list. -/
def equation {gamma : Ctx Base} {type : Ty Base} (source : Term Const gamma type)
    (assumptions : List (Formula Const gamma)) : ProofSyntax Const assumptions (.eq source (expandInline source)) :=
  match source with
  | .var index => .eqRefl (.var index)
  | .const symbol => .eqRefl (.const symbol)
  | .app function argument => ProofSyntax.appCongr (equation function assumptions) (equation argument assumptions)
  | .lam body => .eqLam (equation body (weakenHyps assumptions))
  | .top => truthEquation
  | .bot => falsityEquation
  | .and first second => .eqTrans (ProofSyntax.andCongr (equation first assumptions) (equation second assumptions))
      (conjunctionEquation (expandInline first) (expandInline second))
  | .or first second => .eqTrans (ProofSyntax.orCongr (equation first assumptions) (equation second assumptions))
      (disjunctionEquation (expandInline first) (expandInline second))
  | .imp first second => ProofSyntax.impCongr (equation first assumptions) (equation second assumptions)
  | .not body => .eqTrans (ProofSyntax.notCongr (equation body assumptions)) (negationEquation (expandInline body))
  | .eq first second => ProofSyntax.eqCongr (equation first assumptions) (equation second assumptions)
  | .all body => allCongr (equation body (weakenHyps assumptions))
  | .ex body => .eqTrans (exCongr (equation body (weakenHyps assumptions))) (existentialEquation (expandInline body))
termination_by structural source

#print axioms truthEquation
#print axioms conjunctionEquation
#print axioms existentialEquation
#print axioms equation
end Mettapedia.Logic.HOL.ImpredicativeEncodingEquations
