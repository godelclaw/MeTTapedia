import Mettapedia.Logic.HOL.Syntax.PartialConstSubstitution
import Mettapedia.Logic.HOL.ProofSyntaxCongruence

/-!
# Equality proofs for partial expansion of constants

Closed defining equations extend under object binders and compose through all
HOL term constructors. A successful partial constant expansion therefore has
an actual retained equality proof relative to those equations. Unused missing
replacements impose no premise; a missing used replacement still fails.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.ConstantExpansionProofs
open ContextualTrinity
universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
variable {Γ : Ctx Base} {σ τ : Ty Base}

def assumptionsAt (theory : List (ClosedFormula Const)) (context : Ctx Base) :=
  theory.map (weakenCtx context)

theorem assumptionsAt_cons (theory : List (ClosedFormula Const)) (type : Ty Base) (context : Ctx Base) :
    assumptionsAt theory (type :: context) = weakenHyps (assumptionsAt theory context) := by
  simp [assumptionsAt, weakenHyps, List.map_map, weakenCtx_cons]

/-- Extend the context of a derivation and all its closed assumptions. -/
def weakenProof {theory : List (ClosedFormula Const)} {formula : ClosedFormula Const}
    (context : Ctx Base) (proof : ProofSyntax Const theory formula) :
    ProofSyntax Const (assumptionsAt theory context) (weakenCtx context formula) :=
  match context with
  | [] => ProofSyntax.castIndices (by change theory = theory.map id; simp) rfl proof
  | type :: context =>
      ProofSyntax.castIndices (assumptionsAt_cons theory type context).symm rfl
        (ProofSyntax.rename Rename.weaken (weakenProof context proof))

theorem weakenCtx_eq (context : Ctx Base) (left right : ClosedTerm Const τ) :
    weakenCtx context (.eq left right) = .eq (weakenCtx context left) (weakenCtx context right) := by
  induction context with
  | nil => rfl
  | cons type context ih => simp only [weakenCtx_cons, ih, weaken, rename]

variable {assumptions : List (Formula Const Γ)}

/-- The premise supplies only the equations of individual constants. The
construction derives the equation of the entire expanded term, including
lambda, universal and existential binders. -/
def expand (theory : List (ClosedFormula Const))
    (replacements : ∀ {type}, Const type → Option (ClosedTerm Const type))
    (equations : ∀ {type} (constant : Const type) (body : ClosedTerm Const type),
      replacements constant = some body → ProofSyntax Const theory (.eq (.const constant) body)) :
    {Γ : Ctx Base} → {τ : Ty Base} → (term : Term Const Γ τ) →
    {result : Term Const Γ τ} → substConst? replacements term = some result →
    ProofSyntax Const (assumptionsAt theory Γ) (.eq term result)
  | _, _, .var index, result, success => by
      cases Option.some.inj success
      exact .eqRefl (.var index)
  | Γ, _, .const constant, result, success => by
      cases computed : replacements constant with
      | none => simp [substConst?, computed] at success
      | some body =>
          have same : weakenCtx Γ body = result := by simpa [substConst?, computed] using success
          subst result
          exact ProofSyntax.castIndices rfl
            (by rw [weakenCtx_eq, weakenCtx_const])
            (weakenProof Γ (equations constant body computed))
  | _, _, .app function argument, result, success => by
      cases hf : substConst? replacements function <;> cases ha : substConst? replacements argument <;>
        simp [substConst?, hf, ha] at success
      subst result
      exact .eqTrans (.eqApp argument (expand theory replacements equations function hf))
        (.eqAppArg _ (expand theory replacements equations argument ha))
  | _, _, .top, result, success => by
      cases Option.some.inj success
      exact .eqRefl .top
  | _, _, .bot, result, success => by
      cases Option.some.inj success
      exact .eqRefl .bot
  | _, _, .and left right, result, success => by
      cases hl : substConst? replacements left <;> cases hr : substConst? replacements right <;>
        simp [substConst?, hl, hr] at success
      subst result
      exact ProofSyntax.andCongr (expand theory replacements equations left hl)
        (expand theory replacements equations right hr)
  | _, _, .or left right, result, success => by
      cases hl : substConst? replacements left <;> cases hr : substConst? replacements right <;>
        simp [substConst?, hl, hr] at success
      subst result
      exact ProofSyntax.orCongr (expand theory replacements equations left hl)
        (expand theory replacements equations right hr)
  | _, _, .imp left right, result, success => by
      cases hl : substConst? replacements left <;> cases hr : substConst? replacements right <;>
        simp [substConst?, hl, hr] at success
      subst result
      exact ProofSyntax.impCongr (expand theory replacements equations left hl)
        (expand theory replacements equations right hr)
  | _, _, .eq left right, result, success => by
      cases hl : substConst? replacements left <;> cases hr : substConst? replacements right <;>
        simp [substConst?, hl, hr] at success
      subst result
      exact ProofSyntax.eqCongr (expand theory replacements equations left hl)
        (expand theory replacements equations right hr)
  | _, _, .not body, result, success => by
      cases hb : substConst? replacements body <;> simp [substConst?, hb] at success
      subst result
      exact castEq rfl rfl (holeCongr (.not (.var .vz)) (expand theory replacements equations body hb))
  | _, _, .lam body, result, success => by
      cases hb : substConst? replacements body <;> simp [substConst?, hb] at success
      subst result
      exact ProofSyntax.eqLam (ProofSyntax.castIndices (assumptionsAt_cons theory _ _) rfl
        (expand theory replacements equations body hb))
  | _, _, .all body, result, success => by
      cases hb : substConst? replacements body <;> simp [substConst?, hb] at success
      subst result
      exact allCongr (ProofSyntax.castIndices (assumptionsAt_cons theory _ _) rfl
        (expand theory replacements equations body hb))
  | _, _, .ex body, result, success => by
      cases hb : substConst? replacements body <;> simp [substConst?, hb] at success
      subst result
      exact exCongr (ProofSyntax.castIndices (assumptionsAt_cons theory _ _) rfl
        (expand theory replacements equations body hb))

end Mettapedia.Logic.HOL.ConstantExpansionProofs
