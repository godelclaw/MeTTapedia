import Mathlib.Logic.Relation

/-!
# Direct finite-index case analysis for compiled programs

Case analysis needs the zero branch or the immediate predecessor. This
implementation selects that branch directly, without computing the unused
induction results of the original Fin.cases implementation. The compiler
rewrite is justified for every dependent motive; logical definitions and
their kernel reduction rules remain unchanged.
-/

set_option autoImplicit false
universe u
namespace Mettapedia.Logic.FinCases

def casesDirect {n : Nat} {motive : Fin (n + 1) → Sort u}
    (zero : motive 0) (successor : ∀ index : Fin n, motive index.succ)
    (index : Fin (n + 1)) : motive index :=
  match index with
  | ⟨0, _⟩ => zero
  | ⟨value + 1, bound⟩ => successor ⟨value, Nat.lt_of_succ_lt_succ bound⟩

@[csimp] theorem cases_eq_casesDirect : @Fin.cases.{u} = @casesDirect.{u} := by
  funext n motive zero successor index
  rcases index with ⟨value, bound⟩
  cases value <;> rfl

#print axioms cases_eq_casesDirect
end Mettapedia.Logic.FinCases
