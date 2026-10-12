import Mettapedia.Logic.EvidenceStateInsufficiency

/-!
# Observational and interventional quantities as count states

`P(y | x)` and `P(y | do(x))` are two `(n⁺, n⁻)` states. One call to
`Counts.revise` pools exactly one of them.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.Logic.EvidenceStateInsufficiency

/-- The two quantities, kept as separate evidence states. -/
structure QueryState where
  observational : Counts
  interventional : Counts
deriving DecidableEq, Repr

/-- Pool one observational observation into the observational state. -/
def poolObservational (state : QueryState) (observation : Bool) : QueryState where
  observational := state.observational.revise observation
  interventional := state.interventional

/-- Pool one experimental observation into the interventional state. -/
def poolInterventional (state : QueryState) (observation : Bool) : QueryState where
  observational := state.observational
  interventional := state.interventional.revise observation

theorem pool_observational_keeps_interventional (state : QueryState) (observation : Bool) :
    (poolObservational state observation).interventional = state.interventional ∧
      (poolObservational state observation).observational =
        state.observational.revise observation := by
  constructor <;> rfl

theorem pool_interventional_keeps_observational (state : QueryState) (observation : Bool) :
    (poolInterventional state observation).observational = state.observational ∧
      (poolInterventional state observation).interventional =
        state.interventional.revise observation := by
  constructor <;> rfl

/-- The canonical `(n⁺, n⁻)` state of a ratio `num / den`. -/
def countsOfRatio (num den : Nat) : Counts :=
  let g := Nat.gcd num den
  ⟨num / g, den / g - num / g⟩

end Mettapedia.GSLT.Causality.DoCalculus
