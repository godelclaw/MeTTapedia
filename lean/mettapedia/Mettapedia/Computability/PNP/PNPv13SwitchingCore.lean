import Mettapedia.Computability.PNP.PNPv13SwitchingFieldedSuffixObstructions

/-!
# PNP v13 switching: core interfaces

Unfielded and concrete recursive switching obligations over induced success histories.
-/

namespace Mettapedia.Computability.PNP

open scoped BigOperators

universe u

/-- Recursive v13 instantiation from an existing success history: every next
coordinate has an atom-ledger certificate relative to the current success
prefix. -/
def V13SwitchingInstantiatedFrom {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) : List (V13SwitchedStep Ω) → Prop
  | [] => True
  | step :: rest =>
      V13PrefixInstantiated hist step ∧
        V13SwitchingInstantiatedFrom (hist ++ [step.successEvent]) rest

/-- Recursive v13 instantiation from the empty success history. -/
def V13SwitchingInstantiated {Ω : Type u} [Fintype Ω]
    (steps : List (V13SwitchedStep Ω)) : Prop :=
  V13SwitchingInstantiatedFrom ([] : List (FiniteEvent Ω)) steps

/-- Recursive semantic v13 instantiation from an existing success history:
every next coordinate has a concrete cell-map certificate relative to the
current success prefix. -/
def V13ConcreteSwitchingInstantiatedFrom {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) : List (V13SwitchedStep Ω) → Prop
  | [] => True
  | step :: rest =>
      V13ConcretePrefixInstantiated hist step ∧
        V13ConcreteSwitchingInstantiatedFrom (hist ++ [step.successEvent]) rest

/-- Recursive semantic v13 instantiation from the empty success history. -/
def V13ConcreteSwitchingInstantiated {Ω : Type u} [Fintype Ω]
    (steps : List (V13SwitchedStep Ω)) : Prop :=
  V13ConcreteSwitchingInstantiatedFrom ([] : List (FiniteEvent Ω)) steps

end Mettapedia.Computability.PNP
