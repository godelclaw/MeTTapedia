import Mettapedia.Computability.PNP.PNPv13SwitchingHistoryConcretePrefix

/-!
# PNP v13 fielded switching instantiation

Recursive switching obligations whose steps carry externally supplied history fields.
-/

namespace Mettapedia.Computability.PNP

open scoped BigOperators

universe u

/-- A switched coordinate together with the fixed history field relative to
which its cellwise half-success obligation is to be checked. -/
structure V13FieldedStep (Ω : Type u) where
  field : V13HistoryField Ω
  step : V13SwitchedStep Ω

/-- A switched coordinate paired with the forbidden success-revealing fixed
field.  This is a reusable negative test case for v13 instantiation attempts:
on any positive-mass success prefix, the fielded certificate must fail. -/
def v13SuccessFieldedStep {Ω : Type u} (step : V13SwitchedStep Ω) :
    V13FieldedStep Ω where
  field := v13SuccessHistoryField step
  step := step

/-- The success-event history induced by an ordered list of fixed-field
switched coordinates. -/
def v13FieldedSuccessEvents {Ω : Type u} :
    List (V13FieldedStep Ω) → List (FiniteEvent Ω)
  | [] => []
  | item :: rest => item.step.successEvent :: v13FieldedSuccessEvents rest

@[simp] theorem v13FieldedSuccessEvents_length {Ω : Type u}
    (items : List (V13FieldedStep Ω)) :
    (v13FieldedSuccessEvents items).length = items.length := by
  induction items with
  | nil =>
      rfl
  | cons item rest ih =>
      simp [v13FieldedSuccessEvents, ih]

/-- Recursive fixed-field v13 instantiation from an existing success history:
every next coordinate has a cellwise half-success certificate for its externally
specified history field. -/
def V13FieldSwitchingInstantiatedFrom {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) : List (V13FieldedStep Ω) → Prop
  | [] => True
  | item :: rest =>
      V13FieldPrefixInstantiation item.field hist item.step ∧
        V13FieldSwitchingInstantiatedFrom (hist ++ [item.step.successEvent]) rest

/-- Recursive fixed-field v13 instantiation from the empty success history. -/
def V13FieldSwitchingInstantiated {Ω : Type u} [Fintype Ω]
    (items : List (V13FieldedStep Ω)) : Prop :=
  V13FieldSwitchingInstantiatedFrom ([] : List (FiniteEvent Ω)) items

/-- The residual fixed-field obligation after decomposition automaticity: for
each ordered fielded step, every cell of the supplied field must satisfy the
cellwise half-success inequality relative to the current success prefix. -/
def V13FieldSwitchingCellHalfFrom {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) : List (V13FieldedStep Ω) → Prop
  | [] => True
  | item :: rest =>
      (∀ cell,
        2 * v13ConcreteSuccessCount (Ω := Ω) hist item.step item.field.cellOf cell ≤
          v13ConcretePrefixCount (Ω := Ω) hist item.field.cellOf cell) ∧
        V13FieldSwitchingCellHalfFrom (hist ++ [item.step.successEvent]) rest

/-- Empty-history form of the residual fixed-field cell-half obligation. -/
def V13FieldSwitchingCellHalf {Ω : Type u} [Fintype Ω]
    (items : List (V13FieldedStep Ω)) : Prop :=
  V13FieldSwitchingCellHalfFrom ([] : List (FiniteEvent Ω)) items

end Mettapedia.Computability.PNP
