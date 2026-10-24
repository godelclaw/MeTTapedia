import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralWeakHeadSearch

/-! # Positive and separating controls for bounded structural conversion search -/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.StructuralWeakHeadSearch.Controls
open StructuralConversionCode

def decoder : RootDecoder (RootComputation.empty (Head := Nat)) := .ofEmpty _ rfl

def searchRoot {n : Nat} (_ : Tm Nat n) : Option (decoder.Code n) := none

def source : Tm Nat 2 := .app (.lam (.var 0)) (.var 0)
def nestedSource : Tm Nat 0 := .lam (.app (.lam (.var 0)) (.var 0))

def betaRecipe : Code Nat decoder.Code 2 :=
  (compare decoder searchRoot (headEq := Eq) 16 source (.var 0)).getD (.refl source)

theorem beta_checked : compare decoder searchRoot (headEq := Eq) 16 source (.var 0) =
    some betaRecipe := by rfl

theorem beta_converts : Conv (Eq : Nat → Nat → Prop) source (.var 0) RootComputation.empty :=
  compare_sound decoder searchRoot 16 beta_checked

theorem binder_checked :
    (compare decoder searchRoot (headEq := Eq) 16 nestedSource (.lam (.var 0))).isSome = true := by
  decide +kernel

theorem projection_checked :
    (compare decoder searchRoot (headEq := Eq) 16
      (.fst (.pair (.var 0) (.var 1)) : Tm Nat 2) (.var 0)).isSome = true := by
  decide +kernel

/-- The leading beta receipt must survive the subsequent Sigma comparison. -/
def structuredSource : Tm Nat 0 :=
  .app (.lam (.sigma (.head 0) (.app (.lam (.var 0)) (.head 0)))) (.head 0)

theorem structured_prefix_checked :
    (compare decoder searchRoot (headEq := Eq) 16 structuredSource
      (.sigma (.head 0) (.head 0))).isSome = true := by decide +kernel

/-- The reduction of a Pi domain must remain in the enclosing receipt. -/
theorem pi_domain_checked :
    (compare decoder searchRoot (headEq := Eq) 16
      (.pi structuredSource (.head 0))
      (.pi (.sigma (.head 0) (.head 0)) (.head 0))).isSome = true := by decide +kernel

/-- The proposed target is checked; an unrelated variable is refused. -/
theorem changed_result_refused :
    (compare decoder searchRoot (headEq := Eq) 16 source (.var 1)).isSome = false := by
  decide +kernel

/-- Producer failure at zero fuel can coexist with an explicit conversion. -/
theorem zero_fuel_refuses_convertible :
    compare decoder searchRoot (headEq := Eq) 0 source (.var 0) = none ∧
      Conv (Eq : Nat → Nat → Prop) source (.var 0) RootComputation.empty :=
  ⟨by rfl, beta_converts⟩

#print axioms beta_converts
#print axioms zero_fuel_refuses_convertible
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.StructuralWeakHeadSearch.Controls
