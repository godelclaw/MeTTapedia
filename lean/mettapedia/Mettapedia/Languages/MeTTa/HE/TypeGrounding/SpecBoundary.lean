import Mettapedia.Languages.MeTTa.HE.TypeGrounding.SimpleAgreement

/-!
# Where HE's specified type relation and its grounding part

Three witnesses on small declaration spaces pin the places where the
specified exact type relation (`Spec.Type.Presentation.Exact`) disagrees with
the grounded reading of HE typing.  In each the reference runtime agrees with
the grounded reading, not with the specification.

* **Gradual recovery from an ill-typed argument.**  With `(: g (-> A B))`,
  `(: f (-> B R))` and `(: b C)`, the specification assigns the ill-typed
  `(g b)` the gradual candidate `%Undefined%`, which every expected type
  accepts, so `(f (g b))` is assigned `R`.  HOL rejects `(f (g b))`, and so
  does the reference runtime, whose `get-type` returns no type for either
  expression.  This is why `hol_iff_exact` requires that no subatom falls
  back to `%Undefined%`.
* **The tuple rule is absent.**  With `(: Truth Bool)` and `(: Z Nat)`, the
  specification assigns `(Truth Z)` only `%Undefined%`; the reference runtime
  assigns the tuple type `(Bool Nat)` (`TypeGrounding.Tuples`).
* **Meta-typed parameters.**  With `(: f (-> Expression R))`,
  `(: g (-> A B))` and `(: a A)`, the specification matches the parameter
  type `Expression` structurally against the argument's type `B` and assigns
  `(f (g a))` only `%Undefined%`; the reference runtime accepts the argument
  because it is an expression, and assigns `R`.
-/

namespace Mettapedia.Languages.MeTTa.HE.TypeGrounding.SpecBoundary

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type
open Spec.Type.Presentation
open Spec.Type.Presentation.Exact

/-! ## Helpers for small concrete spaces -/

private def arrow (arguments : List Atom) (result : Atom) : Atom :=
  .expression (.symbol "->" :: (arguments ++ [result]))

/-- The declaration `(: name type)`. -/
def annotation (name : String) (type : Atom) : Atom :=
  .expression [.symbol ":", .symbol name, type]

theorem staticSymbol (name : String) (notReserved : name ∉ reservedTypeNames) :
    StaticType (.symbol name) := by
  refine .base ?_ ?_ ?_ rfl
  · rintro ⟨_, equal⟩
    cases equal
  · rintro ⟨reserved, member, equal⟩
    cases equal
    exact notReserved member
  · intro occurs
    have equal := occurs.symbol_eq
    simp only [Atom.undefinedType, Atom.symbol.injEq] at equal
    exact notReserved (by rw [← equal]; simp [reservedTypeNames])

private theorem staticUnary (argument result : String)
    (argumentNotReserved : argument ∉ reservedTypeNames)
    (resultNotReserved : result ∉ reservedTypeNames) :
    StaticType (arrow [.symbol argument] (.symbol result)) := by
  refine .arrow (argumentTypes := [.symbol argument]) (returnType := .symbol result)
    rfl (by simp) ?_ ?_ (staticSymbol result resultNotReserved)
  · intro argumentType member
    simp only [List.mem_singleton] at member
    subst member
    exact staticSymbol argument argumentNotReserved
  · rintro ⟨_, equal⟩
    cases equal

/-- The singleton candidate list of an argument whose packages are
published. -/
private theorem published_observed (types : List Atom) :
    (types.map fun type => [publishedPackage type]).map observedTypes =
      types.map fun type => [type] := by
  simp [observedTypes, publishedPackage, RuntimeTypePackage.published]

/-! ## Gradual recovery from an ill-typed argument -/

private def recoverySpace : Space :=
  Space.ofList [annotation "g" (arrow [.symbol "A"] (.symbol "B")),
    annotation "f" (arrow [.symbol "B"] (.symbol "R")),
    annotation "b" (.symbol "C")]

private def illTypedInner : Atom := .expression [.symbol "g", .symbol "b"]
private def recoveredOuter : Atom := .expression [.symbol "f", illTypedInner]

private theorem recovery_g : declaredType? recoverySpace (.symbol "g") =
    some (arrow [.symbol "A"] (.symbol "B")) := by
  decide

private theorem recovery_f : declaredType? recoverySpace (.symbol "f") =
    some (arrow [.symbol "B"] (.symbol "R")) := by
  decide

private theorem recovery_b : declaredType? recoverySpace (.symbol "b") =
    some (.symbol "C") := by
  decide

private theorem reserved_A : "A" ∉ reservedTypeNames := by decide
private theorem reserved_B : "B" ∉ reservedTypeNames := by decide
private theorem reserved_C : "C" ∉ reservedTypeNames := by decide
private theorem reserved_R : "R" ∉ reservedTypeNames := by decide

/-- The specification assigns the ill-typed `(g b)` the gradual candidate. -/
theorem spec_ill_typed_argument_is_undefined :
    ExactTypes recoverySpace illTypedInner [Atom.undefinedType] := by
  refine ⟨[publishedPackage Atom.undefinedType], ?_, rfl⟩
  apply application_packages_failure (by decide) (by decide) recovery_g rfl
    (argumentPackages := .cons (constant_packages recovery_b) .nil)
    (actualTypes := [.symbol "C"]) (published_observed [.symbol "C"]) (by simp [TypeSubst.typeVars])
  intro result success
  cases success with
  | mk shape fold =>
      have function : FunctionTypeRel (arrow [.symbol "A"] (.symbol "B"))
          [.symbol "A"] (.symbol "B") := rfl
      obtain ⟨rfl, rfl⟩ := FunctionTypeRel.unique shape function
      obtain ⟨_, accepted⟩ := argumentList_static fold
        (by simpa using staticSymbol "A" reserved_A)
        (by simpa using Or.inr (staticSymbol "C" reserved_C))
      cases accepted with
      | cons headAccepted _ =>
          rcases headAccepted with undefined | equal
          · simp [Atom.undefinedType] at undefined
          · simp at equal

/-- Through the gradual candidate the specification types `(f (g b))` as
`R`. -/
theorem spec_recovers_through_undefined :
    ExactTypes recoverySpace recoveredOuter [.symbol "R"] := by
  obtain ⟨packages, innerRel, innerObserved⟩ := spec_ill_typed_argument_is_undefined
  refine ⟨[inferredPackage [] (.symbol "R")], ?_, by simp [observedTypes, inferredPackage]⟩
  apply application_packages_success (by decide) (by decide) recovery_f
    (staticUnary "B" "R" reserved_B reserved_R) rfl
    (argumentPackages := .cons innerRel .nil)
    (actualTypes := [Atom.undefinedType]) (by simp [innerObserved])
    (by simp [TypeSubst.typeVars, Atom.undefinedType])
  exact .cons (Or.inl rfl) .nil

/-- HOL rejects `(f (g b))` at every type. -/
theorem hol_rejects_recovered_outer (type : Atom) :
    ¬HOLTyped recoverySpace recoveredOuter type := by
  intro typed
  have outer := (elaborates_application_iff (name := "f") (arguments := [illTypedInner])
    recovery_f (rfl : FunctionTypeRel (arrow [.symbol "B"] (.symbol "R"))
      [.symbol "B"] (.symbol "R")) (by simp) rfl).mp typed
  obtain ⟨_, all⟩ := outer
  cases all with
  | cons innerElaborates _ =>
      have inner := (elaborates_application_iff (name := "g") (arguments := [.symbol "b"])
        recovery_g (rfl : FunctionTypeRel (arrow [.symbol "A"] (.symbol "B"))
          [.symbol "A"] (.symbol "B")) (by simp) rfl).mp innerElaborates
      obtain ⟨_, argumentAll⟩ := inner
      cases argumentAll with
      | cons argumentElaborates _ =>
          obtain ⟨declared, lookup, holEq⟩ := elaborates_declared_iff.mp argumentElaborates
          rw [recovery_b] at lookup
          cases lookup
          have := toTy_injective (staticSymbol "A" reserved_A)
            (staticSymbol "C" reserved_C) holEq
          simp at this

/-- **The fallback condition of `hol_iff_exact` cannot be dropped.**  The
specification assigns `(f (g b))` the single candidate `R`, HOL rejects it,
and its subatom `(g b)` falls back to `%Undefined%`. -/
theorem fallback_condition_needed :
    ExactTypes recoverySpace recoveredOuter [.symbol "R"] ∧
      ¬HOLTyped recoverySpace recoveredOuter (.symbol "R") ∧
      ¬NoUndefinedFallback recoverySpace recoveredOuter :=
  ⟨spec_recovers_through_undefined, hol_rejects_recovered_outer _,
    fun noFallback => noFallback illTypedInner
      (Subatom.of_mem (by simp)) spec_ill_typed_argument_is_undefined⟩

/-! ## The tuple rule is absent from the specification -/

/-- `(: Truth Bool)` and `(: Z Nat)`. -/
def truthZSpace : Space :=
  Space.ofList [annotation "Truth" (.symbol "Bool"), annotation "Z" (.symbol "Nat")]

/-- The specification assigns `(Truth Z)` only the gradual candidate: a head
whose declared type is not an arrow contributes no application candidate. -/
theorem spec_tuple_is_undefined :
    ExactTypes truthZSpace (.expression [.symbol "Truth", .symbol "Z"])
      [Atom.undefinedType] := by
  refine ⟨[publishedPackage Atom.undefinedType], ?_, rfl⟩
  apply application_packages_failure (by decide) (by decide)
    (by decide : declaredType? truthZSpace (.symbol "Truth") = some (.symbol "Bool")) rfl
    (argumentPackages := .cons (constant_packages
      (by decide : declaredType? truthZSpace (.symbol "Z") = some (.symbol "Nat"))) .nil)
    (actualTypes := [.symbol "Nat"]) (published_observed [.symbol "Nat"])
    (by simp [TypeSubst.typeVars])
  intro result success
  cases success with
  | mk shape _ => simp at shape

/-! ## Meta-typed parameters -/

private def metaSpace : Space :=
  Space.ofList [annotation "f" (arrow [Atom.expressionType] (.symbol "R")),
    annotation "g" (arrow [.symbol "A"] (.symbol "B")),
    annotation "a" (.symbol "A")]

private theorem meta_g : declaredType? metaSpace (.symbol "g") =
    some (arrow [.symbol "A"] (.symbol "B")) := by
  decide

/-- The inner application `(g a)` has the single candidate `B`. -/
private theorem meta_inner :
    ExactTypes metaSpace (.expression [.symbol "g", .symbol "a"]) [.symbol "B"] := by
  refine ⟨[inferredPackage [] (.symbol "B")], ?_, by simp [observedTypes, inferredPackage]⟩
  apply application_packages_success (by decide) (by decide) meta_g
    (staticUnary "A" "B" reserved_A reserved_B) rfl
    (argumentPackages := .cons (constant_packages
      (by decide : declaredType? metaSpace (.symbol "a") = some (.symbol "A"))) .nil)
    (actualTypes := [.symbol "A"]) (published_observed [.symbol "A"]) (by simp [TypeSubst.typeVars])
  exact .cons (Or.inr rfl) .nil

/-- The specification matches the meta-type parameter `Expression`
structurally against the argument's type and assigns `(f (g a))` only the
gradual candidate. -/
theorem spec_meta_parameter_is_undefined :
    ExactTypes metaSpace
      (.expression [.symbol "f", .expression [.symbol "g", .symbol "a"]])
      [Atom.undefinedType] := by
  obtain ⟨packages, innerRel, innerObserved⟩ := meta_inner
  refine ⟨[publishedPackage Atom.undefinedType], ?_, rfl⟩
  apply application_packages_failure (by decide) (by decide)
    (by decide : declaredType? metaSpace (.symbol "f") =
      some (arrow [Atom.expressionType] (.symbol "R"))) rfl
    (argumentPackages := .cons innerRel .nil)
    (actualTypes := [.symbol "B"]) (by simp [innerObserved]) (by simp [TypeSubst.typeVars])
  intro result success
  cases success with
  | mk shape fold =>
      have function : FunctionTypeRel (arrow [Atom.expressionType] (.symbol "R"))
          [Atom.expressionType] (.symbol "R") := rfl
      obtain ⟨rfl, rfl⟩ := FunctionTypeRel.unique shape function
      cases fold with
      | cons head _ =>
          have reduced := head.reduced_of_nonWildcard (by decide) (by decide)
            (by decide) (by decide)
          obtain ⟨equal, _⟩ := reduced_ground_eq reduced rfl rfl
            (fun occurs => by
              have := occurs.symbol_eq
              simp [Atom.undefinedType] at this)
            (fun occurs => by
              have := occurs.symbol_eq
              simp [Atom.undefinedType] at this)
          simp [Atom.expressionType] at equal

/-! ## A typed static application -/

private def applicationSpace : Space :=
  Space.ofList [annotation "g" (arrow [.symbol "A"] (.symbol "B")),
    annotation "a" (.symbol "A")]

/-- Positive: with `(: g (-> A B))` and `(: a A)`, HOL types `(g a)` at `B`,
and HE's exact relation gives it the single candidate `B` with no
`%Undefined%` fallback. -/
theorem static_application_agrees :
    HOLTyped applicationSpace (.expression [.symbol "g", .symbol "a"]) (.symbol "B") ∧
      ExactTypes applicationSpace (.expression [.symbol "g", .symbol "a"]) [.symbol "B"] ∧
      NoUndefinedFallback applicationSpace (.expression [.symbol "g", .symbol "a"]) := by
  have declaredG : declaredType? applicationSpace (.symbol "g") =
      some (arrow [.symbol "A"] (.symbol "B")) := by
    decide
  have declaredA : declaredType? applicationSpace (.symbol "a") = some (.symbol "A") := by
    decide
  have function : FunctionTypeRel (arrow [.symbol "A"] (.symbol "B"))
      [.symbol "A"] (.symbol "B") := rfl
  have typed : HOLTyped applicationSpace (.expression [.symbol "g", .symbol "a"])
      (.symbol "B") :=
    (holTyped_iff_elaborates _ _ _).mpr
      ((elaborates_application_iff (name := "g") (arguments := [.symbol "a"]) declaredG
        function (by simp) rfl).mpr
        ⟨rfl, .cons (elaborates_declared_iff.mpr ⟨_, declaredA, rfl⟩) .nil⟩)
  have saturated : SaturatedTerm applicationSpace
      (.expression [.symbol "g", .symbol "a"]) := by
    refine .application (by decide) (by decide) declaredG
      (staticUnary "A" "B" reserved_A reserved_B) function rfl ?_
    intro argument member
    simp only [List.mem_singleton] at member
    subst member
    exact .constant declaredA (staticSymbol "A" reserved_A)
  exact ⟨typed, (hol_iff_exact saturated (staticSymbol "B" reserved_B)).mp typed⟩

#print axioms fallback_condition_needed
#print axioms spec_tuple_is_undefined
#print axioms spec_meta_parameter_is_undefined
#print axioms static_application_agrees

end Mettapedia.Languages.MeTTa.HE.TypeGrounding.SpecBoundary
