import Mettapedia.GSLT.LanguageDef.IndexedInductiveNatVec

/-!
# Named index lowering for the sequential Nat/Vec signature

This is the binding stage for the declared natural index-expression fragment,
after a parser has resolved the zero, successor and addition operations, and field names.
It consumes syntax data, not source text. Recursive fields block their names:
they must not accidentally expose a shadowed length variable to a later index.
The independent named-environment evaluator agrees with successful lowering.
Text parsing, family-name resolution and dependent type formation remain
separate stages.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.IndexedNatVecNames

open IndexedInductiveNatVec
open Mettapedia.TypeTheory.IndexedPolynomial.Description

inductive Scope : List Vectors.DataSort → Type where
  | empty : Scope []
  | bind {context} (name : String) (sort : Vectors.DataSort)
      (prior : Scope context) : Scope (sort :: context)
  | blocked {context} (name : String) (prior : Scope context) : Scope context

/-- Resolve the nearest binding, including non-length bindings that shadow it. -/
def Scope.resolve : {context : List Vectors.DataSort} → Scope context →
    String → Option (Vectors.LengthVariable context)
  | _, .empty, _ => none
  | _, .bind name sort prior, sought =>
      if name = sought then
        match sort with
        | .length => some .here
        | .payload => none
      else (prior.resolve sought).map .there
  | _, .blocked name prior, sought =>
      if name = sought then none else prior.resolve sought

/-- Named evaluation, independently traversing the value environment. -/
def Scope.read {A : Type} : {context : List Vectors.DataSort} → Scope context →
    Env (Vectors.value A) context → String → Option Natural.Carrier
  | _, .empty, _, _ => none
  | _, .bind name sort prior, environment, sought =>
      if name = sought then
        match sort with
        | .length => some environment.1
        | .payload => none
      else prior.read environment.2 sought
  | _, .blocked name prior, environment, sought =>
      if name = sought then none else prior.read environment sought

theorem Scope.resolve_sound {A : Type} {context : List Vectors.DataSort}
    (scope : Scope context) (name : String) (reference : Vectors.LengthVariable context)
    (resolved : scope.resolve name = some reference)
    (environment : Env (Vectors.value A) context) :
    scope.read environment name = some (reference.lookup environment) := by
  induction scope with
  | empty => simp [resolve] at resolved
  | bind binder sort prior ih =>
      by_cases same : binder = name
      · cases sort with
        | length =>
            simp only [resolve, same, ↓reduceIte, Option.some.injEq] at resolved
            cases resolved
            simp [read, same, Vectors.LengthVariable.lookup]
        | payload => simp [resolve, same] at resolved
      · simp only [resolve, same, ↓reduceIte] at resolved
        cases found : prior.resolve name with
        | none => simp [found] at resolved
        | some previous =>
            simp only [found, Option.map_some, Option.some.injEq] at resolved
            cases resolved
            simpa [read, same, Vectors.LengthVariable.lookup] using ih previous found environment.2
  | blocked binder prior ih =>
      by_cases same : binder = name
      · simp [resolve, same] at resolved
      · simpa [read, same] using ih reference
          (by simpa [resolve, same] using resolved) environment

/-- Named lookup succeeds exactly when scoped lookup does, with the same value. -/
theorem Scope.read_eq_map {A : Type} {context : List Vectors.DataSort}
    (scope : Scope context) (environment : Env (Vectors.value A) context) (name : String) :
    scope.read environment name = (scope.resolve name).map (fun ref => ref.lookup environment) := by
  induction scope with
  | empty => rfl
  | bind binder sort prior ih =>
      by_cases same : binder = name
      · cases sort <;> simp [read, resolve, same, Vectors.LengthVariable.lookup]
      · simpa [read, resolve, same, Option.map_map, Function.comp_def, Vectors.LengthVariable.lookup] using
          ih environment.2
  | blocked binder prior ih =>
      by_cases same : binder = name
      · simp [read, resolve, same]
      · simpa [read, resolve, same] using ih environment

inductive Index where
  | zero
  | successor (term : Index)
  | addition (left right : Index)
  | name (identifier : String)
  deriving Repr

def Index.lower {context : List Vectors.DataSort} (scope : Scope context) :
    Index → Option (Vectors.IndexExpr context)
  | .zero => some .zero
  | .successor term => (term.lower scope).map .successor
  | .addition left right => do
      let left ← left.lower scope
      let right ← right.lower scope
      pure (.addition left right)
  | .name identifier => (scope.resolve identifier).map .variable

noncomputable def Index.evaluate {A : Type} {context : List Vectors.DataSort} (scope : Scope context)
    (environment : Env (Vectors.value A) context) : Index → Option Natural.Carrier
  | .zero => some Natural.zero
  | .successor term => (term.evaluate scope environment).map Natural.succ
  | .addition left right => do
      let left ← left.evaluate scope environment
      let right ← right.evaluate scope environment
      pure (Natural.add left right)
  | .name identifier => scope.read environment identifier

theorem Index.lower_sound {A : Type} {context : List Vectors.DataSort}
    (scope : Scope context) (source : Index) (target : Vectors.IndexExpr context)
    (lowered : source.lower scope = some target)
    (environment : Env (Vectors.value A) context) :
    source.evaluate scope environment = some (target.eval environment) := by
  induction source generalizing target with
  | zero =>
      simp only [lower, Option.some.injEq] at lowered
      cases lowered
      rfl
  | successor source ih =>
      cases found : source.lower scope with
      | none => simp [lower, found] at lowered
      | some body =>
          simp only [lower, found, Option.map_some, Option.some.injEq] at lowered
          cases lowered
          simp [evaluate, ih body found, Vectors.IndexExpr.eval]
  | name identifier =>
      cases found : scope.resolve identifier with
      | none => simp [lower, found] at lowered
      | some reference =>
          simp only [lower, found, Option.map_some, Option.some.injEq] at lowered
          cases lowered
          exact scope.resolve_sound identifier reference found environment
  | addition left right ihLeft ihRight =>
      cases leftFound : left.lower scope with
      | none => simp [lower, leftFound] at lowered
      | some leftTerm =>
          cases rightFound : right.lower scope with
          | none => simp [lower, leftFound, rightFound] at lowered
          | some rightTerm =>
              simp [lower, leftFound, rightFound] at lowered
              cases lowered
              simp [evaluate, ihLeft leftTerm leftFound, ihRight rightTerm rightFound,
                Vectors.IndexExpr.eval]

/-- Lowering and the independent named evaluator agree on failures as well as values. -/
theorem Index.evaluate_eq_map {A : Type} {context : List Vectors.DataSort}
    (scope : Scope context) (source : Index) (environment : Env (Vectors.value A) context) :
    source.evaluate scope environment =
      (source.lower scope).map (fun term => term.eval environment) := by
  induction source with
  | zero => rfl
  | name identifier =>
      simpa [lower, evaluate, Option.map_map, Function.comp_def, Vectors.IndexExpr.eval] using
        scope.read_eq_map environment identifier
  | successor source ih =>
      simp [lower, evaluate, ih, Option.map_map, Function.comp_def, Vectors.IndexExpr.eval]
  | addition left right ihLeft ihRight =>
      cases leftFound : left.lower scope <;> cases rightFound : right.lower scope <;>
        simp [lower, evaluate, ihLeft, ihRight, leftFound, rightFound, Vectors.IndexExpr.eval]

theorem Index.lower_complete {A : Type} {context : List Vectors.DataSort}
    (scope : Scope context) (source : Index) (environment : Env (Vectors.value A) context)
    (value : Natural.Carrier) (evaluates : source.evaluate scope environment = some value) :
    ∃ target, source.lower scope = some target ∧ target.eval environment = value := by
  rw [source.evaluate_eq_map scope environment] at evaluates
  exact Option.map_eq_some_iff.mp evaluates

/-- Field names survive in this source; lowering scopes indices and preserves
the ordered data/recursive telescope for existing admission. -/
inductive ConstructorBody where
  | result (index : Index)
  | data (name : String) (sort : Vectors.DataSort) (rest : ConstructorBody)
  | recursive (name : String) (index : Index) (rest : ConstructorBody)

def ConstructorBody.lower (A : Type) : {context : List Vectors.DataSort} →
    Scope context → ConstructorBody → Option (IndexedInductive.RawCode (Vectors.interface A) context)
  | _, scope, .result index => (index.lower scope).map .result
  | _, scope, .data name sort rest =>
      (rest.lower A (.bind name sort scope)).map (.data sort)
  | _, scope, .recursive name index rest => do
      let index ← index.lower scope
      let rest ← rest.lower A (.blocked name scope)
      pure (.recursive index rest)

/-- Executable scope checking depends on index syntax, not on evaluation in
the semantic natural carrier. The comparison below connects it to lowering. -/
def ConstructorBody.wellScoped : {context : List Vectors.DataSort} →
    Scope context → ConstructorBody → Bool
  | _, scope, .result index => (index.lower scope).isSome
  | _, scope, .data name sort rest => rest.wellScoped (.bind name sort scope)
  | _, scope, .recursive name index rest =>
      (index.lower scope).isSome && rest.wellScoped (.blocked name scope)

theorem ConstructorBody.wellScoped_eq (A : Type) {context : List Vectors.DataSort}
    (scope : Scope context) (source : ConstructorBody) :
    source.wellScoped scope = (source.lower A scope).isSome := by
  induction source generalizing context with
  | result index => cases found : index.lower scope <;> simp [wellScoped, lower, found] <;> rfl
  | data name sort rest ih =>
      rw [wellScoped, ih]
      cases found : rest.lower A (.bind name sort scope) <;> simp [lower, found] <;> rfl
  | recursive name index rest ih =>
      rw [wellScoped, ih]
      cases found : index.lower scope <;>
        cases tail : rest.lower A (.blocked name scope) <;> simp [lower, found, tail]

structure Constructor where
  name : String
  body : ConstructorBody

def Constructor.lower (A : Type) (source : Constructor) :
    Option (IndexedInductive.RawConstructor (Vectors.interface A) []) :=
  (source.body.lower A .empty).map fun body => ⟨source.name, body⟩

noncomputable def admit? (A : Type) (source : List Constructor) :
    Option (IndexedInductive.Admitted (Vectors.interface A) []) := do
  let rows ← source.mapM (Constructor.lower A)
  IndexedInductive.admitList? rows

def vectorSource (lengthName payloadName tailName : String) : List Constructor :=
  [⟨"Nil", .result .zero⟩,
   ⟨"Cons", .data lengthName .length (.data payloadName .payload
     (.recursive tailName (.name lengthName)
       (.result (.successor (.name lengthName)))))⟩]

theorem vector_source_admitted (A : Type) :
    admit? A (vectorSource "n" "a" "xs") = some (Vectors.admitted A) := by
  rfl

theorem alpha_renamed_source (A : Type) :
    admit? A (vectorSource "length" "element" "tail") = some (Vectors.admitted A) := by
  rfl

theorem payload_cannot_be_index (A : Type) :
    admit? A (vectorSource "n" "n" "xs") = none := rfl

theorem recursive_field_cannot_reveal_shadowed_index (A : Type) :
    admit? A (vectorSource "n" "a" "n") = none := rfl

theorem unknown_index_rejected (A : Type) :
    admit? A [⟨"Bad", .result (.name "missing")⟩] = none := rfl

theorem changed_index_has_different_meaning :
    Index.evaluate (A := Bool) .empty PUnit.unit (.successor .zero) ≠
      Index.evaluate (A := Bool) .empty PUnit.unit .zero := by
  simpa [Index.evaluate] using Natural.succ_ne_zero Natural.zero

/-- The append result index uses the admitted addition operation. Host addition
appears only after applying the independently proved representation. -/
theorem named_addition_representation (n m : Natural.Carrier) :
    (Index.evaluate (A := Bool)
      (.bind "m" .length (.bind "n" .length .empty))
      (m, (n, PUnit.unit)) (.addition (.name "n") (.name "m"))).map Natural.toNat =
        some (Natural.toNat n + Natural.toNat m) := by
  simp [Index.evaluate, Scope.read, Natural.toNat_add]

end Mettapedia.GSLT.LanguageDef.ModuleSource.IndexedNatVecNames
