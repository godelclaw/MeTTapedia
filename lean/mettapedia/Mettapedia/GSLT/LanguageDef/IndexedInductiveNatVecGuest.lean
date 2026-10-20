import Mettapedia.GSLT.LanguageDef.IndexedInductiveGuest
import Mettapedia.GSLT.LanguageDef.ModuleSource.IndexedNatVecNames

/-!
# Guest index syntax for the authored Nat/Vec declarations

The natural carrier is the admitted source family. Its zero, successor and
addition are represented by named guest operations. Index compilation is
capture-safe under guest substitution. An independent evaluator of this guest
index fragment agrees with the source evaluator, including addition.

This semantic comparison does not identify an `Add` application with a numeral
by raw syntax, and it grants no guest conversion authority. Formation and the
declared computation rules for arithmetic remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductiveNatVecGuest

open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open IndexedInductiveNatVec IndexedInductive.Guest

def naturalLiteral {n : Nat} : Nat → Tm Unit n
  | 0 => .const `Zero
  | k + 1 => .app (.const `Succ) (naturalLiteral k)

/-- This interpretation recognizes only the declared natural index operations.
Other guest syntax remains uninterpreted. -/
noncomputable def evaluate : Tm Unit 0 → Option Natural.Carrier
  | .const name => if name = `Zero then some Natural.zero else none
  | .app (.const name) argument =>
      if name = `Succ then (evaluate argument).map Natural.succ else none
  | .app (.app (.const name) left) right =>
      if name = `Add then do
        let left ← evaluate left
        let right ← evaluate right
        pure (Natural.add left right)
      else none
  | _ => none

theorem evaluate_literal (k : Nat) : evaluate (naturalLiteral k) = some (Natural.fromNat k) := by
  induction k with
  | zero => simp [naturalLiteral, evaluate, Natural.fromNat]
  | succ k ih => simp [naturalLiteral, evaluate, ih, Natural.fromNat]

noncomputable def quoteNatural {n : Nat} (value : Natural.Carrier) : Tm Unit n :=
  naturalLiteral (Natural.toNat value)

theorem evaluate_quoteNatural (value : Natural.Carrier) :
    evaluate (quoteNatural value) = some value := by
  rw [quoteNatural, evaluate_literal, Natural.fromNat_toNat]

def lookup {A : Type} {n : Nat} : {context : List Vectors.DataSort} →
    Vectors.LengthVariable context → TermEnv (Vectors.interface A) Unit n context → Tm Unit n
  | _, .here, environment => environment.1
  | _, .there reference, environment => lookup reference environment.2

theorem lookup_substitute {A : Type} {n m : Nat} (substitution : Sub Unit n m)
    {context : List Vectors.DataSort} (reference : Vectors.LengthVariable context)
    (environment : TermEnv (Vectors.interface A) Unit n context) :
    subst substitution (lookup reference environment) =
      lookup reference (mapEnv (subst substitution) environment) := by
  induction reference with
  | here => rfl
  | there reference ih => exact ih environment.2

def term {A : Type} {n : Nat} {context : List Vectors.DataSort} :
    Vectors.IndexExpr context → TermEnv (Vectors.interface A) Unit n context → Tm Unit n
  | .zero, _ => .const `Zero
  | .variable reference, environment => lookup reference environment
  | .successor expression, environment => .app (.const `Succ) (term expression environment)
  | .addition left right, environment =>
      .app (.app (.const `Add) (term left environment)) (term right environment)

def indexSyntax (A : Type) : IndexSyntax (Vectors.interface A) Unit where
  term := term
  substitute := by
    intro context n m expression environment substitution
    induction expression with
    | zero => rfl
    | «variable» reference => exact lookup_substitute substitution reference environment
    | successor expression ih => simp only [term, subst, ih]
    | addition left right ihLeft ihRight => simp only [term, subst, ihLeft, ihRight]

noncomputable def quoteData {A : Type} (payload : A → Tm Unit 0) :
    ∀ sort, Vectors.value A sort → Tm Unit 0
  | .length, value => quoteNatural value
  | .payload, value => payload value

theorem lookup_evaluate {A : Type} (payload : A → Tm Unit 0)
    {context : List Vectors.DataSort} (reference : Vectors.LengthVariable context)
    (environment : Env (Vectors.value A) context) :
    evaluate (lookup reference (quoteEnv (quoteData payload) environment)) =
      some (reference.lookup environment) := by
  induction reference with
  | here => exact evaluate_quoteNatural environment.1
  | @there context sort reference ih =>
      cases sort <;> exact ih environment.2

/-- The concrete guest index interpretation agrees with the authored natural
operations for every expression and source data environment. -/
theorem evaluate_term {A : Type} (payload : A → Tm Unit 0)
    {context : List Vectors.DataSort} (expression : Vectors.IndexExpr context)
    (environment : Env (Vectors.value A) context) :
    evaluate (term expression (quoteEnv (quoteData payload) environment)) =
      some (expression.eval environment) := by
  induction expression with
  | zero => simp [term, evaluate, Vectors.IndexExpr.eval]
  | «variable» reference => exact lookup_evaluate payload reference environment
  | successor expression ih => simp [term, evaluate, ih, Vectors.IndexExpr.eval]
  | addition left right ihLeft ihRight =>
      simp [term, evaluate, ihLeft, ihRight, Vectors.IndexExpr.eval]

/-- Guest result-index meaning agrees with the actual authored polynomial
fibre, including constructors whose result uses the admitted addition. -/
theorem source_index_meaning {A : Type} (payload : A → Tm Unit 0)
    {family : Natural.Carrier → Type}
    (quoteChild : ∀ index, family index → Tm Unit 0)
    {context : List Vectors.DataSort} (code : Code (Vectors.interface A) context)
    {environment : Env (Vectors.value A) context} {index : Natural.Carrier}
    (arguments : Arguments family code environment index) :
    evaluate (resultIndex (indexSyntax A) code (quoteEnv (quoteData payload) environment)
      (sourceArguments (quoteData payload) quoteChild code arguments)) = some index := by
  exact resultIndex_sourceMeaning (indexSyntax A) (quoteData payload) quoteChild evaluate
    (evaluate_term payload) code arguments

/-- Every recursive index has the source child's actual fibre, even when it
contains addition. The ordered child payloads are retained without decoding. -/
theorem source_children_meaning {A : Type} (payload : A → Tm Unit 0)
    {family : Natural.Carrier → Type}
    (quoteChild : ∀ index, family index → Tm Unit 0)
    {context : List Vectors.DataSort} (code : Code (Vectors.interface A) context)
    {environment : Env (Vectors.value A) context} {index : Natural.Carrier}
    (arguments : Arguments family code environment index) :
    (recursiveArguments (indexSyntax A) code (quoteEnv (quoteData payload) environment)
      (sourceArguments (quoteData payload) quoteChild code arguments)).map
        (fun pair => (evaluate pair.1, pair.2)) =
      sourceRecursiveArguments quoteChild some code arguments := by
  exact recursiveArguments_sourceMeaning (indexSyntax A) (quoteData payload) quoteChild evaluate
    (evaluate_term payload) code arguments

noncomputable def vectorTable (A : Type) := table (indexSyntax A) (Vectors.admitted A) `VecRec

def consReceipt : SchemaTableConversionCode.Code Unit 0 :=
  ⟨1, [.const `Nil, .const `element, .const `Zero,
    .const `consCase, .const `nilCase, .const `P]⟩

def methods : List (Tm Unit 0) := [.const `nilCase, .const `consCase]

def consLeft : Tm Unit 0 := recursor `VecRec (.const `P) methods
  (.app (.const `Succ) (.const `Zero))
  (Declaration.IndexedFamily.applyArgs (.const `Cons) [.const `Zero, .const `element, .const `Nil])

def consRight : Tm Unit 0 := Declaration.IndexedFamily.applyArgs (.const `consCase)
  [.const `Zero, .const `element, .const `Nil,
    recursor `VecRec (.const `P) methods (.const `Zero) (.const `Nil)]

theorem authored_cons_replay (A : Type) :
    SchemaTableConversionCode.decode (vectorTable A) (fun _ => true) consReceipt =
      some (consLeft, consRight) := by rfl

theorem authored_cons_unfold (A : Type) :
    Unfold (indexSyntax A) (Vectors.admitted A) `VecRec consLeft consRight :=
  (decode_iff_unfold (indexSyntax A) (Vectors.admitted A) `VecRec consLeft consRight).mp
    ⟨consReceipt, authored_cons_replay A⟩

namespace Named

open ModuleSource.IndexedNatVecNames

/-- Successful binding connects the independent named evaluator to guest
index meaning. Failed lookup remains failure in the composed route. -/
theorem lowering_meaning {A : Type} (payload : A → Tm Unit 0)
    {context : List Vectors.DataSort} (scope : Scope context) (source : Index)
    (environment : Env (Vectors.value A) context) :
    (source.lower scope).bind
        (fun target => evaluate (term target (quoteEnv (quoteData payload) environment))) =
      source.evaluate scope environment := by
  rw [Index.evaluate_eq_map]
  cases found : source.lower scope with
  | none => rfl
  | some target => exact evaluate_term payload target environment

noncomputable def generatedTable (A : Type) (source : List Constructor) :
    Option (AlgebraicSchema.SchemaTable Unit) :=
  (admit? A source).map (fun admitted => table (indexSyntax A) admitted `VecRec)

/-- The named source feeds admission and this same schema generator. -/
theorem vector_table (A : Type) :
    generatedTable A (vectorSource "n" "a" "xs") = some (vectorTable A) := by
  simp only [generatedTable, vector_source_admitted, Option.map_some, vectorTable]

theorem renamed_vector_table (A : Type) :
    generatedTable A (vectorSource "length" "element" "tail") = some (vectorTable A) := by
  simp only [generatedTable, alpha_renamed_source, Option.map_some, vectorTable]

theorem blocked_name_refuses_generation (A : Type) :
    generatedTable A (vectorSource "n" "a" "n") = none := by
  simp only [generatedTable, recursive_field_cannot_reveal_shadowed_index, Option.map_none]

/-- A receipt from the named admitted source replays through the same table. -/
theorem vector_cons_replay (A : Type) :
    (generatedTable A (vectorSource "n" "a" "xs")).bind
        (fun generated => SchemaTableConversionCode.decode generated (fun _ => true) consReceipt) =
      some (consLeft, consRight) := by
  rw [vector_table]
  exact authored_cons_replay A

end Named

theorem wrong_authored_child_index (A : Type) :
    SchemaTableConversionCode.decode (vectorTable A) (fun _ => true) consReceipt ≠
      some (consLeft, Declaration.IndexedFamily.applyArgs (.const `consCase)
        [.const `Zero, .const `element, .const `Nil,
          recursor `VecRec (.const `P) methods
            (.app (.const `Succ) (.const `Zero)) (.const `Nil)]) := by
  rw [authored_cons_replay]
  decide

/-- Semantic agreement is weaker than a raw-syntax equality: arithmetic
conversion still needs the declared computation route. -/
theorem addition_is_not_literal :
    term (A := Unit) (n := 0) (context := []) (.addition .zero .zero) PUnit.unit ≠
      naturalLiteral 0 := by decide

theorem addition_meaning :
    evaluate (term (A := Unit) (n := 0) (context := []) (.addition .zero .zero) PUnit.unit) =
      some Natural.zero := by simp [term, evaluate, Natural.add_zero]

#print axioms evaluate_quoteNatural
#print axioms evaluate_term
#print axioms source_index_meaning
#print axioms source_children_meaning
#print axioms authored_cons_unfold
#print axioms Named.lowering_meaning
#print axioms Named.vector_cons_replay
#print axioms addition_is_not_literal

end Mettapedia.GSLT.LanguageDef.IndexedInductiveNatVecGuest
