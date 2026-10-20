import Mettapedia.GSLT.LanguageDef.IndexedInductiveGuest
import Mettapedia.GSLT.LanguageDef.IndexedInductiveExamples

/-!
# Indexed and mutual guest schema controls

These instances interpret the actual admitted vector and tagged mutual source
inventories. Open index syntax commutes with substitution and, on quoted data,
agrees with the source index evaluation. Kernel-evaluated replay controls keep
indices, ordered payload fields, all methods and constructor origins visible.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.Controls

open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open IndexedInductiveExamples

def numeral {n : Nat} : Nat → Tm Unit n
  | 0 => .const `zero
  | k + 1 => .app (.const `succ) (numeral k)

theorem numeral_substitute {n m : Nat} (substitution : Sub Unit n m) (k : Nat) :
    subst substitution (numeral k) = numeral k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [numeral, subst, ih]

def boolean {n : Nat} (value : Bool) : Tm Unit n :=
  if value then .const `true else .const `false

theorem boolean_substitute {n m : Nat} (substitution : Sub Unit n m) (value : Bool) :
    subst substitution (boolean value) = boolean value := by cases value <;> rfl

namespace Vector

def lookup {n : Nat} : {context : List Vectors.DataSort} →
    Vectors.NatVariable context → TermEnv Vectors.interface Unit n context → Tm Unit n
  | _, .here, environment => environment.1
  | _, .there reference, environment => lookup reference environment.2

theorem lookup_substitute {n m : Nat} (substitution : Sub Unit n m)
    {context : List Vectors.DataSort} (reference : Vectors.NatVariable context)
    (environment : TermEnv Vectors.interface Unit n context) :
    subst substitution (lookup reference environment) =
      lookup reference (mapEnv (subst substitution) environment) := by
  induction reference with
  | here => rfl
  | there reference ih => exact ih environment.2

def term {n : Nat} {context : List Vectors.DataSort} :
    Vectors.IndexExpr context → TermEnv Vectors.interface Unit n context → Tm Unit n
  | .literal k, _ => numeral k
  | .variable reference, environment => lookup reference environment
  | .successor expression, environment => .app (.const `succ) (term expression environment)

def indexSyntax : IndexSyntax Vectors.interface Unit where
  term := term
  substitute := by
    intro context n m expression environment substitution
    induction expression with
    | literal k => exact numeral_substitute substitution k
    | «variable» reference => exact lookup_substitute substitution reference environment
    | successor expression ih => simp only [term, subst, ih]

def quoteEnvironment {n : Nat} : {context : List Vectors.DataSort} →
    Env Vectors.value context → TermEnv Vectors.interface Unit n context
  | [], _ => PUnit.unit
  | .length :: _, environment => (numeral environment.1, quoteEnvironment environment.2)
  | .payload :: _, environment => (boolean environment.1, quoteEnvironment environment.2)

theorem lookup_quote {n : Nat} {context : List Vectors.DataSort}
    (reference : Vectors.NatVariable context) (environment : Env Vectors.value context) :
    lookup (n := n) reference (quoteEnvironment environment) = numeral (reference.lookup environment) := by
  induction reference with
  | here => rfl
  | @there context sort reference ih =>
      cases sort <;> exact ih environment.2

/-- Index syntax computes the source index meaning on every data environment. -/
theorem term_quote {n : Nat} {context : List Vectors.DataSort}
    (expression : Vectors.IndexExpr context) (environment : Env Vectors.value context) :
    term (n := n) expression (quoteEnvironment environment) = numeral (expression.eval environment) := by
  induction expression with
  | literal => rfl
  | «variable» reference => exact lookup_quote reference environment
  | successor expression ih => simp only [term, Vectors.IndexExpr.eval, numeral, ih]

def quoteData {n : Nat} : ∀ sort, Vectors.value sort → Tm Unit n
  | .length, value => numeral value
  | .payload, value => boolean value

theorem quoteEnv_agrees {n : Nat} {context : List Vectors.DataSort}
    (environment : Env Vectors.value context) :
    quoteEnv (I := Vectors.interface) (n := n) quoteData environment = quoteEnvironment environment := by
  induction context with
  | nil => rfl
  | cons sort rest ih =>
      cases sort <;>
        exact congrArg (Prod.mk _) (ih environment.2)

theorem indexCompatibility {n : Nat} {context : List Vectors.DataSort}
    (expression : Vectors.IndexExpr context) (environment : Env Vectors.value context) :
    indexSyntax.term (n := n) expression (quoteEnv quoteData environment) =
      numeral (Vectors.interface.evalIndex expression environment) := by
  rw [quoteEnv_agrees]
  exact term_quote expression environment

/-- The admitted vector source's index constraint survives guest schema
generation for every source constructor argument tuple, not only the controls. -/
theorem source_index_retained {n : Nat} {family : Nat → Type}
    (quoteChild : ∀ index, family index → Tm Unit n) {context : List Vectors.DataSort}
    (code : Code Vectors.interface context) {environment : Env Vectors.value context} {index : Nat}
    (arguments : Arguments family code environment index) :
    resultIndex indexSyntax code (quoteEnv quoteData environment)
      (sourceArguments quoteData quoteChild code arguments) = numeral index :=
  resultIndex_sourceArguments indexSyntax quoteData quoteChild numeral
    indexCompatibility code arguments

theorem source_children_retained {n : Nat} {family : Nat → Type}
    (quoteChild : ∀ index, family index → Tm Unit n) {context : List Vectors.DataSort}
    (code : Code Vectors.interface context) {environment : Env Vectors.value context} {index : Nat}
    (arguments : Arguments family code environment index) :
    recursiveArguments indexSyntax code (quoteEnv quoteData environment)
        (sourceArguments quoteData quoteChild code arguments) =
      sourceRecursiveArguments quoteChild numeral code arguments :=
  recursiveArguments_sourceArguments indexSyntax quoteData quoteChild numeral
    indexCompatibility code arguments

def schemaTable := table indexSyntax Vectors.admitted `vecRec

def nilReceipt : SchemaTableConversionCode.Code Unit 0 :=
  ⟨0, [.const `consCase, .const `nilCase, .const `P]⟩

def consReceipt : SchemaTableConversionCode.Code Unit 0 :=
  ⟨1, [.const `nil, boolean true, numeral 0,
    .const `consCase, .const `nilCase, .const `P]⟩

def methods : List (Tm Unit 0) := [.const `nilCase, .const `consCase]

def nilLeft : Tm Unit 0 := recursor `vecRec (.const `P) methods (numeral 0) (.const `nil)

def consLeft : Tm Unit 0 := recursor `vecRec (.const `P) methods (numeral 1)
  (Declaration.IndexedFamily.applyArgs (.const `cons) [numeral 0, boolean true, .const `nil])

def consRight : Tm Unit 0 := Declaration.IndexedFamily.applyArgs (.const `consCase)
  [numeral 0, boolean true, .const `nil, nilLeft]

/-- The dependent tail is newer than its length, which is newer than the
methods and motive. These are de Bruijn slots, not source-field ordinals. -/
theorem cons_telescope_slots :
    (fieldSlot Vectors.admitted ⟨1, by decide⟩ ⟨0, by decide⟩).val = 2 ∧
    (fieldSlot Vectors.admitted ⟨1, by decide⟩ ⟨1, by decide⟩).val = 1 ∧
    (fieldSlot Vectors.admitted ⟨1, by decide⟩ ⟨2, by decide⟩).val = 0 ∧
    (methodSlot Vectors.admitted ⟨1, by decide⟩ ⟨0, by decide⟩).val = 4 ∧
    (methodSlot Vectors.admitted ⟨1, by decide⟩ ⟨1, by decide⟩).val = 3 ∧
    (motiveSlot Vectors.admitted ⟨1, by decide⟩).val = 5 := by decide

theorem complete_inventory : schemaTable.length = 2 := rfl

theorem nil_replay : SchemaTableConversionCode.decode schemaTable (fun _ => true) nilReceipt =
    some (nilLeft, .const `nilCase) := by decide

theorem cons_replay : SchemaTableConversionCode.decode schemaTable (fun _ => true) consReceipt =
    some (consLeft, consRight) := by decide

/-- A child's index is its original length, not the constructor's result length. -/
theorem changed_recursive_index_rejected :
    SchemaTableConversionCode.decode schemaTable (fun _ => true) consReceipt ≠
      some (consLeft, Declaration.IndexedFamily.applyArgs (.const `consCase)
        [numeral 0, boolean true, .const `nil,
          recursor `vecRec (.const `P) methods (numeral 1) (.const `nil)]) := by decide

theorem changed_payload_rejected :
    SchemaTableConversionCode.decode schemaTable (fun _ => true) consReceipt ≠
      some (consLeft, Declaration.IndexedFamily.applyArgs (.const `consCase)
        [numeral 0, boolean false, .const `nil, nilLeft]) := by decide

theorem obsolete_source_order_is_not_canonical :
    SchemaTableConversionCode.decode schemaTable (fun _ => true)
      ⟨1, [numeral 0, boolean true, .const `nil, .const `P, .const `nilCase, .const `consCase]⟩ ≠
        some (consLeft, consRight) := by decide

theorem missing_field_rejected :
    SchemaTableConversionCode.decode (n := 0) schemaTable (fun _ => true)
      ⟨1, [numeral 0, .const `nil, .const `P, .const `nilCase, .const `consCase]⟩ = none := by decide

theorem extra_constructor_rejected :
    SchemaTableConversionCode.decode (n := 0) schemaTable (fun _ => true) ⟨2, []⟩ = none := by decide

theorem policy_refusal :
    SchemaTableConversionCode.decode schemaTable (fun _ => false) consReceipt = none := by decide

theorem cons_unfold : Unfold indexSyntax Vectors.admitted `vecRec consLeft consRight :=
  (decode_iff_unfold indexSyntax Vectors.admitted `vecRec consLeft consRight).mp
    ⟨consReceipt, cons_replay⟩

end Vector

namespace Mutual

def indexSyntax : IndexSyntax IndexedInductiveExamples.Mutual.interface Unit where
  term := fun index _ => boolean index
  substitute := fun index _ substitution => boolean_substitute substitution index

/-- Tags remain the actual source family indices. -/
theorem term_quote {n : Nat} (tag : Bool) :
    indexSyntax.term (n := n) (context := []) tag PUnit.unit = boolean tag := rfl

def schemaTable := table indexSyntax IndexedInductiveExamples.Mutual.admitted `parityRec

def methods : List (Tm Unit 0) := [.const `zeroCase, .const `oddCase, .const `evenCase]

def oddReceipt : SchemaTableConversionCode.Code Unit 0 :=
  ⟨1, [.const `zero, .const `evenCase, .const `oddCase, .const `zeroCase, .const `P]⟩

def oddLeft : Tm Unit 0 := recursor `parityRec (.const `P) methods (boolean true)
  (.app (.const `odd) (.const `zero))

def oddRight : Tm Unit 0 := Declaration.IndexedFamily.applyArgs (.const `oddCase)
  [.const `zero, recursor `parityRec (.const `P) methods (boolean false) (.const `zero)]

theorem complete_inventory : schemaTable.length = 3 := rfl

theorem cross_family_replay :
    SchemaTableConversionCode.decode schemaTable (fun _ => true) oddReceipt = some (oddLeft, oddRight) := by
  decide

theorem wrong_child_family_rejected :
    SchemaTableConversionCode.decode schemaTable (fun _ => true) oddReceipt ≠
      some (oddLeft, Declaration.IndexedFamily.applyArgs (.const `oddCase)
        [.const `zero, recursor `parityRec (.const `P) methods (boolean true) (.const `zero)]) := by decide

theorem cross_family_unfold :
    Unfold indexSyntax IndexedInductiveExamples.Mutual.admitted `parityRec oddLeft oddRight :=
  (decode_iff_unfold indexSyntax IndexedInductiveExamples.Mutual.admitted `parityRec oddLeft oddRight).mp
    ⟨oddReceipt, cross_family_replay⟩

end Mutual

#print axioms Vector.term_quote
#print axioms Vector.source_index_retained
#print axioms Vector.source_children_retained
#print axioms Vector.cons_unfold
#print axioms Vector.changed_recursive_index_rejected
#print axioms Mutual.cross_family_unfold
#print axioms Mutual.wrong_child_family_rejected

end Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.Controls
