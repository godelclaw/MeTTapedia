import Mettapedia.OSLF.Syntax.BindingWireBinary
import Mettapedia.Languages.OpenTheory.StorageSize
import Mettapedia.Languages.OpenTheory.Definitions
import Mettapedia.Computability.WordTemplateMachine

/-!
# Executable storage of shared simple-type syntax

Binary numeric fields and UTF-8 names retain full structural syntax, including
symbol provenance. Checked terms are decoded through their original type
checks, and theorem dependencies retain their Booleanity validation. Finite
sets have a deterministic structural ordering.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OpenTheory.SyntaxEncoding

open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.Binding.WireCodec.Binary

/-- Namespace components and the final component remain separate strings. -/
def nameCodec : Codec Name :=
  (Codec.prod (Codec.list Codec.string) Codec.string).mapped
    (fun value => (value.namespaceComponents, value.component))
    (fun value => some ⟨value.1, value.2⟩) (fun _ => rfl)

mutual
  def putTy : Ty → Data
    | .var value => .pair (.atom 0) (nameCodec.put value)
    | .op operator arguments => .pair (.atom 1) (.pair (putTypeOp operator) (putTys arguments))
  def putTys : List Ty → Data
    | [] => .atom 0
    | value :: values => .pair (putTy value) (putTys values)
  def putTypeOp : TypeOp → Data
    | .mk value provenance => .pair (nameCodec.put value) (putTypeOpProvenance provenance)
  def putTypeOpProvenance : TypeOpProvenance → Data
    | .undefined => .atom 0
    | .defined predicate parameters => .pair (.atom 1)
        (.pair (putSourceTerm predicate) ((Codec.list nameCodec).put parameters))
  def putConst : Const → Data
    | .mk value provenance => .pair (nameCodec.put value) (putConstProvenance provenance)
  def putConstProvenance : ConstProvenance → Data
    | .undefined => .atom 0
    | .defined definition => .pair (.atom 1) (putSourceTerm definition)
    | .abstraction operator => .pair (.atom 2) (putTypeOp operator)
    | .representation operator => .pair (.atom 3) (putTypeOp operator)
  def putSourceTerm : SourceTerm → Data
    | .const symbol annotation => .pair (.atom 0) (.pair (putConst symbol) (putTy annotation))
    | .var value annotation => .pair (.atom 1) (.pair (nameCodec.put value) (putTy annotation))
    | .app function argument => .pair (.atom 2) (.pair (putSourceTerm function) (putSourceTerm argument))
    | .abs binder domain body => .pair (.atom 3)
        (.pair (nameCodec.put binder) (.pair (putTy domain) (putSourceTerm body)))
end

mutual
  def getTy : Data → Option Ty
    | .pair (.atom 0) value => (nameCodec.get value).map Ty.var
    | .pair (.atom 1) (.pair operator arguments) => do
        return .op (← getTypeOp operator) (← getTys arguments)
    | _ => none
  def getTys : Data → Option (List Ty)
    | .atom 0 => some []
    | .pair value values => do return (← getTy value) :: (← getTys values)
    | _ => none
  def getTypeOp : Data → Option TypeOp
    | .pair value provenance => do return .mk (← nameCodec.get value) (← getTypeOpProvenance provenance)
    | _ => none
  def getTypeOpProvenance : Data → Option TypeOpProvenance
    | .atom 0 => some .undefined
    | .pair (.atom 1) (.pair predicate parameters) => do
        return .defined (← getSourceTerm predicate) (← (Codec.list nameCodec).get parameters)
    | _ => none
  def getConst : Data → Option Const
    | .pair value provenance => do return .mk (← nameCodec.get value) (← getConstProvenance provenance)
    | _ => none
  def getConstProvenance : Data → Option ConstProvenance
    | .atom 0 => some .undefined
    | .pair (.atom 1) definition => (getSourceTerm definition).map ConstProvenance.defined
    | .pair (.atom 2) operator => (getTypeOp operator).map ConstProvenance.abstraction
    | .pair (.atom 3) operator => (getTypeOp operator).map ConstProvenance.representation
    | _ => none
  def getSourceTerm : Data → Option SourceTerm
    | .pair (.atom 0) (.pair symbol annotation) => do
        return .const (← getConst symbol) (← getTy annotation)
    | .pair (.atom 1) (.pair value annotation) => do
        return .var (← nameCodec.get value) (← getTy annotation)
    | .pair (.atom 2) (.pair function argument) => do
        return .app (← getSourceTerm function) (← getSourceTerm argument)
    | .pair (.atom 3) (.pair binder (.pair domain body)) => do
        return .abs (← nameCodec.get binder) (← getTy domain) (← getSourceTerm body)
    | _ => none
end

mutual
  theorem getTy_putTy (value : Ty) : getTy (putTy value) = some value := by
    cases value with
    | var value => simp [putTy, getTy, nameCodec.get_put]
    | op operator arguments => simp [putTy, getTy, getTypeOp_putTypeOp operator, getTys_putTys arguments]
  termination_by sizeOf value
  theorem getTys_putTys (values : List Ty) : getTys (putTys values) = some values := by
    cases values with
    | nil => rfl
    | cons value values => simp [putTys, getTys, getTy_putTy value, getTys_putTys values]
  termination_by sizeOf values
  theorem getTypeOp_putTypeOp (value : TypeOp) : getTypeOp (putTypeOp value) = some value := by
    cases value with
    | mk value provenance => simp [putTypeOp, getTypeOp, nameCodec.get_put,
        getTypeOpProvenance_putTypeOpProvenance provenance]
  termination_by sizeOf value
  theorem getTypeOpProvenance_putTypeOpProvenance (value : TypeOpProvenance) :
      getTypeOpProvenance (putTypeOpProvenance value) = some value := by
    cases value with
    | undefined => rfl
    | defined predicate parameters => simp [putTypeOpProvenance, getTypeOpProvenance,
        getSourceTerm_putSourceTerm predicate, (Codec.list nameCodec).get_put]
  termination_by sizeOf value
  theorem getConst_putConst (value : Const) : getConst (putConst value) = some value := by
    cases value with
    | mk value provenance => simp [putConst, getConst, nameCodec.get_put,
        getConstProvenance_putConstProvenance provenance]
  termination_by sizeOf value
  theorem getConstProvenance_putConstProvenance (value : ConstProvenance) :
      getConstProvenance (putConstProvenance value) = some value := by
    cases value with
    | undefined => rfl
    | defined definition => simp [putConstProvenance, getConstProvenance, getSourceTerm_putSourceTerm definition]
    | abstraction operator => simp [putConstProvenance, getConstProvenance, getTypeOp_putTypeOp operator]
    | representation operator => simp [putConstProvenance, getConstProvenance, getTypeOp_putTypeOp operator]
  termination_by sizeOf value
  theorem getSourceTerm_putSourceTerm (value : SourceTerm) :
      getSourceTerm (putSourceTerm value) = some value := by
    cases value with
    | const symbol annotation => simp [putSourceTerm, getSourceTerm, getConst_putConst symbol, getTy_putTy annotation]
    | var value annotation => simp [putSourceTerm, getSourceTerm, nameCodec.get_put, getTy_putTy annotation]
    | app function argument => simp [putSourceTerm, getSourceTerm,
        getSourceTerm_putSourceTerm function, getSourceTerm_putSourceTerm argument]
    | abs binder domain body => simp [putSourceTerm, getSourceTerm, nameCodec.get_put,
        getTy_putTy domain, getSourceTerm_putSourceTerm body]
  termination_by sizeOf value
end

def tyCodec : Codec Ty := ⟨putTy, getTy, getTy_putTy⟩
local instance : DecidableEq Ty := tyCodec.decEq

def typeOpCodec : Codec TypeOp := ⟨putTypeOp, getTypeOp, getTypeOp_putTypeOp⟩
def constantCodec : Codec Const := ⟨putConst, getConst, getConst_putConst⟩
def sourceTermCodec : Codec SourceTerm := ⟨putSourceTerm, getSourceTerm, getSourceTerm_putSourceTerm⟩
def sourceVarCodec : Codec SourceVar :=
  (Codec.prod nameCodec tyCodec).mapped
    (fun value => (value.name, value.ty)) (fun value => some ⟨value.1, value.2⟩) (fun _ => rfl)

/-- Bound indices are direct binary fields, including indices beyond machine words. -/
def putTerm : DBTerm → Data
  | .const symbol annotation => .pair (.atom 0) (.pair (putConst symbol) (putTy annotation))
  | .free value => .pair (.atom 1) (sourceVarCodec.put value)
  | .bound index => .pair (.atom 2) (.atom index)
  | .app function argument => .pair (.atom 3) (.pair (putTerm function) (putTerm argument))
  | .abs domain body => .pair (.atom 4) (.pair (putTy domain) (putTerm body))

def getTerm : Data → Option DBTerm
  | .pair (.atom 0) (.pair symbol annotation) => do return .const (← getConst symbol) (← getTy annotation)
  | .pair (.atom 1) value => (sourceVarCodec.get value).map DBTerm.free
  | .pair (.atom 2) (.atom index) => some (.bound index)
  | .pair (.atom 3) (.pair function argument) => do return .app (← getTerm function) (← getTerm argument)
  | .pair (.atom 4) (.pair domain body) => do return .abs (← getTy domain) (← getTerm body)
  | _ => none

theorem getTerm_putTerm (value : DBTerm) : getTerm (putTerm value) = some value := by
  induction value with
  | const symbol annotation => simp [putTerm, getTerm, getConst_putConst, getTy_putTy]
  | free value => simp [putTerm, getTerm, sourceVarCodec.get_put]
  | bound index => rfl
  | app function argument first second => simp [putTerm, getTerm, first, second]
  | abs domain body ih => simp [putTerm, getTerm, getTy_putTy, ih]

def dbTermCodec : Codec DBTerm := ⟨putTerm, getTerm, getTerm_putTerm⟩

/-- Retain the displayed type and validate it against the existing type checker. -/
def admitCanonical (value : DBTerm × Ty) : Option CanonicalTerm :=
  if checked : value.1.inferType [] = some value.2 then some ⟨value.1, value.2, checked⟩ else none

theorem admitCanonical_fields (value : CanonicalTerm) :
    admitCanonical (value.term, value.ty) = some value := by
  cases value with
  | mk term ty checked =>
      unfold admitCanonical
      rw [dif_pos checked]

def canonicalCodec : Codec CanonicalTerm :=
  (Codec.prod dbTermCodec tyCodec).mapped (fun value => (value.term, value.ty))
    admitCanonical admitCanonical_fields

def admitCheckedSource (value : SourceTerm × Ty) : Option CheckedSourceTerm :=
  if checked : value.1.inferType = some value.2 then some ⟨value.1, value.2, checked⟩ else none

theorem admitCheckedSource_fields (value : CheckedSourceTerm) :
    admitCheckedSource (value.source, value.ty) = some value := by
  cases value with
  | mk source ty checked =>
      unfold admitCheckedSource
      rw [dif_pos checked]

def checkedSourceCodec : Codec CheckedSourceTerm :=
  (Codec.prod sourceTermCodec tyCodec).mapped (fun value => (value.source, value.ty))
    admitCheckedSource admitCheckedSource_fields

def sequentCodec : Codec Sequent :=
  (Codec.prod (finsetCodec canonicalCodec) canonicalCodec).mapped
    (fun value => (value.hyp, value.concl)) (fun value => some ⟨value.1, value.2⟩) (fun _ => rfl)

instance sequentBoolDecidable (value : Sequent) : Decidable value.IsBool :=
  decidable_of_iff (value.isBoolB = true) value.isBoolB_eq_true_iff

/-- Axiom tags are reconstructed only after their original Booleanity check. -/
def admitTheorem (value : Finset Sequent × Sequent) : Option Theorem :=
  if boolean : ∀ tagged ∈ value.1, tagged.IsBool then some ⟨value.1, boolean, value.2⟩ else none

theorem admitTheorem_fields (value : Theorem) :
    admitTheorem (value.axioms, value.sequent) = some value := by
  cases value with
  | mk axioms boolean sequent =>
      unfold admitTheorem
      rw [dif_pos boolean]

def theoremCodec : Codec Theorem :=
  (Codec.prod (finsetCodec sequentCodec) sequentCodec).mapped
    (fun value => (value.axioms, value.sequent)) admitTheorem admitTheorem_fields

private theorem one_digit : (Nat.digits 2 1).length = 1 := rfl

theorem string_payload_bound (value : String) :
    dataWeight (Codec.string.put value) + 1 ≤ 64 * StorageSize.string value := by
  have bound := dataWeight_string value
  unfold StorageSize.string
  omega

theorem name_payload_bound (value : Name) :
    dataWeight (nameCodec.put value) + 1 ≤ 64 * StorageSize.name value := by
  have names := dataWeight_list_le Codec.string StorageSize.string 64 (by decide)
    string_payload_bound value.namespaceComponents
  have component := string_payload_bound value.component
  change 1 + dataWeight ((Codec.list Codec.string).put value.namespaceComponents) +
    dataWeight (Codec.string.put value.component) + 1 ≤ _
  unfold StorageSize.name StorageSize.list
  omega

mutual
  theorem ty_payload_bound (value : Ty) :
      dataWeight (putTy value) + 1 ≤ 64 * StorageSize.ty value := by
    cases value with
    | var value =>
        have child := name_payload_bound value
        simp only [putTy, dataWeight, Nat.digits_zero, List.length_nil, StorageSize.ty]
        omega
    | op operator arguments =>
        have first := typeOp_payload_bound operator
        have second := tys_payload_bound arguments
        simp only [putTy, dataWeight, one_digit, StorageSize.ty]
        omega
  termination_by sizeOf value
  theorem tys_payload_bound (values : List Ty) :
      dataWeight (putTys values) + 1 ≤ 64 * StorageSize.types values := by
    cases values with
    | nil => simp [putTys, dataWeight, StorageSize.types]
    | cons value values =>
        have first := ty_payload_bound value
        have second := tys_payload_bound values
        simp only [putTys, dataWeight, StorageSize.types]
        omega
  termination_by sizeOf values
  theorem typeOp_payload_bound (value : TypeOp) :
      dataWeight (putTypeOp value) + 1 ≤ 64 * StorageSize.typeOp value := by
    cases value with
    | mk value provenance =>
        have first := name_payload_bound value
        have second := typeOpProvenance_payload_bound provenance
        simp only [putTypeOp, dataWeight, StorageSize.typeOp]
        omega
  termination_by sizeOf value
  theorem typeOpProvenance_payload_bound (value : TypeOpProvenance) :
      dataWeight (putTypeOpProvenance value) + 1 ≤ 64 * StorageSize.typeOpProvenance value := by
    cases value with
    | undefined => simp [putTypeOpProvenance, dataWeight, StorageSize.typeOpProvenance]
    | defined predicate parameters =>
        have first := sourceTerm_payload_bound predicate
        have second := dataWeight_list_le nameCodec StorageSize.name 64 (by decide)
          name_payload_bound parameters
        simp only [putTypeOpProvenance, dataWeight, one_digit,
          StorageSize.typeOpProvenance, StorageSize.list]
        omega
  termination_by sizeOf value
  theorem constant_payload_bound (value : Const) :
      dataWeight (putConst value) + 1 ≤ 64 * StorageSize.constant value := by
    cases value with
    | mk value provenance =>
        have first := name_payload_bound value
        have second := constantProvenance_payload_bound provenance
        simp only [putConst, dataWeight, StorageSize.constant]
        omega
  termination_by sizeOf value
  theorem constantProvenance_payload_bound (value : ConstProvenance) :
      dataWeight (putConstProvenance value) + 1 ≤ 64 * StorageSize.constantProvenance value := by
    cases value with
    | undefined => simp [putConstProvenance, dataWeight, StorageSize.constantProvenance]
    | defined definition =>
        have child := sourceTerm_payload_bound definition
        simp only [putConstProvenance, dataWeight, one_digit,
          StorageSize.constantProvenance]
        omega
    | abstraction operator =>
        have child := typeOp_payload_bound operator
        have tag : (Nat.digits 2 2).length = 2 := rfl
        simp only [putConstProvenance, dataWeight, tag, StorageSize.constantProvenance]
        omega
    | representation operator =>
        have child := typeOp_payload_bound operator
        have tag : (Nat.digits 2 3).length = 2 := rfl
        simp only [putConstProvenance, dataWeight, tag, StorageSize.constantProvenance]
        omega
  termination_by sizeOf value
  theorem sourceTerm_payload_bound (value : SourceTerm) :
      dataWeight (putSourceTerm value) + 1 ≤ 64 * StorageSize.sourceTerm value := by
    cases value with
    | const symbol annotation =>
        have first := constant_payload_bound symbol
        have second := ty_payload_bound annotation
        simp only [putSourceTerm, dataWeight, Nat.digits_zero, List.length_nil, StorageSize.sourceTerm]
        omega
    | var value annotation =>
        have first := name_payload_bound value
        have second := ty_payload_bound annotation
        simp only [putSourceTerm, dataWeight, one_digit, StorageSize.sourceTerm]
        omega
    | app function argument =>
        have first := sourceTerm_payload_bound function
        have second := sourceTerm_payload_bound argument
        have tag : (Nat.digits 2 2).length = 2 := rfl
        simp only [putSourceTerm, dataWeight, tag, StorageSize.sourceTerm]
        omega
    | abs binder domain body =>
        have first := name_payload_bound binder
        have second := ty_payload_bound domain
        have third := sourceTerm_payload_bound body
        have tag : (Nat.digits 2 3).length = 2 := rfl
        simp only [putSourceTerm, dataWeight, tag, StorageSize.sourceTerm]
        omega
  termination_by sizeOf value
end

theorem sourceVar_payload_bound (value : SourceVar) :
    dataWeight (sourceVarCodec.put value) + 1 ≤ 64 * StorageSize.sourceVar value := by
  have first := name_payload_bound value.name
  have second := ty_payload_bound value.ty
  change 1 + dataWeight (nameCodec.put value.name) + dataWeight (putTy value.ty) + 1 ≤ _
  unfold StorageSize.sourceVar
  omega

theorem term_payload_bound (value : DBTerm) :
    dataWeight (putTerm value) + 1 ≤ 64 * StorageSize.term value := by
  induction value with
  | const symbol annotation =>
      have first := constant_payload_bound symbol
      have second := ty_payload_bound annotation
      simp only [putTerm, dataWeight, Nat.digits_zero, List.length_nil, StorageSize.term]
      omega
  | free value =>
      have child := sourceVar_payload_bound value
      simp only [putTerm, dataWeight, one_digit, StorageSize.term]
      omega
  | bound index =>
      have tag : (Nat.digits 2 2).length = 2 := rfl
      simp only [putTerm, dataWeight, tag, StorageSize.term, StorageSize.nat]
      omega
  | app function argument first second =>
      have tag : (Nat.digits 2 3).length = 2 := rfl
      simp only [putTerm, dataWeight, tag, StorageSize.term]
      omega
  | abs domain body ih =>
      have first := ty_payload_bound domain
      have tag : (Nat.digits 2 4).length = 3 := rfl
      simp only [putTerm, dataWeight, tag, StorageSize.term]
      omega

theorem canonical_payload_bound (value : CanonicalTerm) :
    dataWeight (canonicalCodec.put value) + 1 ≤ 64 * StorageSize.canonical value := by
  have first := term_payload_bound value.term
  have second := ty_payload_bound value.ty
  change 1 + dataWeight (putTerm value.term) + dataWeight (putTy value.ty) + 1 ≤ _
  unfold StorageSize.canonical
  omega

theorem checkedSource_payload_bound (value : CheckedSourceTerm) :
    dataWeight (checkedSourceCodec.put value) + 1 ≤ 64 * StorageSize.checkedSource value := by
  have first := sourceTerm_payload_bound value.source
  have second := ty_payload_bound value.ty
  change 1 + dataWeight (putSourceTerm value.source) + dataWeight (putTy value.ty) + 1 ≤ _
  unfold StorageSize.checkedSource
  omega

theorem sequent_payload_bound (value : Sequent) :
    dataWeight (sequentCodec.put value) + 1 ≤ 64 * StorageSize.sequent value := by
  have first := dataWeight_finset_le canonicalCodec StorageSize.canonical 64 (by decide)
    canonical_payload_bound value.hyp
  have second := canonical_payload_bound value.concl
  change 1 + dataWeight ((finsetCodec canonicalCodec).put value.hyp) +
    dataWeight (canonicalCodec.put value.concl) + 1 ≤ _
  unfold StorageSize.sequent StorageSize.finset
  omega

theorem theorem_payload_bound (value : Theorem) :
    dataWeight (theoremCodec.put value) + 1 ≤ 64 * StorageSize.theoremData value := by
  have first := dataWeight_finset_le sequentCodec StorageSize.sequent 64 (by decide)
    sequent_payload_bound value.axioms
  have second := sequent_payload_bound value.sequent
  change 1 + dataWeight ((finsetCodec sequentCodec).put value.axioms) +
    dataWeight (sequentCodec.put value.sequent) + 1 ≤ _
  unfold StorageSize.theoremData StorageSize.finset
  omega

namespace Controls

/-- Same printed symbol, different definition provenance: distinct stored values. -/
theorem definition_provenance_retained (value : Name) (definition : SourceTerm) :
    encodeWith constantCodec (.mk value .undefined) ≠
      encodeWith constantCodec (.mk value (.defined definition)) := by
  intro same
  have reconstructed := encodeWith_injective constantCodec same
  cases reconstructed

/-- An escaping de Bruijn variable remains valid raw data, but cannot be
reconstructed as a checked closed term. -/
theorem escaping_canonical_refused : admitCanonical (.bound 0, Ty.bool) = none := by
  simp [admitCanonical, DBTerm.inferType]

theorem unknown_term_constructor_refused : getTerm (.pair (.atom 99) (.atom 0)) = none := rfl

/-- A typed non-Boolean sequent can be stored as raw current data, but cannot
be admitted as an axiom dependency. -/
theorem nonBoolean_tag_refused :
    admitTheorem ({SequentExamples.nonBooleanSequent}, SequentExamples.nonBooleanSequent) = none := by
  have notBoolean : ¬ SequentExamples.nonBooleanSequent.IsBool := by
    intro boolean
    have conclusion := boolean.1
    simp [SequentExamples.nonBooleanSequent, SequentExamples.individualVariable,
      CanonicalTerm.IsBool, Ty.bool, Examples.individual, TypeOp.bool, Name.global] at conclusion
  have refused : ¬ ∀ tagged ∈ ({SequentExamples.nonBooleanSequent} : Finset Sequent), tagged.IsBool := by
    intro allBoolean
    exact notBoolean (allBoolean _ (Finset.mem_singleton_self _))
  unfold admitTheorem
  rw [dif_neg refused]

/-- Closed binding syntax retains its displayed domain and bound occurrence. -/
theorem binder_roundtrip :
    decodeWith dbTermCodec (encodeWith dbTermCodec (.abs Ty.bool (.bound 0))) =
      some (.abs Ty.bool (.bound 0)) := decodeWith_encodeWith dbTermCodec _

end Controls

namespace Templates

open Mettapedia.Computability.WordTemplateMachine

variable {arity : Nat}

/-- Literal original syntax and indexed complete fields share the same
finite-alphabet template representation. -/
def literal (data : Data) : Indexed.Template Alphabet arity :=
  (encodeData data).map Sum.inl

def pair (first second : Indexed.Template Alphabet arity) : Indexed.Template Alphabet arity :=
  .inl 4 :: first ++ second

@[simp] theorem literal_exact (data : Data) (words : Fin arity → List Alphabet) :
    Indexed.instantiate (literal data) words = encodeData data := by
  exact Indexed.instantiate_literals _ _

@[simp] theorem pair_exact (first second : Indexed.Template Alphabet arity)
    (words : Fin arity → List Alphabet) :
    Indexed.instantiate (pair first second) words =
      4 :: Indexed.instantiate first words ++ Indexed.instantiate second words := by
  simp [pair]

theorem pair_data (first second : Indexed.Template Alphabet arity)
    (words : Fin arity → List Alphabet) (left right : Data)
    (leftExact : Indexed.instantiate first words = encodeData left)
    (rightExact : Indexed.instantiate second words = encodeData right) :
    Indexed.instantiate (pair first second) words = encodeData (.pair left right) := by
  rw [pair_exact, leftExact, rightExact, encodeData_pair]
  rfl

/-- Curried application retains each operand occurrence as a complete field. -/
def application (first second : Indexed.Template Alphabet arity) : Indexed.Template Alphabet arity :=
  pair (literal (.atom 3)) (pair first second)

theorem application_exact (first second : Indexed.Template Alphabet arity)
    (words : Fin arity → List Alphabet) (left right : DBTerm)
    (leftExact : Indexed.instantiate first words = encodeWith dbTermCodec left)
    (rightExact : Indexed.instantiate second words = encodeWith dbTermCodec right) :
    Indexed.instantiate (application first second) words = encodeWith dbTermCodec (.app left right) := by
  simpa only [application, dbTermCodec, encodeWith, putTerm] using
    pair_data (literal (.atom 3)) (pair first second) words (.atom 3)
      (.pair (putTerm left) (putTerm right)) (literal_exact _ _)
      (pair_data first second words (putTerm left) (putTerm right) leftExact rightExact)

/-- Named application uses the original source tag, retaining each supplied
complete source field rather than treating it as raw de Bruijn syntax. -/
def sourceApplication (first second : Indexed.Template Alphabet arity) : Indexed.Template Alphabet arity :=
  pair (literal (.atom 2)) (pair first second)

theorem sourceApplication_exact (first second : Indexed.Template Alphabet arity)
    (words : Fin arity → List Alphabet) (left right : SourceTerm)
    (leftExact : Indexed.instantiate first words = encodeWith sourceTermCodec left)
    (rightExact : Indexed.instantiate second words = encodeWith sourceTermCodec right) :
    Indexed.instantiate (sourceApplication first second) words =
      encodeWith sourceTermCodec (.app left right) := by
  simpa only [sourceApplication, sourceTermCodec, encodeWith, putSourceTerm] using
    pair_data (literal (.atom 2)) (pair first second) words (.atom 2)
      (.pair (putSourceTerm left) (putSourceTerm right)) (literal_exact _ _)
      (pair_data first second words (putSourceTerm left) (putSourceTerm right) leftExact rightExact)

def sourceAbstraction (binder : Name) (domain : Ty) (body : Indexed.Template Alphabet arity) :
    Indexed.Template Alphabet arity :=
  pair (literal (.atom 3)) (pair (literal (nameCodec.put binder)) (pair (literal (putTy domain)) body))

theorem sourceAbstraction_exact (binder : Name) (domain : Ty) (body : Indexed.Template Alphabet arity)
    (words : Fin arity → List Alphabet) (value : SourceTerm)
    (bodyExact : Indexed.instantiate body words = encodeWith sourceTermCodec value) :
    Indexed.instantiate (sourceAbstraction binder domain body) words =
      encodeWith sourceTermCodec (.abs binder domain value) := by
  simp only [sourceAbstraction, pair_exact, literal_exact, bodyExact]
  simp only [encodeWith, sourceTermCodec, putSourceTerm, encodeData_pair]
  rfl

/-- Displayed typing is stored without replacing the original admission check. -/
def canonical (type : Ty) (term : Indexed.Template Alphabet arity) : Indexed.Template Alphabet arity :=
  pair term (literal (tyCodec.put type))

theorem canonical_exact (type : Ty) (term : Indexed.Template Alphabet arity)
    (words : Fin arity → List Alphabet) (value : CanonicalTerm)
    (sameType : value.ty = type)
    (termExact : Indexed.instantiate term words = encodeWith dbTermCodec value.term) :
    Indexed.instantiate (canonical type term) words = encodeWith canonicalCodec value := by
  simp only [canonical, pair_exact, literal_exact]
  rw [termExact, ← sameType]
  simp only [encodeWith, canonicalCodec, Codec.mapped, Codec.prod, encodeData_pair]
  rfl

/-- Fixed authored dependency sets retain their complete original sequent
bytes; the result term remains a dynamic field. -/
def theoremTemplate (axioms : Finset Sequent) (hypotheses : Finset CanonicalTerm)
    (conclusion : Indexed.Template Alphabet arity) : Indexed.Template Alphabet arity :=
  pair (literal ((finsetCodec sequentCodec).put axioms))
    (pair (literal ((finsetCodec canonicalCodec).put hypotheses)) conclusion)

theorem theoremTemplate_exact (axioms : Finset Sequent) (hypotheses : Finset CanonicalTerm)
    (conclusion : Indexed.Template Alphabet arity) (words : Fin arity → List Alphabet)
    (value : Theorem) (sameAxioms : value.axioms = axioms)
    (sameHypotheses : value.sequent.hyp = hypotheses)
    (conclusionExact : Indexed.instantiate conclusion words = encodeWith canonicalCodec value.sequent.concl) :
    Indexed.instantiate (theoremTemplate axioms hypotheses conclusion) words = encodeWith theoremCodec value := by
  simp only [theoremTemplate, pair_exact, literal_exact, conclusionExact]
  rw [← sameAxioms, ← sameHypotheses]
  simp only [encodeWith, theoremCodec, sequentCodec, Codec.mapped, Codec.prod, encodeData_pair]
  rfl

/-- The primitive equality operator has its original complete type annotation. -/
def equality (operandType : Ty) (left right : Indexed.Template Alphabet arity) :
    Indexed.Template Alphabet arity :=
  application
    (application (literal (putTerm (.const Const.equality (Ty.equality operandType)))) left) right

theorem equality_exact (operandType : Ty) (left right : Indexed.Template Alphabet arity)
    (words : Fin arity → List Alphabet) (first second : DBTerm)
    (leftExact : Indexed.instantiate left words = encodeWith dbTermCodec first)
    (rightExact : Indexed.instantiate right words = encodeWith dbTermCodec second) :
    Indexed.instantiate (equality operandType left right) words =
      encodeWith dbTermCodec (CanonicalTerm.equalityDB operandType first second) := by
  apply application_exact _ _ _ _ _ _ rightExact
  exact application_exact _ _ _ _ _ (literal_exact _ _) leftExact

theorem equalityCanonical_exact (left right : Indexed.Template Alphabet arity)
    (words : Fin arity → List Alphabet) (first second : CanonicalTerm)
    (sameType : first.ty = second.ty)
    (leftExact : Indexed.instantiate left words = encodeWith dbTermCodec first.term)
    (rightExact : Indexed.instantiate right words = encodeWith dbTermCodec second.term) :
    Indexed.instantiate (canonical Ty.bool (equality first.ty left right)) words =
      encodeWith canonicalCodec (CanonicalTerm.equalityOfSameType first second sameType) := by
  apply canonical_exact Ty.bool (equality first.ty left right) words
    (CanonicalTerm.equalityOfSameType first second sameType) rfl
  exact equality_exact _ _ _ _ _ _ leftExact rightExact

/-- A single substitution word can occupy one slot of a larger physical
field packet without introducing another template compiler. -/
def single (slot : Fin arity) (template : Template Alphabet) : Indexed.Template Alphabet arity :=
  template.map fun token => match token with
    | none => .inr slot
    | some symbol => .inl symbol

theorem single_exact (slot : Fin arity) (template : Template Alphabet)
    (words : Fin arity → List Alphabet) :
    Indexed.instantiate (single slot template) words =
      Mettapedia.Computability.WordTemplateMachine.instantiate template (words slot) := by
  induction template with
  | nil => rfl
  | cons token rest ih =>
      simp only [single] at ih
      cases token <;> simp [single, ih]

/-- Indexed authored plans compose by replacing their finite holes with
other plans over the same complete field words. -/
def substitute {sourceArity targetArity : Nat}
    (template : Indexed.Template Alphabet sourceArity)
    (slots : Fin sourceArity → Indexed.Template Alphabet targetArity) :
    Indexed.Template Alphabet targetArity :=
  template.flatMap fun token => match token with
    | .inl symbol => [.inl symbol]
    | .inr index => slots index

theorem substitute_exact {sourceArity targetArity : Nat}
    (template : Indexed.Template Alphabet sourceArity)
    (slots : Fin sourceArity → Indexed.Template Alphabet targetArity)
    (words : Fin targetArity → List Alphabet) :
    Indexed.instantiate (substitute template slots) words =
      Indexed.instantiate template (fun index => Indexed.instantiate (slots index) words) := by
  induction template with
  | nil => rfl
  | cons token rest ih =>
      simp only [substitute] at ih
      cases token <;> simp [substitute, Indexed.instantiate_append, ih]

end Templates

end Mettapedia.Languages.OpenTheory.SyntaxEncoding
