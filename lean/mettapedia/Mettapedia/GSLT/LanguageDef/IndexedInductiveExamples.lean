import Mettapedia.GSLT.LanguageDef.IndexedInductiveElimination

/-!
# Indexed and mutual constructor descriptions

The vector example uses an explicit index-expression syntax and retains both
length indices and Boolean payloads. The mutual example crosses between two
family indices. Their interpretations are compared with independent Lean data,
rather than with another abbreviation of the compiled polynomial.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductiveExamples

open Mettapedia.TypeTheory
open IndexedPolynomial
open IndexedPolynomial.Description

namespace Vectors

inductive DataSort where
  | length
  | payload
  deriving DecidableEq

def value : DataSort → Type
  | .length => Nat
  | .payload => Bool

inductive NatVariable : List DataSort → Type where
  | here {context} : NatVariable (.length :: context)
  | there {context sort} : NatVariable context → NatVariable (sort :: context)

def NatVariable.lookup : {context : List DataSort} → NatVariable context →
    Env value context → Nat
  | _, .here, environment => environment.1
  | _, .there reference, environment => reference.lookup environment.2

inductive IndexExpr (context : List DataSort) where
  | literal : Nat → IndexExpr context
  | variable : NatVariable context → IndexExpr context
  | successor : IndexExpr context → IndexExpr context

def IndexExpr.eval {context : List DataSort} :
    IndexExpr context → Env value context → Nat
  | .literal n, _ => n
  | .variable reference, environment => reference.lookup environment
  | .successor expression, environment => expression.eval environment + 1

def interface : Interface where
  SortCode := DataSort
  Value := value
  Index := Nat
  IndexExpr := IndexExpr
  evalIndex := IndexExpr.eval

def nilCode : Code interface [] := .result (.literal 0)

def consCode : Code interface [] :=
  .data .length (.data .payload
    (.recursive (.variable (.there .here))
      (.result (.successor (.variable (.there .here))))))

def constructors : List (NamedConstructor interface []) :=
  [⟨"nil", nilCode⟩, ⟨"cons", consCode⟩]

def admitted : IndexedInductive.Admitted interface [] :=
  ⟨constructors, by decide⟩

def source : IndexedInductive.Document interface [] := .bundle
  [.declaration ⟨"nil", .result (.literal 0)⟩,
   .declaration ⟨"cons", .data .length (.data .payload
     (.recursive (.variable (.there .here))
       (.result (.successor (.variable (.there .here))))))⟩]

/-- The generic coGSLT admits this indexed inventory without a vector adapter. -/
theorem source_admitted : IndexedInductive.admit? source = some admitted :=
  IndexedInductive.admit_quote admitted

/-- A constructor consuming a function from the recursive family is refused. -/
theorem negative_occurrence_rejected :
    IndexedInductive.RawCode.decode interface (context := [])
      (.functionField (.family (.literal 0)) (.ground .payload)
        (.result (.literal 0))) = none := rfl

theorem duplicate_constructor_rejected :
    IndexedInductive.admitList?
      [IndexedInductive.quoteConstructor (⟨"nil", nilCode⟩ : NamedConstructor interface []),
        IndexedInductive.quoteConstructor ⟨"nil", nilCode⟩] = none := by
  rfl

abbrev polynomial := admitted.polynomial

abbrev Vector (length : Nat) := admitted.Family PUnit.unit length

def nil : Vector 0 := by
  refine admitted.construct ⟨⟨0, by decide⟩, ?_⟩
  change ULift (PLift ((0 : Nat) = 0))
  exact ⟨⟨rfl⟩⟩

def cons {length : Nat} (head : Bool) (tail : Vector length) : Vector (length + 1) := by
  refine admitted.construct ⟨⟨1, by decide⟩, ?_⟩
  change Σ n : Nat, Σ _ : Bool, Vector n × ULift (PLift (n + 1 = length + 1))
  exact ⟨length, head, tail, ⟨⟨rfl⟩⟩⟩

/-- Ordinary list storage, checked independently by `List.length`. -/
abbrev ListVector (length : Nat) := { xs : List Bool // xs.length = length }

def listMethods : Algebra.Displayed (Algebra.initial polynomial)
    (fun _ length _ => ListVector length) where
  act := by
    intro environment length shape children hypotheses
    rcases shape with ⟨occurrence, shape⟩
    refine Fin.cases ?_ (fun occurrence => ?_) occurrence shape children hypotheses
    · intro shape _children _hypotheses
      exact ⟨[], shape.down.down⟩
    · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) occurrence
      intro shape _children hypotheses
      rcases shape with ⟨tailLength, head, equation⟩
      exact ⟨head :: (hypotheses none).val,
        (congrArg Nat.succ (hypotheses none).property).trans equation.down.down⟩

noncomputable def toList {length : Nat} (vector : Vector length) : ListVector length :=
  (admitted.eliminate listMethods).toFun PUnit.unit length vector

@[simp] theorem toList_nil : toList nil = ⟨[], rfl⟩ := rfl

@[simp] theorem toList_cons {length : Nat} (head : Bool) (tail : Vector length) :
    (toList (cons head tail)).val = head :: (toList tail).val := rfl

def fromList : (xs : List Bool) → Vector xs.length
  | [] => nil
  | head :: tail => cons head (fromList tail)

/-- A fold written directly against authored, ordered constructor arguments. -/
def listSourceMethods : admitted.Methods (fun _ _ => List Bool) := by
  intro environment length arguments
  rcases arguments with ⟨occurrence, arguments⟩
  refine Fin.cases ?_ (fun occurrence => ?_) occurrence arguments
  · intro _
    exact []
  · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) occurrence
    intro arguments
    exact arguments.2.1 :: arguments.2.2.1

noncomputable def sourceList {length : Nat} (vector : Vector length) : List Bool :=
  admitted.fold listSourceMethods PUnit.unit length vector

@[simp] theorem sourceList_nil : sourceList nil = [] := rfl

/-- This computation law is obtained from the generic source-argument theorem. -/
@[simp] theorem sourceList_cons {length : Nat} (head : Bool) (tail : Vector length) :
    sourceList (cons head tail) = head :: sourceList tail := by
  let arguments : InventoryArguments admitted.constructors PUnit.unit
      (admitted.Family PUnit.unit) (length + 1) := by
    refine ⟨⟨1, by decide⟩, ?_⟩
    change Σ n : Nat, Σ _ : Bool, Vector n × ULift (PLift (n + 1 = length + 1))
    exact ⟨length, head, tail, ⟨⟨rfl⟩⟩⟩
  exact admitted.fold_construct listSourceMethods arguments

theorem sourceList_fromList (xs : List Bool) : sourceList (fromList xs) = xs := by
  induction xs with
  | nil => rfl
  | cons head tail ih => simp only [fromList, sourceList_cons, ih]

/-- The authored-argument fold and the dependent list interpretation agree on
every compiled value, including values not supplied by `fromList`. -/
theorem sourceList_agrees {length : Nat} (vector : Vector length) :
    sourceList vector = (toList vector).val := by
  refine @Fix.rec _ _ polynomial PUnit.unit
    (fun _ tree => sourceList tree = (toList tree).val) ?_ length vector
  intro _length shape children hypotheses
  rcases shape with ⟨occurrence, shape⟩
  revert shape children hypotheses
  refine Fin.cases ?_ (fun occurrence => ?_) occurrence
  · intro _shape _children _hypotheses
    rfl
  · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) occurrence
    intro shape _children hypotheses
    rcases shape with ⟨_tailLength, head, _equation⟩
    exact congrArg (List.cons head) (hypotheses none)

/-- The generated dependent section preserves every ordered source element. -/
theorem toList_fromList (xs : List Bool) : (toList (fromList xs)).val = xs := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
      simp only [fromList, toList_cons, ih]

def listCons {length : Nat} (head : Bool) (tail : ListVector length) :
    ListVector (length + 1) :=
  ⟨head :: tail.val, congrArg Nat.succ tail.property⟩

/-- The inverse uses ordinary list recursion and its independently checked length. -/
def fromListVector {length : Nat} (vector : ListVector length) : Vector length :=
  vector.property ▸ fromList vector.val

theorem fromListVector_listCons {length : Nat} (head : Bool) (tail : ListVector length) :
    fromListVector (listCons head tail) = cons head (fromListVector tail) := by
  rcases tail with ⟨tail, equation⟩
  cases equation
  rfl

theorem toList_fromListVector {length : Nat} (vector : ListVector length) :
    toList (fromListVector vector) = vector := by
  rcases vector with ⟨values, equation⟩
  cases equation
  apply Subtype.ext
  exact toList_fromList values

/-- Every compiled vector is reconstructed, not only vectors created by the
ordinary-list encoder. The index constraint fixes each constructor's output. -/
theorem fromListVector_toList {length : Nat} (vector : Vector length) :
    fromListVector (toList vector) = vector := by
  refine @Fix.rec _ _ polynomial PUnit.unit
    (fun _ tree => fromListVector (toList tree) = tree) ?_ length vector
  intro _length shape children hypotheses
  rcases shape with ⟨occurrence, shape⟩
  revert shape children hypotheses
  refine Fin.cases ?_ (fun occurrence => ?_) occurrence
  · intro shape children _hypotheses
    rcases shape with ⟨⟨equation⟩⟩
    cases equation
    change nil = Fix.roll _ children
    change Fix.roll _ _ = Fix.roll _ children
    apply congrArg (Fix.roll _)
    funext position
    exact PEmpty.elim position
  · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) occurrence
    intro shape children hypotheses
    rcases shape with ⟨tailLength, head, ⟨⟨equation⟩⟩⟩
    cases equation
    change fromListVector (listCons head (toList (children none))) = Fix.roll _ children
    apply (fromListVector_listCons head (toList (children none))).trans
    apply (congrArg (cons head) (hypotheses none)).trans
    change Fix.roll _ _ = Fix.roll _ children
    apply congrArg (Fix.roll _)
    funext position
    cases position with
    | none => rfl
    | some impossible => exact PEmpty.elim impossible

/-- The admitted indexed family is exactly ordinary length-checked list storage. -/
noncomputable def listEquiv (length : Nat) : Vector length ≃ ListVector length where
  toFun := toList
  invFun := fromListVector
  left_inv := fromListVector_toList
  right_inv := toList_fromListVector

theorem missing_payload_rejected :
    (toList (cons true nil)).val ≠ [] := by
  simp only [toList_cons, toList_nil]
  exact List.cons_ne_nil _ _

theorem changed_payload_rejected :
    (toList (cons true nil)).val ≠ [false] := by
  decide

/-- Constructor result constraints prohibit a nil constructor at a positive index. -/
theorem nil_at_wrong_index_rejected :
    ¬ Nonempty (Description.Shape nilCode PUnit.unit (1 : Nat)) := by
  rintro ⟨equation⟩
  exact Nat.noConfusion equation.down.down

end Vectors

namespace Mutual

def interface : Interface where
  SortCode := Empty
  Value := Empty.elim
  Index := Bool
  IndexExpr := fun _ => Bool
  evalIndex := fun expression _ => expression

def zeroCode : Code interface [] := .result false
def oddCode : Code interface [] := .recursive false (.result true)
def evenCode : Code interface [] := .recursive true (.result false)

def constructors : List (NamedConstructor interface []) :=
  [⟨"zero", zeroCode⟩, ⟨"odd", oddCode⟩, ⟨"even", evenCode⟩]

def admitted : IndexedInductive.Admitted interface [] :=
  ⟨constructors, by decide⟩

def source : IndexedInductive.Document interface [] := .bundle
  [.declaration ⟨"zero", .result false⟩,
   .declaration ⟨"odd", .recursive false (.result true)⟩,
   .declaration ⟨"even", .recursive true (.result false)⟩]

theorem source_admitted : IndexedInductive.admit? source = some admitted :=
  IndexedInductive.admit_quote admitted

abbrev polynomial := admitted.polynomial
abbrev Family (tag : Bool) := admitted.Family PUnit.unit tag

def zero : Family false := by
  refine admitted.construct ⟨⟨0, by decide⟩, ?_⟩
  change ULift (PLift (false = false))
  exact ⟨⟨rfl⟩⟩

def odd (evenChild : Family false) : Family true := by
  refine admitted.construct ⟨⟨1, by decide⟩, ?_⟩
  change Family false × ULift (PLift (true = true))
  exact ⟨evenChild, ⟨⟨rfl⟩⟩⟩

def even (oddChild : Family true) : Family false := by
  refine admitted.construct ⟨⟨2, by decide⟩, ?_⟩
  change Family true × ULift (PLift (false = false))
  exact ⟨oddChild, ⟨⟨rfl⟩⟩⟩

mutual
  inductive EvenData where
    | zero
    | next : OddData → EvenData
  inductive OddData where
    | next : EvenData → OddData
end

def dataFamily : Bool → Type
  | false => EvenData
  | true => OddData

/-- Methods switch from the even family to the odd family and back. -/
def dataMethods : Algebra.Displayed (Algebra.initial polynomial)
    (fun _ tag _ => dataFamily tag) where
  act := by
    intro environment tag shape children hypotheses
    rcases shape with ⟨occurrence, shape⟩
    refine Fin.cases ?_ (fun occurrence => ?_) occurrence shape children hypotheses
    · intro shape _children _hypotheses
      cases shape.down.down
      exact EvenData.zero
    · refine Fin.cases ?_ (fun occurrence => ?_) occurrence
      · intro shape _children hypotheses
        cases shape.down.down
        exact OddData.next (hypotheses none)
      · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) occurrence
        intro shape _children hypotheses
        cases shape.down.down
        exact EvenData.next (hypotheses none)

noncomputable def toData {tag : Bool} (tree : Family tag) : dataFamily tag :=
  (admitted.eliminate dataMethods).toFun PUnit.unit tag tree

@[simp] theorem toData_zero : toData zero = EvenData.zero := rfl
@[simp] theorem toData_odd (child : Family false) :
    toData (odd child) = OddData.next (toData child) := rfl
@[simp] theorem toData_even (child : Family true) :
    toData (even child) = EvenData.next (toData child) := rfl

mutual
  def fromEven : EvenData → Family false
    | .zero => zero
    | .next child => even (fromOdd child)
  def fromOdd : OddData → Family true
    | .next child => odd (fromEven child)
end

mutual
  theorem toData_fromEven (tree : EvenData) : toData (fromEven tree) = tree := by
    cases tree with
    | zero => rfl
    | next child =>
        change EvenData.next (toData (fromOdd child)) = EvenData.next child
        exact congrArg EvenData.next (toData_fromOdd child)
  theorem toData_fromOdd (tree : OddData) : toData (fromOdd tree) = tree := by
    cases tree with
    | next child =>
        change OddData.next (toData (fromEven child)) = OddData.next child
        exact congrArg OddData.next (toData_fromEven child)
end

/-- Interpret ordinary mutual data back in the corresponding source fibre. -/
def fromData : {tag : Bool} → dataFamily tag → Family tag
  | false, tree => fromEven tree
  | true, tree => fromOdd tree

theorem toData_fromData {tag : Bool} (tree : dataFamily tag) :
    toData (fromData tree) = tree := by
  cases tag with
  | false => exact toData_fromEven tree
  | true => exact toData_fromOdd tree

/-- The compiled family has no additional values beyond the ordinary mutual
datatypes. Every constructor occurrence and recursive child is reconstructed. -/
theorem fromData_toData {tag : Bool} (tree : Family tag) :
    fromData (toData tree) = tree := by
  refine @Fix.rec _ _ polynomial PUnit.unit
    (fun _ value => fromData (toData value) = value) ?_ tag tree
  intro tag shape children hypotheses
  rcases shape with ⟨occurrence, shape⟩
  revert shape children hypotheses
  refine Fin.cases ?_ (fun occurrence => ?_) occurrence
  · intro shape children _hypotheses
    rcases shape with ⟨⟨equation⟩⟩
    cases equation
    change zero = Fix.roll _ children
    change Fix.roll _ _ = Fix.roll _ children
    apply congrArg (Fix.roll _)
    funext position
    exact PEmpty.elim position
  · refine Fin.cases ?_ (fun occurrence => ?_) occurrence
    · intro shape children hypotheses
      rcases shape with ⟨⟨equation⟩⟩
      cases equation
      change odd (fromData (toData (children none))) = Fix.roll _ children
      apply (congrArg odd (hypotheses none)).trans
      change Fix.roll _ _ = Fix.roll _ children
      apply congrArg (Fix.roll _)
      funext position
      cases position with
      | none => rfl
      | some impossible => exact PEmpty.elim impossible
    · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) occurrence
      intro shape children hypotheses
      rcases shape with ⟨⟨equation⟩⟩
      cases equation
      change even (fromData (toData (children none))) = Fix.roll _ children
      apply (congrArg even (hypotheses none)).trans
      change Fix.roll _ _ = Fix.roll _ children
      apply congrArg (Fix.roll _)
      funext position
      cases position with
      | none => rfl
      | some impossible => exact PEmpty.elim impossible

/-- A genuine equivalence in each family fibre, with both inverse laws. -/
noncomputable def dataEquiv (tag : Bool) : Family tag ≃ dataFamily tag where
  toFun := toData
  invFun := fromData
  left_inv := fromData_toData
  right_inv := toData_fromData

/-- Two alternating recursive calls retain both source constructors. -/
theorem two_crossings_compute :
    toData (even (odd zero)) = EvenData.next (OddData.next EvenData.zero) := rfl

theorem dropped_crossings_rejected : toData (even (odd zero)) ≠ EvenData.zero := by
  intro equal
  exact EvenData.noConfusion equal

theorem zero_in_odd_family_rejected :
    ¬ Nonempty (Description.Shape zeroCode PUnit.unit true) := by
  rintro ⟨equation⟩
  exact Bool.noConfusion equation.down.down

end Mutual

#print axioms Vectors.source_admitted
#print axioms Vectors.toList_fromList
#print axioms Vectors.sourceList_cons
#print axioms Vectors.sourceList_fromList
#print axioms Vectors.sourceList_agrees
#print axioms Vectors.fromListVector_toList
#print axioms Vectors.listEquiv
#print axioms Vectors.nil_at_wrong_index_rejected
#print axioms Mutual.source_admitted
#print axioms Mutual.toData_fromEven
#print axioms Mutual.toData_fromOdd
#print axioms Mutual.fromData_toData
#print axioms Mutual.dataEquiv

end Mettapedia.GSLT.LanguageDef.IndexedInductiveExamples
