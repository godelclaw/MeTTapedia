import Mettapedia.GSLT.LanguageDef.CettaWireTerm
import Mettapedia.TypeTheory.IndexedContainer
import Mettapedia.TypeTheory.IndexedPolynomial

/-!
# Physical values for the registered List and Vector containers

The shared algebraic-list carrier stores complete ordered payloads. Its
decoder recovers a List container's shape and checks a Vector container's
declared output length. Both directions retain the element codec contract;
neither creates evidence that an arbitrary payload has a guest type.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerWire

open Mettapedia.TypeTheory
open CettaWire

universe u uBase uIndex uShape uPosition

abbrev ListValue (Element : Type u) := IndexedContainer.Examples.list.Extension Element ()
abbrev VectorValue (Element : Type u) (length : Nat) :=
  IndexedContainer.Examples.vector.Extension Element length

def listItems {Element : Type u} (value : ListValue Element) : List Element :=
  (IndexedContainer.Examples.listExtensionEquiv Element).symm value

def encodeListValue {Element : Type u} (encode : Element → Term)
    (value : ListValue Element) : Term := encodeList encode (listItems value)

def decodeListValue {Element : Type u} (decode : Term → Option Element) (term : Term) :
    Option (ListValue Element) :=
  (decodeList decode term).map (IndexedContainer.Examples.listExtensionEquiv Element)

@[simp] theorem listItems_length {Element : Type u} (value : ListValue Element) :
    (listItems value).length = value.1 := by
  exact List.length_ofFn

@[simp] theorem decodeListValue_encodeListValue {Element : Type u}
    (decode : Term → Option Element) (encode : Element → Term)
    (elementRoundTrip : ∀ value, decode (encode value) = some value)
    (value : ListValue Element) :
    decodeListValue decode (encodeListValue encode value) = some value := by
  simp [decodeListValue, encodeListValue, decodeList_encodeList decode encode elementRoundTrip,
    listItems]

theorem encodeListValue_decodeListValue {Element : Type u}
    (decode : Term → Option Element) (encode : Element → Term)
    (elementExact : ∀ term value, decode term = some value → encode value = term)
    (term : Term) (value : ListValue Element)
    (accepted : decodeListValue decode term = some value) :
    encodeListValue encode value = term := by
  obtain ⟨items, decoded, rfl⟩ := Option.map_eq_some_iff.mp accepted
  simpa [encodeListValue, listItems] using
    encodeList_decodeList decode encode elementExact term items decoded

def vectorAsList {Element : Type u} {length : Nat} (value : VectorValue Element length) :
    ListValue Element := ⟨length, value.2⟩

def listAsVector {Element : Type u} {length : Nat} (value : ListValue Element)
    (sameLength : value.1 = length) : VectorValue Element length :=
  ⟨(), fun position => value.2 (Fin.cast sameLength.symm position)⟩

@[simp] theorem vectorAsList_listAsVector {Element : Type u} {length : Nat}
    (value : ListValue Element) (sameLength : value.1 = length) :
    vectorAsList (listAsVector value sameLength) = value := by
  cases sameLength
  cases value
  rfl

@[simp] theorem listAsVector_vectorAsList {Element : Type u} {length : Nat}
    (value : VectorValue Element length) : listAsVector (vectorAsList value) rfl = value := by
  rcases value with ⟨shape, children⟩
  cases shape
  rfl

def encodeVectorValue {Element : Type u} {length : Nat} (encode : Element → Term)
    (value : VectorValue Element length) : Term := encodeListValue encode (vectorAsList value)

def decodeVectorValue {Element : Type u} (decode : Term → Option Element)
    (length : Nat) (term : Term) : Option (VectorValue Element length) := do
  let value ← decodeListValue decode term
  if sameLength : (show Nat from value.1) = length then some (listAsVector value sameLength) else none

@[simp] theorem decodeVectorValue_encodeVectorValue {Element : Type u}
    (decode : Term → Option Element) (encode : Element → Term)
    (elementRoundTrip : ∀ value, decode (encode value) = some value)
    {length : Nat} (value : VectorValue Element length) :
    decodeVectorValue decode length (encodeVectorValue encode value) = some value := by
  simp [decodeVectorValue, encodeVectorValue,
    decodeListValue_encodeListValue decode encode elementRoundTrip, vectorAsList]
  rcases value with ⟨shape, children⟩
  cases shape
  rfl

theorem encodeVectorValue_decodeVectorValue {Element : Type u}
    (decode : Term → Option Element) (encode : Element → Term)
    (elementExact : ∀ term value, decode term = some value → encode value = term)
    (length : Nat) (term : Term) (value : VectorValue Element length)
    (accepted : decodeVectorValue decode length term = some value) :
    encodeVectorValue encode value = term := by
  cases decoded : decodeListValue decode term with
  | none => simp [decodeVectorValue, decoded] at accepted
  | some listed =>
      by_cases sameLength : (show Nat from listed.1) = length
      · have same : listAsVector listed sameLength = value := by
          simpa [decodeVectorValue, decoded, sameLength] using accepted
        subst value
        exact (congrArg (encodeListValue encode)
          (vectorAsList_listAsVector listed sameLength)).trans
            (encodeListValue_decodeListValue decode encode elementExact term listed decoded)
      · simp [decodeVectorValue, decoded] at accepted
        obtain ⟨lengthEq, _⟩ := accepted
        exact (sameLength lengthEq).elim

/-- The decoder cannot change the declared output index to accommodate an
incorrect physical payload length. -/
theorem wrong_vector_length_refused {Element : Type u}
    (decode : Term → Option Element) (encode : Element → Term)
    (elementRoundTrip : ∀ value, decode (encode value) = some value)
    {actual : Nat} (value : VectorValue Element actual) (expected : Nat)
    (different : actual ≠ expected) :
    decodeVectorValue decode expected (encodeVectorValue encode value) = none := by
  simp [decodeVectorValue, encodeVectorValue,
    decodeListValue_encodeListValue decode encode elementRoundTrip, vectorAsList, different]

theorem list_wire_injective {Element : Type u}
    (decode : Term → Option Element) (encode : Element → Term)
    (elementRoundTrip : ∀ value, decode (encode value) = some value) :
    Function.Injective (encodeListValue encode) := by
  intro first second same
  have decoded := congrArg (decodeListValue decode) same
  rw [decodeListValue_encodeListValue decode encode elementRoundTrip,
    decodeListValue_encodeListValue decode encode elementRoundTrip] at decoded
  exact Option.some.inj decoded

theorem vector_wire_injective {Element : Type u}
    (decode : Term → Option Element) (encode : Element → Term)
    (elementRoundTrip : ∀ value, decode (encode value) = some value) {length : Nat} :
    Function.Injective (encodeVectorValue (length := length) encode) := by
  intro first second same
  have decoded := congrArg (decodeVectorValue decode length) same
  rw [decodeVectorValue_encodeVectorValue decode encode elementRoundTrip,
    decodeVectorValue_encodeVectorValue decode encode elementRoundTrip] at decoded
  exact Option.some.inj decoded

namespace Recursive

variable {Base : Type uBase} {Index : Base → Type uIndex}

/-- Serialize the complete fixed family, using the selected traversal order
at every constructor. The algebraic payloads are not executed by encoding. -/
def encodeFix
    (polynomial : IndexedPolynomial.{uBase, uIndex, uShape, uPosition} Base Index)
    (positions : ∀ base index, (shape : polynomial.Shape base index) →
      List (polynomial.Position shape))
    (encodeShape : ∀ base index, polynomial.Shape base index → Term)
    (base : Base) (index : Index base) (tree : IndexedPolynomial.Fix polynomial base index) : Term :=
  match tree with
  | .roll shape children =>
      .application "InductiveNode" [encodeShape base index shape,
        encodeList id ((positions base index shape).map fun position =>
          encodeFix polynomial positions encodeShape base _ (children position))]
termination_by structural tree

@[simp] theorem encodeFix_roll
    (polynomial : IndexedPolynomial.{uBase, uIndex, uShape, uPosition} Base Index)
    (positions : ∀ base index, (shape : polynomial.Shape base index) →
      List (polynomial.Position shape))
    (encodeShape : ∀ base index, polynomial.Shape base index → Term)
    {base : Base} {index : Index base} (shape : polynomial.Shape base index)
    (children : ∀ position, IndexedPolynomial.Fix polynomial base (polynomial.next shape position)) :
    encodeFix polynomial positions encodeShape base index (.roll shape children) =
      .application "InductiveNode" [encodeShape base index shape,
        encodeList id ((positions base index shape).map fun position =>
          encodeFix polynomial positions encodeShape base _ (children position))] := rfl

/-- Executable structural encoding agrees with the independent generated
recursor's semantic action. -/
theorem encodeFix_eq_fold
    (polynomial : IndexedPolynomial.{uBase, uIndex, uShape, uPosition} Base Index)
    (positions : ∀ base index, (shape : polynomial.Shape base index) →
      List (polynomial.Position shape))
    (encodeShape : ∀ base index, polynomial.Shape base index → Term)
    (base : Base) (index : Index base) (tree : IndexedPolynomial.Fix polynomial base index) :
    encodeFix polynomial positions encodeShape base index tree =
      IndexedPolynomial.Fix.fold polynomial (carrier := fun _ _ => Term) (fun current currentIndex layer =>
        Term.application "InductiveNode" [encodeShape current currentIndex layer.1,
          encodeList id ((positions current currentIndex layer.1).map layer.2)]) base index tree := by
  induction tree with
  | @roll index shape children ih =>
      rw [encodeFix_roll, IndexedPolynomial.Fix.fold_roll]
      have childrenSame := funext ih
      exact congrArg (fun values => Term.application "InductiveNode"
        [encodeShape base index shape, encodeList id ((positions base index shape).map values)]) childrenSame

/-- The wire distinguishes the complete semantic tree when shape encoding is
faithful and the traversal visits every recursive position. -/
theorem encodeFix_injective
    (polynomial : IndexedPolynomial.{uBase, uIndex, uShape, uPosition} Base Index)
    (positions : ∀ base index, (shape : polynomial.Shape base index) →
      List (polynomial.Position shape))
    (complete : ∀ base index (shape : polynomial.Shape base index) position,
      position ∈ positions base index shape)
    (encodeShape : ∀ base index, polynomial.Shape base index → Term)
    (shapeInjective : ∀ base index, Function.Injective (encodeShape base index))
    (base : Base) (index : Index base) :
    Function.Injective (encodeFix polynomial positions encodeShape base index) := by
  intro first
  induction first with
  | @roll index shape children ih =>
      intro second same
      cases second with
      | roll otherShape otherChildren =>
          simp only [encodeFix_roll, Term.application.injEq, List.cons.injEq,
            and_true, true_and] at same
          have shapeSame := shapeInjective base index same.1
          subst otherShape
          have childCodes := encodeList_injective id (fun _ _ eq => eq) same.2
          have childrenSame : children = otherChildren := by
            funext position
            exact ih position
              (List.map_inj_left.mp childCodes position (complete base index shape position))
          subst otherChildren
          rfl

end Recursive

namespace Controls

def boolTerm : Bool → Term
  | false => .symbol "False"
  | true => .symbol "True"

def decodeBool : Term → Option Bool
  | .symbol "False" => some false
  | .symbol "True" => some true
  | _ => none

theorem bool_roundtrip (value : Bool) : decodeBool (boolTerm value) = some value := by
  cases value <;> rfl

def twoValues : VectorValue Bool 2 := ⟨(), fun position => position.val == 1⟩

def twoWire : Term := encodeVectorValue boolTerm twoValues

theorem twoWire_exact : twoWire = .application "LCons"
    [.symbol "False", .application "LCons" [.symbol "True", .symbol "LNil"]] := rfl

theorem two_roundtrip : decodeVectorValue decodeBool 2 twoWire = some twoValues :=
  decodeVectorValue_encodeVectorValue decodeBool boolTerm bool_roundtrip twoValues

theorem wrong_index_refused : decodeVectorValue decodeBool 3 twoWire = none :=
  wrong_vector_length_refused decodeBool boolTerm bool_roundtrip twoValues 3 (by decide)

def verdicts : List (String × Bool) :=
  [("container vector retains both Boolean payloads", (decodeVectorValue decodeBool 2 twoWire).isSome),
   ("container vector refuses a changed output index", (decodeVectorValue decodeBool 3 twoWire).isNone),
   ("container vector refuses a dropped child", (decodeVectorValue decodeBool 2
      (encodeList boolTerm [false])).isNone),
   ("container vector retains repeated children", (decodeVectorValue decodeBool 2
      (encodeList boolTerm [false, false])).isSome),
   ("container vector refuses an ill-typed payload", (decodeVectorValue decodeBool 2
      (encodeList id [.symbol "False", .natural 1])).isNone),
   ("container list refuses malformed cons arity", (decodeListValue decodeBool
      (.application "LCons" [.symbol "True"])).isNone),
   ("container list distinguishes a string from the nil symbol", (decodeListValue decodeBool
      (.string "LNil")).isNone),
   ("container vector admits the zero-length case", (decodeVectorValue decodeBool 0
      (.symbol "LNil")).isSome)]

theorem all_verdicts : verdicts.all (fun entry => entry.2) = true := by decide +kernel

end Controls

#print axioms decodeListValue_encodeListValue
#print axioms encodeListValue_decodeListValue
#print axioms decodeVectorValue_encodeVectorValue
#print axioms encodeVectorValue_decodeVectorValue
#print axioms wrong_vector_length_refused
#print axioms Controls.two_roundtrip
#print axioms Controls.wrong_index_refused
#print axioms Controls.all_verdicts
#print axioms Recursive.encodeFix_injective
#print axioms Recursive.encodeFix_eq_fold

end Mettapedia.GSLT.LanguageDef.IndexedContainerWire
