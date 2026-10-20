import Mettapedia.TypeTheory.NaturalDependentTransport
import Mettapedia.TypeTheory.IndexedPolynomial

/-!
# Length-indexed vectors under a natural-number representation

The fibres are the existing indexed-polynomial vectors, reindexed along the
inverse natural-number equivalence. Their total space retains both the length
and the vector. Dependent elimination below retains a motive over that whole
space; its constructor equations are semantic equalities after transport.

The parity counterexample rules out replacing a representation equivalence by
a many-to-one observation when dependent fibres must be preserved.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.NaturalVectorTransport

universe u v w x

open IndexedPolynomial
open NaturalAlgebra

variable {Carrier : Type u} {Element : Type v}

abbrev Family (representation : Nat ≃ Carrier) (Element : Type v) (length : Carrier) :=
  VectorExample.VectorP Element (representation.symm length)

abbrev Total (representation : Nat ≃ Carrier) (Element : Type v) :=
  Σ length, Family representation Element length

/-- Reindex the length while retaining the entire vector fibre. -/
def totalEquiv (representation : Nat ≃ Carrier) :
    (Σ length, VectorExample.VectorP Element length) ≃ Total representation Element :=
  Equiv.sigmaCongrLeft' representation

def nil (representation : Nat ≃ Carrier) : Total representation Element :=
  totalEquiv representation ⟨0, VectorExample.nil⟩

def cons (representation : Nat ≃ Carrier) (head : Element)
    (tail : Total representation Element) : Total representation Element :=
  let source := (totalEquiv representation).symm tail
  totalEquiv representation ⟨source.1 + 1, VectorExample.cons head source.2⟩

@[simp] theorem cons_encode (representation : Nat ≃ Carrier) (head : Element)
    (length : Nat) (tail : VectorExample.VectorP Element length) :
    cons representation head (totalEquiv representation ⟨length, tail⟩) =
      totalEquiv representation ⟨length + 1, VectorExample.cons head tail⟩ := by
  unfold cons
  rw [Equiv.symm_apply_apply]

@[simp] theorem nil_length {algebra : Algebra Carrier}
    (representation : Iso natAlgebra algebra) :
    (nil representation.toEquiv (Element := Element)).1 = algebra.zero :=
  representation.map_zero

@[simp] theorem cons_length {algebra : Algebra Carrier}
    (representation : Iso natAlgebra algebra) (head : Element)
    (tail : Total representation.toEquiv Element) :
    (cons representation.toEquiv head tail).1 = algebra.succ tail.1 := by
  change representation.toEquiv (natAlgebra.succ (representation.toEquiv.symm tail.1)) = _
  rw [representation.map_succ, Equiv.apply_symm_apply]

private theorem transport_section {Index : Sort u} (family : Index → Sort v)
    (dependentFunction : ∀ index, family index) {first second : Index} (same : first = second) :
    same ▸ dependentFunction first = dependentFunction second := by
  cases same
  rfl

private theorem transport_reindexed {Source : Sort u} {Target : Sort v}
    (family : Target → Sort w) (index : Source → Target)
    (dependentFunction : ∀ value, family (index value))
    {first second : Source} (same : first = second) :
    congrArg index same ▸ dependentFunction first = dependentFunction second := by
  cases same
  rfl

noncomputable def alongVectors (representation : Nat ≃ Carrier)
    (motive : Total representation Element → Sort w)
    (nilCase : motive (nil representation))
    (consCase : ∀ head tail, motive tail → motive (cons representation head tail)) :
    ∀ length (vector : VectorExample.VectorP Element length),
      motive (totalEquiv representation ⟨length, vector⟩) :=
  VectorExample.eliminate (fun length vector =>
    motive (totalEquiv representation ⟨length, vector⟩)) nilCase
    (fun length head tail previous =>
      cons_encode representation head length tail ▸
        consCase head (totalEquiv representation ⟨length, tail⟩) previous)

/-- Eliminate a represented vector with a motive depending on its represented
length and its complete value. -/
noncomputable def eliminate (representation : Nat ≃ Carrier)
    (motive : Total representation Element → Sort w)
    (nilCase : motive (nil representation))
    (consCase : ∀ head tail, motive tail → motive (cons representation head tail))
    (vector : Total representation Element) : motive vector :=
  (totalEquiv representation).apply_symm_apply vector ▸
    alongVectors representation motive nilCase consCase
      ((totalEquiv representation).symm vector).1
      ((totalEquiv representation).symm vector).2

@[simp] theorem eliminate_encode (representation : Nat ≃ Carrier)
    (motive : Total representation Element → Sort w)
    (nilCase : motive (nil representation))
    (consCase : ∀ head tail, motive tail → motive (cons representation head tail))
    (length : Nat) (vector : VectorExample.VectorP Element length) :
    eliminate representation motive nilCase consCase (totalEquiv representation ⟨length, vector⟩) =
      alongVectors representation motive nilCase consCase length vector :=
  transport_reindexed motive (totalEquiv representation)
    (fun pair => alongVectors representation motive nilCase consCase pair.1 pair.2)
    ((totalEquiv representation).symm_apply_apply ⟨length, vector⟩)

@[simp] theorem eliminate_nil (representation : Nat ≃ Carrier)
    (motive : Total representation Element → Sort w)
    (nilCase : motive (nil representation))
    (consCase : ∀ head tail, motive tail → motive (cons representation head tail)) :
    eliminate representation motive nilCase consCase (nil representation) = nilCase := by
  unfold nil
  rw [eliminate_encode]
  exact VectorExample.eliminate_nil _ _ _

@[simp] theorem eliminate_cons (representation : Nat ≃ Carrier)
    (motive : Total representation Element → Sort w)
    (nilCase : motive (nil representation))
    (consCase : ∀ head tail, motive tail → motive (cons representation head tail))
    (head : Element) (tail : Total representation Element) :
    eliminate representation motive nilCase consCase (cons representation head tail) =
      consCase head tail (eliminate representation motive nilCase consCase tail) := by
  obtain ⟨⟨length, vector⟩, rfl⟩ := (totalEquiv representation).surjective tail
  have equation := transport_section motive
    (eliminate representation motive nilCase consCase)
    (cons_encode representation head length vector)
  rw [eliminate_encode] at equation
  rw [eliminate_encode]
  have computation := VectorExample.eliminate_cons
    (fun length vector => motive (totalEquiv representation ⟨length, vector⟩))
    nilCase
    (fun length head tail previous => cons_encode representation head length tail ▸
      consCase head (totalEquiv representation ⟨length, tail⟩) previous)
    length head vector
  change alongVectors representation motive nilCase consCase _ _ = _ at computation
  rw [computation] at equation
  exact eq_of_heq ((eqRec_heq _ _).symm.trans ((heq_of_eq equation).trans (eqRec_heq _ _)))

/-- The constructor equations determine the full dependent vector section. -/
theorem eliminate_unique (representation : Nat ≃ Carrier)
    (motive : Total representation Element → Sort w)
    (nilCase : motive (nil representation))
    (consCase : ∀ head tail, motive tail → motive (cons representation head tail))
    (other : ∀ vector, motive vector)
    (other_nil : other (nil representation) = nilCase)
    (other_cons : ∀ head tail,
      other (cons representation head tail) = consCase head tail (other tail)) :
    other = eliminate representation motive nilCase consCase := by
  funext vector
  apply eliminate representation (fun vector =>
    other vector = eliminate representation motive nilCase consCase vector)
  · rw [other_nil, eliminate_nil]
  · intro head tail hypothesis
    rw [other_cons, eliminate_cons, hypothesis]

/-- The same indexed vector carried by a different natural-number representation. -/
def changeRepresentation {Other : Type w} (first : Nat ≃ Carrier) (second : Nat ≃ Other) :
    Total first Element ≃ Total second Element :=
  (totalEquiv first).symm.trans (totalEquiv second)

@[simp] theorem changeRepresentation_nil {Other : Type w}
    (first : Nat ≃ Carrier) (second : Nat ≃ Other) :
    changeRepresentation first second (nil first (Element := Element)) = nil second := by
  change totalEquiv second ((totalEquiv first).symm (totalEquiv first _)) = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem changeRepresentation_cons {Other : Type w}
    (first : Nat ≃ Carrier) (second : Nat ≃ Other) (head : Element)
    (tail : Total first Element) :
    changeRepresentation first second (cons first head tail) =
      cons second head (changeRepresentation first second tail) := by
  obtain ⟨⟨length, vector⟩, rfl⟩ := (totalEquiv first).surjective tail
  rw [cons_encode]
  change totalEquiv second ((totalEquiv first).symm (totalEquiv first _)) =
    cons second head (totalEquiv second ((totalEquiv first).symm (totalEquiv first _)))
  simp only [Equiv.symm_apply_apply, cons_encode]

/-- Natural reindexing preserves the vector's dependent eliminator, not merely
its untyped erased list. -/
theorem eliminate_changeRepresentation {Other : Type x}
    (first : Nat ≃ Carrier) (second : Nat ≃ Other)
    (motive : Total second Element → Sort w)
    (nilCase : motive (nil second))
    (consCase : ∀ head tail, motive tail → motive (cons second head tail))
    (vector : Total first Element) :
    eliminate first (fun vector => motive (changeRepresentation first second vector))
      ((changeRepresentation_nil first second).symm ▸ nilCase)
      (fun head tail previous => (changeRepresentation_cons first second head tail).symm ▸
        consCase head (changeRepresentation first second tail) previous) vector =
    eliminate second motive nilCase consCase (changeRepresentation first second vector) := by
  have nilLaw :
      eliminate second motive nilCase consCase
        (changeRepresentation first second (nil first)) =
      (changeRepresentation_nil first second).symm ▸ nilCase := by
    have equation := transport_section motive (eliminate second motive nilCase consCase)
      (changeRepresentation_nil first second).symm
    rw [eliminate_nil] at equation
    exact equation.symm
  have consLaw : ∀ head tail,
      eliminate second motive nilCase consCase
        (changeRepresentation first second (cons first head tail)) =
      (changeRepresentation_cons first second head tail).symm ▸
        consCase head (changeRepresentation first second tail)
          (eliminate second motive nilCase consCase (changeRepresentation first second tail)) := by
    intro head tail
    have equation := transport_section motive (eliminate second motive nilCase consCase)
      (changeRepresentation_cons first second head tail).symm
    rw [eliminate_cons] at equation
    exact equation.symm
  exact (congrFun (eliminate_unique first
    (fun vector => motive (changeRepresentation first second vector))
    ((changeRepresentation_nil first second).symm ▸ nilCase)
    (fun head tail previous => (changeRepresentation_cons first second head tail).symm ▸
      consCase head (changeRepresentation first second tail) previous)
    (fun vector => eliminate second motive nilCase consCase
      (changeRepresentation first second vector)) nilLaw consLaw) vector).symm

noncomputable def erase (representation : Nat ≃ Carrier)
    (vector : Total representation Element) : ListExample.ListP Element :=
  eliminate representation (fun _ => ListExample.ListP Element)
    ListExample.nil (fun head _ previous => ListExample.cons head previous) vector

@[simp] theorem erase_nil (representation : Nat ≃ Carrier) :
    erase representation (nil representation (Element := Element)) = ListExample.nil := by
  simp [erase]

@[simp] theorem erase_cons (representation : Nat ≃ Carrier) (head : Element)
    (tail : Total representation Element) :
    erase representation (cons representation head tail) =
      ListExample.cons head (erase representation tail) := by
  simp [erase]

theorem erase_changeRepresentation {Other : Type w}
    (first : Nat ≃ Carrier) (second : Nat ≃ Other) (vector : Total first Element) :
    erase second (changeRepresentation first second vector) = erase first vector := by
  apply eliminate first (fun vector =>
    erase second (changeRepresentation first second vector) = erase first vector)
  · simp
  · intro head tail hypothesis
    simpa using congrArg (ListExample.cons head) hypothesis

theorem changeRepresentation_length {Other : Type w}
    (first : Nat ≃ Carrier) (second : Nat ≃ Other) (vector : Total first Element) :
    (changeRepresentation first second vector).1 = second (first.symm vector.1) := rfl

/-- Every value retains exactly its represented length under vector erasure. -/
theorem erase_length (representation : Nat ≃ Carrier) (vector : Total representation Element) :
    representation (ListExample.length (erase representation vector)) = vector.1 := by
  apply eliminate representation (fun vector =>
    representation (ListExample.length (erase representation vector)) = vector.1)
  · rw [erase_nil]
    rfl
  · intro head tail previous
    simp only [erase_cons, ListExample.length_cons]
    change representation (ListExample.length (erase representation tail) + 1) =
      representation (representation.symm tail.1 + 1)
    apply congrArg representation
    simpa using congrArg Nat.succ
      (congrArg representation.symm previous)

namespace Controls

/-- An observation merging even lengths cannot preserve every vector fibre. -/
theorem parity_cannot_transport_empty_vectors :
    ¬ Nonempty (Σ (family : Bool → Type),
      ∀ length, VectorExample.VectorP Empty length ≃ family (length % 2 == 0)) := by
  rintro ⟨⟨family, comparison⟩⟩
  have atZero : family true := comparison 0 VectorExample.nil
  have atTwo : VectorExample.VectorP Empty 2 := (comparison 2).symm atZero
  have impossible := VectorExample.empty_vector_length_zero 2 atTwo
  contradiction

theorem duplicated_elements_retained (representation : Nat ≃ Carrier) (element : Element) :
    erase representation (cons representation element
      (cons representation element (nil representation))) =
    ListExample.cons element (ListExample.cons element ListExample.nil) := by
  simp

end Controls

end Mettapedia.TypeTheory.NaturalVectorTransport
