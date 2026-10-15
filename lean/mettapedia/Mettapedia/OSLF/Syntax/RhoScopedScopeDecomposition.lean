import Mettapedia.OSLF.Syntax.RhoScopedParallelInventory
import Mettapedia.OSLF.Syntax.RhoFiniteQuotationOrigins
import Mettapedia.Algebra.SupportSeparatedDecomposition

/-!
# Scope decomposition on the complete scoped rho equation quotient

The name eta equation prevents quotation from being injective on all
process classes. Canonical body readback is faithful on non-drop classes.
Together with separation of complete component inventories, this earns
unique decomposition of quoted parallel scopes in every source context.

An independently supplied component classifier computes the two parts.
Its admission conditions concern every member of the scope extensions.
The existential scope semantics is defined independently of that readback.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoScopedScopeDecomposition

open RhoSchema RhoQuotationClassFibres RhoScopedParallelInventory
open RhoFiniteQuotationOrigins RhoSchema.IntrinsicEncoding
open RhoIntrinsicReadback RhoCanonicalNamePairs
open Mettapedia.Algebra

variable {context : Ctx sig}

/-- This canonical process body is not erased by the source name eta equation. -/
def Exposed (process : Process context) : Prop :=
  dropBody (encodeEquationClass process) = none

theorem exposed_iff_not_drop (process : Process context) :
    Exposed process ↔ ¬ ∃ name : Name context, process = drop name := by
  constructor
  · rintro exposed ⟨name, rfl⟩
    unfold Exposed at exposed
    rw [encode_drop] at exposed
    cases exposed
  · intro notDrop
    cases result : dropBody (encodeEquationClass process) with
    | none => exact result
    | some child =>
      have shape := dropBody_shape result
      have decoded := read_encoded_equation_class process
      change readProcessClass context (encodeEquationClass process) = some process at decoded
      rw [shape, readProcessClass_drop] at decoded
      obtain ⟨childName, _childReadout, same⟩ := Option.map_eq_some_iff.mp decoded
      exact False.elim (notDrop ⟨childName, same.symm⟩)

theorem exposed_of_component_count_ne_one (process : Process context)
    (count : (read process).card ≠ 1) : Exposed process := by
  apply (exposed_iff_not_drop process).mpr
  rintro ⟨name, rfl⟩
  apply count
  have same := congrArg Multiset.card (values_read (drop name))
  rw [RhoIntrinsicCanonicalBag.drop_components] at same
  simpa only [values, Multiset.card_map, Multiset.card_singleton] using same

theorem exposed_join_of_nonempty {first second : Process context}
    (firstNonempty : 0 < (read first).card) (secondNonempty : 0 < (read second).card) :
    Exposed (join first second) := by
  apply exposed_of_component_count_ne_one
  rw [read_join, Multiset.card_add]
  omega

theorem exposed_body_readback {process : Process context} (exposed : Exposed process) :
    bodyOrigin context (encodeEquationClass (quote process)) = some process := by
  apply bodyOrigin_of_not_drop process
  intro name same
  unfold Exposed at exposed
  rw [same] at exposed
  cases exposed

/-- Faithfulness is derived from the actual canonical decoder. -/
theorem quote_injective_on_exposed {first second : Process context}
    (firstExposed : Exposed first) (secondExposed : Exposed second)
    (same : quote first = quote second) : first = second := by
  have firstRead := exposed_body_readback firstExposed
  have secondRead := exposed_body_readback secondExposed
  rw [same, secondRead] at firstRead
  exact (Option.some.inj firstRead).symm

def inventoryScope (scope : Process context → Prop) : Multiset (Prime context) → Prop :=
  fun inventory => scope (write inventory)

theorem inventoryScope_read (scope : Process context → Prop) (process : Process context) :
    inventoryScope scope (read process) ↔ scope process := by
  simp only [inventoryScope, write_read]

/-- Separation uses complete components, including components with empty name support. -/
def ComponentSeparated (left right : Process context → Prop) : Prop :=
  SupportSeparatedDecomposition.GradeZero (inventoryScope left) (inventoryScope right)

/-- All admitted composite bodies remain available to canonical name readback. -/
def ExposedComposites (left right : Process context → Prop) : Prop :=
  ∀ first second, left first → right second → Exposed (join first second)

theorem exposedComposites_of_nonempty {left right : Process context → Prop}
    (firstNonempty : ∀ process, left process → 0 < (read process).card)
    (secondNonempty : ∀ process, right process → 0 < (read process).card) :
    ExposedComposites left right := by
  intro first second firstAdmitted secondAdmitted
  exact exposed_join_of_nonempty (firstNonempty first firstAdmitted)
    (secondNonempty second secondAdmitted)

/-- Scope membership retains actual process classes and their quotation equation. -/
def Composite (left right : Process context → Prop) (name : Name context) : Prop :=
  ∃ first second, left first ∧ right second ∧ quote (join first second) = name

theorem process_split_unique {left right : Process context → Prop}
    (separated : ComponentSeparated left right)
    {first second first' second' : Process context}
    (firstAdmitted : left first) (secondAdmitted : right second)
    (firstAdmitted' : left first') (secondAdmitted' : right second')
    (same : join first second = join first' second') :
    first = first' ∧ second = second' := by
  let : DecidableEq (Prime context) := fun first second =>
    decidable_of_iff (first.val = second.val) Subtype.ext_iff.symm
  have sameInventory := congrArg read same
  rw [read_join, read_join] at sameInventory
  obtain ⟨sameFirst, sameSecond⟩ := SupportSeparatedDecomposition.split_unique separated
    ((inventoryScope_read left first).mpr firstAdmitted)
    ((inventoryScope_read right second).mpr secondAdmitted)
    ((inventoryScope_read left first').mpr firstAdmitted')
    ((inventoryScope_read right second').mpr secondAdmitted') sameInventory
  exact ⟨read_injective context sameFirst, read_injective context sameSecond⟩

theorem quoted_split_unique {left right : Process context → Prop}
    (separated : ComponentSeparated left right) (exposed : ExposedComposites left right)
    {first second first' second' : Process context}
    (firstAdmitted : left first) (secondAdmitted : right second)
    (firstAdmitted' : left first') (secondAdmitted' : right second')
    (same : quote (join first second) = quote (join first' second')) :
    first = first' ∧ second = second' :=
  process_split_unique separated firstAdmitted secondAdmitted firstAdmitted' secondAdmitted'
    (quote_injective_on_exposed (exposed _ _ firstAdmitted secondAdmitted)
      (exposed _ _ firstAdmitted' secondAdmitted') same)

theorem composite_unique {left right : Process context → Prop}
    (separated : ComponentSeparated left right) (exposed : ExposedComposites left right)
    {name : Name context} (member : Composite left right name) :
    ∃! pair : Process context × Process context,
      left pair.1 ∧ right pair.2 ∧ quote (join pair.1 pair.2) = name := by
  obtain ⟨first, second, firstAdmitted, secondAdmitted, same⟩ := member
  refine ⟨(first, second), ⟨firstAdmitted, secondAdmitted, same⟩, ?_⟩
  rintro ⟨first', second'⟩ ⟨firstAdmitted', secondAdmitted', same'⟩
  obtain ⟨sameFirst, sameSecond⟩ := quoted_split_unique separated exposed
    firstAdmitted' secondAdmitted' firstAdmitted secondAdmitted (same'.trans same.symm)
  exact Prod.ext sameFirst sameSecond

def leftPart (classify : Prime context → Bool) (process : Process context) : Process context :=
  write (SupportSeparatedDecomposition.leftPart classify (read process))

def rightPart (classify : Prime context → Bool) (process : Process context) : Process context :=
  write (SupportSeparatedDecomposition.rightPart classify (read process))

theorem parts_join (classify : Prime context → Bool) (process : Process context) :
    join (leftPart classify process) (rightPart classify process) = process := by
  rw [leftPart, rightPart, ← write_add, SupportSeparatedDecomposition.parts_add, write_read]

def LeftSupported (classify : Prime context → Bool) (left : Process context → Prop) : Prop :=
  SupportSeparatedDecomposition.LeftSupported classify (inventoryScope left)

def RightSupported (classify : Prime context → Bool) (right : Process context → Prop) : Prop :=
  SupportSeparatedDecomposition.RightSupported classify (inventoryScope right)

theorem classified_component_separation {classify : Prime context → Bool}
    {left right : Process context → Prop} (first : LeftSupported classify left)
    (second : RightSupported classify right) : ComponentSeparated left right :=
  SupportSeparatedDecomposition.classified_gradeZero first second

theorem leftPart_join {classify : Prime context → Bool}
    {left right : Process context → Prop} (first : LeftSupported classify left)
    (second : RightSupported classify right) {a b : Process context}
    (admittedA : left a) (admittedB : right b) : leftPart classify (join a b) = a := by
  rw [leftPart, read_join, SupportSeparatedDecomposition.leftPart_split first second
    ((inventoryScope_read left a).mpr admittedA)
    ((inventoryScope_read right b).mpr admittedB), write_read]

theorem rightPart_join {classify : Prime context → Bool}
    {left right : Process context → Prop} (first : LeftSupported classify left)
    (second : RightSupported classify right) {a b : Process context}
    (admittedA : left a) (admittedB : right b) : rightPart classify (join a b) = b := by
  rw [rightPart, read_join, SupportSeparatedDecomposition.rightPart_split first second
    ((inventoryScope_read left a).mpr admittedA)
    ((inventoryScope_read right b).mpr admittedB), write_read]

/-- Body decoding and a single component partition give a candidate, before scope testing. -/
def readPair (classify : Prime context → Bool) (name : Name context) :
    Option (Process context × Process context) :=
  (bodyOrigin context (encodeEquationClass name)).map
    (fun body => (leftPart classify body, rightPart classify body))

theorem readPair_of_member {classify : Prime context → Bool}
    {left right : Process context → Prop} (first : LeftSupported classify left)
    (second : RightSupported classify right) (exposed : ExposedComposites left right)
    {a b : Process context} (admittedA : left a) (admittedB : right b) :
    readPair classify (quote (join a b)) = some (a, b) := by
  rw [readPair, exposed_body_readback (exposed _ _ admittedA admittedB)]
  simp only [Option.map_some, leftPart_join first second admittedA admittedB,
    rightPart_join first second admittedA admittedB]

theorem readPair_sound {classify : Prime context → Bool}
    {name : Name context} {pair : Process context × Process context}
    (readout : readPair classify name = some pair) :
    quote (join pair.1 pair.2) = name := by
  obtain ⟨body, decoded, same⟩ := Option.map_eq_some_iff.mp readout
  cases same
  rw [parts_join]
  exact bodyOrigin_sound decoded

/-- The independently defined existential semantics agrees with testing the decoded parts. -/
theorem composite_iff_readPair {classify : Prime context → Bool}
    {left right : Process context → Prop} (first : LeftSupported classify left)
    (second : RightSupported classify right) (exposed : ExposedComposites left right)
    (name : Name context) :
    Composite left right name ↔
      ∃ pair, readPair classify name = some pair ∧ left pair.1 ∧ right pair.2 := by
  constructor
  · rintro ⟨a, b, admittedA, admittedB, rfl⟩
    exact ⟨(a, b), readPair_of_member first second exposed admittedA admittedB,
      admittedA, admittedB⟩
  · rintro ⟨pair, readout, admittedA, admittedB⟩
    exact ⟨pair.1, pair.2, admittedA, admittedB, readPair_sound readout⟩

end Mettapedia.OSLF.Binding.RhoScopedScopeDecomposition
