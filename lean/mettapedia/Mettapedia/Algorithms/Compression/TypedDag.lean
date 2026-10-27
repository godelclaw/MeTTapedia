import Mettapedia.Algorithms.Compression.CompactDag
import Mathlib.Data.List.Forall2

/-!
# Checked sorts along chronological DAG execution

The static algorithm checks actual earlier-reference types against a decoded
operator contract. Runtime leaves and results inspect an independent value-kind
function; declared sorts do not make an opaque value into a tensor. Operators
are partial and need not themselves return a correctly sorted value.

The representation and runtime traversal are the existing CompactDag records
and fold. A failed value is a node result, not traversal failure. Successful
inference supplies every operand contract when a kernel is actually invoked.
This is an algorithm-level interface, not verification of a particular decoder,
physical tensor observer, shape policy or C kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Compression.TypedDag

open KolmogorovComplexity CompactDag

structure Contract (Label : Type) where
  inputs : List Label
  output : Label
  deriving DecidableEq, Repr

variable {Label Value : Type} [DecidableEq Label]

def checked (kind : Value → Option Label) (expected : Label) : Option Value → Option Value
  | none => none
  | some value => if kind value = some expected then some value else none

def Fits (kind : Value → Option Label) (expected : Label) (value : Option Value) : Prop :=
  ∀ actual, value = some actual → kind actual = some expected

def Aligned (kind : Value → Option Label) (types : List Label) (values : List (Option Value)) : Prop :=
  List.Forall₂ (Fits kind) types values

theorem checked_fits (kind : Value → Option Label) (expected : Label) (value : Option Value) :
    Fits kind expected (checked kind expected value) := by
  intro actual found
  cases value with
  | none => simp [checked] at found
  | some value =>
      simp only [checked] at found
      split at found
      · rename_i same
        cases Option.some.inj found
        exact same
      · cases found

omit [DecidableEq Label] in
theorem aligned_get (kind : Value → Option Label) {types : List Label}
    {values : List (Option Value)} (aligned : Aligned kind types values)
    (index : Nat) (expected : Label) (found : types[index]? = some expected) :
    ∃ value, values[index]? = some value ∧ Fits kind expected value := by
  induction aligned generalizing index expected with
  | nil => simp at found
  | cons head tail ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst expected
          exact ⟨_, rfl, head⟩
      | succ index =>
          exact ih index expected (by simpa using found)

omit [DecidableEq Label] in
theorem gather_aligned (kind : Value → Option Label) {types selected : List Label}
    {values : List (Option Value)} (aligned : Aligned kind types values)
    (references : List Nat) (found : gather types references = some selected) :
    ∃ arguments, gather values references = some arguments ∧ Aligned kind selected arguments := by
  induction references generalizing selected with
  | nil =>
      cases Option.some.inj found
      exact ⟨[], rfl, .nil⟩
  | cons index rest ih =>
      cases first : types[index]? with
      | none => simp [gather, first] at found
      | some expected =>
          cases later : gather types rest with
          | none => simp [gather, first, later] at found
          | some tail =>
              simp [gather, first, later] at found
              subst selected
              obtain ⟨value, valueFound, agrees⟩ := aligned_get kind aligned index expected first
              obtain ⟨arguments, argumentsFound, alignedTail⟩ := ih later
              exact ⟨value :: arguments, by simp [gather, valueFound, argumentsFound], .cons agrees alignedTail⟩

def arguments : List (Option Value) → Option (List Value)
  | [] => some []
  | none :: _ => none
  | some first :: rest => (arguments rest).map (first :: ·)

omit [DecidableEq Label] in
theorem arguments_sorted (kind : Value → Option Label) {types : List Label}
    {values : List (Option Value)} (aligned : Aligned kind types values)
    (actual : List Value) (found : arguments values = some actual) :
    actual.map kind = types.map some := by
  induction aligned generalizing actual with
  | nil => cases Option.some.inj found; rfl
  | @cons expected value types values fits tail ih =>
      cases value with
      | none => simp [arguments] at found
      | some value =>
          cases later : arguments values with
          | none => simp [arguments, later] at found
          | some rest =>
              simp [arguments, later] at found
              subst actual
              simp [fits value rfl, ih rest later]

def inferRecord (leafType : BinString → Option Label)
    (contract : BinString → Option (Contract Label)) (types : List Label) : Record → Option Label
  | .leaf bytes => leafType bytes
  | .node tag references => do
      let declaration ← contract tag
      let inputs ← gather types references
      if inputs = declaration.inputs then some declaration.output else none

def inferRecords (leafType : BinString → Option Label)
    (contract : BinString → Option (Contract Label)) : List Record → List Label → Option (List Label)
  | [], types => some types
  | record :: rest, types => do
      let output ← inferRecord leafType contract types record
      inferRecords leafType contract rest (types ++ [output])

def leafValue (kind : Value → Option Label) (leafType : BinString → Option Label)
    (fetch : BinString → Option Value) (bytes : BinString) : Option Value :=
  (leafType bytes).bind (fun expected => checked kind expected (fetch bytes))

def nodeValue (kind : Value → Option Label) (contract : BinString → Option (Contract Label))
    (kernel : BinString → List Value → Option Value)
    (tag : BinString) (values : List (Option Value)) : Option Value := do
  let declaration ← contract tag
  let inputs ← arguments values
  checked kind declaration.output (kernel tag inputs)

omit [DecidableEq Label] in
/-- Static earlier-reference checks establish the actual operand kinds even
though the runtime algebra does not redundantly recheck its input sorts. -/
theorem operator_arguments_sorted (kind : Value → Option Label)
    {types : List Label} {values selected : List (Option Value)}
    (aligned : Aligned kind types values) (references : List Nat) (expected : List Label)
    (typed : gather types references = some expected)
    (read : gather values references = some selected) (actual : List Value)
    (ready : arguments selected = some actual) :
    actual.map kind = expected.map some := by
  obtain ⟨found, same, agrees⟩ := gather_aligned kind aligned references typed
  have identical : found = selected := Option.some.inj (same.symm.trans read)
  subst found
  exact arguments_sorted kind agrees actual ready

theorem record_sound (kind : Value → Option Label) (leafType : BinString → Option Label)
    (contract : BinString → Option (Contract Label)) (fetch : BinString → Option Value)
    (kernel : BinString → List Value → Option Value) {types : List Label}
    {values : List (Option Value)} (aligned : Aligned kind types values)
    (record : Record) (expected : Label) (typed : inferRecord leafType contract types record = some expected) :
    ∃ result, CompactDag.interpret (leafValue kind leafType fetch) (nodeValue kind contract kernel)
        values record = some result ∧ Fits kind expected result := by
  cases record with
  | leaf bytes =>
      simp only [inferRecord] at typed
      refine ⟨leafValue kind leafType fetch bytes, rfl, ?_⟩
      simpa only [leafValue, typed, Option.bind_some] using checked_fits kind expected (fetch bytes)
  | node tag references =>
      cases declaration : contract tag with
      | none => simp [inferRecord, declaration] at typed
      | some signature =>
          cases selected : gather types references with
          | none => simp [inferRecord, declaration, selected] at typed
          | some inputTypes =>
              by_cases same : inputTypes = signature.inputs
              · simp [inferRecord, declaration, selected, same] at typed
                subst expected
                obtain ⟨inputs, read, _agrees⟩ := gather_aligned kind aligned references selected
                refine ⟨nodeValue kind contract kernel tag inputs, by simp [CompactDag.interpret, read], ?_⟩
                cases ready : arguments inputs with
                | none => simp [nodeValue, declaration, ready, Fits]
                | some actual =>
                    simpa [nodeValue, declaration, ready] using
                      checked_fits kind signature.output (kernel tag actual)
              · simp [inferRecord, declaration, selected, same] at typed

theorem inferRecords_sound (kind : Value → Option Label) (leafType : BinString → Option Label)
    (contract : BinString → Option (Contract Label)) (fetch : BinString → Option Value)
    (kernel : BinString → List Value → Option Value)
    (records : List Record) (types finalTypes : List Label) (values : List (Option Value))
    (aligned : Aligned kind types values)
    (typed : inferRecords leafType contract records types = some finalTypes) :
    ∃ results, CompactDag.foldRecords (leafValue kind leafType fetch) (nodeValue kind contract kernel)
        records values = some results ∧ Aligned kind finalTypes results := by
  induction records generalizing types values with
  | nil =>
      cases Option.some.inj typed
      exact ⟨values, rfl, aligned⟩
  | cons record rest ih =>
      cases first : inferRecord leafType contract types record with
      | none => simp [inferRecords, first] at typed
      | some output =>
          obtain ⟨result, executed, fits⟩ := record_sound kind leafType contract fetch kernel aligned record output first
          have nextTyped : inferRecords leafType contract rest (types ++ [output]) = some finalTypes := by
            simpa [inferRecords, first] using typed
          have nextAligned : Aligned kind (types ++ [output]) (values ++ [result]) :=
            List.rel_append aligned (.cons fits .nil)
          obtain ⟨results, finished, agrees⟩ := ih (types ++ [output]) (values ++ [result]) nextAligned nextTyped
          exact ⟨results, by simp [CompactDag.foldRecords, executed, finished], agrees⟩

theorem roots_sound (kind : Value → Option Label) (leafType : BinString → Option Label)
    (contract : BinString → Option (Contract Label)) (fetch : BinString → Option Value)
    (kernel : BinString → List Value → Option Value) (forest : Forest)
    (types roots : List Label)
    (typed : inferRecords leafType contract forest.records [] = some types)
    (selected : gather types forest.roots = some roots) :
    ∃ results, CompactDag.evaluate (leafValue kind leafType fetch) (nodeValue kind contract kernel)
        forest = some results ∧ Aligned kind roots results := by
  obtain ⟨values, evaluated, agrees⟩ := inferRecords_sound kind leafType contract fetch kernel
    forest.records [] types [] .nil typed
  obtain ⟨results, read, resultTypes⟩ := gather_aligned kind agrees forest.roots selected
  exact ⟨results, by simp [CompactDag.evaluate, evaluated, read], resultTypes⟩

end Mettapedia.Algorithms.Compression.TypedDag
