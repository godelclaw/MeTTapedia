import Mettapedia.Algorithms.Compression.TypedDag
import Mettapedia.Algorithms.Compression.ParameterRegion

/-!
# Complete typed operand selection for chronological DAG extensions

The executable selector scans earlier node sorts in position order and forms
their ordered Cartesian product. The independent production rule requires a
successful gather of exactly the declared input sorts. Their equivalence
justifies sort filtering, including repeated operands; it does not justify
shape, cost or dead-node pruning.

Duplicate instruction occurrences and tuple order are retained. The existing
ParameterRegion frontier supplies resumable product traversal. These laws do
not yet identify the complete nested builder worklist with bounded derivations.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Compression.TypedDagRegion

open KolmogorovComplexity CompactDag TypedDag

variable {Label : Type} [DecidableEq Label]

def indices : List Label → Label → Nat → List Nat
  | [], _, _ => []
  | first :: rest, wanted, start =>
      let later := indices rest wanted (start + 1)
      if first = wanted then start :: later else later

theorem indices_mem_iff (types : List Label) (wanted : Label) (start index : Nat) :
    index ∈ indices types wanted start ↔
      ∃ offset, types[offset]? = some wanted ∧ index = start + offset := by
  induction types generalizing start with
  | nil => simp [indices]
  | cons first rest ih =>
      constructor
      · intro found
        by_cases same : first = wanted
        · simp only [indices, same, ↓reduceIte, List.mem_cons] at found
          rcases found with equal | later
          · exact ⟨0, by simp [same], by omega⟩
          · obtain ⟨offset, typed, position⟩ := (ih (start + 1)).mp later
            exact ⟨offset + 1, by simpa using typed, by omega⟩
        · simp only [indices, same, ↓reduceIte] at found
          obtain ⟨offset, typed, position⟩ := (ih (start + 1)).mp found
          exact ⟨offset + 1, by simpa using typed, by omega⟩
      · rintro ⟨offset, typed, position⟩
        cases offset with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at typed
            simp [indices, typed, position]
        | succ offset =>
            have later : index ∈ indices rest wanted (start + 1) :=
              (ih (start + 1)).mpr ⟨offset, by simpa using typed, by omega⟩
            by_cases same : first = wanted <;> simp [indices, same, later]

theorem indices_zero_mem_iff (types : List Label) (wanted : Label) (index : Nat) :
    index ∈ indices types wanted 0 ↔ types[index]? = some wanted := by
  rw [indices_mem_iff]
  simp

def tuples (types wanted : List Label) : List (List Nat) :=
  ParameterRegion.product (wanted.map fun sort => indices types sort 0)

theorem tuples_mem_iff (types wanted : List Label) (references : List Nat) :
    references ∈ tuples types wanted ↔ gather types references = some wanted := by
  induction wanted generalizing references with
  | nil =>
      cases references with
      | nil => simp [tuples, ParameterRegion.product, gather]
      | cons index tail =>
          cases typed : types[index]? <;> cases remaining : gather types tail <;>
            simp [tuples, ParameterRegion.product, gather, typed, remaining]
  | cons first rest ih =>
      constructor
      · intro found
        simp only [tuples, List.map_cons, ParameterRegion.product, List.mem_flatMap, List.mem_map] at found
        obtain ⟨index, present, tail, later, equality⟩ := found
        subst references
        have typed := (indices_zero_mem_iff types first index).mp present
        have remaining := ih tail |>.mp later
        simp [gather, typed, remaining]
      · intro found
        cases references with
        | nil => simp [gather] at found
        | cons index tail =>
            cases typed : types[index]? with
            | none => simp [gather, typed] at found
            | some actual =>
                cases remaining : gather types tail with
                | none => simp [gather, typed, remaining] at found
                | some later =>
                    simp [gather, typed, remaining] at found
                    obtain ⟨rfl, rfl⟩ := found
                    exact List.mem_flatMap.mpr ⟨index,
                      (indices_zero_mem_iff types actual index).mpr typed,
                      List.mem_map.mpr ⟨tail, (ih tail).mpr remaining, rfl⟩⟩

def extensions (contract : BinString → Option (Contract Label)) (tags : List BinString)
    (types : List Label) : List (Record × Label) :=
  tags.flatMap fun tag =>
    match contract tag with
    | none => []
    | some declaration => (tuples types declaration.inputs).map fun references =>
        (.node tag references, declaration.output)

inductive Extends (contract : BinString → Option (Contract Label))
    (tags : List BinString) (types : List Label) : Record → Label → Prop where
  | node (tag references declaration)
      (present : tag ∈ tags) (decoded : contract tag = some declaration)
      (typed : gather types references = some declaration.inputs) :
      Extends contract tags types (.node tag references) declaration.output

theorem extensions_mem_iff (contract : BinString → Option (Contract Label))
    (tags : List BinString) (types : List Label) (record : Record) (output : Label) :
    (record, output) ∈ extensions contract tags types ↔ Extends contract tags types record output := by
  constructor
  · intro found
    obtain ⟨tag, present, member⟩ := List.mem_flatMap.mp found
    cases decoded : contract tag with
    | none => simp [decoded] at member
    | some declaration =>
        simp only [decoded, List.mem_map] at member
        obtain ⟨references, chosen, equality⟩ := member
        cases equality
        exact .node tag references declaration present decoded ((tuples_mem_iff _ _ _).mp chosen)
  · intro found
    cases found with
    | node tag references declaration present decoded typed =>
        exact List.mem_flatMap.mpr ⟨tag, present, by
          simp only [decoded]
          exact List.mem_map.mpr ⟨references, (tuples_mem_iff _ _ _).mpr typed, rfl⟩⟩

theorem extension_infers (leafType : BinString → Option Label)
    (contract : BinString → Option (Contract Label)) (tags : List BinString)
    (types : List Label) (record : Record) (output : Label)
    (found : (record, output) ∈ extensions contract tags types) :
    inferRecord leafType contract types record = some output := by
  cases (extensions_mem_iff contract tags types record output).mp found with
  | node tag references declaration _ decoded typed =>
      simp [inferRecord, decoded, typed]

namespace Controls

theorem repeated_operands_remain_independent_positions :
    tuples [false, true, false] [false, false] = [[0, 0], [0, 2], [2, 0], [2, 2]] := by decide

theorem absent_sort_yields_no_operand_tuple :
    tuples [false, false] [false, true] = [] := by decide

theorem duplicate_instructions_preserve_occurrences :
    extensions (fun _ => some (⟨[false], true⟩ : Contract Bool)) [[], []] [false] =
      [(.node [] [0], true), (.node [] [0], true)] := by decide

end Controls

end Mettapedia.Algorithms.Compression.TypedDagRegion
