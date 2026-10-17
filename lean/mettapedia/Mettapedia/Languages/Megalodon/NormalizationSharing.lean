import Mettapedia.Languages.Megalodon.NormalizationGrowth
import Mettapedia.GSLT.LanguageDef.InferenceSharedCettaWireCompilation

/-!
# Shared storage for the expanded Mathdata normalization family

The original chronological pattern table represents the expanded normal form
with four initial nodes and two application nodes per level. Both occurrences
of the normalized argument refer to the same earlier node. Materialization is
the existing shared-pattern consumer, so this representation does not introduce
a second term semantics or checking authority.

The finite wire below admits application nodes only. Its fields use the existing
binary natural, UTF-8 string, product and list codecs; decoding reconstructs
the original shared nodes and invokes their original materializer. Storage
bounds concern that exact finite word, including every reference bit. They do
not establish an executed polynomial-time compiler into the shared format.
Emitting the full expanded tree wire from these shared packets still requires
superpolynomial work; merely using the shared representation does not make tree
serialization or arbitrary semantic checking inexpensive.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.NormalizationSharing

open MathdataKernel
open NormalizationGrowth
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.GSLT.LanguageDef.InferencePatternSharing
open Mettapedia.GSLT.LanguageDef.InferenceSharedCettaWire
open Mettapedia.GSLT.LanguageDef.InferenceSharedCettaWireCompilation
open Mettapedia.GSLT.LanguageDef.ProofSystems
open Turing Polynomial

/-- The root is the last physical node at every level, including the leaf. -/
def root (n : Nat) : Nat := 2 * n + 3

/-- Storage fields for the application-node fragment of the existing carrier. -/
abbrev Row := Nat × (String × List Nat)

def rowNode (row : Row) : SharedPatternNode := ⟨row.1, .apply row.2.1 row.2.2⟩

def rows : Nat → List Row
  | 0 => [(0, "MNZero", []), (1, "MTmPrim", [0]),
      (2, "MNSucc", [0]), (3, "MTmPrim", [2])]
  | n + 1 => rows n ++
      [(2 * n + 4, "MTmApp", [1, root n]),
       (2 * n + 5, "MTmApp", [2 * n + 4, root n])]

def nodes (n : Nat) : List SharedPatternNode := (rows n).map rowNode

theorem nodes_succ (n : Nat) : nodes (n + 1) = nodes n ++
    [⟨2 * n + 4, .apply "MTmApp" [1, root n]⟩,
     ⟨2 * n + 5, .apply "MTmApp" [2 * n + 4, root n]⟩] := by
  simp only [nodes, rows, List.map_append]; rfl

/-- Expanded values appear only in this specification of materialization. -/
def table : Nat → Array Pattern
  | 0 => #[TermQuantifiedKernel.encodeNat 0,
      TermQuantifiedKernel.encodeTm (.prim 0), TermQuantifiedKernel.encodeNat 1,
      TermQuantifiedKernel.encodeTm (expanded 0)]
  | n + 1 => (table n).push
      (TermQuantifiedKernel.encodeTm (.app (.prim 0) (expanded n))) |>.push
      (TermQuantifiedKernel.encodeTm (expanded (n + 1)))

theorem rows_length (n : Nat) : (rows n).length = 2 * n + 4 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rows, List.length_append, ih, List.length_cons,
      List.length_nil]; omega

theorem nodes_length (n : Nat) : (nodes n).length = 2 * n + 4 := by
  simp only [nodes, List.length_map, rows_length]

theorem table_size (n : Nat) : (table n).size = 2 * n + 4 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [table, Array.size_push, ih]; omega

theorem root_lookup (n : Nat) : (table n)[root n]? =
    some (TermQuantifiedKernel.encodeTm (expanded n)) := by
  cases n with
  | zero => rfl
  | succ n => simp only [table, Array.getElem?_push, Array.size_push, table_size, root]
              simp; omega

theorem head_lookup (n : Nat) : (table n)[1]? =
    some (TermQuantifiedKernel.encodeTm (.prim 0)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [table, Array.getElem?_push, Array.size_push, table_size]
                 have first : 1 ≠ 2 * n + 4 := by omega
                 have second : 1 ≠ 2 * n + 4 + 1 := by omega
                 simp only [first, second, if_false, ih]

theorem nodes_materialize (n : Nat) : materializePatternNodes (nodes n) = some (table n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [nodes_succ]
      unfold materializePatternNodes
      rw [materializePatternNodesLoop_append]
      unfold materializePatternNodes at ih
      rw [ih, nodes_length]
      simp only [Nat.zero_add]
      have oldRoot : ((table n).push
          (TermQuantifiedKernel.encodeTm (.app (.prim 0) (expanded n))))[root n]? =
          some (TermQuantifiedKernel.encodeTm (expanded n)) := by
        rw [Array.getElem?_push]
        have distinct : root n ≠ (table n).size := by rw [table_size]; unfold root; omega
        simp only [distinct, if_false, root_lookup]
      have newRoot : ((table n).push
          (TermQuantifiedKernel.encodeTm (.app (.prim 0) (expanded n))))[2 * n + 4]? =
          some (TermQuantifiedKernel.encodeTm (.app (.prim 0) (expanded n))) := by
        simp only [Array.getElem?_push, table_size, if_true]
      have ids : 2 * n + 5 = 2 * n + 4 + 1 := by omega
      have firstKey : materializePatternNodeKey? (table n)
          (.apply "MTmApp" [1, root n]) =
          some (TermQuantifiedKernel.encodeTm (.app (.prim 0) (expanded n))) := by
        simp only [materializePatternNodeKey?, resolvePatternIds, head_lookup,
          root_lookup, Bind.bind, Option.bind]; rfl
      have secondKey : materializePatternNodeKey? ((table n).push
          (TermQuantifiedKernel.encodeTm (.app (.prim 0) (expanded n))))
          (.apply "MTmApp" [2 * n + 4, root n]) =
          some (TermQuantifiedKernel.encodeTm (expanded (n + 1))) := by
        simp only [materializePatternNodeKey?, resolvePatternIds, newRoot,
          oldRoot, Bind.bind, Option.bind]; rfl
      simp only [materializePatternNodesLoop, bne_self_eq_false, Bool.false_eq_true,
        ↓reduceIte, firstKey, secondKey, Bind.bind, Option.bind, ids]
      rfl

/-- Unfolding the original graph recovers the original expanded term quotation. -/
theorem unfolded_exact (n : Nat) :
    (materializePatternNodes (nodes n)).bind (fun values => values[root n]?) =
      some (TermQuantifiedKernel.encodeTm (expanded n)) := by
  rw [nodes_materialize]; exact root_lookup n

/-- Every application row has only earlier children, even when a child occurs
twice. Node IDs also stay within the exact chronological table length. -/
theorem rows_bounds (n : Nat) (row : Row) (member : row ∈ rows n) :
    row.1 < 2 * n + 4 ∧ row.2.1.utf8ByteSize ≤ 7 ∧
      row.2.2.length ≤ 2 ∧ ∀ child ∈ row.2.2, child < row.1 := by
  induction n with
  | zero =>
      simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      all_goals decide
  | succ n ih =>
      rw [rows, List.mem_append] at member
      rcases member with earlier | added
      · rcases ih earlier with ⟨idBound, nameBound, countBound, childBound⟩
        exact ⟨by omega, nameBound, countBound, childBound⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at added
        rcases added with rfl | rfl
        all_goals
          refine ⟨by omega, by change "MTmApp".utf8ByteSize ≤ 7; decide,
            by change 2 ≤ 2; omega, ?_⟩
          intro child childIn
          simp only [List.mem_cons, List.not_mem_nil, or_false] at childIn
          rcases childIn with rfl | rfl <;> unfold root <;> omega

theorem nodes_chronological (n : Nat) (node : SharedPatternNode)
    (member : node ∈ nodes n) :
    ∃ head children, node.key = .apply head children ∧
      node.id < (nodes n).length ∧ ∀ child ∈ children, child < node.id := by
  rcases List.mem_map.mp member with ⟨row, rowIn, rfl⟩
  rcases rows_bounds n row rowIn with ⟨idBound, _, _, childBound⟩
  exact ⟨row.2.1, row.2.2, rfl, by simpa only [rowNode, nodes_length] using idBound,
    childBound⟩

/-- A forward child is refused by the existing materializer, not silently
interpreted as a missing, default or cyclic term. -/
theorem future_reference_refused (values : Array Pattern) (head : String)
    (child : Nat) (rest : List Nat) (future : values.size ≤ child) :
    materializePatternNodeKey? values (.apply head (child :: rest)) = none := by
  have missing : values[child]? = none := by simp [future]
  simp only [materializePatternNodeKey?, resolvePatternIds, missing, Bind.bind, Option.bind]

def rowCodec : Codec Row := Codec.prod Codec.nat (Codec.prod Codec.string (Codec.list Codec.nat))

def packetCodec : Codec (List Row × Nat) := Codec.prod (Codec.list rowCodec) Codec.nat

/-- Application-node fields and the final physical root, on five symbols. -/
def sharedWire (n : Nat) : List Alphabet := encodeWith packetCodec (rows n, root n)

/-- Decode storage fields, reconstruct original nodes, and use the original
checked materializer and root lookup. -/
def unfoldWire (word : List Alphabet) : Option Pattern := do
  let (rowFields, rootId) ← decodeWith packetCodec word
  let values ← materializePatternNodes (rowFields.map rowNode)
  values[rootId]?

theorem sharedWire_decode (n : Nat) : decodeWith packetCodec (sharedWire n) =
    some (rows n, root n) := decodeWith_encodeWith packetCodec _

theorem sharedWire_unfold (n : Nat) : unfoldWire (sharedWire n) =
    some (TermQuantifiedKernel.encodeTm (expanded n)) := by
  simp only [unfoldWire, sharedWire_decode, Bind.bind, Option.bind]
  exact unfolded_exact n

theorem future_root_refused (n rootId : Nat) (future : 2 * n + 4 ≤ rootId) :
    unfoldWire (encodeWith packetCodec (rows n, rootId)) = none := by
  simp only [unfoldWire, decodeWith_encodeWith, Bind.bind, Option.bind]
  change (materializePatternNodes (nodes n)).bind _ = none
  rw [nodes_materialize]
  simp only [Option.bind_some]
  simp [table_size, future]

/-- Even correctly encoded row fields are refused when their child is not
already available in the original chronological table. -/
theorem future_child_wire_refused (n child : Nat) (head : String) (rest : List Nat)
    (future : 2 * n + 4 ≤ child) :
    unfoldWire (encodeWith packetCodec
      (rows n ++ [(2 * n + 4, head, child :: rest)], 2 * n + 4)) = none := by
  simp only [unfoldWire, decodeWith_encodeWith, Bind.bind, Option.bind]
  simp only [List.map_append, List.map_cons, List.map_nil]
  change (materializePatternNodesLoop (nodes n ++ [rowNode _]) 0 #[]).bind _ = none
  rw [materializePatternNodesLoop_append]
  have initialReplay : materializePatternNodesLoop (nodes n) 0 #[] = some (table n) :=
    nodes_materialize n
  rw [initialReplay, nodes_length]
  have missing := future_reference_refused (table n) head child rest (by simpa [table_size] using future)
  simp only [Nat.zero_add, materializePatternNodesLoop, rowNode, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte, missing, Bind.bind, Option.bind]

theorem trailing_symbol_refused (n : Nat) (symbol : Alphabet) :
    decodeWith packetCodec (sharedWire n ++ [symbol]) = none := by
  unfold sharedWire
  exact decodeWith_trailing_refused packetCodec _ [symbol] (by simp)

private theorem listWeight_le {α : Type} (codec : Codec α) (values : List α)
    (limit : Nat) (bounded : ∀ value ∈ values, dataWeight (codec.put value) ≤ limit) :
    dataWeight ((Codec.list codec).put values) ≤ (limit + 1) * values.length + 2 := by
  induction values with
  | nil => simp only [dataWeight_list_nil, List.length_nil, Nat.mul_zero]; omega
  | cons value values ih =>
      have head := bounded value (by simp)
      have rest := ih (fun value member => bounded value (by simp [member]))
      rw [dataWeight_list_cons, List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

private theorem natWeight_le (value maximum : Nat) (bounded : value ≤ maximum) :
    dataWeight (Codec.nat.put value) ≤ 2 + (Nat.digits 2 maximum).length := by
  exact Nat.add_le_add_left (Nat.le_length_digits_le 2 value maximum bounded) 2

private theorem rowWeight_le (n : Nat) (row : Row) (member : row ∈ rows n) :
    dataWeight (rowCodec.put row) ≤ 91 + 3 * (Nat.digits 2 (2 * n + 3)).length := by
  rcases rows_bounds n row member with ⟨idBound, nameBound, countBound, childBound⟩
  have idWeight := natWeight_le row.1 (2 * n + 3) (by omega)
  have nameWeight := dataWeight_string row.2.1
  have childrenWeight := listWeight_le Codec.nat row.2.2
      (2 + (Nat.digits 2 (2 * n + 3)).length) (fun child childIn =>
        natWeight_le child (2 * n + 3) (by have earlier := childBound child childIn; omega))
  have childrenBound := Nat.mul_le_mul_left
      (2 + (Nat.digits 2 (2 * n + 3)).length + 1) countBound
  simp only [rowCodec, dataWeight_prod]
  omega

/-- The complete finite word is linear in the number of levels times the
binary address width. The bound includes names, all ordered child occurrences,
list/product framing and the final root. -/
theorem sharedWire_length_bound (n : Nat) : (sharedWire n).length ≤
    (92 + 3 * (Nat.digits 2 (2 * n + 3)).length) * (2 * n + 4) +
      (Nat.digits 2 (2 * n + 3)).length + 5 := by
  have nodeWeight := listWeight_le rowCodec (rows n)
      (91 + 3 * (Nat.digits 2 (2 * n + 3)).length) (rowWeight_le n)
  have rootWeight := natWeight_le (root n) (2 * n + 3) (Nat.le_refl _)
  change (writeData (packetCodec.put (rows n, root n)) []).length ≤ _
  rw [writeData_length, List.length_nil, Nat.add_zero]
  simp only [packetCodec, dataWeight_prod]
  rw [rows_length] at nodeWeight
  rw [show 91 + 3 * (Nat.digits 2 (2 * n + 3)).length + 1 =
    92 + 3 * (Nat.digits 2 (2 * n + 3)).length by omega] at nodeWeight
  omega

/-- A conservative polynomial corollary, with the original full binary wire
still charged. It is a storage bound, not an execution-time bound. -/
theorem sharedWire_length_quadratic (n : Nat) : (sharedWire n).length ≤ 512 * (n + 1) ^ 2 := by
  have bound := sharedWire_length_bound n
  have width : (Nat.digits 2 (2 * n + 3)).length ≤ 2 * n + 4 := by
    rw [Nat.length_digits 2 (2 * n + 3) (by decide) (by omega)]
    have logarithm := Nat.log_le_self 2 (2 * n + 3)
    omega
  have product := Nat.mul_le_mul_right (2 * n + 4) (by
    have : 3 * (Nat.digits 2 (2 * n + 3)).length ≤ 3 * (2 * n + 4) :=
      Nat.mul_le_mul_left 3 width
    omega : 92 + 3 * (Nat.digits 2 (2 * n + 3)).length ≤ 92 + 3 * (2 * n + 4))
  nlinarith

theorem sharedWire_length_input_polynomial (n : Nat) :
    (sharedWire n).length ≤ 512 * ((wire (input n)).length + 1) ^ 2 := by
  have bound := sharedWire_length_quadratic n
  rw [input_wire_length]
  exact bound.trans (Nat.mul_le_mul_left 512 (Nat.pow_le_pow_left (by omega) 2))

/-- One typed normalization family, two exact representations: the expanded
tree is exponential, while the original shared pattern table has linearly many
nodes and a polynomial complete serialized word. -/
theorem representation_contrast (n : Nat) :
    (wire (input n)).length = 1244 * n + 305 ∧
    (wire (expanded n)).length + 429 = 734 * 2 ^ n ∧
    (nodes n).length = 2 * n + 4 ∧
    (sharedWire n).length ≤ 512 * (n + 1) ^ 2 ∧
    unfoldWire (sharedWire n) = some (TermQuantifiedKernel.encodeTm (expanded n)) :=
  ⟨input_wire_length n, expanded_wire_length n, nodes_length n,
    sharedWire_length_quadratic n, sharedWire_unfold n⟩

/-- The tree-to-DAG size ratio is unbounded for this same normal-form family.
This compares complete finite words, not just counts of constructors. -/
theorem arbitrarily_large_storage_ratio (factor : Nat) :
    ∃ n, factor * (sharedWire n).length < (wire (expanded n)).length := by
  let bound : Nat[X] := C (factor * 512) * (X + C 1) ^ 2
  obtain ⟨n, exponential⟩ :=
    Mettapedia.GSLT.LanguageDef.ProofSystems.exists_eval_lt_two_pow bound 1 0
  have shared := Nat.mul_le_mul_left factor (sharedWire_length_quadratic n)
  have small : factor * (512 * (n + 1) ^ 2) < 2 ^ n := by
    simpa only [bound, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_add, Polynomial.eval_X, Nat.one_mul, Nat.add_zero, Nat.mul_assoc] using exponential
  exact ⟨n, (shared.trans_lt small).trans_le (exponential_le_output n)⟩

/-- A machine that emits the full tree serialization pays for its physical
output even when its input is a compact shared packet. -/
theorem expanded_from_shared_output_work (machine : FinTM2)
    (sourceAlphabet : machine.Γ machine.k₀ ≃ Alphabet)
    (targetAlphabet : machine.Γ machine.k₁ ≃ Alphabet) (n time : Nat)
    (run : TM2OutputsInTime machine ((sharedWire n).map sourceAlphabet.symm)
      (some ((wire (expanded n)).map targetAlphabet.symm)) time) :
    2 ^ n ≤ (sharedWire n).length +
      Mettapedia.Computability.StackMachineSpaceGrowth.machinePushBound machine * time := by
  have emitted := Mettapedia.Computability.StackMachineSpaceGrowth.output_length_le machine run
  simp only [List.length_map] at emitted
  exact (exponential_le_output n).trans emitted

/-- Compact input storage does not permit a polynomial-time producer of the
full expanded original tree wire. This is not a lower bound for checking or for
constructing and retaining a shared heap representation. -/
theorem no_polynomial_shared_expansion : IsEmpty
    (TM2ComputableInPolyTime sharedWire wire expanded) := by
  refine ⟨fun implementation => ?_⟩
  let outputBound : Nat[X] := X + C
    (Mettapedia.Computability.StackMachineSpaceGrowth.machinePushBound implementation.tm) *
      implementation.time
  let inputBound : Nat[X] := C 512 * (X + C 1) ^ 2
  obtain ⟨n, tooSmall⟩ := exists_eval_lt_two_pow (outputBound.comp inputBound) 1 0
  have emitted := expanded_from_shared_output_work implementation.tm
    implementation.inputAlphabet implementation.outputAlphabet n _ (implementation.outputsFun n)
  have paid : 2 ^ n ≤ outputBound.eval (sharedWire n).length := by
    simpa only [outputBound, eval_add, eval_X, eval_mul, eval_C] using emitted
  have inputSize : (sharedWire n).length ≤ inputBound.eval n := by
    simpa only [inputBound, eval_mul, eval_C, eval_pow, eval_add, eval_X] using
      sharedWire_length_quadratic n
  have stillTooSmall := eval_mono outputBound inputSize
  simp only [eval_comp, Nat.one_mul, Nat.add_zero] at tooSmall
  omega

end Mettapedia.Languages.Megalodon.NormalizationSharing
