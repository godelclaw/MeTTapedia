import Mettapedia.Algorithms.Compression.FramedTree

/-!
# PV1 wire values over the common framed record codec

The tags and vector/field boundaries here are those of the portable-value
schema. Scalar and tensor payloads remain packed bytes. UTF-8, canonical
unsigned integers and CTN1 payload admission are separate checks; this layer
does not turn an arbitrary payload into a valid native value or an executable
operation. In particular the theorem is not a C or floating-point proof.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Compression.PortableValueWire

open KolmogorovComplexity FramedTree

def byte (value : Nat) : BinString :=
  [value.testBit 7, value.testBit 6, value.testBit 5, value.testBit 4,
   value.testBit 3, value.testBit 2, value.testBit 1, value.testBit 0]

def word (values : List Nat) : BinString := values.flatMap byte

inductive LiteralKind where
  | symbol | text | natural | bytes
  deriving DecidableEq

def literalTag : LiteralKind → BinString
  | .symbol => byte 1
  | .text => byte 2
  | .natural => byte 3
  | .bytes => byte 4

inductive ScalarKind where
  | i64 | f64
  deriving DecidableEq

def scalarWord : ScalarKind → BinString
  | .i64 => word [105, 54, 52]
  | .f64 => word [102, 54, 52]

inductive Value where
  | literal : LiteralKind → BinString → Value
  | scalar : ScalarKind → BinString → Value
  | tensor : BinString → BinString → Value
  | expr : List Value → Value

def toTree : Value → Tree
  | .literal kind payload => .node (literalTag kind) [.leaf payload]
  | .scalar kind payload => .node (byte 7) [.leaf (scalarWord kind), .leaf payload]
  | .tensor dtype payload => .node (byte 8) [.leaf dtype, .leaf payload]
  | .expr children => .node (byte 5) [.node [] (children.map toTree)]

def read : Nat → Tree → Option Value
  | 0, _ => none
  | _ + 1, .node tag [.leaf payload] =>
      if tag = byte 1 then some (.literal .symbol payload)
      else if tag = byte 2 then some (.literal .text payload)
      else if tag = byte 3 then some (.literal .natural payload)
      else if tag = byte 4 then some (.literal .bytes payload)
      else none
  | _ + 1, .node tag [.leaf dtype, .leaf payload] =>
      if tag = byte 7 then
        if dtype = scalarWord .i64 then some (.scalar .i64 payload)
        else if dtype = scalarWord .f64 then some (.scalar .f64 payload)
        else none
      else if tag = byte 8 then some (.tensor dtype payload) else none
  | fuel + 1, .node tag [.node vector children] =>
      if tag = byte 5 ∧ vector = [] then (children.mapM (read fuel)).map .expr else none
  | _ + 1, _ => none

theorem read_toTree (value : Value) : ∀ fuel, FramedTree.size (toTree value) ≤ fuel →
    read fuel (toTree value) = some value := by
  induction value using Value.rec
    (motive_2 := fun children => ∀ fuel,
      (∀ child ∈ children, FramedTree.size (toTree child) ≤ fuel) →
      (children.map toTree).mapM (read fuel) = some children) with
  | literal kind payload =>
      intro fuel enough
      cases fuel with
      | zero => simp [toTree, FramedTree.size] at enough
      | succ fuel => cases kind <;> simp [read, toTree, literalTag, byte] <;> decide
  | scalar kind payload =>
      intro fuel enough
      cases fuel with
      | zero => simp [toTree, FramedTree.size] at enough
      | succ fuel => cases kind <;> simp [read, toTree, scalarWord, word, byte]
  | tensor dtype payload =>
      intro fuel enough
      cases fuel with
      | zero => simp [toTree, FramedTree.size] at enough
      | succ fuel => simp [read, toTree, byte]
  | expr children ih =>
      intro fuel enough
      cases fuel with
      | zero => simp [toTree, FramedTree.size] at enough
      | succ fuel =>
          have bounds : ∀ child ∈ children, FramedTree.size (toTree child) ≤ fuel := by
            intro child present
            have member : FramedTree.size (toTree child) ∈
                children.map (fun value => FramedTree.size (toTree value)) :=
              List.mem_map.mpr ⟨child, present, rfl⟩
            have bound : FramedTree.size (toTree child) ≤
                (children.map (fun value => FramedTree.size (toTree value))).sum :=
              List.single_le_sum (fun value _ => Nat.zero_le value) _ member
            simp only [toTree, FramedTree.size, List.map_cons, List.map_nil, List.sum_cons,
              List.sum_nil, List.map_map, Function.comp_def] at enough
            omega
          simp [read, toTree, ih fuel bounds]
  | nil => simp
  | cons first rest head tail =>
      rename_i fuel enough
      simp [head fuel (enough first (by simp)),
        tail fuel (fun child present => enough child (by simp [present]))]

def version : BinString := word [80, 86, 49]

def archive (value : Value) : Tree := .node (byte 6) [.leaf version, toTree value]

def encode (value : Value) : BinString := FramedTree.encode (archive value)

def decode (bits : BinString) : Option Value := do
  let tree ← FramedTree.decodeAll bits
  match tree with
  | .node tag [.leaf format, body] =>
      if tag = byte 6 ∧ format = version then read (FramedTree.size body) body else none
  | _ => none

theorem decode_encode (value : Value) : decode (encode value) = some value := by
  simp [decode, encode, archive, FramedTree.decodeAll_encode, read_toTree]

theorem encode_injective : Function.Injective encode := by
  intro first second same
  have reconstructed := decode_encode first
  rw [same, decode_encode] at reconstructed
  exact (Option.some.inj reconstructed).symm

def byteLength (value : Value) : Nat := FramedTree.byteLength (archive value)

theorem encoded_length (value : Value) : (encode value).length = 8 * byteLength value :=
  FramedTree.encoded_length _

theorem literal_kind_preserved (first second : LiteralKind) (payload other : BinString)
    (same : encode (.literal first payload) = encode (.literal second other)) :
    first = second ∧ payload = other := by
  exact Value.literal.inj (encode_injective same)

theorem scalar_kind_preserved (first second : ScalarKind) (payload other : BinString)
    (same : encode (.scalar first payload) = encode (.scalar second other)) :
    first = second ∧ payload = other := by
  exact Value.scalar.inj (encode_injective same)

theorem tensor_metadata_preserved (dtype other payload rest : BinString)
    (same : encode (.tensor dtype payload) = encode (.tensor other rest)) :
    dtype = other ∧ payload = rest := by
  exact Value.tensor.inj (encode_injective same)

theorem expression_occurrences_preserved (first second : List Value)
    (same : encode (.expr first) = encode (.expr second)) : first = second := by
  exact Value.expr.inj (encode_injective same)

namespace Controls

theorem text_is_not_symbol :
    encode (.literal .text []) ≠ encode (.literal .symbol []) := by
  intro same
  have := (literal_kind_preserved _ _ _ _ same).1
  cases this

theorem scalar_is_not_tensor : encode (.scalar .f64 []) ≠ encode (.tensor [] []) := by
  intro same
  have := encode_injective same
  cases this

theorem malformed_scalar_dtype_refused :
    read 1 (.node (byte 7) [.leaf [], .leaf []]) = none := by decide

theorem missing_vector_frame_refused :
    read 1 (.node (byte 5) [.leaf []]) = none := by decide

theorem truncated_child_budget_is_not_exhaustion :
    read 1 (toTree (.expr [.literal .symbol []])) = none ∧
      read 3 (toTree (.expr [.literal .symbol []])) = some (.expr [.literal .symbol []]) := by
  constructor <;> simp [read, toTree, literalTag, byte]

end Controls

#print axioms read_toTree
#print axioms decode_encode
#print axioms encode_injective
#print axioms encoded_length
#print axioms literal_kind_preserved
#print axioms scalar_kind_preserved
#print axioms tensor_metadata_preserved
#print axioms expression_occurrences_preserved
#print axioms Controls.text_is_not_symbol
#print axioms Controls.scalar_is_not_tensor
#print axioms Controls.malformed_scalar_dtype_refused
#print axioms Controls.missing_vector_frame_refused
#print axioms Controls.truncated_child_budget_is_not_exhaustion

end Mettapedia.Algorithms.Compression.PortableValueWire
