import Mettapedia.Algorithms.Compression.Framing

/-!
# Recursive records for compression artifacts

Leaves carry packed payloads; nodes carry a tag and an ordered vector of child
records. The tag and every child boundary are part of the encoding. Signature,
dictionary, template, substitution and residual schemas use these records rather
than borrowing an uncharged external table. A semantic artifact checker assigns
meaning to the tags separately from this transport decoder.

The native byte instance restricts leaf payloads and tags to byte-aligned bit
strings. Nested records are already aligned by the common framing layer.
-/

namespace Mettapedia.Algorithms.Compression.FramedTree

open KolmogorovComplexity

inductive Tree where
  | leaf : BinString → Tree
  | node : BinString → List Tree → Tree
  deriving Repr

def nodeMarker : BinString := List.replicate 7 false ++ [true]

def encode : Tree → BinString
  | .leaf payload => Framing.encodePadded [[], payload]
  | .node tag children =>
      Framing.encodePadded [nodeMarker, tag, Framing.encodePadded (children.map encode)]

def size : Tree → Nat
  | .leaf _ => 1
  | .node _ children => 1 + (children.map size).sum

/-- A failed bounded decode does not assert that the record is malformed.
The public decoder below derives a sufficient budget from the actual input. -/
def decode : Nat → BinString → Option Tree
  | 0, _ => none
  | fuel + 1, input => do
      let fields ← Framing.decodePadded input
      match fields with
      | [marker, payload] =>
          if marker = [] then some (.leaf payload) else none
      | [marker, tag, packedChildren] =>
          if marker = nodeMarker then do
            let children ← Framing.decodePadded packedChildren
            let decoded ← children.mapM (decode fuel)
            pure (.node tag decoded)
          else none
      | _ => none

def decodeAll (input : BinString) : Option Tree := decode input.length input

def byteLength (tree : Tree) : Nat := (encode tree).length / 8

theorem encode_aligned (tree : Tree) : (encode tree).length % 8 = 0 := by
  cases tree <;> simp only [encode, Framing.encodePadded_length] <;> omega

theorem encoded_length (tree : Tree) : (encode tree).length = 8 * byteLength tree := by
  have aligned := encode_aligned tree
  unfold byteLength
  omega

private theorem payloads_lt_framed (fields : List BinString) :
    (fields.map List.length).sum < (Framing.encodePadded fields).length := by
  have overhead : (fields.map List.length).sum ≤
      (fields.map fun field => field.length + 2 * (binaryBits field.length).length + 1).sum := by
    induction fields with
    | nil => rfl
    | cons head tail ih => simp only [List.map_cons, List.sum_cons]; omega
  have header : 0 < (Framing.writeNat fields.length).length := by
    simp [Framing.writeNat, e2encode_length]
  have covered := (Framing.byteLength_covers fields).1
  rw [← Framing.encodePadded_length] at covered
  rw [Framing.encoded_length] at covered
  omega

theorem size_le_encoded (tree : Tree) : size tree ≤ (encode tree).length := by
  induction tree using Tree.rec with
  | leaf payload =>
      have bound := payloads_lt_framed [[], payload]
      simp only [encode, size]
      omega
  | node tag children ih =>
      have inner := payloads_lt_framed (children.map encode)
      have outer := payloads_lt_framed [nodeMarker, tag,
        Framing.encodePadded (children.map encode)]
      have summed : (children.map size).sum ≤ (children.map (fun child => (encode child).length)).sum :=
        ih
      simp only [List.map_map, Function.comp_def] at inner
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at outer
      simp only [encode, size]
      omega
  | nil => simp
  | cons head tail headResult tailResult =>
      simp only [List.map_cons, List.sum_cons]
      omega

theorem decode_encode (tree : Tree) : ∀ fuel, size tree ≤ fuel →
    decode fuel (encode tree) = some tree := by
  induction tree using Tree.rec
    (motive_2 := fun children => ∀ fuel,
      (∀ child ∈ children, size child ≤ fuel) →
        (children.map encode).mapM (decode fuel) = some children) with
  | leaf payload =>
      intro fuel enough
      cases fuel with
      | zero => simp [size] at enough
      | succ fuel => simp [decode, encode, Framing.decodePadded_encode]
  | node tag children ih =>
      intro fuel enough
      cases fuel with
      | zero => simp [size] at enough
      | succ fuel =>
          have childBudgets : ∀ child ∈ children, size child ≤ fuel := by
            intro child member
            have bound : size child ≤ (children.map size).sum :=
              List.single_le_sum (fun value _ => Nat.zero_le value) (size child)
                (List.mem_map.mpr ⟨child, member, rfl⟩)
            simp only [size] at enough
            omega
          have decoded : (children.map encode).mapM (decode fuel) = some children :=
            ih fuel childBudgets
          simp [decode, encode, Framing.decodePadded_encode, decoded]
  | nil => simp
  | cons head tail headResult tailResult =>
      rename_i fuel enough
      have hhead := headResult fuel (enough head (by simp))
      have htail := tailResult fuel (fun child member => enough child (by simp [member]))
      simp [hhead, htail]

theorem decodeAll_encode (tree : Tree) : decodeAll (encode tree) = some tree :=
  decode_encode tree _ (size_le_encoded tree)

theorem encode_injective : Function.Injective encode := by
  intro left right equal
  have decoded := decodeAll_encode left
  rw [equal, decodeAll_encode] at decoded
  exact (Option.some.inj decoded).symm

private theorem mapM_reconstruct {α β : Type} (read : α → Option β) (write : β → α)
    (sound : ∀ input value, read input = some value → write value = input) :
    ∀ (inputs : List α) (values : List β), inputs.mapM read = some values → values.map write = inputs
  | [], values, found => by cases Option.some.inj found; rfl
  | input :: inputs, values, found => by
      cases first : read input with
      | none => simp [first] at found
      | some value =>
          cases rest : inputs.mapM read with
          | none => simp [first, rest] at found
          | some tail =>
              simp [first, rest] at found
              subst values
              simp [sound input value first, mapM_reconstruct read write sound inputs tail rest]

/-- Accepted nested records have exactly their canonical encoding. An extra
field, alternate marker or trailing byte cannot alias an admitted tree. -/
theorem decode_sound (fuel : Nat) : ∀ input tree,
    decode fuel input = some tree → encode tree = input := by
  induction fuel with
  | zero => intro input tree found; cases found
  | succ fuel ih =>
      intro input tree found
      simp only [decode] at found
      cases framed : Framing.decodePadded input with
      | none => simp [framed] at found
      | some fields =>
          simp [framed] at found
          split at found
          · rename_i marker payload
            split at found
            · rename_i markerEmpty
              cases Option.some.inj found
              simpa [encode, markerEmpty] using Framing.decodePadded_sound framed
            · cases found
          · rename_i marker tag packedChildren
            split at found
            · rename_i markerCorrect
              cases children : Framing.decodePadded packedChildren with
              | none => simp [children] at found
              | some encodedChildren =>
                  cases decoded : encodedChildren.mapM (decode fuel) with
                  | none => simp [children, decoded] at found
                  | some values =>
                      simp [children, decoded] at found
                      subst tree
                      have equalChildren := mapM_reconstruct (decode fuel) encode ih
                        encodedChildren values decoded
                      have equalFrame := Framing.decodePadded_sound children
                      simpa [encode, equalChildren, equalFrame, markerCorrect] using
                        Framing.decodePadded_sound framed
            · cases found
          · cases found

theorem decodeAll_sound {input : BinString} {tree : Tree}
    (found : decodeAll input = some tree) : encode tree = input :=
  decode_sound _ _ _ found

theorem truncated_leaf_refused : decodeAll [false] = none := by decide

theorem empty_node_has_framing : 0 < (encode (.node [] [])).length := by
  have enough := size_le_encoded (.node [] [])
  simp only [size, List.map_nil, List.sum_nil] at enough
  omega

end Mettapedia.Algorithms.Compression.FramedTree
