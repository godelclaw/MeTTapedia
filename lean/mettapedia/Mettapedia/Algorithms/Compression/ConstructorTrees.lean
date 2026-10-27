import Mettapedia.Algorithms.Compression.TreeArchive

/-!
# Constructor-aware ranked trees

Unlike the tag-as-child byte-tree view, a constructor's label and arity jointly
select its ranked operator. A differing label therefore cannot be abstracted
as an ordinary callable argument. Payloads remain separate nullary operators.
The dictionary is complete source data; any interning order is allowed.

These are representation and matching laws. The executable text-tag view
separately checks UTF-8 and never invokes the decoded constructor label.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Compression.ConstructorTrees

open KolmogorovComplexity FramedTree
open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierCanonicalSchema

inductive Key where
  | payload : BinString → Key
  | constructor : BinString → Nat → Key
  deriving DecidableEq, Repr

def keys : Tree → List Key
  | .leaf value => [.payload value]
  | .node tag children => .constructor tag children.length :: children.flatMap keys

def Covers (catalogue : List Key) (tree : Tree) : Prop :=
  ∀ key ∈ keys tree, key ∈ catalogue

def catalogue (forest : List Tree) : List Key := (forest.flatMap keys).eraseDups

theorem catalogue_covers (forest : List Tree) (tree : Tree) (present : tree ∈ forest) :
    Covers (catalogue forest) tree := by
  intro key used
  simp only [catalogue, List.mem_eraseDups, List.mem_flatMap]
  exact ⟨tree, present, used⟩

def encode (table : List Key) : Tree → Prog
  | .leaf payload => .node (table.idxOf (.payload payload)) []
  | .node tag children =>
      .node (table.idxOf (.constructor tag children.length)) (children.map (encode table))

def decode (table : List Key) : Nat → Prog → Option Tree
  | 0, _ => none
  | fuel + 1, .node index children =>
      match table[index]? with
      | some (.payload bytes) => if children.isEmpty then some (.leaf bytes) else none
      | some (.constructor tag arity) =>
          if children.length = arity then
            (children.mapM (decode table fuel)).map (.node tag)
          else none
      | none => none

theorem covers_children {table : List Key} {tag : BinString} {children : List Tree}
    (covered : Covers table (.node tag children)) :
    ∀ child ∈ children, Covers table child := by
  intro child present key used
  apply covered key
  simp only [keys, List.mem_cons, List.mem_flatMap]
  exact Or.inr ⟨child, present, used⟩

theorem decode_encode (table : List Key) (tree : Tree) :
    ∀ fuel, size tree ≤ fuel → Covers table tree → decode table fuel (encode table tree) = some tree := by
  induction tree using Tree.rec
    (motive_2 := fun children => ∀ fuel,
      (∀ child ∈ children, size child ≤ fuel) →
      (∀ child ∈ children, Covers table child) →
      (children.map (encode table)).mapM (decode table fuel) = some children) with
  | leaf payload =>
      intro fuel enough covered
      cases fuel with
      | zero => simp [size] at enough
      | succ fuel =>
          have present := covered (.payload payload) (by simp [keys])
          simp [encode, decode, List.getElem?_idxOf present]
  | node tag children ih =>
      intro fuel enough covered
      cases fuel with
      | zero => simp [size] at enough
      | succ fuel =>
          have present := covered (.constructor tag children.length) (by simp [keys])
          have budgets : ∀ child ∈ children, size child ≤ fuel := by
            intro child member
            have bounded := List.single_le_sum (fun n _ => Nat.zero_le n) (size child)
              (List.mem_map.mpr ⟨child, member, rfl⟩)
            simp only [size] at enough
            omega
          simp [encode, decode, List.getElem?_idxOf present, ih fuel budgets (covers_children covered)]
  | nil => simp
  | cons first rest firstResult restResult =>
      rename_i fuel enough covered
      have head := firstResult fuel (enough first (by simp)) (covered first (by simp))
      have tail := restResult fuel (fun child present => enough child (by simp [present]))
        (fun child present => covered child (by simp [present]))
      simp [head, tail]

theorem distinct_constructor_indices (table : List Key) (first second : BinString)
    (firstArity secondArity : Nat)
    (present : Key.constructor first firstArity ∈ table)
    (different : first ≠ second ∨ firstArity ≠ secondArity) :
    table.idxOf (.constructor first firstArity) ≠ table.idxOf (.constructor second secondArity) := by
  intro equal
  have identical := (List.idxOf_inj present).mp equal
  cases identical
  rcases different with different | different <;> exact different rfl

theorem encode_injective_on_covered (table : List Key) (first second : Tree)
    (left : Covers table first) (right : Covers table second)
    (same : encode table first = encode table second) : first = second := by
  have decoded := decode_encode table first (size first + size second) (by omega) left
  rw [same, decode_encode table second _ (by omega) right] at decoded
  exact (Option.some.inj decoded).symm

theorem forest_decode_encode (table : List Key) (forest : List Tree) (fuel : Nat)
    (covered : ∀ tree ∈ forest, Covers table tree) (enough : ∀ tree ∈ forest, size tree ≤ fuel) :
    (forest.map (encode table)).mapM (decode table fuel) = some forest := by
  induction forest with
  | nil => rfl
  | cons first rest ih =>
      have head := decode_encode table first fuel (enough first (by simp)) (covered first (by simp))
      have tail := ih (fun tree present => covered tree (by simp [present]))
        (fun tree present => enough tree (by simp [present]))
      simp [head, tail]

theorem forest_roundtrip (forest : List Tree) (fuel : Nat)
    (enough : ∀ tree ∈ forest, size tree ≤ fuel) :
    (forest.map (encode (catalogue forest))).mapM (decode (catalogue forest) fuel) = some forest :=
  forest_decode_encode _ forest fuel (catalogue_covers forest) enough

theorem matched_tree_reconstructed (table : List Key) (tree : Tree) (covered : Covers table tree)
    (before after : TemplateMatching.Environment) (pattern : SchemaPattern)
    (matched : TemplateMatching.matchPattern before pattern (encode table tree) = some after) :
    (TemplateMatching.expand after pattern).bind (decode table (size tree)) = some tree := by
  rw [(TemplateMatching.matchPattern_sound before after pattern _ matched).2]
  exact decode_encode table tree _ (by omega) covered

namespace Controls

theorem tags_are_constructor_identity_not_callable_arguments :
    encode [.constructor [false] 1, .constructor [true] 1, .payload []]
      (.node [false] [.leaf []]) = .node 0 [.node 2 []] ∧
    encode [.constructor [false] 1, .constructor [true] 1, .payload []]
      (.node [true] [.leaf []]) = .node 1 [.node 2 []] := by
  constructor <;> simp [encode]

theorem wrong_arity_is_refused :
    decode [.constructor [] 2, .payload []] 3 (.node 0 [.node 1 []]) = none := by decide

theorem repeated_children_are_not_deduplicated :
    decode [.constructor [] 2, .payload [true]] 3 (.node 0 [.node 1 [], .node 1 []]) =
      some (.node [] [.leaf [true], .leaf [true]]) := by rfl

end Controls
end Mettapedia.Algorithms.Compression.ConstructorTrees
