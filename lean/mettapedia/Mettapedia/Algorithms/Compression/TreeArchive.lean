import Mettapedia.Algorithms.Compression.FramedTree
import Mettapedia.Algorithms.Compression.TemplateMatching

/-!
# Byte-payload trees in the ranked template representation

This is the representation used by the ordinary IC tree adapter. A payload
dictionary entry is a nullary operator. A node-arity entry takes its tag as a
payload argument followed by its ordered children. The decoder checks that
arity and refuses a non-payload tag. No source operator is executed.

The dictionary may have any complete interning order; the executable builder
uses chronological DAG records. Its construction is checked separately. These
laws connect the resulting indexed representation to actual template matching,
without granting binder transformations or certifying a native implementation.
-/

namespace Mettapedia.Algorithms.Compression.TreeArchive

open KolmogorovComplexity FramedTree
open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierCanonicalSchema

inductive Key where
  | bytes : BinString → Key
  | arity : Nat → Key
  deriving DecidableEq, Repr

def keyStream : Tree → List Key
  | .leaf payload => [.bytes payload]
  | .node tag children => .arity children.length :: .bytes tag :: children.flatMap keyStream

def Covers (catalogue : List Key) (tree : Tree) : Prop :=
  ∀ key ∈ keyStream tree, key ∈ catalogue

/-- A simple complete reference dictionary. Sharing and chronological insertion
may change its order, but must retain the same membership property. -/
def referenceCatalogue (forest : List Tree) : List Key :=
  (forest.flatMap keyStream).eraseDups

theorem referenceCatalogue_covers (forest : List Tree) (tree : Tree) (member : tree ∈ forest) :
    Covers (referenceCatalogue forest) tree := by
  intro key used
  simp only [referenceCatalogue, List.mem_eraseDups, List.mem_flatMap]
  exact ⟨tree, member, used⟩

def encode (catalogue : List Key) : Tree → Prog
  | .leaf payload => .node (catalogue.idxOf (.bytes payload)) []
  | .node tag children =>
      .node (catalogue.idxOf (.arity children.length))
        (.node (catalogue.idxOf (.bytes tag)) [] :: children.map (encode catalogue))

def readPayload (catalogue : List Key) : Prog → Option BinString
  | .node index [] =>
      match catalogue[index]? with
      | some (.bytes payload) => some payload
      | _ => none
  | .node _ (_ :: _) => none

/-- Fuel denotes traversal budget, never evidence of malformed input. -/
def decode (catalogue : List Key) : Nat → Prog → Option Tree
  | 0, _ => none
  | fuel + 1, .node index children =>
      match catalogue[index]? with
      | some (.bytes payload) => if children.isEmpty then some (.leaf payload) else none
      | some (.arity arity) =>
          match children with
          | [] => none
          | tag :: rest =>
              if rest.length = arity then do
                let payload ← readPayload catalogue tag
                let values ← rest.mapM (decode catalogue fuel)
                pure (.node payload values)
              else none
      | none => none

theorem readPayload_encode (catalogue : List Key) (payload : BinString)
    (present : Key.bytes payload ∈ catalogue) :
    readPayload catalogue (.node (catalogue.idxOf (.bytes payload)) []) = some payload := by
  simp [readPayload, List.getElem?_idxOf present]

theorem covers_children {catalogue : List Key} {tag : BinString} {children : List Tree}
    (covered : Covers catalogue (.node tag children)) :
    ∀ child ∈ children, Covers catalogue child := by
  intro child member key used
  apply covered key
  simp only [keyStream, List.mem_cons, List.mem_flatMap]
  exact Or.inr (Or.inr ⟨child, member, used⟩)

/-- Every ordered child occurrence is decoded, including duplicate edges.
The hypothesis concerns dictionary membership, not the desired round-trip. -/
theorem decode_encode (catalogue : List Key) (tree : Tree) :
    ∀ fuel, size tree ≤ fuel → Covers catalogue tree →
      decode catalogue fuel (encode catalogue tree) = some tree := by
  induction tree using Tree.rec
    (motive_2 := fun children => ∀ fuel,
      (∀ child ∈ children, size child ≤ fuel) →
      (∀ child ∈ children, Covers catalogue child) →
      (children.map (encode catalogue)).mapM (decode catalogue fuel) = some children) with
  | leaf payload =>
      intro fuel enough covered
      cases fuel with
      | zero => simp [size] at enough
      | succ fuel =>
          have present := covered (.bytes payload) (by simp [keyStream])
          simp [encode, decode, List.getElem?_idxOf present]
  | node tag children ih =>
      intro fuel enough covered
      cases fuel with
      | zero => simp [size] at enough
      | succ fuel =>
          have present := covered (.arity children.length) (by simp [keyStream])
          have tagPresent := covered (.bytes tag) (by simp [keyStream])
          have budgets : ∀ child ∈ children, size child ≤ fuel := by
            intro child member
            have bounded := List.single_le_sum (fun n _ => Nat.zero_le n) (size child)
              (List.mem_map.mpr ⟨child, member, rfl⟩)
            simp only [size] at enough
            omega
          have childrenRead := ih fuel budgets (covers_children covered)
          simp [encode, decode, List.getElem?_idxOf present,
            readPayload_encode catalogue tag tagPresent, childrenRead]
  | nil => simp
  | cons head tail first rest =>
      rename_i fuel enough covered
      have hhead := first fuel (enough head (by simp)) (covered head (by simp))
      have htail := rest fuel (fun child member => enough child (by simp [member]))
        (fun child member => covered child (by simp [member]))
      simp [hhead, htail]

theorem encode_injective_on_covered (catalogue : List Key) (left right : Tree)
    (leftCovered : Covers catalogue left) (rightCovered : Covers catalogue right)
    (same : encode catalogue left = encode catalogue right) : left = right := by
  have decoded := decode_encode catalogue left (size left + size right)
    (by omega) leftCovered
  rw [same, decode_encode catalogue right _ (by omega) rightCovered] at decoded
  exact (Option.some.inj decoded).symm

/-- A successful match supplies the reconstructing environment. The decoder
then recovers the original byte tree, including its source-variable records. -/
theorem matched_template_reconstructs (catalogue : List Key) (tree : Tree)
    (covered : Covers catalogue tree) (before after : TemplateMatching.Environment)
    (pattern : SchemaPattern)
    (matched : TemplateMatching.matchPattern before pattern (encode catalogue tree) = some after) :
    (TemplateMatching.expand after pattern).bind (decode catalogue (size tree)) = some tree := by
  rw [(TemplateMatching.matchPattern_sound before after pattern _ matched).2]
  exact decode_encode catalogue tree _ (by omega) covered

example : decode [] 1 (.node 0 []) = none := by rfl
example : readPayload [.arity 0] (.node 0 []) = none := by rfl
example : decode [.arity 1, .bytes []] 1 (.node 0 [.node 1 []]) = none := by rfl

end Mettapedia.Algorithms.Compression.TreeArchive
