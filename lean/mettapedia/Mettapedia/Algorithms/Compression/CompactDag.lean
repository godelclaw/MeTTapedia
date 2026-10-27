import Mettapedia.Algorithms.Compression.FramedTree

/-!
# Compact record DAGs and their memoized interpretation

Chronological records reference earlier node positions. A forest retains root
order and duplicate roots. The interpreter resolves records, not an uncharged
external tree; an invalid reference is failure. A second interpreter evaluates
an algebra once per record. Its agreement with unfolded tree folding is proved
for actual functions, without treating an effectful or nondeterministic visitor
as such an algebra.

Exact structural interning is an implementation optimization checked separately.
Neither numeric ids nor decoded records confer runtime handle authority.
-/

namespace Mettapedia.Algorithms.Compression.CompactDag

open FramedTree KolmogorovComplexity

inductive Record where
  | leaf : BinString → Record
  | node : BinString → List Nat → Record
  deriving DecidableEq, Repr

structure Forest where
  roots : List Nat
  records : List Record
  deriving DecidableEq, Repr

def gather {α : Type} (values : List α) : List Nat → Option (List α)
  | [] => some []
  | index :: rest => do
      let value ← values[index]?
      let tail ← gather values rest
      pure (value :: tail)

def resolve (values : List Tree) : Record → Option Tree
  | .leaf bytes => some (.leaf bytes)
  | .node tag children => (gather values children).map (.node tag)

def interpret {α : Type} (leaf : BinString → α) (node : BinString → List α → α)
    (values : List α) : Record → Option α
  | .leaf bytes => some (leaf bytes)
  | .node tag children => (gather values children).map (node tag)

def fold {α : Type} (leaf : BinString → α) (node : BinString → List α → α) : Tree → α
  | .leaf bytes => leaf bytes
  | .node tag children => node tag (children.map (fold leaf node))

def unfoldRecords : List Record → List Tree → Option (List Tree)
  | [], values => some values
  | record :: rest, values => do
      let value ← resolve values record
      unfoldRecords rest (values ++ [value])

def foldRecords {α : Type} (leaf : BinString → α) (node : BinString → List α → α) :
    List Record → List α → Option (List α)
  | [], values => some values
  | record :: rest, values => do
      let value ← interpret leaf node values record
      foldRecords leaf node rest (values ++ [value])

def unfold (forest : Forest) : Option (List Tree) := do
  let values ← unfoldRecords forest.records []
  gather values forest.roots

def evaluate {α : Type} (leaf : BinString → α) (node : BinString → List α → α)
    (forest : Forest) : Option (List α) := do
  let values ← foldRecords leaf node forest.records []
  gather values forest.roots

theorem gather_map {α β : Type} (f : α → β) (values : List α) (indices : List Nat) :
    gather (values.map f) indices = (gather values indices).map (List.map f) := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      simp only [gather, List.getElem?_map, ih]
      cases found : values[index]? <;> cases tail : gather values rest <;> rfl

theorem interpret_resolve {α : Type} (leaf : BinString → α) (node : BinString → List α → α)
    (values : List Tree) (record : Record) :
    interpret leaf node (values.map (fold leaf node)) record =
      (resolve values record).map (fold leaf node) := by
  cases record with
  | leaf bytes => simp [interpret, resolve, fold]
  | node tag children =>
      simp [interpret, resolve, gather_map, Option.map_map, Function.comp_def, fold]

/-- The memoized record interpreter computes the fold of every actual
unfolded record, including records sharing children or not selected as roots. -/
theorem foldRecords_unfoldRecords {α : Type}
    (leaf : BinString → α) (node : BinString → List α → α)
    (records : List Record) (values : List Tree) :
    foldRecords leaf node records (values.map (fold leaf node)) =
      (unfoldRecords records values).map (List.map (fold leaf node)) := by
  induction records generalizing values with
  | nil => rfl
  | cons record rest ih =>
      simp only [foldRecords, unfoldRecords, interpret_resolve]
      cases found : resolve values record with
      | none => rfl
      | some value =>
          simpa using
            ih (values ++ [value])

/-- Shared traversal agrees with the ordered forest's unfolded interpretation;
root multiplicity is preserved, not silently changed into set membership. -/
theorem evaluate_unfold {α : Type} (leaf : BinString → α) (node : BinString → List α → α)
    (forest : Forest) :
    evaluate leaf node forest = (unfold forest).map (List.map (fold leaf node)) := by
  unfold evaluate unfold
  have records := foldRecords_unfoldRecords leaf node forest.records []
  simp only [List.map_nil] at records
  rw [records]
  cases found : unfoldRecords forest.records [] with
  | none => rfl
  | some values => simpa using gather_map (fold leaf node) values forest.roots

theorem unfoldRecords_length (records : List Record) (before after : List Tree)
    (found : unfoldRecords records before = some after) :
    after.length = before.length + records.length := by
  induction records generalizing before with
  | nil => cases Option.some.inj found; simp
  | cons record rest ih =>
      cases step : resolve before record with
      | none => simp [unfoldRecords, step] at found
      | some value =>
          have next := ih (before ++ [value]) (by simpa [unfoldRecords, step] using found)
          simp only [List.length_append, List.length_cons, List.length_nil] at next ⊢
          omega

theorem gather_length {α : Type} (values result : List α) (indices : List Nat)
    (found : gather values indices = some result) : result.length = indices.length := by
  induction indices generalizing result with
  | nil => cases Option.some.inj found; rfl
  | cons index rest ih =>
      cases head : values[index]? with
      | none => simp [gather, head] at found
      | some value =>
          cases tail : gather values rest with
          | none => simp [gather, head, tail] at found
          | some later =>
              simp [gather, head, tail] at found
              subst result
              simp [ih later tail]

/-! ## Exact unfolded encoding lengths without materializing encoded children -/

def leafLength (bytes : BinString) : Nat := Framing.measure [0, bytes.length]

def nodeLength (tag : BinString) (children : List Nat) : Nat :=
  Framing.measure [nodeMarker.length, tag.length,
    8 * Framing.measure (children.map (fun length => 8 * length))]

theorem leafLength_eq (bytes : BinString) : leafLength bytes = byteLength (.leaf bytes) := by
  simp [leafLength, byteLength, encode, Framing.encodePadded_length, Framing.byteLength_measure]

theorem nodeLength_eq (tag : BinString) (children : List Tree) :
    nodeLength tag (children.map byteLength) = byteLength (.node tag children) := by
  have lengths : (children.map encode).map List.length =
      (children.map byteLength).map (fun length => 8 * length) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro child _
    exact encoded_length child
  simp only [byteLength, encode, Framing.encodePadded_length]
  simp only [Framing.byteLength_measure, List.map_cons, List.map_nil,
    Framing.encodePadded_length]
  rw [lengths]
  simp [nodeLength]

theorem measured_fold (tree : Tree) : fold leafLength nodeLength tree = byteLength tree := by
  induction tree using Tree.rec
    (motive_2 := fun children => children.map (fold leafLength nodeLength) = children.map byteLength) with
  | leaf bytes => simpa [fold] using leafLength_eq bytes
  | node tag children ih => simpa only [fold, ih] using nodeLength_eq tag children
  | nil => rfl
  | cons head tail headResult tailResult => simp only [List.map_cons, headResult, tailResult]

/-- Shared length evaluation gives every complete unfolded encoding's exact
byte length, even when its actual byte vector would be exponentially larger. -/
theorem measured_evaluate (forest : Forest) :
    evaluate leafLength nodeLength forest = (unfold forest).map (List.map byteLength) := by
  rw [evaluate_unfold]
  congr 1
  funext trees
  exact List.map_congr_left fun tree _ => measured_fold tree

private def shared : Forest := ⟨[1, 1, 0], [.leaf [], .node [true] [0, 0]]⟩

example : evaluate (fun _ => 1) (fun _ children => 1 + children.sum) shared = some [3, 3, 1] := by decide

example : unfold ⟨[0], [.node [] [0]]⟩ = none := by decide

example : unfold ⟨[1], [.leaf []]⟩ = none := by decide

example : unfold ⟨[], []⟩ = some [] := by rfl

end Mettapedia.Algorithms.Compression.CompactDag
