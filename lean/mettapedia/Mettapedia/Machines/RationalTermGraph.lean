import Mathlib.Data.List.Forall2
import Mathlib.Data.List.Lex
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Prod
import Mettapedia.Data.Fin.OptionSequence
import Mettapedia.Machines.PeTTaLeafEquality
import Mettapedia.TypeTheory.MaterialSets.Hypersets.Bisimulation

/-!
# Ordered term graphs and finite observations

A rational term has a finite graph presentation, but its observable unfolding
can be infinite. Constructor names and argument positions are retained here;
graph sharing and the number of nodes used to present a cycle are not part of
term equality. This differs from the unlabelled membership graphs used for
hypersets, which forget both argument order and repeated edges.

`bisimilar_iff_observe_eq` proves that the relational graph definition agrees
with every finite unfolding. It holds without assuming that the presentation
is finite, and thus applies in particular to finite runtime graphs. The
examples distinguish this equality from graph identity and from unlabelled
graph bisimilarity. `checkCertificate` checks a finite candidate relation using
only labels, child lists, and pair membership. Accepted certificates are sound,
and finite graphs have such a certificate exactly when their roots are
bisimilar. Certificate generation and its efficiency are separate obligations.

Labels are a parameter: a language must separately specify variable identity,
numeric leaf comparison, and the distinction between atoms and zero-argument
compounds.

`LayerReader` admits finite keyed inventories from a partial structural
reader. Its direct bounded traversal agrees with the admitted graph at every
depth, while keeping the supplied keys and all ordered child occurrences.

Bisimilarity is an equivalence (`Bisimilar.refl`, `.symm`, `.trans`). A
transport (`IsTransport`) copies a graph into another presentation, each node
to one node with its label and the images of its ordered children, as a copy
across a foreign boundary with node memoization does; a transported node is
the term it was copied from (`IsTransport.bisimilar`), and transports compose,
so a round trip returns the same term (`IsTransport.round_trip`). A boundary
that converts labels is a transport of the relabelled graph (`Graph.mapLabel`).
A hash of a bounded unfolding gives equal terms equal hashes and needs no
cycle detection (`observe_hash_compatible`).

`PeTTaEq` is PeTTa's `==` on term graphs: bisimilarity once numeric leaves are
replaced by their value class (`PeTTaLeafEquality.cls`), atoms, variables and
compound names kept. On two leaves it is exactly the runtime's leaf decision
(`pettaClass_number_eq_iff`). The examples are the rational terms of the
reference's `numeric_equality` test: a cycle equals itself with a NaN leaf, an
integer leaf and a float leaf of the same value give equal cycles, a cycle
equals its unrolling, and unequal leaves or zero-argument compounds of
different names give unequal ones.

The file does not verify a runtime's conversion code, unification, or garbage
collection.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RationalTermGraph

universe u v w x

/-- Ordered children preserve constructor arity, argument position, and repeated
arguments. A finite node type gives a finite presentation of a rational term. -/
structure Graph (Node : Type u) (Label : Type v) where
  label : Node → Label
  children : Node → List Node

/-- The observation at the depth boundary reveals nothing further. -/
inductive Observation (Label : Type v) where
  | cut
  | node (label : Label) (children : List (Observation Label))

/-- Finite unfolding, including the complete ordered child list at each revealed
node. This terminates even for a cyclic graph. -/
def observe {Node : Type u} {Label : Type v} (g : Graph Node Label) :
    Nat → Node → Observation Label
  | 0, _ => .cut
  | depth + 1, node =>
      .node (g.label node) ((g.children node).map (observe g depth))

/-- A graph bisimulation compares corresponding argument positions. -/
def IsBisimulation {A : Type u} {B : Type w} {Label : Type v}
    (g : Graph A Label) (h : Graph B Label) (R : A → B → Prop) : Prop :=
  ∀ ⦃a b⦄, R a b → g.label a = h.label b ∧
    List.Forall₂ R (g.children a) (h.children b)

/-- Equality by ordered unfolding, independent of graph presentation. -/
def Bisimilar {A : Type u} {B : Type w} {Label : Type v}
    (g : Graph A Label) (h : Graph B Label) (a : A) (b : B) : Prop :=
  ∃ R, IsBisimulation g h R ∧ R a b

/-- Bisimilar roots expose equal labels and bisimilar children at every
corresponding position, including repeated children and cycles. -/
theorem Bisimilar.layer {A : Type u} {B : Type w} {Label : Type v}
    {g : Graph A Label} {h : Graph B Label} {a : A} {b : B}
    (related : Bisimilar g h a b) :
    g.label a = h.label b ∧ List.Forall₂ (Bisimilar g h) (g.children a) (h.children b) := by
  obtain ⟨relation, simulation, member⟩ := related
  obtain ⟨labels, children⟩ := simulation member
  exact ⟨labels, children.imp fun _ _ pair => ⟨relation, simulation, pair⟩⟩

private theorem forall₂_iff_map_eq {A : Type u} {B : Type w} {C : Type v}
    (f : A → C) (g : B → C) (xs : List A) (ys : List B) :
    List.Forall₂ (fun x y => f x = g y) xs ys ↔ xs.map f = ys.map g := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp
  | cons x xs ih =>
      cases ys with
      | nil => simp
      | cons y ys => simp [List.forall₂_cons, ih]

private theorem forall₂_forall {A : Type u} {B : Type w}
    (R : Nat → A → B → Prop) (xs : List A) (ys : List B) :
    (∀ depth, List.Forall₂ (R depth) xs ys) ↔
      List.Forall₂ (fun x y => ∀ depth, R depth x y) xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp
  | cons x xs ih =>
      cases ys with
      | nil => simp
      | cons y ys => simp [List.forall₂_cons, forall_and, ih]

/-- A bisimulation certifies equality at every finite observation depth. -/
theorem IsBisimulation.observe_eq {A : Type u} {B : Type w} {Label : Type v}
    {g : Graph A Label} {h : Graph B Label} {R : A → B → Prop}
    (hR : IsBisimulation g h R) {a b} (hab : R a b) (depth : Nat) :
    observe g depth a = observe h depth b := by
  induction depth generalizing a b with
  | zero => rfl
  | succ depth ih =>
      obtain ⟨hl, hc⟩ := hR hab
      simp only [observe, Observation.node.injEq, hl, true_and]
      apply (forall₂_iff_map_eq _ _ _ _).mp
      exact hc.imp fun _ _ hxy => ih hxy

/-- Agreement at every finite depth itself supplies a bisimulation. -/
theorem isBisimulation_observe_eq {A : Type u} {B : Type w} {Label : Type v}
    (g : Graph A Label) (h : Graph B Label) :
    IsBisimulation g h (fun a b => ∀ depth, observe g depth a = observe h depth b) := by
  intro a b hab
  have layer (depth : Nat) := Observation.node.inj (hab (depth + 1))
  refine ⟨(layer 0).1, ?_⟩
  apply (forall₂_forall _ _ _).mp
  intro depth
  exact (forall₂_iff_map_eq _ _ _ _).mpr (layer depth).2

/-- The graph relation and independently defined finite unfoldings characterize
the same equality, including on cyclic presentations. -/
theorem bisimilar_iff_observe_eq {A : Type u} {B : Type w} {Label : Type v}
    {g : Graph A Label} {h : Graph B Label} {a b} :
    Bisimilar g h a b ↔ ∀ depth, observe g depth a = observe h depth b := by
  constructor
  · rintro ⟨R, hR, hab⟩ depth
    exact hR.observe_eq hab depth
  · intro hab
    exact ⟨_, isBisimulation_observe_eq g h, hab⟩

/-- A finite distinguishing observation refutes bisimilarity. -/
theorem not_bisimilar_of_observe_ne {A : Type u} {B : Type w} {Label : Type v}
    {g : Graph A Label} {h : Graph B Label} {a b depth}
    (hne : observe g depth a ≠ observe h depth b) : ¬ Bisimilar g h a b := by
  intro hab
  exact hne (bisimilar_iff_observe_eq.mp hab depth)

section Certificates

variable {A : Type u} {B : Type w} {Label : Type v}
variable [DecidableEq A] [DecidableEq B] [DecidableEq Label]

/-- Check corresponding child positions against a supplied finite relation.
Unequal arities fail; a repeated child must satisfy each occurrence separately. -/
def checkChildren (pairs : List (A × B)) : List A → List B → Bool
  | [], [] => true
  | a :: as, b :: bs => decide ((a, b) ∈ pairs) && checkChildren pairs as bs
  | _, _ => false

theorem checkChildren_eq_true_iff (pairs : List (A × B)) (xs : List A) (ys : List B) :
    checkChildren pairs xs ys = true ↔
      List.Forall₂ (fun a b => (a, b) ∈ pairs) xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [checkChildren]
  | cons x xs ih =>
      cases ys with
      | nil => simp [checkChildren]
      | cons y ys => simp [checkChildren, List.forall₂_cons, ih]

/-- A certificate must include the requested root pair. Every listed pair is
checked independently for equal labels and related corresponding children.
The checker traverses finite lists; it never recursively unfolds the graph. -/
def checkCertificate (g : Graph A Label) (h : Graph B Label)
    (pairs : List (A × B)) (a : A) (b : B) : Bool :=
  decide ((a, b) ∈ pairs) && pairs.all (fun p =>
    decide (g.label p.1 = h.label p.2) &&
      checkChildren pairs (g.children p.1) (h.children p.2))

theorem checkCertificate_eq_true_iff (g : Graph A Label) (h : Graph B Label)
    (pairs : List (A × B)) (a : A) (b : B) :
    checkCertificate g h pairs a b = true ↔
      (a, b) ∈ pairs ∧ IsBisimulation g h (fun x y => (x, y) ∈ pairs) := by
  simp only [checkCertificate, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    checkChildren_eq_true_iff, IsBisimulation]
  constructor
  · rintro ⟨hab, hall⟩
    exact ⟨hab, fun x y hxy => hall (x, y) hxy⟩
  · rintro ⟨hab, hall⟩
    exact ⟨hab, fun p hp => hall hp⟩

/-- A successful finite certificate certifies the semantic graph equality. -/
theorem checkCertificate_sound {g : Graph A Label} {h : Graph B Label}
    {pairs : List (A × B)} {a : A} {b : B}
    (hcheck : checkCertificate g h pairs a b = true) : Bisimilar g h a b := by
  obtain ⟨hab, hall⟩ := (checkCertificate_eq_true_iff g h pairs a b).mp hcheck
  exact ⟨_, hall, hab⟩

/-- For finite node types, every bisimilar root pair has a finite certificate.
This existence proof enumerates the witnessing relation; it does not claim an
efficient algorithm for discovering that relation. -/
theorem exists_certificate_iff_bisimilar [Fintype A] [Fintype B]
    (g : Graph A Label) (h : Graph B Label) (a : A) (b : B) :
    (∃ pairs, checkCertificate g h pairs a b = true) ↔ Bisimilar g h a b := by
  constructor
  · rintro ⟨pairs, hcheck⟩
    exact checkCertificate_sound hcheck
  · rintro ⟨R, hR, hab⟩
    classical
    let pairs := (Finset.univ.filter (fun p : A × B => R p.1 p.2)).toList
    have mem_iff (x : A) (y : B) : (x, y) ∈ pairs ↔ R x y := by
      simp [pairs]
    refine ⟨pairs, (checkCertificate_eq_true_iff g h pairs a b).mpr
      ⟨(mem_iff a b).mpr hab, ?_⟩⟩
    intro x y hxy
    obtain ⟨hl, hc⟩ := hR ((mem_iff x y).mp hxy)
    exact ⟨hl, hc.imp fun x' y' hxy' => (mem_iff x' y').mpr hxy'⟩

end Certificates

section Equivalence

variable {A : Type u} {B : Type w} {C : Type x} {Label : Type v}

theorem Bisimilar.refl (g : Graph A Label) (a : A) : Bisimilar g g a a :=
  bisimilar_iff_observe_eq.mpr fun _ => rfl

theorem Bisimilar.symm {g : Graph A Label} {h : Graph B Label} {a : A} {b : B}
    (hab : Bisimilar g h a b) : Bisimilar h g b a :=
  bisimilar_iff_observe_eq.mpr fun depth =>
    (bisimilar_iff_observe_eq.mp hab depth).symm

theorem Bisimilar.trans {g : Graph A Label} {h : Graph B Label} {k : Graph C Label}
    {a : A} {b : B} {c : C} (hab : Bisimilar g h a b) (hbc : Bisimilar h k b c) :
    Bisimilar g k a c :=
  bisimilar_iff_observe_eq.mpr fun depth =>
    (bisimilar_iff_observe_eq.mp hab depth).trans (bisimilar_iff_observe_eq.mp hbc depth)

/-- A hash of a bounded unfolding gives bisimilar nodes equal hashes: it reads
finitely many nodes, so it never loops on a cycle. -/
theorem observe_hash_compatible {H : Type x} (hash : Observation Label → H)
    (depth : Nat) {g : Graph A Label} {h : Graph B Label} {a : A} {b : B}
    (hab : Bisimilar g h a b) : hash (observe g depth a) = hash (observe h depth b) := by
  rw [bisimilar_iff_observe_eq.mp hab depth]

end Equivalence

section Transport

variable {A : Type u} {B : Type w} {C : Type x} {Label : Type v}

/-- A transport of `g` into `h`: every node of `g` goes to one node of `h`
with the same label, whose ordered children are the images of the node's
children. A copy that visits each node once and records where it went (node
memoization) is one, and so is a copy that shares nothing. -/
structure IsTransport (g : Graph A Label) (h : Graph B Label) (m : A → B) : Prop where
  label : ∀ a, h.label (m a) = g.label a
  children : ∀ a, h.children (m a) = (g.children a).map m

theorem IsTransport.isBisimulation {g : Graph A Label} {h : Graph B Label} {m : A → B}
    (hm : IsTransport g h m) : IsBisimulation g h (fun a b => m a = b) := by
  rintro a _ rfl
  refine ⟨(hm.label a).symm, ?_⟩
  rw [hm.children a, List.forall₂_map_right_iff]
  exact List.forall₂_same.mpr fun _ _ => rfl

/-- A transported node is the term it was copied from, cycles and sharing
included. -/
theorem IsTransport.bisimilar {g : Graph A Label} {h : Graph B Label} {m : A → B}
    (hm : IsTransport g h m) (a : A) : Bisimilar g h a (m a) :=
  ⟨_, hm.isBisimulation, rfl⟩

theorem IsTransport.comp {g : Graph A Label} {h : Graph B Label} {k : Graph C Label}
    {m : A → B} {n : B → C} (hm : IsTransport g h m) (hn : IsTransport h k n) :
    IsTransport g k (n ∘ m) where
  label a := by rw [Function.comp_apply, hn.label, hm.label]
  children a := by rw [Function.comp_apply, hn.children, hm.children, List.map_map]

/-- Across a boundary and back, a term is itself. -/
theorem IsTransport.round_trip {g : Graph A Label} {h : Graph B Label}
    {m : A → B} {n : B → A} (hm : IsTransport g h m) (hn : IsTransport h g n) (a : A) :
    Bisimilar g g a (n (m a)) :=
  (hm.comp hn).bisimilar a

end Transport

/-! ## Finite keyed inventories

Keys identify native cursor occurrences; labels are observations selected by
the caller. Admission checks the entire inventory before constructing a graph.
Neither equal labels nor equal unfoldings authorize collapsing distinct keys.
-/

/-- A finite cursor row retains the exact ordered child-key list. -/
structure KeyedRow (Key : Type u) (Label : Type v) where
  key : Key
  label : Label
  children : List Key
  deriving DecidableEq

/-- Every key names one row and every child names a row in this inventory. -/
def KeyedInventoryValid {Key : Type u} {Label : Type v} (rows : List (KeyedRow Key Label)) : Prop :=
  (rows.map KeyedRow.key).Nodup ∧
    ∀ row ∈ rows, ∀ child ∈ row.children, child ∈ rows.map KeyedRow.key

instance {Key : Type u} {Label : Type v} [DecidableEq Key]
    (rows : List (KeyedRow Key Label)) : Decidable (KeyedInventoryValid rows) := by
  unfold KeyedInventoryValid
  infer_instance

/-- An admitted table retains its raw inventory, including repeated edges. -/
structure KeyedTable (Key : Type u) (Label : Type v) where
  rows : List (KeyedRow Key Label)
  valid : KeyedInventoryValid rows

/-- Checked executable admission. Duplicate row keys and dangling children
are refused rather than repaired or silently erased. -/
def decodeKeyedTable? {Key : Type u} {Label : Type v} [DecidableEq Key]
    (rows : List (KeyedRow Key Label)) : Option (KeyedTable Key Label) :=
  if valid : KeyedInventoryValid rows then some ⟨rows, valid⟩ else none

theorem decodeKeyedTable?_sound {Key : Type u} {Label : Type v} [DecidableEq Key]
    {rows : List (KeyedRow Key Label)} {table : KeyedTable Key Label}
    (decoded : decodeKeyedTable? rows = some table) :
    table.rows = rows ∧ KeyedInventoryValid rows := by
  unfold decodeKeyedTable? at decoded
  split at decoded
  · next valid =>
    cases Option.some.inj decoded
    exact ⟨rfl, valid⟩
  · simp at decoded

theorem decodeKeyedTable?_complete {Key : Type u} {Label : Type v} [DecidableEq Key]
    (rows : List (KeyedRow Key Label)) (valid : KeyedInventoryValid rows) :
    ∃ table, decodeKeyedTable? rows = some table := by
  exact ⟨⟨rows, valid⟩, by simp [decodeKeyedTable?, valid]⟩

theorem decodeKeyedTable?_isSome_iff {Key : Type u} {Label : Type v} [DecidableEq Key]
    (rows : List (KeyedRow Key Label)) :
    (decodeKeyedTable? rows).isSome = true ↔ KeyedInventoryValid rows := by
  simp [decodeKeyedTable?]

namespace KeyedTable

variable {Key : Type u} {Label : Type v}

/-- Nodes are actual inventory positions, without a distinguished default. -/
abbrev Node (table : KeyedTable Key Label) := Fin table.rows.length

def key (table : KeyedTable Key Label) (node : table.Node) : Key := table.rows[node.val].key

theorem key_mem (table : KeyedTable Key Label) (node : table.Node) :
    table.key node ∈ table.rows.map KeyedRow.key :=
  List.mem_map.mpr ⟨table.rows[node.val], List.getElem_mem node.isLt, rfl⟩

theorem key_injective (table : KeyedTable Key Label) : Function.Injective table.key := by
  intro first second same
  apply Fin.ext
  apply (List.Nodup.getElem_inj_iff table.valid.1
    (hi := by rw [List.length_map]; exact first.isLt)
    (hj := by rw [List.length_map]; exact second.isLt)).mp
  simpa [key] using same

variable [DecidableEq Key]

/-- The checked first position of a key. The membership proof only supplies
the finite bound; it does not choose a node. -/
def nodeOf (table : KeyedTable Key Label) (wanted : Key)
    (present : wanted ∈ table.rows.map KeyedRow.key) : table.Node :=
  ⟨(table.rows.map KeyedRow.key).idxOf wanted,
    by simpa using List.idxOf_lt_length_of_mem present⟩

theorem key_nodeOf (table : KeyedTable Key Label) (wanted : Key)
    (present : wanted ∈ table.rows.map KeyedRow.key) :
    table.key (table.nodeOf wanted present) = wanted := by
  have bound := List.idxOf_lt_length_of_mem present
  have found := List.getElem_idxOf bound
  simp only [List.getElem_map] at found
  exact found

def node? (table : KeyedTable Key Label) (wanted : Key) : Option table.Node :=
  if present : wanted ∈ table.rows.map KeyedRow.key then
    some (table.nodeOf wanted present) else none

theorem node?_key (table : KeyedTable Key Label) (node : table.Node) :
    table.node? (table.key node) = some node := by
  have same : table.nodeOf (table.key node) (table.key_mem node) = node :=
    table.key_injective (table.key_nodeOf _ _)
  simp only [node?, dif_pos (table.key_mem node), same]

theorem node?_eq_some_iff (table : KeyedTable Key Label) (wanted : Key) (node : table.Node) :
    table.node? wanted = some node ↔ table.key node = wanted := by
  constructor
  · intro found
    unfold node? at found
    split at found
    · next present =>
      cases Option.some.inj found
      exact table.key_nodeOf wanted present
    · simp at found
  · intro same
    rw [← same]
    exact table.node?_key node

theorem node?_complete (table : KeyedTable Key Label) (wanted : Key)
    (present : wanted ∈ table.rows.map KeyedRow.key) :
    ∃ node, table.node? wanted = some node :=
  ⟨table.nodeOf wanted present, by simp [node?, present]⟩

theorem node?_none_iff (table : KeyedTable Key Label) (wanted : Key) :
    table.node? wanted = none ↔ wanted ∉ table.rows.map KeyedRow.key := by
  simp [node?]

/-- Each ordered child occurrence is mapped to its admitted finite node.
Closure supplies bounds; no child is filtered out. -/
def graph (table : KeyedTable Key Label) : Graph table.Node Label where
  label node := table.rows[node.val].label
  children node := table.rows[node.val].children.attach.map fun child =>
    table.nodeOf child.val
      (table.valid.2 table.rows[node.val] (List.getElem_mem node.isLt) child.val child.property)

theorem graph_label (table : KeyedTable Key Label) (node : table.Node) :
    table.graph.label node = table.rows[node.val].label := rfl

/-- The child-key list is exact, including argument order and multiplicity. -/
theorem graph_children_keys (table : KeyedTable Key Label) (node : table.Node) :
    (table.graph.children node).map table.key = table.rows[node.val].children := by
  simp [graph, List.map_map, Function.comp_def, key_nodeOf]

end KeyedTable

/-- Independent first-row lookup on the written keyed inventory. This does not
use the finite-node constructor or its position search. -/
def lookupKeyed {Key : Type u} {Label : Type v} [DecidableEq Key]
    (rows : List (KeyedRow Key Label)) (wanted : Key) : Option (KeyedRow Key Label) :=
  rows.find? (fun row => decide (row.key = wanted))

theorem lookupKeyed_none_iff {Key : Type u} {Label : Type v} [DecidableEq Key]
    (rows : List (KeyedRow Key Label)) (wanted : Key) :
    lookupKeyed rows wanted = none ↔ wanted ∉ rows.map KeyedRow.key := by
  rw [lookupKeyed, List.find?_eq_none]
  constructor
  · intro absent present
    obtain ⟨row, member, same⟩ := List.mem_map.mp present
    exact absent row member (by simp [same])
  · intro absent row member matched
    exact absent (List.mem_map.mpr ⟨row, member, of_decide_eq_true matched⟩)

theorem lookupKeyed_some {Key : Type u} {Label : Type v} [DecidableEq Key]
    {rows : List (KeyedRow Key Label)} {wanted : Key} {row : KeyedRow Key Label}
    (found : lookupKeyed rows wanted = some row) : row ∈ rows ∧ row.key = wanted :=
  ⟨List.mem_of_find?_eq_some found, of_decide_eq_true
    (List.find?_some (p := fun item : KeyedRow Key Label => decide (item.key = wanted)) found)⟩

theorem lookupKeyed_of_member {Key : Type u} {Label : Type v} [DecidableEq Key]
    {rows : List (KeyedRow Key Label)} (unique : (rows.map KeyedRow.key).Nodup)
    (row : KeyedRow Key Label) (member : row ∈ rows) :
    lookupKeyed rows row.key = some row := by
  cases found : lookupKeyed rows row.key with
  | none =>
    exact False.elim ((lookupKeyed_none_iff rows row.key).mp found
      (List.mem_map.mpr ⟨row, member, rfl⟩))
  | some first =>
    obtain ⟨firstMember, sameKey⟩ := lookupKeyed_some found
    have same : first = row := List.inj_on_of_nodup_map unique firstMember member sameKey
    exact congrArg some same

namespace KeyedTable

variable {Key : Type u} {Label : Type v} [DecidableEq Key]

theorem lookupKeyed_node (table : KeyedTable Key Label) (node : table.Node) :
    lookupKeyed table.rows (table.key node) = some table.rows[node.val] :=
  lookupKeyed_of_member table.valid.1 _ (List.getElem_mem node.isLt)

/-- The executable position lookup returns precisely the linear oracle's row. -/
theorem node?_readback (table : KeyedTable Key Label) (wanted : Key) (node : table.Node)
    (found : table.node? wanted = some node) :
    lookupKeyed table.rows wanted = some table.rows[node.val] := by
  rw [← (table.node?_eq_some_iff wanted node).mp found]
  exact table.lookupKeyed_node node

/-- Position search and independent row search agree on success and absence. -/
theorem node?_lookup_eq (table : KeyedTable Key Label) (wanted : Key) :
    (table.node? wanted).map (fun node => table.rows[node.val]) =
      lookupKeyed table.rows wanted := by
  cases found : table.node? wanted with
  | none =>
    exact ((lookupKeyed_none_iff table.rows wanted).mpr
      ((table.node?_none_iff wanted).mp found)).symm
  | some node => exact (table.node?_readback wanted node found).symm

theorem node?_graph_readback (table : KeyedTable Key Label) (wanted : Key)
    (node : table.Node) (row : KeyedRow Key Label)
    (found : table.node? wanted = some node) (read : lookupKeyed table.rows wanted = some row) :
    table.graph.label node = row.label ∧
      (table.graph.children node).map table.key = row.children := by
  have same : table.rows[node.val] = row :=
    Option.some.inj ((table.node?_readback wanted node found).symm.trans read)
  rw [table.graph_label, table.graph_children_keys, same]
  exact ⟨rfl, rfl⟩

end KeyedTable

/-- A partial structural observation at a key. A layer exposes its label and
ordered child occurrences without choosing a finite graph presentation. -/
abbrev LayerReader (Key : Type u) (Label : Type v) := Key → Option (Label × List Key)

namespace LayerReader

variable {Key : Type u} {Label : Type v}

def readRow? (reader : LayerReader Key Label) (key : Key) : Option (KeyedRow Key Label) :=
  (reader key).map (fun layer => ⟨key, layer.1, layer.2⟩)

theorem readRow?_sound {reader : LayerReader Key Label} {key : Key}
    {row : KeyedRow Key Label} (read : reader.readRow? key = some row) :
    row.key = key ∧ reader key = some (row.label, row.children) := by
  obtain ⟨⟨label, children⟩, layer, same⟩ := Option.map_eq_some_iff.mp read
  cases same
  exact ⟨rfl, layer⟩

def readRows? (reader : LayerReader Key Label) (keys : List Key) :
    Option (List (KeyedRow Key Label)) :=
  (Fin.sequenceOption keys.length
    (fun index => reader.readRow? keys[index.val])).map List.ofFn

theorem readRows?_member {reader : LayerReader Key Label} {keys : List Key}
    {rows : List (KeyedRow Key Label)} (read : reader.readRows? keys = some rows)
    (row : KeyedRow Key Label) (member : row ∈ rows) :
    ∃ key ∈ keys, reader.readRow? key = some row := by
  obtain ⟨family, sequence, same⟩ := Option.map_eq_some_iff.mp read
  subst rows
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
  exact ⟨keys[index.val], List.getElem_mem index.isLt,
    Fin.sequenceOption_sound keys.length sequence index⟩

theorem readRows?_keys {reader : LayerReader Key Label} {keys : List Key}
    {rows : List (KeyedRow Key Label)} (read : reader.readRows? keys = some rows) :
    rows.map KeyedRow.key = keys := by
  obtain ⟨family, sequence, same⟩ := Option.map_eq_some_iff.mp read
  subst rows
  have keysEqual : (fun index => (family index).key) = (fun index => keys[index.val]) := by
    funext index
    exact (readRow?_sound (Fin.sequenceOption_sound keys.length sequence index)).1
  simpa only [List.map_ofFn, Function.comp_def, keysEqual] using
    (List.ofFn_getElem (xs := keys))

/-- Read the full supplied inventory and then check unique keys and closure.
Duplicate children are retained; duplicate row keys and dangling children fail. -/
def readTable? [DecidableEq Key] (reader : LayerReader Key Label) (keys : List Key) :
    Option (KeyedTable Key Label) :=
  (reader.readRows? keys).bind decodeKeyedTable?

theorem readTable?_isSome_iff [DecidableEq Key] (reader : LayerReader Key Label)
    (keys : List Key) :
    (reader.readTable? keys).isSome = true ↔
      ∃ rows, reader.readRows? keys = some rows ∧ KeyedInventoryValid rows := by
  cases read : reader.readRows? keys with
  | none => simp [readTable?, read]
  | some rows => simp [readTable?, read, decodeKeyedTable?_isSome_iff]

/-- Admission keeps exactly the supplied key order. It neither deduplicates
keys nor replaces their identity with equality of their observed labels. -/
theorem readTable?_keys [DecidableEq Key] {reader : LayerReader Key Label} {keys : List Key}
    {table : KeyedTable Key Label} (read : reader.readTable? keys = some table) :
    table.rows.map KeyedRow.key = keys := by
  obtain ⟨rows, reads, admitted⟩ := Option.bind_eq_some_iff.mp read
  rw [(decodeKeyedTable?_sound admitted).1]
  exact readRows?_keys reads

/-- The commuting layer equation follows from executable row reads and
checked admission, without assuming a graph correspondence. -/
theorem readTable?_layer [DecidableEq Key] {reader : LayerReader Key Label} {keys : List Key}
    {table : KeyedTable Key Label} (read : reader.readTable? keys = some table)
    (node : table.Node) :
    reader (table.key node) =
      some (table.graph.label node, (table.graph.children node).map table.key) := by
  obtain ⟨rows, reads, admitted⟩ := Option.bind_eq_some_iff.mp read
  have same := (decodeKeyedTable?_sound admitted).1
  have member : table.rows[node.val] ∈ rows := by
    rw [← same]
    exact List.getElem_mem node.isLt
  obtain ⟨key, _, decoded⟩ := readRows?_member reads table.rows[node.val] member
  obtain ⟨keyEqual, layer⟩ := readRow?_sound decoded
  rw [table.graph_label, table.graph_children_keys]
  simpa only [KeyedTable.key, keyEqual] using layer

/-- Direct bounded traversal is independent of inventory admission and finite
node construction. Even depth zero checks that its root layer is readable. -/
def observe (reader : LayerReader Key Label) : Nat → Key → Option (Observation Label)
  | 0, key => (reader key).map (fun _ => .cut)
  | depth + 1, key =>
      match reader key with
      | none => none
      | some (label, children) =>
          (children.mapM (reader.observe depth)).map (Observation.node label)

/-- Every finite graph observation agrees with direct structural reads, at
arbitrary depth and with the ordered list of repeated child occurrences intact. -/
theorem readTable?_observe [DecidableEq Key] {reader : LayerReader Key Label} {keys : List Key}
    {table : KeyedTable Key Label} (read : reader.readTable? keys = some table)
    (depth : Nat) (node : table.Node) :
    reader.observe depth (table.key node) =
      some (RationalTermGraph.observe table.graph depth node) := by
  induction depth generalizing node with
  | zero => simp [observe, readTable?_layer read node, RationalTermGraph.observe]
  | succ depth ih =>
      simp only [observe, readTable?_layer read node, RationalTermGraph.observe]
      have children (nodes : List table.Node) :
          (nodes.map table.key).mapM (reader.observe depth) =
            some (nodes.map (RationalTermGraph.observe table.graph depth)) := by
        induction nodes with
        | nil => rfl
        | cons first rest restIH => simp [ih first, restIH]
      rw [children]
      rfl

/-- Two independently read presentations have the same graph unfolding
exactly when all direct finite observations agree. Their key types may differ. -/
theorem readTable?_bisimilar_iff {OtherKey : Type w} [DecidableEq Key] [DecidableEq OtherKey]
    {firstReader : LayerReader Key Label} {secondReader : LayerReader OtherKey Label}
    {firstKeys : List Key} {secondKeys : List OtherKey}
    {first : KeyedTable Key Label} {second : KeyedTable OtherKey Label}
    (firstRead : firstReader.readTable? firstKeys = some first)
    (secondRead : secondReader.readTable? secondKeys = some second)
    (left : first.Node) (right : second.Node) :
    Bisimilar first.graph second.graph left right ↔
      ∀ depth, firstReader.observe depth (first.key left) =
        secondReader.observe depth (second.key right) := by
  rw [bisimilar_iff_observe_eq]
  simp only [readTable?_observe firstRead, readTable?_observe secondRead, Option.some.injEq]

end LayerReader

/-- Independently unfold the keyed inventory by linear row lookup. Missing
roots or children give `none`, including at the depth boundary. -/
def observeKeyed {Key : Type u} {Label : Type v} [DecidableEq Key]
    (rows : List (KeyedRow Key Label)) : Nat → Key → Option (Observation Label) :=
  LayerReader.observe (fun wanted =>
    (lookupKeyed rows wanted).map (fun row => (row.label, row.children)))

/-- The admitted finite graph and the independent keyed unfolding expose the
same finite observations at every depth, including on cyclic inventories. -/
theorem KeyedTable.observeKeyed_graph {Key : Type u} {Label : Type v} [DecidableEq Key]
    (table : KeyedTable Key Label) (depth : Nat) (node : table.Node) :
    observeKeyed table.rows depth (table.key node) = some (observe table.graph depth node) := by
  induction depth generalizing node with
  | zero => simp [observeKeyed, LayerReader.observe, table.lookupKeyed_node, observe]
  | succ depth ih =>
    simp only [observeKeyed, LayerReader.observe, table.lookupKeyed_node,
      Option.map_some, observe]
    rw [← table.graph_children_keys node]
    have children (nodes : List table.Node) :
        (nodes.map table.key).mapM (observeKeyed table.rows depth) =
          some (nodes.map (observe table.graph depth)) := by
      induction nodes with
      | nil => rfl
      | cons first rest restIH => simp [ih first, restIH]
    simp only [observeKeyed] at children
    rw [children]
    rfl

theorem observeKeyed_missing {Key : Type u} {Label : Type v} [DecidableEq Key]
    (rows : List (KeyedRow Key Label)) (wanted : Key)
    (missing : wanted ∉ rows.map KeyedRow.key) (depth : Nat) :
    observeKeyed rows depth wanted = none := by
  cases depth <;>
    simp [observeKeyed, LayerReader.observe, (lookupKeyed_none_iff rows wanted).mpr missing]

namespace KeyedControls

private def cyclicRows : List (KeyedRow Nat Nat) :=
  [⟨10, 7, [20, 20, 10]⟩, ⟨20, 8, [10]⟩]

private def cyclicReader : LayerReader Nat Nat
  | 10 => some (7, [20, 20, 10])
  | 20 => some (8, [10])
  | _ => none

theorem layer_reader_keeps_the_inventory_and_repeated_children :
    cyclicReader.readRows? [10, 20] = some cyclicRows ∧
    (cyclicReader.readTable? [10, 20]).isSome = true := by decide

theorem layer_reader_rejects_duplicate_dangling_and_unreadable_keys :
    (cyclicReader.readTable? [10, 20, 10]).isSome = false ∧
    (cyclicReader.readTable? [10]).isSome = false ∧
    (cyclicReader.readTable? [10, 20, 999]).isSome = false := by decide

theorem layer_reader_unfolds_cycles_and_checks_depth_boundary :
    cyclicReader.observe 2 10 =
      some (.node 7 [.node 8 [.cut], .node 8 [.cut], .node 7 [.cut, .cut, .cut]]) ∧
    cyclicReader.observe 0 999 = none := by
  constructor <;> rfl

private def cyclicTable : KeyedTable Nat Nat :=
  (decodeKeyedTable? cyclicRows).get (by decide)

private def root : cyclicTable.Node := ⟨0, by decide⟩

/-- The inventory is finite while its presentation contains both a cycle and
two occurrences of the same child at distinct ordered positions. -/
theorem cycles_and_repeated_children_are_admitted :
    (decodeKeyedTable? cyclicRows).isSome = true ∧
    cyclicTable.node? 10 = some root ∧
    cyclicTable.graph.label root = 7 ∧
    (cyclicTable.graph.children root).map Fin.val = [1, 1, 0] ∧
    (cyclicTable.graph.children root).map cyclicTable.key = [20, 20, 10] := by decide

theorem cyclic_unfolding_keeps_child_order_and_multiplicity :
    observe cyclicTable.graph 2 root =
      .node 7 [.node 8 [.cut], .node 8 [.cut], .node 7 [.cut, .cut, .cut]] ∧
    observeKeyed cyclicRows 2 10 =
      some (.node 7 [.node 8 [.cut], .node 8 [.cut], .node 7 [.cut, .cut, .cut]]) := by
  constructor <;> rfl

theorem duplicate_keys_and_unknown_children_are_refused :
    (decodeKeyedTable? [⟨10, 7, []⟩, ⟨10, 8, []⟩] : Option (KeyedTable Nat Nat)) = none ∧
    (decodeKeyedTable? [⟨10, 7, [20]⟩] : Option (KeyedTable Nat Nat)) = none ∧
    observeKeyed ([⟨10, 7, [20]⟩] : List (KeyedRow Nat Nat)) 1 10 = none ∧
    observeKeyed cyclicRows 0 999 = none := by decide

private def worldRows : List (KeyedRow (Nat × Nat) Nat) :=
  [⟨(7, 31), 1, []⟩, ⟨(9, 31), 2, []⟩]

private def addressOnlyRows : List (KeyedRow Nat Nat) :=
  worldRows.map fun row => ⟨row.key.2, row.label, row.children.map Prod.snd⟩

/-- Equal addresses in different worlds are distinct keys. Erasing the world
turns them into duplicate rows and cannot be an admitted representation. -/
theorem key_collapse_is_not_admission :
    (decodeKeyedTable? worldRows).isSome = true ∧
    decodeKeyedTable? addressOnlyRows = none := by decide

private def equalLabelRows : List (KeyedRow Nat Nat) := [⟨10, 7, []⟩, ⟨20, 7, []⟩]

private def equalLabelTable : KeyedTable Nat Nat :=
  (decodeKeyedTable? equalLabelRows).get (by decide)

/-- Equal labels and unfoldings do not collapse the two actual keyed nodes. -/
theorem equal_observations_keep_distinct_keys :
    equalLabelTable.node? 10 ≠ equalLabelTable.node? 20 ∧
    observeKeyed equalLabelRows 3 10 = observeKeyed equalLabelRows 3 20 := by
  exact ⟨by decide, rfl⟩

end KeyedControls

section Relabel

variable {A : Type u} {B : Type w} {C : Type x} {Label : Type v} {K : Type v}

/-- The graph with every label replaced by its image: a boundary that converts
labels (a foreign number to the runtime's) transports this graph. -/
def Graph.mapLabel (f : Label → K) (g : Graph A Label) : Graph A K where
  label a := f (g.label a)
  children := g.children

/-- Equality of terms whose labels compare through `f`. -/
def BisimilarBy (f : Label → K) (g : Graph A Label) (h : Graph B Label)
    (a : A) (b : B) : Prop :=
  Bisimilar (g.mapLabel f) (h.mapLabel f) a b

theorem BisimilarBy.refl (f : Label → K) (g : Graph A Label) (a : A) :
    BisimilarBy f g g a a :=
  Bisimilar.refl _ a

theorem BisimilarBy.symm {f : Label → K} {g : Graph A Label} {h : Graph B Label}
    {a : A} {b : B} (hab : BisimilarBy f g h a b) : BisimilarBy f h g b a :=
  Bisimilar.symm hab

theorem BisimilarBy.trans {f : Label → K} {g : Graph A Label} {h : Graph B Label}
    {k : Graph C Label} {a : A} {b : B} {c : C} (hab : BisimilarBy f g h a b)
    (hbc : BisimilarBy f h k b c) : BisimilarBy f g k a c :=
  Bisimilar.trans hab hbc

/-- Equal terms are equal through any label map. -/
theorem Bisimilar.by_map (f : Label → K) {g : Graph A Label} {h : Graph B Label}
    {a : A} {b : B} (hab : Bisimilar g h a b) : BisimilarBy f g h a b := by
  obtain ⟨R, hR, hr⟩ := hab
  refine ⟨R, fun x y hxy => ?_, hr⟩
  obtain ⟨hl, hc⟩ := hR hxy
  exact ⟨congrArg f hl, hc⟩

/-- A transport keeps a node's term through any label map. -/
theorem IsTransport.bisimilarBy (f : Label → K) {g : Graph A Label}
    {h : Graph B Label} {m : A → B} (hm : IsTransport g h m) (a : A) :
    BisimilarBy f g h a (m a) :=
  (hm.bisimilar a).by_map f

end Relabel

/-- Preserve leaf classes in addition to any chosen numeric comparison policy.
The numeric parameter can carry exact values, or an identity-sensitive format;
choosing it is a language obligation, not a graph-algorithm decision. -/
inductive TermLabel (Symbol : Type u) (Variable : Type v) (Number : Type w) where
  | atom (name : Symbol)
  | variable (id : Variable)
  | number (value : Number)
  | compound (name : Symbol)
  deriving DecidableEq

/-- A zero-argument compound and a symbol of the same spelling are distinct. -/
theorem atom_ne_compound {Symbol : Type u} {Variable : Type v} {Number : Type w}
    (name : Symbol) :
    (TermLabel.atom name : TermLabel Symbol Variable Number) ≠ .compound name := by
  intro h
  cases h

/-- Distinct variable identities do not become equal merely because both are
unbound. Alpha-renaming requires a separate, consistent renaming relation. -/
theorem variable_ne_of_ne {Symbol : Type u} {Variable : Type v} {Number : Type w}
    {x y : Variable} (hne : x ≠ y) :
    (TermLabel.variable x : TermLabel Symbol Variable Number) ≠ .variable y := by
  intro h
  exact hne (TermLabel.variable.inj h)

section PeTTa

open Mettapedia.Machines.PeTTaLeafEquality

variable {Symbol : Type u} {Variable : Type v}

/-- A label as PeTTa's `==` reads it: a number by its value class, an atom, a
variable and a compound name as they are. -/
def TermLabel.pettaClass : TermLabel Symbol Variable Num → TermLabel Symbol Variable Cls
  | .atom name => .atom name
  | .variable id => .variable id
  | .number value => .number (cls value)
  | .compound name => .compound name

/-- On two numeric leaves the class comparison is the runtime's decision. -/
theorem pettaClass_number_eq_iff (x y : Num) :
    (TermLabel.number x : TermLabel Symbol Variable Num).pettaClass =
      (TermLabel.number y).pettaClass ↔ valueEq x y = true := by
  simp [TermLabel.pettaClass, valueEq_iff]

/-- A number is never an atom, a variable, or a compound name. -/
theorem pettaClass_number_ne_atom (x : Num) (name : Symbol) :
    (TermLabel.number x : TermLabel Symbol Variable Num).pettaClass ≠
      (TermLabel.atom name).pettaClass := by
  simp [TermLabel.pettaClass]

/-- PeTTa's `==` on term graphs, cyclic ones included. -/
def PeTTaEq {A : Type w} {B : Type x} (g : Graph A (TermLabel Symbol Variable Num))
    (h : Graph B (TermLabel Symbol Variable Num)) (a : A) (b : B) : Prop :=
  BisimilarBy TermLabel.pettaClass g h a b

end PeTTa

namespace Examples

/-- One node presenting the infinite unary term `f(f(...))`. -/
def oneCycle : Graph Unit Nat where
  label _ := 0
  children _ := [()]

/-- Two nodes presenting the same infinite unary term. -/
def twoCycle : Graph Bool Nat where
  label _ := 0
  children b := [!b]

/-- Equality of rational terms is weaker than graph isomorphism: a cycle may
have a different number of nodes while unfolding to the same term. -/
theorem one_cycle_bisimilar_two_cycle (b : Bool) :
    Bisimilar oneCycle twoCycle () b := by
  refine ⟨fun a b => oneCycle.label a = twoCycle.label b, ?_, rfl⟩
  intro a c hac
  exact ⟨hac, .cons rfl .nil⟩

/-- The complete two-pair certificate validates the differently sized cycles. -/
theorem complete_cycle_certificate :
    checkCertificate oneCycle twoCycle [((), false), ((), true)] () false = true := by
  decide

/-- Merely listing the roots is insufficient: the next argument pair is absent. -/
theorem incomplete_cycle_certificate_rejected :
    checkCertificate oneCycle twoCycle [((), false)] () false = false := by
  decide

/-- Local conditions on an empty relation cannot certify an omitted root. -/
theorem empty_cycle_certificate_rejected :
    checkCertificate oneCycle twoCycle [] () false = false := by
  decide

inductive PairNode where
  | root | left | right
  deriving DecidableEq

/-- Swap only argument positions, retaining node labels and graph nodes. -/
def pairGraph (swapped : Bool) : Graph PairNode Nat where
  label
    | .root => 0
    | .left => 1
    | .right => 2
  children
    | .root => if swapped then [.right, .left] else [.left, .right]
    | _ => []

/-- Forgetting argument positions yields an ordinary unlabelled edge relation. -/
def unlabelledEdge {Node : Type u} {Label : Type v} (g : Graph Node Label)
    (a b : Node) : Prop := b ∈ g.children a

/-- The unlabelled representation cannot see that arguments were swapped. -/
theorem pair_unlabelled_edges_eq :
    unlabelledEdge (pairGraph false) = unlabelledEdge (pairGraph true) := by
  funext a b
  cases a <;> cases b <;> simp [unlabelledEdge, pairGraph]

/-- Consequently hyperset-style bisimilarity accepts the swapped pair. -/
theorem pair_unlabelled_bisimilar :
    Mettapedia.TypeTheory.MaterialSets.Hypersets.Bisimilar
      (unlabelledEdge (pairGraph false)) (unlabelledEdge (pairGraph true))
      PairNode.root PairNode.root := by
  rw [pair_unlabelled_edges_eq]
  exact Mettapedia.TypeTheory.MaterialSets.Hypersets.Bisimilar.rfl

/-- Ordered term equality rejects it at depth two. -/
theorem pair_not_bisimilar :
    ¬ Bisimilar (pairGraph false) (pairGraph true) PairNode.root PairNode.root := by
  apply not_bisimilar_of_observe_ne (depth := 2)
  simp [observe, pairGraph]

/-- Listing the unequal leaf pairs does not hide their unequal labels. -/
theorem swapped_pair_certificate_rejected :
    checkCertificate (pairGraph false) (pairGraph true)
      [(.root, .root), (.left, .right), (.right, .left)]
      PairNode.root PairNode.root = false := by
  decide

/-- A repeated argument is semantically significant, although membership
relations discard repeated edges. -/
def repeatedArgument (twice : Bool) : Graph Bool Nat where
  label b := if b then 1 else 0
  children b := if b then [] else if twice then [true, true] else [true]

theorem repeated_argument_unlabelled_edges_eq :
    unlabelledEdge (repeatedArgument false) = unlabelledEdge (repeatedArgument true) := by
  funext a b
  cases a <;> cases b <;> simp [unlabelledEdge, repeatedArgument]

theorem repeated_argument_not_bisimilar :
    ¬ Bisimilar (repeatedArgument false) (repeatedArgument true) false false := by
  apply not_bisimilar_of_observe_ne (depth := 1)
  simp [observe, repeatedArgument]

/-- A related child cannot justify a mismatch in the number of arguments. -/
theorem unequal_arity_certificate_rejected :
    checkCertificate (repeatedArgument false) (repeatedArgument true)
      [(false, false), (true, true)] false false = false := by
  decide

end Examples

namespace PeTTaExamples

open Mettapedia.Machines.PeTTaLeafEquality

inductive Sym where
  | f | z | q
  deriving DecidableEq

/-- Nodes of `c = f(leaf, c)`. -/
inductive Loop where
  | root | leaf
  deriving DecidableEq

/-- `c = f(n, c)`, with `leaf` the first argument. -/
def loop (leaf : TermLabel Sym Nat Num) : Graph Loop (TermLabel Sym Nat Num) where
  label
    | .root => .compound .f
    | .leaf => leaf
  children
    | .root => [.leaf, .root]
    | .leaf => []

/-- Nodes of `d = f(n, f(n, d))`, the same term unrolled once. -/
inductive Loop2 where
  | root | leaf | inner | innerLeaf
  deriving DecidableEq

def loop2 (leaf : TermLabel Sym Nat Num) : Graph Loop2 (TermLabel Sym Nat Num) where
  label
    | .root => .compound .f
    | .inner => .compound .f
    | _ => leaf
  children
    | .root => [.leaf, .inner]
    | .inner => [.innerLeaf, .root]
    | _ => []

/-- A cycle with a NaN leaf is `==` to itself, and to the cycle of another NaN. -/
theorem nan_loop_eq :
    PeTTaEq (loop (.number (.nan 1))) (loop (.number (.nan 2))) Loop.root Loop.root :=
  checkCertificate_sound (pairs := [(.root, .root), (.leaf, .leaf)]) (by decide)

/-- `c = f(1, c)` and `d = f(1.0, d)` are `==`. -/
theorem int_float_loop_eq :
    PeTTaEq (loop (.number (.int 1))) (loop (.number (.fin 1))) Loop.root Loop.root :=
  checkCertificate_sound (pairs := [(.root, .root), (.leaf, .leaf)]) (by decide)

/-- `c = f(1, c)` and its unrolling `d = f(1, f(1, d))` are `==`. -/
theorem loop_eq_unrolled :
    PeTTaEq (loop (.number (.int 1))) (loop2 (.number (.int 1))) Loop.root Loop2.root :=
  checkCertificate_sound
    (pairs := [(.root, .root), (.leaf, .leaf), (.root, .inner), (.leaf, .innerLeaf)])
    (by decide)

/-- `c = f(1, c)` and `d = f(2, d)` are not. -/
theorem loop_ne_other_leaf :
    ¬ PeTTaEq (loop (.number (.int 1))) (loop (.number (.int 2))) Loop.root Loop.root := by
  apply not_bisimilar_of_observe_ne (depth := 2)
  simp [observe, loop, Graph.mapLabel, TermLabel.pettaClass, cls]

/-- `f(z(), c)` and `f(q(), d)`: zero-argument compounds of different names
are different leaves. -/
theorem loop_ne_other_compound :
    ¬ PeTTaEq (loop (.compound .z)) (loop (.compound .q)) Loop.root Loop.root := by
  apply not_bisimilar_of_observe_ne (depth := 2)
  simp [observe, loop, Graph.mapLabel, TermLabel.pettaClass]

/-- A zero-argument compound is not the atom of its name. -/
theorem loop_ne_atom_leaf :
    ¬ PeTTaEq (loop (.compound .z)) (loop (.atom .z)) Loop.root Loop.root := by
  apply not_bisimilar_of_observe_ne (depth := 2)
  simp [observe, loop, Graph.mapLabel, TermLabel.pettaClass]

end PeTTaExamples

namespace Lexicographic

/-- A completed pair can be certified from its label and its already certified
children. This does not permit using the pair currently being checked as its
own completed premise. -/
theorem completed_pair {A : Type u} {B : Type w} {Label : Type v}
    {g : Graph A Label} {h : Graph B Label} {a : A} {b : B}
    (labels : g.label a = h.label b)
    (children : List.Forall₂ (Bisimilar g h) (g.children a) (h.children b)) :
    Bisimilar g h a b := by
  apply bisimilar_iff_observe_eq.mpr
  intro depth
  cases depth with
  | zero => rfl
  | succ depth =>
    simp only [observe, Observation.node.injEq]
    refine ⟨labels, ?_⟩
    have equalities := children.imp
      (fun _ _ related => (bisimilar_iff_observe_eq.mp related) depth)
    simpa only [← List.forall₂_eq_eq_eq, List.forall₂_map_left_iff,
      List.forall₂_map_right_iff] using equalities

/-- A looping first child followed by a distinguishing leaf. Recording just
the active root pair must not suppress the later distinction. -/
def pendingPairGraph (value : Nat) : Graph Bool Nat where
  label | false => 0 | true => value
  children | false => [false, true] | true => []

theorem pending_pair_is_not_a_certificate :
    ¬ Bisimilar (pendingPairGraph 1) (pendingPairGraph 2) false false := by
  intro related
  have observed := (bisimilar_iff_observe_eq.mp related) 2
  simp [observe, pendingPairGraph] at observed

inductive CrossedNode where
  | a | b | zero | one
  deriving DecidableEq

/-- The equations A = s(B, 0) and B = s(A, 1), as one finite ordered graph. -/
def crossedCycles : Graph CrossedNode Nat where
  label | .a | .b => 0 | .zero => 1 | .one => 2
  children | .a => [.b, .zero] | .b => [.a, .one] | _ => []

theorem crossed_cycles_distinct :
    ¬ Bisimilar crossedCycles crossedCycles .a .b := by
  intro related
  have observed := (bisimilar_iff_observe_eq.mp related) 2
  simp [observe, crossedCycles] at observed

private theorem distinct_head_lex {α : Type u} {r : α → α → Prop}
    {a b : α} {as bs : List α} (different : a ≠ b) :
    List.Lex r (a :: as) (b :: bs) ↔ r a b := by
  constructor
  · intro ordered
    cases ordered with
    | rel related => exact related
    | cons _ => exact (different rfl).elim
  · exact List.Lex.rel

/-- Even this four-node graph rules out a total asymmetric term order that
obeys the ordinary recursive child-lexicographic equations. This is a failure
of the requested extension, not a claim that finite graphs cannot be given
some other, explicitly chosen order. -/
theorem no_total_recursive_lex_order
    (lt : CrossedNode → CrossedNode → Prop)
    (asymmetric : ∀ left right, lt left right → ¬ lt right left)
    (total : lt .a .b ∨ lt .b .a)
    (forward : lt .a .b ↔
      List.Lex lt (crossedCycles.children .a) (crossedCycles.children .b))
    (backward : lt .b .a ↔
      List.Lex lt (crossedCycles.children .b) (crossedCycles.children .a)) : False := by
  have ab : lt .a .b → lt .b .a := by
    intro ordered
    exact (distinct_head_lex (by decide : CrossedNode.b ≠ .a)).mp
      (forward.mp ordered)
  have ba : lt .b .a → lt .a .b := by
    intro ordered
    exact (distinct_head_lex (by decide : CrossedNode.a ≠ .b)).mp
      (backward.mp ordered)
  rcases total with hab | hba
  · exact asymmetric .a .b hab (ab hab)
  · exact asymmetric .b .a hba (ba hba)

end Lexicographic

end Mettapedia.Machines.RationalTermGraph
