import Mathlib.Algebra.BigOperators.Fin
import Mettapedia.Logic.FinitaryRuleSystem.Initiality

/-!
# List-branched finite derivations

`ListBranchedDerivation` is the initial algebra of `F X = J × W × List X`;
`Derivation` instead stores each finite family as an arity and a `Fin n` tuple.
Both syntaxes and evaluators are independently defined.  Conversion preserves
roots, branch order, multiplicity, node count, and replay.  Transport of node
interpretations makes their folds commute and gives list initiality from
indexed initiality, independently of any object logic or bootstrap host.
Replay, ordered witness traces, and node counts retain different observations
of this common finite construction.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.FinitaryRuleSystem

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

universe u v w

/-- A witnessed derivation tree whose finite children are stored as a list. -/
inductive ListBranchedDerivation (J : Type u) (W : Type v) : Type (max u v) where
  | node (conclusion : J) (witness : W)
      (children : List (ListBranchedDerivation J W))

namespace ListBranchedDerivation

variable {J : Type u} {W : Type v}

/-- Root conclusion of a list-branched certificate. -/
def concl : ListBranchedDerivation J W → J
  | .node conclusion _witness _children => conclusion

@[simp]
theorem concl_node (conclusion : J) (witness : W)
    (children : List (ListBranchedDerivation J W)) :
    concl (.node conclusion witness children) = conclusion := rfl

/-- Number of physical rule nodes in a list-branched certificate. -/
def nodeCount : ListBranchedDerivation J W → Nat
  | .node _conclusion _witness children =>
      1 + (children.map nodeCount).sum

@[simp]
theorem nodeCount_node (conclusion : J) (witness : W)
    (children : List (ListBranchedDerivation J W)) :
    nodeCount (.node conclusion witness children) =
      1 + (children.map nodeCount).sum := by
  simp [nodeCount]

/-- Exact replay of a list-branched certificate. -/
def valid {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules) :
    ListBranchedDerivation J interface.W → Bool
  | .node conclusion witness children =>
      interface.isInstance witness (children.map concl) conclusion &&
        (children.map (valid interface)).all id

@[simp]
theorem valid_node {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules)
    (conclusion : J) (witness : interface.W)
    (children : List (ListBranchedDerivation J interface.W)) :
    valid interface (.node conclusion witness children) =
      (interface.isInstance witness (children.map concl) conclusion &&
        (children.map (valid interface)).all id) := by
  simp [valid]

/-- Build the indexed representation from a list of already-converted
children.  `List.equivSigmaTuple` carries the exact finite-list/finite-family
isomorphism. -/
def indexedNodeFromList (conclusion : J) (witness : W)
    (children : List (Derivation J W)) : Derivation J W :=
  let packed := List.equivSigmaTuple children
  .node conclusion witness packed.1 packed.2

@[simp]
theorem indexedNodeFromList_ofFn (conclusion : J) (witness : W)
    (n : Nat) (children : Fin n → Derivation J W) :
    indexedNodeFromList conclusion witness (List.ofFn children) =
      .node conclusion witness n children := by
  unfold indexedNodeFromList
  have packed : List.equivSigmaTuple (List.ofFn children) = ⟨n, children⟩ :=
    List.equivSigmaTuple.right_inv ⟨n, children⟩
  rw [packed]

mutual
  /-- Convert list-branched syntax to the existing indexed syntax. -/
  def toIndexed : ListBranchedDerivation J W → Derivation J W
    | .node conclusion witness children =>
        indexedNodeFromList conclusion witness (toIndexedList children)

  /-- Map the conversion over a list, stated mutually so recursive calls are
  structurally evident to Lean. -/
  def toIndexedList :
      List (ListBranchedDerivation J W) → List (Derivation J W)
    | [] => []
    | child :: children => toIndexed child :: toIndexedList children
end

@[simp]
theorem toIndexedList_eq_map :
    ∀ children : List (ListBranchedDerivation J W),
      toIndexedList children = children.map toIndexed
  | [] => rfl
  | _child :: _children => by
      simp [toIndexedList, toIndexedList_eq_map]

/-- Convert existing indexed syntax to list-branched syntax. -/
def ofIndexed : Derivation J W → ListBranchedDerivation J W
  | .node conclusion witness _n children =>
      .node conclusion witness (List.ofFn fun i => ofIndexed (children i))

@[simp]
theorem ofIndexed_indexedNodeFromList (conclusion : J) (witness : W)
    (children : List (Derivation J W)) :
    ofIndexed (indexedNodeFromList conclusion witness children) =
      .node conclusion witness (children.map ofIndexed) := by
  simp [indexedNodeFromList, List.equivSigmaTuple, ofIndexed]

/-- Converting an indexed tree to a list tree and back is the identity. -/
theorem toIndexed_ofIndexed :
    ∀ tree : Derivation J W, toIndexed (ofIndexed tree) = tree := by
  intro tree
  induction tree with
  | node conclusion witness n children ih =>
      simp only [ofIndexed, toIndexed, toIndexedList_eq_map, List.map_ofFn,
        Function.comp_def, ih, indexedNodeFromList_ofFn]

mutual
  /-- Converting a list tree to an indexed tree and back is the identity. -/
  theorem ofIndexed_toIndexed :
      ∀ tree : ListBranchedDerivation J W,
        ofIndexed (toIndexed tree) = tree
    | .node conclusion witness children => by
        simp only [toIndexed, ofIndexed_indexedNodeFromList]
        congr 1
        exact ofIndexed_toIndexedList children

  theorem ofIndexed_toIndexedList :
      ∀ children : List (ListBranchedDerivation J W),
        (toIndexedList children).map ofIndexed = children
    | [] => rfl
    | child :: children => by
        simp only [toIndexedList, List.map_cons, List.cons.injEq]
        exact ⟨ofIndexed_toIndexed child, ofIndexed_toIndexedList children⟩
end

/-- The exact equivalence between list and indexed finite branching. -/
def equivIndexed : ListBranchedDerivation J W ≃ Derivation J W where
  toFun := toIndexed
  invFun := ofIndexed
  left_inv := ofIndexed_toIndexed
  right_inv := toIndexed_ofIndexed

@[simp]
theorem indexedNodeFromList_concl (conclusion : J) (witness : W)
    (children : List (Derivation J W)) :
    (indexedNodeFromList conclusion witness children).concl = conclusion := by
  simp [indexedNodeFromList, List.equivSigmaTuple, Derivation.concl]

@[simp]
theorem concl_toIndexed : ∀ tree : ListBranchedDerivation J W,
    (toIndexed tree).concl = tree.concl
  | .node conclusion witness children => by
      simp [toIndexed, concl]

@[simp]
theorem concl_ofIndexed (tree : Derivation J W) :
    (ofIndexed tree).concl = tree.concl := by
  cases tree
  rfl

@[simp]
theorem indexedNodeFromList_nodeCount (conclusion : J) (witness : W)
    (children : List (Derivation J W)) :
    (indexedNodeFromList conclusion witness children).nodeCount =
      1 + (children.map Derivation.nodeCount).sum := by
  simp [indexedNodeFromList, List.equivSigmaTuple]

@[simp]
theorem nodeCount_ofIndexed (tree : Derivation J W) :
    (ofIndexed tree).nodeCount = tree.nodeCount := by
  induction tree with
  | node conclusion witness n children ih =>
      simp only [ofIndexed, nodeCount_node, List.map_ofFn, List.sum_ofFn,
        Derivation.nodeCount_node, Function.comp_def, ih]

/-- Node count is invariant under conversion to indexed branching. -/
theorem nodeCount_toIndexed (tree : ListBranchedDerivation J W) :
    (toIndexed tree).nodeCount = tree.nodeCount := by
  simpa only [ofIndexed_toIndexed] using (nodeCount_ofIndexed (toIndexed tree)).symm

theorem nodeCounts_toIndexedList (children : List (ListBranchedDerivation J W)) :
    (toIndexedList children).map Derivation.nodeCount = children.map nodeCount := by
  simp only [toIndexedList_eq_map, List.map_map, Function.comp_def, nodeCount_toIndexed]

@[simp]
theorem indexedNodeFromList_valid {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules)
    (conclusion : J) (witness : interface.W)
    (children : List (Derivation J interface.W)) :
    (indexedNodeFromList conclusion witness children).valid interface =
      (interface.isInstance witness (children.map Derivation.concl) conclusion &&
        (children.map (Derivation.valid interface)).all id) := by
  simp [indexedNodeFromList, List.equivSigmaTuple, Derivation.valid]

@[simp]
theorem valid_ofIndexed {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules) (tree : Derivation J interface.W) :
    (ofIndexed tree).valid interface = tree.valid interface := by
  induction tree with
  | node conclusion witness n children ih =>
      simp only [ofIndexed, valid_node, List.map_ofFn, Function.comp_def,
        concl_ofIndexed, Derivation.valid, ih]

/-- Replay is invariant under conversion to indexed branching. -/
theorem valid_toIndexed {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules) (tree : ListBranchedDerivation J interface.W) :
    (toIndexed tree).valid interface = tree.valid interface := by
  simpa only [ofIndexed_toIndexed] using (valid_ofIndexed interface (toIndexed tree)).symm

theorem validities_toIndexedList {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules)
    (children : List (ListBranchedDerivation J interface.W)) :
    (toIndexedList children).map (Derivation.valid interface) =
      children.map (valid interface) := by
  simp only [toIndexedList_eq_map, List.map_map, Function.comp_def, valid_toIndexed]

/-- Accepted list-branched certificates reconstruct semantic derivability. -/
theorem valid_sound {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules)
    (certificate : ListBranchedDerivation J interface.W)
    (accepted : certificate.valid interface = true) :
    Derives rules certificate.concl := by
  simpa only [concl_toIndexed] using Derivation.valid_sound interface
    (toIndexed certificate) ((valid_toIndexed interface certificate).trans accepted)

/-- Derivability is exactly the existence of an accepted list-branched
certificate with the requested root. -/
theorem derives_iff_exists_accepted {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules) (judgment : J) :
    Derives rules judgment ↔
      ∃ certificate : ListBranchedDerivation J interface.W,
        certificate.valid interface = true ∧ certificate.concl = judgment := by
  constructor
  · intro derivable
    obtain ⟨certificate, accepted, root⟩ :=
      Derives.exists_derivation interface derivable
    exact ⟨ofIndexed certificate, by simpa, by simpa using root⟩
  · rintro ⟨certificate, accepted, root⟩
    rw [← root]
    exact valid_sound interface certificate accepted

/-- An interpretation of one list-branched derivation layer. -/
structure ListNodeAlgebra (J : Type u) (W : Type v) where
  Carrier : Type w
  node : J → W → List Carrier → Carrier

namespace ListNodeAlgebra

variable {J : Type u} {W : Type v}

/-- Interpret indexed children in their supplied order as a finite list. -/
def asIndexed (A : ListNodeAlgebra.{u, v, w} J W) : NodeAlgebra.{u, v, w} J W where
  Carrier := A.Carrier
  node := fun conclusion witness _n children =>
    A.node conclusion witness (List.ofFn children)

/-- A function preserving list-branched node formation. -/
@[ext]
structure Hom (A B : ListNodeAlgebra.{u, v, w} J W) where
  toFun : A.Carrier → B.Carrier
  map_node : ∀ conclusion witness children,
    toFun (A.node conclusion witness children) =
      B.node conclusion witness (children.map toFun)

instance {A B : ListNodeAlgebra.{u, v, w} J W} :
    CoeFun (Hom A B) (fun _ => A.Carrier → B.Carrier) :=
  ⟨Hom.toFun⟩

@[ext]
theorem Hom.ext' {A B : ListNodeAlgebra.{u, v, w} J W} (f g : Hom A B)
    (pointwise : ∀ value, f value = g value) : f = g :=
  Hom.ext (funext pointwise)

def Hom.id (A : ListNodeAlgebra.{u, v, w} J W) : Hom A A where
  toFun := fun value => value
  map_node := by intros; simp

def Hom.comp {A B C : ListNodeAlgebra.{u, v, w} J W}
    (f : Hom A B) (g : Hom B C) : Hom A C where
  toFun := fun value => g (f value)
  map_node := by
    intro conclusion witness children
    rw [f.map_node, g.map_node, List.map_map]
    simp [Function.comp_def]

instance : Category (ListNodeAlgebra.{u, v, w} J W) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := by intros; ext; simp [Hom.comp, Hom.id]
  comp_id := by intros; ext; simp [Hom.comp, Hom.id]
  assoc := by intros; ext; simp [Hom.comp]

/-- The list-branched syntax algebra itself. -/
def syntaxAlgebra : ListNodeAlgebra.{u, v, max u v} J W where
  Carrier := ListBranchedDerivation J W
  node := ListBranchedDerivation.node

/-- Structural fold from list-branched syntax. -/
def fold (A : ListNodeAlgebra.{u, v, max u v} J W) :
    ListBranchedDerivation J W → A.Carrier
  | .node conclusion witness children =>
      A.node conclusion witness (children.map (fold A))

@[simp]
theorem fold_node (A : ListNodeAlgebra.{u, v, max u v} J W)
    (conclusion : J) (witness : W)
    (children : List (ListBranchedDerivation J W)) :
    fold A (.node conclusion witness children) =
      A.node conclusion witness (children.map (fold A)) := by
  simp [fold]

def foldHom (A : ListNodeAlgebra.{u, v, max u v} J W) :
    syntaxAlgebra ⟶ A where
  toFun := fold A
  map_node := by
    intro conclusion witness children
    exact fold_node A conclusion witness children

/-- Every list fold agrees with the indexed fold of the transported algebra. -/
theorem fold_asIndexed (A : ListNodeAlgebra.{u, v, max u v} J W)
    (tree : ListBranchedDerivation J W) :
    NodeAlgebra.fold A.asIndexed (toIndexed tree) = fold A tree := by
  suffices ∀ indexed, NodeAlgebra.fold A.asIndexed indexed = fold A (ofIndexed indexed) by
    simpa only [ofIndexed_toIndexed] using this (toIndexed tree)
  intro indexed
  induction indexed with
  | node conclusion witness n children ih =>
      rw [NodeAlgebra.fold_node, ofIndexed, fold_node, List.map_ofFn]
      exact congrArg (A.node conclusion witness) (congrArg List.ofFn (funext ih))

/-- Every homomorphism from syntax is its structural fold, by indexed initiality. -/
theorem hom_eq_fold_pointwise (A : ListNodeAlgebra.{u, v, max u v} J W)
    (f : syntaxAlgebra ⟶ A) : ∀ tree, f.toFun tree = fold A tree := by
  let g : NodeAlgebra.derivationAlgebra ⟶ A.asIndexed :=
    { toFun := fun indexed => f.toFun (ofIndexed indexed)
      map_node := fun conclusion witness n children => by
        simpa only [NodeAlgebra.derivationAlgebra, syntaxAlgebra, asIndexed,
          ofIndexed, List.map_ofFn, Function.comp_def] using
          f.map_node conclusion witness (List.ofFn fun i => ofIndexed (children i)) }
  intro tree
  change ListBranchedDerivation J W at tree
  have unique := congrArg
    (fun h : NodeAlgebra.derivationAlgebra ⟶ A.asIndexed => h.toFun (toIndexed tree))
    (NodeAlgebra.hom_eq_fold A.asIndexed g)
  change f.toFun (ofIndexed (toIndexed tree)) = _ at unique
  rw [ofIndexed_toIndexed] at unique
  exact unique.trans (fold_asIndexed A tree)

theorem hom_eq_fold_children (A : ListNodeAlgebra.{u, v, max u v} J W)
    (f : syntaxAlgebra ⟶ A) : ∀ children : List (ListBranchedDerivation J W),
    children.map f.toFun = children.map (fold A) :=
  fun _ => List.map_congr_left fun child _ => hom_eq_fold_pointwise A f child

theorem hom_eq_fold (A : ListNodeAlgebra.{u, v, max u v} J W)
    (f : syntaxAlgebra ⟶ A) : f = foldHom A :=
  Hom.ext' _ _ (hom_eq_fold_pointwise A f)

/-- Node-preserving observations commute with a list-branched fold. -/
theorem fold_fusion {A B : ListNodeAlgebra.{u, v, max u v} J W}
    (f : A ⟶ B) (tree : ListBranchedDerivation J W) :
    f.toFun (fold A tree) = fold B tree :=
  congrArg (fun g : syntaxAlgebra ⟶ B => g.toFun tree)
    (hom_eq_fold B (foldHom A ≫ f))

/-- `ListBranchedDerivation` is the initial algebra of
`F X = J × W × List X`. -/
def syntaxAlgebra_isInitial :
    IsInitial (syntaxAlgebra (J := J) (W := W)) :=
  IsInitial.ofUniqueHom foldHom (fun A f => hom_eq_fold A f)

/-- Node interpretation retaining only the root conclusion. -/
def conclusionAlgebra : ListNodeAlgebra.{u, v, max u v} J W where
  Carrier := ULift.{max u v, u} J
  node := fun conclusion _witness _children => ULift.up conclusion

theorem fold_conclusion (tree : ListBranchedDerivation J W) :
    (fold conclusionAlgebra tree).down = tree.concl := by
  cases tree
  simp [conclusionAlgebra, ListBranchedDerivation.concl]

/-- Node interpretation counting physical rule nodes. -/
def nodeCountAlgebra : ListNodeAlgebra.{u, v, max u v} J W where
  Carrier := ULift.{max u v, 0} Nat
  node := fun _conclusion _witness children =>
    ULift.up (1 + (children.map ULift.down).sum)

theorem fold_nodeCount (tree : ListBranchedDerivation J W) :
    (fold nodeCountAlgebra tree).down = tree.nodeCount := by
  let interpreter : syntaxAlgebra ⟶ nodeCountAlgebra (J := J) (W := W) :=
    { toFun := fun t => ULift.up t.nodeCount
      map_node := fun _ _ (children : List (ListBranchedDerivation J W)) => by
        simp only [syntaxAlgebra, nodeCountAlgebra, nodeCount_node, List.map_map, Function.comp_def] }
  exact (congrArg (fun h => (h.toFun tree).down) (hom_eq_fold _ interpreter)).symm

theorem fold_nodeCounts (children : List (ListBranchedDerivation J W)) :
    (children.map (fold nodeCountAlgebra)).map ULift.down =
      children.map ListBranchedDerivation.nodeCount := by
  dsimp only [nodeCountAlgebra]
  rw [List.map_map]
  exact List.map_congr_left fun child _ => fold_nodeCount child

/-- A single fold computing both root conclusion and exact replay. -/
def replayAlgebra {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules) :
    ListNodeAlgebra.{u, v, max u v} J interface.W where
  Carrier := ULift.{max u v, max u 0} (J × Bool)
  node := fun conclusion witness children =>
    ULift.up (conclusion,
      interface.isInstance witness (children.map (fun child => child.down.1))
          conclusion &&
        (children.map (fun child => child.down.2)).all id)

theorem fold_replay {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules) (tree : ListBranchedDerivation J interface.W) :
    (fold (replayAlgebra interface) tree).down = (tree.concl, tree.valid interface) := by
  let interpreter : syntaxAlgebra ⟶ replayAlgebra interface :=
    { toFun := fun t => ULift.up (t.concl, t.valid interface)
      map_node := fun _ _ (children : List (ListBranchedDerivation J interface.W)) => by
        simp only [syntaxAlgebra, replayAlgebra, concl_node, valid_node,
          List.map_map, Function.comp_def] }
  exact (congrArg (fun h => (h.toFun tree).down) (hom_eq_fold _ interpreter)).symm

theorem fold_replays {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules)
    (children : List (ListBranchedDerivation J interface.W)) :
    (children.map (fold (replayAlgebra interface))).map ULift.down =
      children.map fun child => (child.concl, child.valid interface) := by
  dsimp only [replayAlgebra]
  rw [List.map_map]
  exact List.map_congr_left fun child _ => fold_replay interface child

/-- Ordered rule-witness occurrences, including the root and every child. -/
def witnessTraceAlgebra : ListNodeAlgebra.{u, v, max u v} J W where
  Carrier := ULift.{max u v, v} (List W)
  node := fun _ witness children => ULift.up (witness :: children.flatMap ULift.down)

/-- Preorder observation retains witness order and repeated occurrences. -/
def witnessTrace (tree : ListBranchedDerivation J W) : List W :=
  (fold witnessTraceAlgebra tree).down

theorem witnessTrace_toIndexed (tree : ListBranchedDerivation J W) :
    (NodeAlgebra.fold witnessTraceAlgebra.asIndexed (toIndexed tree)).down = witnessTrace tree :=
  congrArg ULift.down (fold_asIndexed _ tree)

/-- Trace length is a node-preserving observation into physical node count. -/
def traceLengthHom : witnessTraceAlgebra ⟶ nodeCountAlgebra (J := J) (W := W) where
  toFun := fun trace => ULift.up trace.down.length
  map_node := fun _ _ (children : List (ULift.{max u v, v} (List W))) => by
    simp [witnessTraceAlgebra, nodeCountAlgebra, List.length_flatMap, List.map_map,
      Function.comp_def, Nat.add_comm]

theorem witnessTrace_length (tree : ListBranchedDerivation J W) :
    (witnessTrace tree).length = tree.nodeCount :=
  (congrArg ULift.down (fold_fusion traceLengthHom tree)).trans (fold_nodeCount tree)

end ListNodeAlgebra

end ListBranchedDerivation

namespace NodeAlgebra

open ListBranchedDerivation

variable {J : Type u} {W : Type v}

/-- Interpret a finite list by its exact indexed tuple, retaining order and repetitions. -/
def asList (A : NodeAlgebra.{u, v, w} J W) :
    ListNodeAlgebra.{u, v, w} J W where
  Carrier := A.Carrier
  node := fun conclusion witness children =>
    let packed := List.equivSigmaTuple children
    A.node conclusion witness packed.1 packed.2

@[simp]
theorem asList_node_ofFn (A : NodeAlgebra.{u, v, w} J W)
    (conclusion : J) (witness : W) (n : Nat) (children : Fin n → A.Carrier) :
    A.asList.node conclusion witness (List.ofFn children) = A.node conclusion witness n children := by
  dsimp only [asList]
  rw [show List.equivSigmaTuple (List.ofFn children) = ⟨n, children⟩ from
    List.equivSigmaTuple.right_inv ⟨n, children⟩]

/-- Indexed interpretation also agrees with its transported list fold. -/
theorem fold_asList (A : NodeAlgebra.{u, v, max u v} J W) (tree : Derivation J W) :
    ListNodeAlgebra.fold A.asList (ofIndexed tree) = fold A tree := by
  induction tree with
  | node conclusion witness n children ih =>
      rw [ofIndexed, ListNodeAlgebra.fold_node, List.map_ofFn]
      exact (asList_node_ofFn A conclusion witness n _).trans
        (congrArg (A.node conclusion witness n) (funext ih))

end NodeAlgebra

end Mettapedia.Logic.FinitaryRuleSystem
