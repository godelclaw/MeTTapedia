import Mettapedia.Logic.PropositionalHilbertChecking
import Foundation.Propositional.Kripke.Logic.Int
import Mathlib.Data.Nat.Find

/-!
# Intuitionistic proofs and finite countermodels

Proof checking uses the original intuitionistic Hilbert calculus. A separate
finite-model checker validates a partial order, a persistent valuation and a
refuting world. All tables are finite data with unbounded natural indices;
no semantic oracle is used to evaluate a submitted model.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.IntuitionisticDecision

open LO LO.Propositional LO.Propositional.Kripke
open PropositionalHilbertChecking

structure ModelPacket where
  worlds : Nat
  edges : List (Nat × Nat)
  values : List (Nat × Nat)
  root : Nat
  deriving DecidableEq

def related (packet : ModelPacket) (source target : Nat) : Prop :=
  (source, target) ∈ packet.edges

instance (packet : ModelPacket) (source target : Nat) : Decidable (related packet source target) :=
  inferInstanceAs (Decidable ((source, target) ∈ packet.edges))

@[mk_iff]
structure WellFormed (packet : ModelPacket) : Prop where
  nonempty : 0 < packet.worlds
  root : packet.root < packet.worlds
  edges : ∀ pair ∈ packet.edges, pair.1 < packet.worlds ∧ pair.2 < packet.worlds
  values : ∀ pair ∈ packet.values, pair.1 < packet.worlds
  reflexive : ∀ world < packet.worlds, related packet world world
  transitive : ∀ first < packet.worlds, ∀ middle < packet.worlds, ∀ last < packet.worlds,
    related packet first middle → related packet middle last → related packet first last
  antisymmetric : ∀ first < packet.worlds, ∀ last < packet.worlds,
    related packet first last → related packet last first → first = last
  persistent : ∀ pair ∈ packet.values, ∀ target < packet.worlds,
    related packet pair.1 target → (target, pair.2) ∈ packet.values

def checkWellFormed (packet : ModelPacket) : Bool :=
  decide (0 < packet.worlds) && decide (packet.root < packet.worlds) &&
    packet.edges.all (fun pair => decide (pair.1 < packet.worlds ∧ pair.2 < packet.worlds)) &&
    packet.values.all (fun pair => decide (pair.1 < packet.worlds)) &&
    (List.range packet.worlds).all (fun world => decide (related packet world world)) &&
    (List.range packet.worlds).all (fun first => (List.range packet.worlds).all fun middle =>
      (List.range packet.worlds).all fun last =>
        decide (related packet first middle → related packet middle last → related packet first last)) &&
    (List.range packet.worlds).all (fun first => (List.range packet.worlds).all fun last =>
      decide (related packet first last → related packet last first → first = last)) &&
    packet.values.all (fun pair => (List.range packet.worlds).all fun target =>
      decide (related packet pair.1 target → (target, pair.2) ∈ packet.values))

theorem checkWellFormed_exact (packet : ModelPacket) : checkWellFormed packet = true ↔ WellFormed packet := by
  simp only [checkWellFormed, wellFormed_iff, Bool.and_eq_true,
    List.all_eq_true, List.mem_range, decide_eq_true_eq, and_assoc]

instance (packet : ModelPacket) : Decidable (WellFormed packet) :=
  decidable_of_iff (checkWellFormed packet = true) (checkWellFormed_exact packet)

def ModelPacket.toModel (packet : ModelPacket) (valid : WellFormed packet) : Kripke.Model where
  World := Fin packet.worlds
  Rel first last := related packet first.val last.val
  world_nonempty := ⟨⟨packet.root, valid.root⟩⟩
  rel_partial_order := {
    refl := fun world => valid.reflexive world.val world.isLt
    trans := fun first middle last => valid.transitive first.val first.isLt middle.val middle.isLt last.val last.isLt
    antisymm := fun first last forward backward => Fin.ext
      (valid.antisymmetric first.val first.isLt last.val last.isLt forward backward) }
  Val := {
    Val := fun name world => (world.val, name) ∈ packet.values
    hereditary := fun {_ target} edge {_} member => valid.persistent _ member target.val target.isLt edge }

def evaluate (packet : ModelPacket) (world : Nat) : Formula → Bool
  | .atom name => decide ((world, name) ∈ packet.values)
  | .falsum => false
  | .and first second => evaluate packet world first && evaluate packet world second
  | .or first second => evaluate packet world first || evaluate packet world second
  | .imp first second => (List.range packet.worlds).all fun target =>
      decide (related packet world target → evaluate packet target first = true → evaluate packet target second = true)

theorem evaluate_exact (packet : ModelPacket) (valid : WellFormed packet)
    (formula : Formula) (world : Fin packet.worlds) :
    evaluate packet world.val formula = true ↔
      Formula.Kripke.Satisfies (packet.toModel valid) world formula := by
  induction formula generalizing world with
  | atom name => simp [evaluate, Formula.Kripke.Satisfies, ModelPacket.toModel]
  | falsum => simp [evaluate, Formula.Kripke.Satisfies]
  | and first second ihFirst ihSecond =>
      simp only [evaluate, Bool.and_eq_true, Formula.Kripke.Satisfies, ihFirst, ihSecond]
  | or first second ihFirst ihSecond =>
      simp only [evaluate, Bool.or_eq_true, Formula.Kripke.Satisfies, ihFirst, ihSecond]
  | imp first second ihFirst ihSecond =>
      simp only [evaluate, List.all_eq_true, List.mem_range, decide_eq_true_eq, Formula.Kripke.Satisfies]
      constructor
      · intro checked target edge firstTrue
        exact (ihSecond target).mp
          (checked target.val target.isLt edge ((ihFirst target).mpr firstTrue))
      · intro validAt target bounded edge firstTrue
        exact (ihSecond ⟨target, bounded⟩).mpr
          (validAt edge ((ihFirst ⟨target, bounded⟩).mp firstTrue))

def checkCountermodel (formula : Formula) (packet : ModelPacket) : Bool :=
  decide (WellFormed packet) && !evaluate packet packet.root formula

theorem countermodel_sound (formula : Formula) (packet : ModelPacket)
    (accepted : checkCountermodel formula packet = true) : ¬ Source .intuitionistic formula := by
  have both := Bool.and_eq_true_iff.mp accepted
  have valid : WellFormed packet := of_decide_eq_true both.1
  have refutes : evaluate packet packet.root formula = false := by
    cases computed : evaluate packet packet.root formula <;> simp_all
  intro proved
  have theorem' : Propositional.Int ⊢ formula := Logic.iff_provable.mpr proved
  have allModels : FrameClass.Int ⊧ formula := Sound.sound theorem'
  have atRoot : Formula.Kripke.Satisfies (packet.toModel valid) ⟨packet.root, valid.root⟩ formula :=
    allModels (Set.mem_univ _) (packet.toModel valid).Val ⟨packet.root, valid.root⟩
  have acceptedTruth := (evaluate_exact packet valid formula ⟨packet.root, valid.root⟩).mpr atRoot
  simp [refutes] at acceptedTruth

def atomBound : Formula → Nat
  | .atom name => name + 1
  | .falsum => 0
  | .and first second | .or first second | .imp first second => max (atomBound first) (atomBound second)

def pairs (rows columns : Nat) : List (Nat × Nat) :=
  (List.range rows).flatMap fun row => (List.range columns).map fun column => (row, column)

theorem mem_pairs (rows columns row column : Nat) :
    (row, column) ∈ pairs rows columns ↔ row < rows ∧ column < columns := by
  simp [pairs, List.mem_flatMap]

def table (rows columns : Nat) (predicate : Nat → Nat → Prop) [DecidableRel predicate] :
    List (Nat × Nat) :=
  (pairs rows columns).filter fun pair => decide (predicate pair.1 pair.2)

theorem mem_table (rows columns : Nat) (predicate : Nat → Nat → Prop) [DecidableRel predicate]
    (row column : Nat) :
    (row, column) ∈ table rows columns predicate ↔
      row < rows ∧ column < columns ∧ predicate row column := by
  simp [table, mem_pairs, and_assoc]

def worldAt {size : Nat} (model : Kripke.Model) (equivalence : Fin size ≃ model.World)
    (fallback : model.World) (index : Nat) : model.World :=
  if bounded : index < size then equivalence ⟨index, bounded⟩ else fallback

theorem worldAt_bounded {size : Nat} (model : Kripke.Model) (equivalence : Fin size ≃ model.World)
    (fallback : model.World) (index : Nat) (bounded : index < size) :
    worldAt model equivalence fallback index = equivalence ⟨index, bounded⟩ := by
  simp [worldAt, bounded]

/-- A finite-model completeness witness. This construction occurs only in
the proof of coverage: the executable checker reads submitted finite tables
and never queries the possibly undecidable source model. -/
noncomputable def capture {size : Nat} (model : Kripke.Model)
    (equivalence : Fin size ≃ model.World) (root : model.World) (cutoff : Nat) : ModelPacket := by
  classical
  let interpret := worldAt model equivalence root
  exact ⟨size, table size size (fun first last => model.Rel (interpret first) (interpret last)),
    table size cutoff (fun world name => model name (interpret world)), (equivalence.symm root).val⟩

theorem capture_edges {size : Nat} (model : Kripke.Model) (equivalence : Fin size ≃ model.World)
    (root : model.World) (cutoff first last : Nat) :
    related (capture model equivalence root cutoff) first last ↔
      first < size ∧ last < size ∧ model.Rel
        (worldAt model equivalence root first) (worldAt model equivalence root last) := by
  classical
  exact mem_table size size (fun first last => model.Rel
    (worldAt model equivalence root first) (worldAt model equivalence root last)) first last

theorem capture_values {size : Nat} (model : Kripke.Model) (equivalence : Fin size ≃ model.World)
    (root : model.World) (cutoff world name : Nat) :
    (world, name) ∈ (capture model equivalence root cutoff).values ↔
      world < size ∧ name < cutoff ∧ model name (worldAt model equivalence root world) := by
  classical
  exact mem_table size cutoff (fun world name => model name (worldAt model equivalence root world)) world name

theorem capture_wellFormed {size : Nat} (model : Kripke.Model) (equivalence : Fin size ≃ model.World)
    (root : model.World) (cutoff : Nat) : WellFormed (capture model equivalence root cutoff) := by
  have nonempty : 0 < size := lt_of_le_of_lt (Nat.zero_le _) (equivalence.symm root).isLt
  refine ⟨nonempty, (equivalence.symm root).isLt, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨first, last⟩ member
    have edge := (capture_edges model equivalence root cutoff first last).mp member
    exact ⟨edge.1, edge.2.1⟩
  · rintro ⟨world, name⟩ member
    exact ((capture_values model equivalence root cutoff world name).mp member).1
  · intro world bounded
    exact (capture_edges model equivalence root cutoff world world).mpr
      ⟨bounded, bounded, model.refl⟩
  · intro first firstBound middle middleBound last lastBound firstEdge secondEdge
    have firstRel := ((capture_edges model equivalence root cutoff first middle).mp firstEdge).2.2
    have secondRel := ((capture_edges model equivalence root cutoff middle last).mp secondEdge).2.2
    exact (capture_edges model equivalence root cutoff first last).mpr
      ⟨firstBound, lastBound, model.trans firstRel secondRel⟩
  · intro first firstBound last lastBound forward backward
    change first < size at firstBound
    change last < size at lastBound
    have forwardRel := ((capture_edges model equivalence root cutoff first last).mp forward).2.2
    have backwardRel := ((capture_edges model equivalence root cutoff last first).mp backward).2.2
    have equal := model.antisymm forwardRel backwardRel
    rw [worldAt_bounded model equivalence root first firstBound,
      worldAt_bounded model equivalence root last lastBound] at equal
    exact congrArg Fin.val (equivalence.injective equal)
  · rintro ⟨world, name⟩ member target targetBound edge
    obtain ⟨worldBound, nameBound, trueAt⟩ :=
      (capture_values model equivalence root cutoff world name).mp member
    have related := ((capture_edges model equivalence root cutoff world target).mp edge).2.2
    exact (capture_values model equivalence root cutoff target name).mpr
      ⟨targetBound, nameBound, model.Val.hereditary related trueAt⟩

theorem evaluate_simulation (packet : ModelPacket) (model : Kripke.Model)
    (interpret : Nat → model.World) (cutoff : Nat)
    (covers : ∀ world, ∃ index < packet.worlds, interpret index = world)
    (edges : ∀ first < packet.worlds, ∀ last < packet.worlds,
      related packet first last ↔ model.Rel (interpret first) (interpret last))
    (values : ∀ world < packet.worlds, ∀ name < cutoff,
      (world, name) ∈ packet.values ↔ model name (interpret world))
    (formula : Formula) (bounded : atomBound formula ≤ cutoff) (world : Nat) (worldBound : world < packet.worlds) :
    evaluate packet world formula = true ↔ Formula.Kripke.Satisfies model (interpret world) formula := by
  induction formula generalizing world with
  | atom name =>
      simpa only [evaluate, decide_eq_true_eq, Formula.Kripke.Satisfies] using
        values world worldBound name (by simp only [atomBound] at bounded; omega)
  | falsum => simp [evaluate, Formula.Kripke.Satisfies]
  | and first second ihFirst ihSecond =>
      have firstBound : atomBound first ≤ cutoff := (Nat.le_max_left _ _).trans bounded
      have secondBound : atomBound second ≤ cutoff := (Nat.le_max_right _ _).trans bounded
      simpa only [evaluate, Bool.and_eq_true, Formula.Kripke.Satisfies] using
        and_congr (ihFirst firstBound world worldBound) (ihSecond secondBound world worldBound)
  | or first second ihFirst ihSecond =>
      have firstBound : atomBound first ≤ cutoff := (Nat.le_max_left _ _).trans bounded
      have secondBound : atomBound second ≤ cutoff := (Nat.le_max_right _ _).trans bounded
      simpa only [evaluate, Bool.or_eq_true, Formula.Kripke.Satisfies] using
        or_congr (ihFirst firstBound world worldBound) (ihSecond secondBound world worldBound)
  | imp first second ihFirst ihSecond =>
      have firstBound : atomBound first ≤ cutoff := (Nat.le_max_left _ _).trans bounded
      have secondBound : atomBound second ≤ cutoff := (Nat.le_max_right _ _).trans bounded
      simp only [evaluate, List.all_eq_true, List.mem_range, decide_eq_true_eq, Formula.Kripke.Satisfies]
      constructor
      · intro checked target edge firstTrue
        obtain ⟨index, indexBound, same⟩ := covers target
        subst target
        exact (ihSecond secondBound index indexBound).mp
          (checked index indexBound ((edges _ worldBound _ indexBound).mpr edge)
            ((ihFirst firstBound index indexBound).mpr firstTrue))
      · intro trueAt target targetBound edge firstTrue
        exact (ihSecond secondBound target targetBound).mpr
          (trueAt ((edges _ worldBound _ targetBound).mp edge)
            ((ihFirst firstBound target targetBound).mp firstTrue))

theorem capture_evaluate {size : Nat} (model : Kripke.Model) (equivalence : Fin size ≃ model.World)
    (root : model.World) (formula : Formula) :
    evaluate (capture model equivalence root (atomBound formula)) (equivalence.symm root).val formula = true ↔
      Formula.Kripke.Satisfies model root formula := by
  have covers : ∀ world, ∃ index < size, worldAt model equivalence root index = world := by
    intro world
    exact ⟨(equivalence.symm world).val, (equivalence.symm world).isLt, by
      simp [worldAt, (equivalence.symm world).isLt]⟩
  have exactEval := evaluate_simulation (capture model equivalence root (atomBound formula)) model
    (worldAt model equivalence root) (atomBound formula) covers
    (by
      intro first firstBound last lastBound
      change first < size at firstBound
      change last < size at lastBound
      simp [capture_edges, firstBound, lastBound])
    (by
      intro world worldBound name nameBound
      change world < size at worldBound
      simp [capture_values, worldBound, nameBound])
    formula (Nat.le_refl _) (equivalence.symm root).val (equivalence.symm root).isLt
  simpa [worldAt, (equivalence.symm root).isLt] using exactEval

/-- Finite-model completeness supplies an actual finite data certificate
for every non-theorem. It supplies no practical bound on search time. -/
theorem countermodel_complete (formula : Formula) (unproved : ¬ Source .intuitionistic formula) :
    ∃ packet, checkCountermodel formula packet = true := by
  classical
  have invalid : ¬ FrameClass.finite_Int ⊧ formula := by
    intro valid
    have proved : Propositional.Int ⊢ formula := Complete.complete (𝓜 := FrameClass.finite_Int) valid
    exact unproved (Logic.iff_provable.mp proved)
  obtain ⟨model, world, finite, refutes⟩ :=
    exists_model_world_of_not_validOnFrameClass invalid
  let : Frame.IsFinite model.toFrame := finite
  let : Fintype model.World := Fintype.ofFinite model.World
  let equivalence := (Fintype.equivFin model.World).symm
  let packet := capture model equivalence world (atomBound formula)
  refine ⟨packet, ?_⟩
  have valid : WellFormed packet := capture_wellFormed _ _ _ _
  have notTrue : evaluate packet packet.root formula ≠ true := by
    intro accepted
    exact refutes ((capture_evaluate model equivalence world formula).mp accepted)
  simp [checkCountermodel, valid, notTrue]

theorem countermodel_coverage (formula : Formula) :
    (∃ packet, checkCountermodel formula packet = true) ↔ ¬ Source .intuitionistic formula :=
  ⟨fun ⟨packet, accepted⟩ => countermodel_sound formula packet accepted, countermodel_complete formula⟩

/-! ## An exhaustive, terminating decision procedure -/

private def codeData : Code → Nat × List Formula
  | .truth => (0, [])
  | .k first second => (1, [first, second])
  | .s first second third => (2, [first, second, third])
  | .andLeft first second => (3, [first, second])
  | .andRight first second => (4, [first, second])
  | .andIntro first second => (5, [first, second])
  | .orLeft first second => (6, [first, second])
  | .orRight first second => (7, [first, second])
  | .orElim first second third => (8, [first, second, third])
  | .explosion formula => (9, [formula])
  | .excludedMiddle formula => (10, [formula])
  | .mp first second => (11, [first, second])

private def readCode : Nat × List Formula → Option Code
  | (0, []) => some .truth
  | (1, [first, second]) => some (.k first second)
  | (2, [first, second, third]) => some (.s first second third)
  | (3, [first, second]) => some (.andLeft first second)
  | (4, [first, second]) => some (.andRight first second)
  | (5, [first, second]) => some (.andIntro first second)
  | (6, [first, second]) => some (.orLeft first second)
  | (7, [first, second]) => some (.orRight first second)
  | (8, [first, second, third]) => some (.orElim first second third)
  | (9, [formula]) => some (.explosion formula)
  | (10, [formula]) => some (.excludedMiddle formula)
  | (11, [first, second]) => some (.mp first second)
  | _ => none

local instance : Encodable Code := Encodable.ofLeftInjection codeData readCode (by intro code; cases code <;> rfl)

instance : Encodable ModelPacket := Encodable.ofLeftInverse
  (fun packet => (packet.worlds, packet.edges, packet.values, packet.root))
  (fun (data : Nat × List (Nat × Nat) × List (Nat × Nat) × Nat) =>
    ⟨data.1, data.2.1, data.2.2.1, data.2.2.2⟩)
  (by intro packet; cases packet; rfl)

abbrev ProofRow := Formula × Code × List Nat
abbrev ProofPacket := List ProofRow × Nat

def ProofRow.node (row : ProofRow) : DerivationGraph.Node Formula Code Unit :=
  ⟨row.1, row.2.1, row.2.2, ()⟩

def ProofRow.ofNode (node : DerivationGraph.Node Formula Code Unit) : ProofRow :=
  (node.conclusion, node.witness, node.parents)

@[simp] theorem ProofRow.node_ofNode (node : DerivationGraph.Node Formula Code Unit) :
    (ProofRow.ofNode node).node = node := by
  cases node with
  | mk conclusion witness parents origin => cases origin; rfl

def checkProof (formula : Formula) (packet : ProofPacket) : Bool :=
  decide ((DerivationGraph.replay (interface .intuitionistic) (packet.1.map ProofRow.node)).bind
    (fun cache => cache[packet.2]?) = some formula)

theorem proof_sound (formula : Formula) (packet : ProofPacket)
    (accepted : checkProof formula packet = true) : Source .intuitionistic formula := by
  have found := of_decide_eq_true accepted
  cases checked : DerivationGraph.replay (interface .intuitionistic) (packet.1.map ProofRow.node) with
  | none => simp [checked] at found
  | some cache =>
      exact derives_source .intuitionistic
        (DerivationGraph.root_sound (interface .intuitionistic) checked (by simpa [checked] using found))

theorem proof_complete (formula : Formula) (proved : Source .intuitionistic formula) :
    ∃ packet, checkProof formula packet = true := by
  obtain ⟨nodes, cache, root, checked, found⟩ := (dag_coverage .intuitionistic () formula).mp proved
  have roundtrip : (nodes.map ProofRow.ofNode).map ProofRow.node = nodes := by
    simp only [List.map_map, Function.comp_def, ProofRow.node_ofNode]
    exact List.map_id nodes
  refine ⟨(nodes.map ProofRow.ofNode, root), ?_⟩
  have rawChecked := (congrArg (DerivationGraph.replay (interface .intuitionistic)) roundtrip).trans checked
  have foundRaw := (congrArg (fun run : Option (Array Formula) => run.bind (fun cache => cache[root]?)) rawChecked).trans found
  exact decide_eq_true foundRaw

abbrev Witness := Sum ProofPacket ModelPacket

def encodeWitness (witness : Witness) : Nat := Encodable.encode witness

def checkWitness (formula : Formula) : Witness → Bool
  | .inl proof => checkProof formula proof
  | .inr model => checkCountermodel formula model

def searchCheck (formula : Formula) (code : Nat) : Bool :=
  match Encodable.decode (α := Witness) code with
  | none => false
  | some witness => checkWitness formula witness

theorem searchCheck_encoded (formula : Formula) (witness : Witness) :
    searchCheck formula (encodeWitness witness) = checkWitness formula witness := by
  simp only [searchCheck, encodeWitness, Encodable.encodek]

theorem eventually_decided (formula : Formula) : ∃ code, searchCheck formula code = true := by
  classical
  by_cases proved : Source .intuitionistic formula
  · obtain ⟨proof, checked⟩ := proof_complete formula proved
    exact ⟨encodeWitness (.inl proof), (searchCheck_encoded formula (.inl proof)).trans checked⟩
  · obtain ⟨model, checked⟩ := countermodel_complete formula proved
    exact ⟨encodeWitness (.inr model), (searchCheck_encoded formula (.inr model)).trans checked⟩

/-- The exhaustive candidate count has an explicit certificate-relative
bound. Decoding and validating one candidate have additional costs. -/
theorem search_index_le (formula : Formula) (witness : Witness)
    (accepted : checkWitness formula witness = true) :
    Nat.find (eventually_decided formula) ≤ encodeWitness witness :=
  Nat.find_min' _ ((searchCheck_encoded formula witness).trans accepted)

def checkedDecision (formula : Formula) (witness : Witness)
    (accepted : checkWitness formula witness = true) : Decidable (Source .intuitionistic formula) :=
  match witness with
  | .inl proof => .isTrue (proof_sound formula proof accepted)
  | .inr model => .isFalse (countermodel_sound formula model accepted)

/-- Exhaustive search of finite data. Its termination follows from proof
coverage and the finite-model property. The existential proof is erased;
execution checks successive codes rather than evaluating an ideal oracle.
No practical search-time or polynomial bound is claimed. -/
def decideProvability (formula : Formula) : Decidable (Source .intuitionistic formula) := by
  let code := Nat.find (eventually_decided formula)
  have accepted : searchCheck formula code = true := Nat.find_spec (eventually_decided formula)
  cases decoded : Encodable.decode (α := Witness) code with
  | none => simp [searchCheck, decoded] at accepted
  | some witness =>
      exact checkedDecision formula witness (by simpa [searchCheck, decoded] using accepted)

def decideFormula (formula : Formula) : Bool := @decide (Source .intuitionistic formula) (decideProvability formula)

theorem decideFormula_exact (formula : Formula) :
    decideFormula formula = true ↔ Source .intuitionistic formula := by
  let := decideProvability formula
  exact decide_eq_true_iff

/-- Supplied proofs or countermodels are tried before exhaustive search.
An incorrect hint is skipped; it never selects the final verdict. -/
def decideWithHints (formula : Formula) : List Witness → Decidable (Source .intuitionistic formula)
  | [] => decideProvability formula
  | witness :: rest =>
      if accepted : checkWitness formula witness = true then checkedDecision formula witness accepted
      else decideWithHints formula rest

def decideHinted (formula : Formula) (hints : List Witness) : Bool :=
  @decide (Source .intuitionistic formula) (decideWithHints formula hints)

theorem decideHinted_exact (formula : Formula) (hints : List Witness) :
    decideHinted formula hints = true ↔ Source .intuitionistic formula := by
  let := decideWithHints formula hints
  exact decide_eq_true_iff

namespace Controls

def fork : ModelPacket := ⟨2, [(0, 0), (0, 1), (1, 1)], [(1, 0)], 0⟩
def excludedMiddle : Formula := .or (.atom 0) (.imp (.atom 0) .falsum)
def truth : Formula := .imp .falsum .falsum
def truthProof : ProofPacket := ([(truth, .truth, [])], 0)

example : checkProof truth truthProof = true := by decide
example : checkProof .falsum truthProof = false := by decide
example : checkProof excludedMiddle ([(excludedMiddle, .excludedMiddle (.atom 0), [])], 0) = false := by decide
example : decideHinted truth [.inl truthProof] = true := by decide
example : decideHinted excludedMiddle [.inr fork] = false := by decide

example : checkCountermodel excludedMiddle fork = true := by decide
example : checkCountermodel (.imp (.atom 0) (.atom 0)) fork = false := by decide
example : checkCountermodel excludedMiddle { fork with edges := [(0, 1)] } = false := by decide
example : checkCountermodel excludedMiddle { fork with values := [(0, 0)] } = false := by decide
example : checkCountermodel excludedMiddle { fork with root := 2 } = false := by decide

theorem excluded_middle_unprovable : ¬ Source .intuitionistic excludedMiddle :=
  countermodel_sound _ fork (by decide)

theorem decide_truth : decideFormula truth = true :=
  (decideFormula_exact truth).mpr Hilbert.Standard.verum

theorem decide_excludedMiddle : decideFormula excludedMiddle = false := by
  cases computed : decideFormula excludedMiddle with
  | false => rfl
  | true => exact False.elim (excluded_middle_unprovable ((decideFormula_exact _).mp computed))

end Controls

end Mettapedia.Logic.IntuitionisticDecision
