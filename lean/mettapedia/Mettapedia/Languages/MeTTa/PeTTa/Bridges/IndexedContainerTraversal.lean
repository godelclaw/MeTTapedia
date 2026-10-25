import Mettapedia.TypeTheory.IndexedPositiveContainer
import Mettapedia.GSLT.LanguageDef.ModuleSource.IndexedPositiveVectorLowering
import Mettapedia.GSLT.LanguageDef.ModuleSource.PositiveInductiveLoweringControls
import Mettapedia.GSLT.LanguageDef.IndexedContainerWire
import Mettapedia.Languages.MeTTa.PeTTa.ProgramQuotation
import Mettapedia.Languages.MeTTa.PeTTa.BridgeForms
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.BridgeEval
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CettaWireAtom
import Mathlib.Tactic.FinCases

/-!
# Execution of ordered inductive traversal and recursion

The quoted MeTTa program traverses a captured constructor list and emits one
`Visited` record per occurrence. Its complete PeTTa execution retains order,
multiplicity and payload syntax. The source adapter uses the selected ordered
position list of an actual indexed-container code. A source-pinned bottom-up
fold lifts one-layer method correctness to the complete polynomial family;
the admitted SearchTree answer-collecting algebra is a concrete instance.
Open-term interpretation, arbitrary source-clause elaboration and native
kernel grounding remain separate interfaces.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.IndexedContainerTraversal

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (applySubst)
open Mettapedia.TypeTheory
open Effects (State)
open Eval BridgeKit ProgramQuotation
open MeTTaIL

def source : QuotedProgram := petta_source_file%
  "../../../../../../../metta/gslt/lib/gslt_inductive_traversal.metta"
  sha256 "258b0a706683261c62d6bf002ff7a26f5c4385d2cc21748e9204ce11ed18e100"

def library : Library := ⟨⟨[], [], [], [], []⟩, source.program, ["gslt:inductive:"]⟩

theorem checked : library.check = true := by decide +kernel

def listAtom : List Atom → Atom
  | [] => .symbol "LNil"
  | head :: tail => .expression [.symbol "LCons", head, listAtom tail]

def visit (item : Atom) : Atom := .expression [.symbol "Visited", item]

theorem visit_injective : Function.Injective visit := by
  intro first second same
  cases same
  rfl

def call (items : List Atom) : Atom :=
  .expression [.symbol "gslt:inductive:visit-positions", listAtom items]

theorem listAtom_injective : Function.Injective listAtom := by
  intro first
  induction first with
  | nil =>
      intro second same
      cases second with
      | nil => rfl
      | cons => cases same
  | cons head tail ih =>
      intro second same
      cases second with
      | nil => cases same
      | cons other rest =>
          simp only [listAtom, Atom.expression.injEq, List.cons.injEq,
            true_and, and_true] at same
          exact congrArg₂ List.cons same.1 (ih same.2)

/-- Exact output records recover the entire ordered input, including repeated
payloads. Merely comparing output lengths would not establish this. -/
theorem output_injective :
    Function.Injective (fun items : List Atom => listAtom (items.map visit)) := by
  intro first second same
  exact (List.map_injective_iff.mpr visit_injective) (listAtom_injective same)

/-- The emitted traversal returns every occurrence once, in input order. -/
theorem returns (state : State) (items : List Atom) :
    PureReturns library.runtime [] state (call items)
      state (listAtom (items.map visit)) := by
  induction items with
  | nil =>
      metta_call checked
      metta_eval with checked unfolding [call, listAtom, visit,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup]
  | cons head tail ih =>
      metta_call checked
      metta_eval [ih] with checked unfolding [call, listAtom, visit,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup]
      apply data_returns
      · decide +kernel
      · simp [applySubst, Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup,
          Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
          Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil, listAtom, visit]

/-- Completion reflects to the single exact ordered result, with no store or
I/O effects and no extra answers. -/
theorem completed_iff (before after : State)
    (items answers input output : List Atom) :
    (∃ fuel, run library.runtime fuel
      { state := before, control := .evaluate [] (call items) } =
        .complete after answers input output) ↔
      after = before ∧ answers = [listAtom (items.map visit)] ∧
        input = [] ∧ output = [] :=
  path_completed_iff library.runtime _ before [listAtom (items.map visit)] [] []
    (returns before items) after answers input output

namespace ContainerValues

open Mettapedia.GSLT.LanguageDef.CettaWire
open Mettapedia.GSLT.LanguageDef.IndexedContainerWire

universe v

def wireCall (value : Term) : Atom :=
  .expression [.symbol "gslt:inductive:visit-positions", CettaWireAtom.encode value]

/-- The common physical list carrier is exactly the captured list expected
by the quoted traversal, with each payload retained as data syntax. -/
theorem encoded_list {Element : Type v} (payload : Element → Term) (items : List Element) :
    CettaWireAtom.encode (encodeList payload items) =
      listAtom (items.map (fun item => CettaWireAtom.encode (payload item))) := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
      simp [encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany, listAtom, ih]

theorem list_value_returns {Element : Type v} (payload : Element → Term)
    (value : ListValue Element) (state : State) :
    PureReturns library.runtime [] state (wireCall (encodeListValue payload value)) state
      (listAtom ((listItems value).map
        (fun item => visit (CettaWireAtom.encode (payload item))))) := by
  simpa only [wireCall, encodeListValue, encoded_list, call, List.map_map,
    Function.comp_def] using
    returns state ((listItems value).map (fun item => CettaWireAtom.encode (payload item)))

theorem vector_value_returns {Element : Type v} (payload : Element → Term)
    {length : Nat} (value : VectorValue Element length) (state : State) :
    PureReturns library.runtime [] state (wireCall (encodeVectorValue payload value)) state
      (listAtom ((listItems (vectorAsList value)).map
        (fun item => visit (CettaWireAtom.encode (payload item))))) :=
  list_value_returns payload (vectorAsList value) state

/-- The semantic output index is the number of captured child observations. -/
theorem vector_observation_count {Element : Type v} {length : Nat}
    (value : VectorValue Element length) :
    (listItems (vectorAsList value)).length = length := listItems_length _

/-- Every completed run on an encoded vector reflects to exactly the
observations of that vector, with no additional answers or effects. -/
theorem vector_value_completed_iff {Element : Type v} (payload : Element → Term)
    {length : Nat} (value : VectorValue Element length)
    (before after : State) (answers input output : List Atom) :
    (∃ fuel, run library.runtime fuel
      { state := before, control := .evaluate [] (wireCall (encodeVectorValue payload value)) } =
        .complete after answers input output) ↔
      after = before ∧
        answers = [listAtom ((listItems (vectorAsList value)).map
          (fun item => visit (CettaWireAtom.encode (payload item))))] ∧
        input = [] ∧ output = [] :=
  path_completed_iff library.runtime _ before _ [] []
    (vector_value_returns payload value before) after answers input output

/-- With a faithful element codec, complete List observations recover the
semantic shape and all payloads, rather than only their cardinality. -/
theorem list_output_injective {Element : Type v}
    (decode : Term → Option Element) (payload : Element → Term)
    (elementRoundTrip : ∀ value, decode (payload value) = some value) :
    Function.Injective (fun value : ListValue Element =>
      listAtom ((listItems value).map
        (fun item => visit (CettaWireAtom.encode (payload item))))) := by
  intro first second same
  apply list_wire_injective decode payload elementRoundTrip
  apply CettaWireAtom.encode_injective
  simp only [encodeListValue, encoded_list]
  apply congrArg listAtom
  apply output_injective
  simpa only [List.map_map, Function.comp_def] using same

theorem vector_output_injective {Element : Type v}
    (decode : Term → Option Element) (payload : Element → Term)
    (elementRoundTrip : ∀ value, decode (payload value) = some value) {length : Nat} :
    Function.Injective (fun value : VectorValue Element length =>
      listAtom ((listItems (vectorAsList value)).map
        (fun item => visit (CettaWireAtom.encode (payload item))))) := by
  intro first second same
  apply vector_wire_injective decode payload elementRoundTrip
  apply CettaWireAtom.encode_injective
  simp only [encodeVectorValue, encodeListValue, encoded_list]
  apply congrArg listAtom
  apply output_injective
  simpa only [List.map_map, Function.comp_def] using same

end ContainerValues

namespace Folding

def source : QuotedProgram := petta_source_file%
  "../../../../../../../metta/gslt/lib/gslt_inductive_fold.metta"
  sha256 "4b5e7376bb0d5463d799d14d4e1984a8e2531df4d1605b14ee5254dc35d8bef1"

def methodsSource : QuotedProgram := petta_source_file%
  "../../../../../../../metta/gslt/lib/gslt_search_tree_fold.metta"
  sha256 "5e9f51011f54ebc5e9217f0bcc2cd4a0c37d69880d74a7a670c70869e390645f"

def library : Library :=
  ⟨⟨[], [], [], [], []⟩, source.program.append methodsSource.program, ["gslt:inductive:"]⟩

theorem checked : library.check = true := by decide +kernel

def node (shape : Atom) (children : List Atom) : Atom :=
  .expression [.symbol "InductiveNode", shape, listAtom children]

def call (method : String) (tree : Atom) : Atom :=
  .expression [.symbol "gslt:inductive:fold", .symbol method, tree]

def childrenCall (method : String) (children : List Atom) : Atom :=
  .expression [.symbol "gslt:inductive:fold-children", .symbol method, listAtom children]

def methodCall (method : String) (shape : Atom) (children : List Atom) : Atom :=
  .expression [.symbol method, shape, listAtom children]

def rebuilt (shape : Atom) (children : List Atom) : Atom :=
  .expression [.symbol "FoldedNode", shape, listAtom children]

def appendCall (first second : List Atom) : Atom :=
  .expression [.symbol "gslt:inductive:append-results", listAtom first, listAtom second]

def flattenCall (lists : List (List Atom)) : Atom :=
  .expression [.symbol "gslt:inductive:flatten-results", listAtom (lists.map listAtom)]

theorem append_returns (state : State) (first second : List Atom) :
    PureReturns library.runtime [] state (appendCall first second) state (listAtom (first ++ second)) := by
  induction first with
  | nil =>
      metta_call checked
      metta_eval with checked unfolding [appendCall, listAtom,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil, List.nil_append,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup]
  | cons head tail ih =>
      metta_call checked
      metta_eval [ih] with checked unfolding [appendCall, listAtom,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil, List.cons_append,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup]

theorem flatten_returns (state : State) (lists : List (List Atom)) :
    PureReturns library.runtime [] state (flattenCall lists) state (listAtom lists.flatten) := by
  induction lists with
  | nil =>
      metta_call checked
      metta_eval with checked unfolding [flattenCall, listAtom,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup]
  | cons first rest ih =>
      have joined := append_returns state first rest.flatten
      metta_call checked
      metta_eval [ih, joined] with checked unfolding [flattenCall, appendCall, listAtom,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil, List.flatten_cons,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup]

theorem solved_method_returns (state : State) (answer : Atom) :
    PureReturns library.runtime [] state
      (methodCall "gslt:inductive:search-answers" (.expression [.symbol "Solved", answer]) [])
      state (listAtom [answer]) := by
  metta_call checked
  metta_eval with checked unfolding [methodCall, listAtom,
    Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil,
    Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
    Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
    Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup]

theorem branch_method_returns (state : State) (length : Nat) (answers : List (List Atom)) :
    PureReturns library.runtime [] state
      (methodCall "gslt:inductive:search-answers"
        (.expression [.symbol "Branch", .grounded (.int length)]) (answers.map listAtom))
      state (listAtom answers.flatten) := by
  have flattened := flatten_returns state answers
  metta_call checked
  metta_eval [flattened] with checked unfolding [methodCall, flattenCall, listAtom,
    Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
    Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
    Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup]

theorem rebuild_returns (state : State) (shape : Atom) (children : List Atom) :
    PureReturns library.runtime [] state
      (methodCall "gslt:inductive:rebuild" shape children) state (rebuilt shape children) := by
  metta_call checked
  apply data_returns
  · decide +kernel
  · simp [rebuilt, Library.bind, Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil,
      Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup]

theorem return_shape_returns (state : State) (shape : Atom) (children : List Atom) :
    PureReturns library.runtime [] state
      (methodCall "gslt:inductive:return-shape" shape children) state shape := by
  metta_call checked
  metta_eval with checked unfolding [methodCall,
    Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil]

theorem children_returns (method : String) (state : State)
    (trees values : List Atom)
    (returned : List.Forall₂ (fun tree value =>
      PureReturns library.runtime [] state (call method tree) state value) trees values) :
    PureReturns library.runtime [] state (childrenCall method trees) state (listAtom values) := by
  induction returned with
  | nil =>
      metta_call checked
      metta_eval with checked unfolding [childrenCall, listAtom,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup]
  | @cons tree value trees values headReturned tailReturned ih =>
      metta_call checked
      metta_eval [headReturned, ih] with checked unfolding [childrenCall, call, listAtom,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup]

theorem construct_application_returns (caller : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (state : State) :
    PureReturns library.runtime caller state
      (.expression [.symbol "cons-atom", .var "method", .expression [.var "shape", .var "folded"]]) state
      (.expression [applySubst caller (.var "method"), applySubst caller (.var "shape"),
        applySubst caller (.var "folded")]) := by
  apply native_binary_call_returns library.runtime caller state state state state "cons-atom"
    (.var "method") (.expression [.var "shape", .var "folded"])
    (applySubst caller (.var "method"))
    (.expression [applySubst caller (.var "shape"), applySubst caller (.var "folded")])
    _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact variable_returns library.runtime caller state "method"
  · exact tuple_variables_return library.runtime caller state ["shape", "folded"]
  · exact StdLib.native_cons state _ _
  · decide +kernel

theorem node_returns (method : String) (state : State) (shape : Atom)
    (trees values : List Atom) (result : Atom)
    (childrenReturned : List.Forall₂ (fun tree value =>
      PureReturns library.runtime [] state (call method tree) state value) trees values)
    (methodReturned : PureReturns library.runtime [] state (methodCall method shape values) state result) :
    PureReturns library.runtime [] state (call method (node shape trees)) state result := by
  have children := children_returns method state trees values childrenReturned
  metta_call checked
  metta_eval [children, methodReturned] with checked unfolding [call, node, childrenCall, methodCall,
    listAtom, Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
    Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
    Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup]
  apply pure_let_returns
  · rfl
  · exact construct_application_returns _ state
  · apply InputOutput.eval_variable_io_returns library.runtime _ state state "application"
      (methodCall method shape values) result [] [] [] [] (by decide)
    · simp [methodCall, Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil]
    · exact methodReturned

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.IndexedContainerWire

universe uBase uIndex uShape uPosition uCarrier

variable {Base : Type uBase} {Index : Base → Type uIndex}

def quoteTree
    (polynomial : IndexedPolynomial.{uBase, uIndex, uShape, uPosition} Base Index)
    (positions : ∀ base index, (shape : polynomial.Shape base index) →
      List (polynomial.Position shape))
    (encodeShape : ∀ base index, polynomial.Shape base index → CettaWire.Term)
    (base : Base) (index : Index base) (tree : IndexedPolynomial.Fix polynomial base index) : Atom :=
  CettaWireAtom.encode (Recursive.encodeFix polynomial positions encodeShape base index tree)

theorem quoteTree_roll
    (polynomial : IndexedPolynomial.{uBase, uIndex, uShape, uPosition} Base Index)
    (positions : ∀ base index, (shape : polynomial.Shape base index) →
      List (polynomial.Position shape))
    (encodeShape : ∀ base index, polynomial.Shape base index → CettaWire.Term)
    {base : Base} {index : Index base} (shape : polynomial.Shape base index)
    (children : ∀ position, IndexedPolynomial.Fix polynomial base (polynomial.next shape position)) :
    quoteTree polynomial positions encodeShape base index (.roll shape children) =
      node (CettaWireAtom.encode (encodeShape base index shape))
        ((positions base index shape).map fun position =>
          quoteTree polynomial positions encodeShape base _ (children position)) := by
  simp [quoteTree, Recursive.encodeFix_roll, CettaWireAtom.encode, CettaWireAtom.encodeMany,
    ContainerValues.encoded_list, node, Function.comp_def]

/-- Constructor-method correctness lifts to execution of the complete
recursive family. The premise concerns one algebra layer, not a complete
recursive call or the theorem being established. -/
theorem fold_returns
    (polynomial : IndexedPolynomial.{uBase, uIndex, uShape, uPosition} Base Index)
    (positions : ∀ base index, (shape : polynomial.Shape base index) →
      List (polynomial.Position shape))
    (encodeShape : ∀ base index, polynomial.Shape base index → CettaWire.Term)
    {Carrier : (base : Base) → Index base → Type uCarrier}
    (algebra : ∀ base index, polynomial.Extension Carrier base index → Carrier base index)
    (encodeResult : ∀ base index, Carrier base index → Atom)
    (method : String) (state : State)
    (methodCorrect : ∀ base index (shape : polynomial.Shape base index)
      (children : ∀ position, Carrier base (polynomial.next shape position)),
      PureReturns library.runtime [] state
        (methodCall method (CettaWireAtom.encode (encodeShape base index shape))
          ((positions base index shape).map fun position =>
            encodeResult base _ (children position))) state
        (encodeResult base index (algebra base index ⟨shape, children⟩)))
    (base : Base) (index : Index base) (tree : IndexedPolynomial.Fix polynomial base index) :
    PureReturns library.runtime [] state
      (call method (quoteTree polynomial positions encodeShape base index tree)) state
      (encodeResult base index (IndexedPolynomial.Fix.fold polynomial algebra base index tree)) := by
  induction tree with
  | @roll index shape children ih =>
      rw [quoteTree_roll, IndexedPolynomial.Fix.fold_roll]
      apply node_returns
      · apply List.forall₂_map_left_iff.mpr
        apply List.forall₂_map_right_iff.mpr
        exact List.forall₂_same.mpr (fun position _ => ih position)
      · exact methodCorrect base index shape _

namespace Search

open PositiveInductiveScenarios.Search

abbrev sourceOrder :=
  Mettapedia.GSLT.LanguageDef.ModuleSource.PositiveInductiveLoweringControls.Search.sourceOrder

def positions (base : IndexedPolynomial.Description.Env interface.Value [])
    (index : interface.Index) (shape : admitted.polynomial.Shape base index) :
    List (admitted.polynomial.Position shape) :=
  IndexedPositiveContainer.Unindexed.blockSourcePositions sourceOrder admitted
    Mettapedia.GSLT.LanguageDef.ModuleSource.PositiveInductiveLoweringControls.WholeFamily.source_registered
    shape

def shapeCode (base : IndexedPolynomial.Description.Env interface.Value [])
    (index : interface.Index) (shape : admitted.polynomial.Shape base index) : CettaWire.Term := by
  rcases shape with ⟨occurrence, payload⟩
  refine Fin.cases ?_ (fun remaining => ?_) occurrence payload
  · intro payload
    exact .application "Solved" [.natural (if (show Bool from payload.1) then 1 else 0)]
  · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) remaining
    intro payload
    exact .application "Branch" [.natural payload.1]

def answerAtom (answer : Bool) : Atom :=
  CettaWireAtom.encode (.natural (if answer then 1 else 0))

def answerResult (_base : IndexedPolynomial.Description.Env interface.Value [])
    (_index : interface.Index) (values : List Bool) : Atom := listAtom (values.map answerAtom)

def quote (tree : SearchTree) : Atom :=
  quoteTree admitted.polynomial positions shapeCode environment rootIndex tree

theorem method_correct (state : State)
    (base : IndexedPolynomial.Description.Env interface.Value []) (index : interface.Index)
    (shape : admitted.polynomial.Shape base index)
    (children : ∀ _position, List Bool) :
    PureReturns library.runtime [] state
      (methodCall "gslt:inductive:search-answers" (CettaWireAtom.encode (shapeCode base index shape))
        ((positions base index shape).map fun position =>
          answerResult base (admitted.polynomial.next shape position) (children position))) state
      (answerResult base index (answerAlgebra.act base index ⟨shape, children⟩)) := by
  rcases shape with ⟨occurrence, payload⟩
  revert payload children
  refine Fin.cases ?_ (fun remaining => ?_) occurrence
  · intro payload children
    change PureReturns library.runtime [] state
      (methodCall "gslt:inductive:search-answers"
        (.expression [.symbol "Solved", answerAtom payload.1]) []) state
      (listAtom [answerAtom payload.1])
    exact solved_method_returns state (answerAtom payload.1)
  · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) remaining
    intro payload children
    rcases payload with ⟨length, witness⟩
    change Nat at length
    change (Fin length ⊕ PEmpty.{1} → List Bool) at children
    change PureReturns library.runtime [] state
      (methodCall "gslt:inductive:search-answers"
        (.expression [.symbol "Branch", .grounded (.int (Int.ofNat length))])
        ((positions base index ⟨(1 : Fin 2), ⟨length, witness⟩⟩).map fun position =>
          listAtom ((children position).map answerAtom))) state
      (listAtom ((List.ofFn fun position => children (.inl position)).flatten.map answerAtom))
    have ordered : positions base index ⟨(1 : Fin 2), ⟨length, witness⟩⟩ =
        (List.ofFn (id : Fin length → Fin length)).map Sum.inl := by
      change (List.append ((List.ofFn (id : Fin length → Fin length)).map
        (Sum.inl : Fin length → Fin length ⊕ PEmpty.{1})) []) = _
      exact List.append_nil _
    rw [ordered]
    change PureReturns library.runtime [] state
      (methodCall "gslt:inductive:search-answers"
        (.expression [.symbol "Branch", .grounded (.int (Int.ofNat length))])
        (((List.ofFn (id : Fin length → Fin length)).map
          (Sum.inl : Fin length → Fin length ⊕ PEmpty.{1})).map
          (fun position : Fin length ⊕ PEmpty.{1} => listAtom ((children position).map answerAtom)))) state
      (listAtom ((List.ofFn fun position : Fin length => children (.inl position)).flatten.map answerAtom))
    clear ordered witness base index occurrence remaining
    have mapped (mapping : Fin length ⊕ PEmpty.{1} → Atom) :
        (((List.ofFn id).map (Sum.inl : Fin length → Fin length ⊕ PEmpty.{1})).map mapping) =
          List.ofFn (fun position => mapping (.inl position)) := by
      simp only [List.map_ofFn, Function.comp_def, id_eq]
    rw [mapped]
    have returned := branch_method_returns state length
      ((List.ofFn fun position => children (.inl position)).map (fun values => values.map answerAtom))
    simpa only [List.map_ofFn, List.map_flatten, Function.comp_def, Int.ofNat_eq_natCast] using returned

/-- The quoted constructor methods execute the existing admitted SearchTree
recursor on every semantic tree, not only on closed test fixtures. -/
theorem answers_return (state : State) (tree : SearchTree) :
    PureReturns library.runtime [] state (call "gslt:inductive:search-answers" (quote tree)) state
      (answerResult environment rootIndex (answers tree)) :=
  fold_returns admitted.polynomial positions shapeCode answerAlgebra.act answerResult
    "gslt:inductive:search-answers" state (method_correct state) environment rootIndex tree

/-- No completed evaluation invents an answer, store effect, input or output
beyond the source recursor's complete ordered result. -/
theorem answers_completed_iff (tree : SearchTree) (before after : State)
    (results input output : List Atom) :
    (∃ fuel, run library.runtime fuel
      { state := before, control := .evaluate [] (call "gslt:inductive:search-answers" (quote tree)) } =
        .complete after results input output) ↔
      after = before ∧ results = [answerResult environment rootIndex (answers tree)] ∧
        input = [] ∧ output = [] :=
  path_completed_iff library.runtime _ before _ [] [] (answers_return before tree)
    after results input output

theorem shapeCode_injective (base : IndexedPolynomial.Description.Env interface.Value [])
    (index : interface.Index) : Function.Injective (shapeCode base index) := by
  rintro ⟨first, payload⟩ ⟨second, other⟩ same
  fin_cases first <;> fin_cases second
  · rcases payload with ⟨answer, witness⟩
    rcases other with ⟨otherAnswer, otherWitness⟩
    have dataSame : answer = otherAnswer := by
      change CettaWire.Term.application "Solved" [.natural (if (show Bool from answer) then 1 else 0)] =
        .application "Solved" [.natural (if (show Bool from otherAnswer) then 1 else 0)] at same
      cases answer <;> cases otherAnswer <;> first | rfl | simp at same
    subst otherAnswer
    have proofSame : witness = otherWitness := by
      change (show ULift (PLift (() = index)) from witness) = otherWitness
      exact Subsingleton.elim _ _
    subst otherWitness
    rfl
  · have names := (CettaWire.Term.application.inj same).1
    exact False.elim ((by decide : "Solved" ≠ "Branch") names)
  · have names := (CettaWire.Term.application.inj same).1
    exact False.elim ((by decide : "Branch" ≠ "Solved") names)
  · rcases payload with ⟨length, witness⟩
    rcases other with ⟨otherLength, otherWitness⟩
    have dataSame : length = otherLength := by
      change CettaWire.Term.application "Branch" [.natural length] =
        .application "Branch" [.natural otherLength] at same
      exact CettaWire.Term.natural.inj ((List.cons.inj (CettaWire.Term.application.inj same).2).1)
    subst otherLength
    have proofSame : witness = otherWitness := by
      change (show ULift (PLift (() = index)) from witness) = otherWitness
      exact Subsingleton.elim _ _
    subst otherWitness
    rfl

/-- Source trees remain distinguishable at the executable input boundary.
Every registered nested-list position participates in the comparison. -/
theorem quote_injective : Function.Injective quote := by
  intro first second same
  apply Recursive.encodeFix_injective admitted.polynomial positions
    (fun _ _ shape position => IndexedPositiveContainer.Unindexed.mem_blockSourcePositions
      sourceOrder admitted
      Mettapedia.GSLT.LanguageDef.ModuleSource.PositiveInductiveLoweringControls.WholeFamily.source_registered
      shape position) shapeCode shapeCode_injective environment rootIndex
  exact CettaWireAtom.encode_injective _ _ same

@[simp] theorem quote_solved (answer : Bool) :
    quote (solved answer) = node (.expression [.symbol "Solved", answerAtom answer]) [] := rfl

@[simp] theorem quote_branch (children : List SearchTree) :
    quote (branch children) =
      node (.expression [.symbol "Branch", .grounded (.int children.length)]) (children.map quote) := by
  change quoteTree admitted.polynomial positions shapeCode environment rootIndex
    (.roll (branchLayer children).1 (branchLayer children).2) = _
  rw [quoteTree_roll]
  have head : CettaWireAtom.encode (shapeCode environment rootIndex (branchLayer children).1) =
      .expression [.symbol "Branch", .grounded (.int children.length)] := rfl
  rw [head]
  apply congrArg (node _)
  change ((((List.ofFn (id : Fin children.length → Fin children.length)).map
      (Sum.inl : Fin children.length → Fin children.length ⊕ PEmpty.{1})) ++ []).map
      (fun position => quoteTree admitted.polynomial positions shapeCode environment
        (admitted.polynomial.next (branchLayer children).1 position)
        ((branchLayer children).2 position))) = _
  rw [List.append_nil]
  refine List.map_map.trans ?_
  change (List.ofFn id).map (fun position => quote (children.get position)) = children.map quote
  rw [List.map_ofFn]
  change List.ofFn (fun position => quote (children.get position)) = children.map quote
  rw [List.ofFn_comp' (fun position => children.get position) quote, List.ofFn_get]

theorem answers_branch_map (children : List SearchTree) :
    answers (branch children) = (children.map answers).flatten := by
  rw [answers_branch, List.ofFn_comp' (fun position => children.get position) answers, List.ofFn_get]

def spine : Nat → SearchTree
  | 0 => solved true
  | depth + 1 => branch [spine depth]

theorem answers_spine (depth : Nat) : answers (spine depth) = [true] := by
  induction depth with
  | zero => exact answers_solved true
  | succ depth ih => simp [spine, ih]

theorem answers_flat (values : List Bool) : answers (branch (values.map solved)) = values := by
  rw [answers_branch_map]
  induction values with
  | nil => rfl
  | cons first rest ih =>
      simpa only [List.map_cons, List.flatten_cons, answers_solved, List.singleton_append] using
        congrArg (List.cons first) ih

def alternating : List Bool := (List.range 32).map (fun value => value % 2 == 0)

structure Fixture where
  label : String
  tree : SearchTree
  expected : List Bool
  exactAnswers : answers tree = expected

def fixtures : List Fixture :=
  [⟨"solved", solved false, [false], answers_solved false⟩,
   ⟨"empty-branch", branch [], [], by simp⟩,
   ⟨"ordered", branch [solved true, solved false], [true, false], by simp⟩,
   ⟨"repeated", branch [solved false, solved false, solved true], [false, false, true],
      by simp⟩,
   ⟨"nested", branch [branch [solved true, solved false], branch [], solved true], [true, false, true],
      by simp⟩,
   ⟨"deep", spine 16, [true], answers_spine 16⟩,
   ⟨"wide", branch (alternating.map solved), alternating, answers_flat alternating⟩]

def fixtureCall (fixture : Fixture) : Atom := call "gslt:inductive:search-answers" (quote fixture.tree)

def fixtureAnswer (fixture : Fixture) : Atom := answerResult environment rootIndex fixture.expected

theorem fixture_returns (fixture : Fixture) (state : State) :
    PureReturns library.runtime [] state (fixtureCall fixture) state (fixtureAnswer fixture) := by
  simpa only [fixtureCall, fixtureAnswer, fixture.exactAnswers] using answers_return state fixture.tree

theorem reordered_answers_differ :
    fixtureAnswer ⟨"first", branch [solved true, solved false], [true, false],
      by simp⟩ ≠
    fixtureAnswer ⟨"second", branch [solved false, solved true], [false, true],
      by simp⟩ := by decide +kernel

end Search

structure ExecutionControl where
  label : String
  expression : Atom
  expected : Atom
  semantics : ∀ state, PureReturns library.runtime [] state expression state expected

def codeData : Atom := .expression [.symbol "+", .grounded (.int 1), .grounded (.int 2)]

def executionControls : List ExecutionControl :=
  Search.fixtures.map (fun fixture =>
    ⟨fixture.label, Search.fixtureCall fixture, Search.fixtureAnswer fixture,
      Search.fixture_returns fixture⟩) ++
  [⟨"method-returns-code", call "gslt:inductive:return-shape" (node codeData []), codeData,
    fun state => node_returns "gslt:inductive:return-shape" state codeData [] [] codeData
      .nil (return_shape_returns state codeData [])⟩]

def controlAnswers? (fuel : Nat) (expression : Atom) : Option (List Atom) :=
  match Eval.evaluate library.runtime fuel Effects.empty expression with
  | .complete _ answers [] [] => some answers
  | _ => none

def modelChecks : Bool := executionControls.all fun control =>
  controlAnswers? 30000 control.expression == some [control.expected]

end Folding

universe u

/-- Input quotation preserves the actual selected position order. Payload
collisions are retained as distinct occurrences, not deduplicated. -/
def orderedInput
    {I : IndexedPolynomial.Description.Interface.{u}}
    {registry : IndexedPositiveContainer.Registry I}
    (ordered : registry.OrderedFinitary) {parameterCount : Nat}
    {context : List I.SortCode}
    (code : IndexedPositiveContainer.Code I registry parameterCount context)
    {environment : IndexedPolynomial.Description.Env I.Value context}
    {index : I.Index}
    (shape : IndexedPositiveContainer.Code.Shape code environment index)
    (payload : IndexedPositiveContainer.Code.Position code shape → Atom) : List Atom :=
  (IndexedPositiveContainer.Code.orderedPositions ordered code shape).map payload

/-- Actual execution is the ordered image of every semantic position. -/
theorem ordered_returns
    {I : IndexedPolynomial.Description.Interface.{u}}
    {registry : IndexedPositiveContainer.Registry I}
    (ordered : registry.OrderedFinitary) {parameterCount : Nat}
    {context : List I.SortCode}
    (code : IndexedPositiveContainer.Code I registry parameterCount context)
    {environment : IndexedPolynomial.Description.Env I.Value context}
    {index : I.Index}
    (shape : IndexedPositiveContainer.Code.Shape code environment index)
    (payload : IndexedPositiveContainer.Code.Position code shape → Atom)
    (state : State) :
    PureReturns library.runtime [] state
      (call (orderedInput ordered code shape payload)) state
      (listAtom ((IndexedPositiveContainer.Code.orderedPositions ordered code shape).map
        (visit ∘ payload))) := by
  simpa only [orderedInput, List.map_map] using
    returns state (orderedInput ordered code shape payload)

/-- Each semantic position contributes one output record, even if different
positions carry equal payloads. -/
theorem ordered_record_count
    {I : IndexedPolynomial.Description.Interface.{u}}
    {registry : IndexedPositiveContainer.Registry I}
    (ordered : registry.OrderedFinitary) {parameterCount : Nat}
    {context : List I.SortCode}
    (code : IndexedPositiveContainer.Code I registry parameterCount context)
    {environment : IndexedPolynomial.Description.Env I.Value context}
    {index : I.Index}
    (shape : IndexedPositiveContainer.Code.Shape code environment index)
    (payload : IndexedPositiveContainer.Code.Position code shape → Atom) :
    ((orderedInput ordered code shape payload).map visit).length =
      @Fintype.card (IndexedPositiveContainer.Code.Position code shape)
        (IndexedPositiveContainer.Code.positionFintype ordered.toFinitary code shape) := by
  rw [List.length_map, orderedInput, List.length_map]
  exact IndexedPositiveContainer.Code.orderedPositions_length ordered code shape

/-- For a fixed constructor shape, equality of complete traversal outputs
reflects equality of the payload observation at every semantic position. -/
theorem ordered_output_eq_iff
    {I : IndexedPolynomial.Description.Interface.{u}}
    {registry : IndexedPositiveContainer.Registry I}
    (ordered : registry.OrderedFinitary) {parameterCount : Nat}
    {context : List I.SortCode}
    (code : IndexedPositiveContainer.Code I registry parameterCount context)
    {environment : IndexedPolynomial.Description.Env I.Value context}
    {index : I.Index}
    (shape : IndexedPositiveContainer.Code.Shape code environment index)
    (first second : IndexedPositiveContainer.Code.Position code shape → Atom) :
    listAtom ((orderedInput ordered code shape first).map visit) =
        listAtom ((orderedInput ordered code shape second).map visit) ↔
      ∀ position, first position = second position := by
  constructor
  · intro same position
    have inputs := output_injective same
    exact List.map_inj_left.mp inputs position
      (IndexedPositiveContainer.Code.mem_orderedPositions ordered code shape position)
  · intro same
    have functions : first = second := funext same
    rw [functions]

namespace Controls

def number (value : Nat) : Atom := .grounded (.int value)

structure Fixture where
  label : String
  items : List Atom

/-- The payload sequence is read from the exact semantic erasure of the
resolved textual VectorTree branch. -/
def textualVectorInput (length : Nat) : List Atom :=
  orderedInput IndexedPositiveContainer.VectorControl.orderedFinitary
    Mettapedia.GSLT.LanguageDef.ModuleSource.IndexedPositiveVectorLowering.Controls.branch.body.erase
    (IndexedPositiveContainer.VectorControl.shapeAt length)
    (fun position => match position with
      | .inl position => number position.val
      | .inr impossible => PEmpty.elim impossible)

theorem textualVectorInput_two : textualVectorInput 2 = [number 0, number 1] := by
  decide +kernel

def fixtures : List Fixture :=
  [⟨"empty", []⟩,
   ⟨"ordered", [number 3, number 1, number 2]⟩,
   ⟨"repeated", [number 4, number 4, number 2]⟩,
   ⟨"code-remains-data", [.expression [.symbol "+", number 1, number 2]]⟩,
   ⟨"textual-vector-branch", textualVectorInput 2⟩,
   ⟨"longer", (List.range 32).map number⟩]

def answers? (fuel : Nat) (items : List Atom) : Option (List Atom) :=
  match Eval.evaluate library.runtime fuel Effects.empty (call items) with
  | .complete _ answers [] [] => some answers
  | _ => none

def modelChecks : Bool := fixtures.all fun fixture =>
  answers? 4000 fixture.items == some [listAtom (fixture.items.map visit)]

theorem model_checks : modelChecks = true := by decide +kernel

theorem missing_repeated_occurrence_refused :
    listAtom (([number 4, number 4, number 2]).map visit) ≠
      listAtom (([number 4, number 2]).map visit) := by decide +kernel

theorem reordered_occurrences_refused :
    listAtom (([number 3, number 1, number 2]).map visit) ≠
      listAtom (([number 1, number 3, number 2]).map visit) := by decide +kernel

theorem zero_fuel_is_unfinished : answers? 0 [number 1] = none := by decide +kernel

end Controls

#print axioms output_injective
#print axioms returns
#print axioms completed_iff
#print axioms ContainerValues.list_value_returns
#print axioms ContainerValues.vector_value_returns
#print axioms ContainerValues.vector_value_completed_iff
#print axioms ContainerValues.list_output_injective
#print axioms ContainerValues.vector_output_injective
#print axioms Folding.children_returns
#print axioms Folding.node_returns
#print axioms Folding.fold_returns
#print axioms Folding.Search.answers_return
#print axioms Folding.Search.answers_completed_iff
#print axioms Folding.Search.quote_injective
#print axioms Folding.Search.fixture_returns
#print axioms Folding.Search.reordered_answers_differ
#print axioms ordered_returns
#print axioms ordered_record_count
#print axioms ordered_output_eq_iff
#print axioms Controls.model_checks
#print axioms Controls.textualVectorInput_two
#print axioms Controls.missing_repeated_occurrence_refused
#print axioms Controls.reordered_occurrences_refused
#print axioms Controls.zero_fuel_is_unfinished

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.IndexedContainerTraversal
