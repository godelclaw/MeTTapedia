import Mettapedia.Languages.HOLLight.ChronologicalTaskExecution
import Mettapedia.Languages.HOLLight.OriginalChildJobsProgram
import Mettapedia.Computability.StackMachineDispatchProgram

/-!
# Physical returned-root prefix extraction

A finite compiled prefix length selects this close operation's returned roots.
The original field visitor parses the root list, two spine boundary instructions
retain the whole unused list as a separate field, and the original indexed word
copier reverses only the selected fields. Original binary natural/list/product
codecs give independent success/refusal readout. Every original root-list image
has a counted execution to the canonical halt, including scratch and register
cleanup, with descriptor-charged linear time.

The controller projection is exactly its selected root order and remaining root
order. This component does not select an authored rule, check premise goals,
emit a rule block, update a cache, or execute a complete close task. The prefix
length remains part of the compiled machine descriptor.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.HOLLight.ReturnedRootPrefixExtraction
open Turing StateTransition Mettapedia.Computability
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.GSLT.LanguageDef
open CertificateDataTraversal
open CertificateArgumentFraming

abbrev Base (count : Nat) := CertificateArgumentFraming.Execution.machine (count+1)
abbrev Phase (count : Nat) := CertificateArgumentFraming.Execution.Phase (count+1)
abbrev Index (count : Nat) := Fin (count+2)
abbrev Cells := CertificateArgumentFraming.Execution.Cells
abbrev Register := CertificateArgumentFraming.Execution.State

def body (count : Nat) : (Base count).Λ → (Base count).Stmt
  | .spine index =>
      if index.val=count then .goto fun _ => .field index .header
      else if index.val=count+1 then .goto fun _ => .checkEnd
      else (Base count).m (.spine index)
  | phase => (Base count).m phase

/-- The original field parser is retained. At the authored cut, the original
remaining list is captured as one complete field; the next spine checks EOF. -/
def machine (count : Nat) : FinTM2 := {Base count with m:=body count}
abbrev config (count : Nat) := CertificateArgumentFraming.Execution.config (count+1)
attribute [local implicit_reducible] machine

theorem body_field (count : Nat) (index : Index count) (phase : CertificateDataTraversal.Phase) :
    body count (.field index phase)=(Base count).m (.field index phase) := rfl

theorem non_spine_step (count : Nat) (state : (machine count).Cfg) (phase : Phase count)
    (present : state.l=some phase)
    (notSpine : ∀ index,phase≠.spine index) :
    (machine count).step state=(Base count).step state := by
  cases state with
  | mk label registers contents =>
      change label=some phase at present
      subst label
      change some (TM2.stepAux (body count phase) registers contents)=
        some (TM2.stepAux ((Base count).m phase) registers contents)
      have same : body count phase=(Base count).m phase := by
        cases phase <;> first | rfl | exact False.elim (notSpine _ rfl)
      rw [same]

theorem spine_cons (count : Nat) (index : Index count) (room : index.val<count)
    (state : Register) (input : List Alphabet) (vector result : List (Option Alphabet)) :
    (machine count).step (config count (some (.spine index)) state (4::input) [] [] [] vector result)=
      some (config count (some (.field index .header)) (some 4,state.2) input [] [] [] vector result) := by
  have notCut : index.val≠count := by omega
  have notEnd : index.val≠count+1 := by omega
  have same : body count (.spine index)=(Base count).m (.spine index) := by
    simp only [body,notCut,notEnd,↓reduceIte]
  have stepSame : (machine count).step (config count (some (.spine index)) state (4::input) [] [] [] vector result)=
      (Base count).step (config count (some (.spine index)) state (4::input) [] [] [] vector result) := by
    change some (TM2.stepAux (body count (.spine index)) state _)=some (TM2.stepAux ((Base count).m (.spine index)) state _)
    rw [same]
  rw [stepSame]
  exact CertificateArgumentFraming.Execution.spine_cons (count+1) index (by omega) state input vector result

theorem cut_step (count : Nat) (index : Index count) (cut : index.val=count)
    (state : Register) (input frames post memo : List Alphabet) (vector result : List (Option Alphabet)) :
    (machine count).step (config count (some (.spine index)) state input frames post memo vector result)=
      some (config count (some (.field index .header)) state input frames post memo vector result) := by
  simp only [FinTM2.step,machine,body,cut,↓reduceIte,TM2.step,TM2.stepAux,config,CertificateArgumentFraming.Execution.config]

theorem end_step (count : Nat) (index : Index count) (ending : index.val=count+1)
    (state : Register) (input frames post memo : List Alphabet) (vector result : List (Option Alphabet)) :
    (machine count).step (config count (some (.spine index)) state input frames post memo vector result)=
      some (config count (some .checkEnd) state input frames post memo vector result) := by
  have notEndCut : count+1≠count := by omega
  simp only [FinTM2.step,machine,body,ending,notEndCut,↓reduceIte,TM2.step,TM2.stepAux,config,CertificateArgumentFraming.Execution.config]

theorem parser_scanning (count : Nat) (index : Index count) (extra : Option (Option Alphabet))
    (vector result : List (Option Alphabet)) (source : PrefixField.machine.Cfg)
    (allowed : PrefixField.scanning source) :
    (machine count).step (CertificateArgumentFraming.Execution.embed (count+1) index extra vector result source)=
      (PrefixField.machine.step source).map (CertificateArgumentFraming.Execution.embed (count+1) index extra vector result) := by
  have atField : ∃ phase,(CertificateArgumentFraming.Execution.embed (count+1) index extra vector result source).l=some (.field index phase) := by
    rcases allowed with atHeader | atNumber | ⟨atComplete,_⟩
    · exact ⟨.header,by simp only [CertificateArgumentFraming.Execution.embed,StackMachineRegisters.withStackConfig,StackMachineRegisters.config,atHeader,Option.map_some,id_eq]⟩
    · exact ⟨.number,by simp only [CertificateArgumentFraming.Execution.embed,StackMachineRegisters.withStackConfig,StackMachineRegisters.config,atNumber,Option.map_some,id_eq]⟩
    · exact ⟨.complete,by simp only [CertificateArgumentFraming.Execution.embed,StackMachineRegisters.withStackConfig,StackMachineRegisters.config,atComplete,Option.map_some,id_eq]⟩
  obtain ⟨phase,atPhase⟩ := atField
  rw [non_spine_step count _ (.field index phase) atPhase (by intro other impossible;cases impossible)]
  exact CertificateArgumentFraming.Execution.parser_scanning (count+1) index extra vector result source allowed

end Mettapedia.Languages.HOLLight.ReturnedRootPrefixExtraction

namespace Mettapedia.Languages.HOLLight.ReturnedRootPrefixExtraction
open Turing StateTransition Mettapedia.Computability
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.GSLT.LanguageDef
open CertificateDataTraversal CertificateArgumentFraming

/-- Intercepted spine boundaries do not alter any original parser, transport
or cleanup instruction. This derives one actual wrapper transition. -/
def preservedStep (count : Nat) (phase : Phase count) (notSpine : ∀ index,phase≠.spine index)
    {before after : (machine count).Cfg} (original : (Base count).step before=some after)
    (present : before.l=some phase) :
    EvalsToInTime (machine count).step before (some after) 1 :=
  StackMachineComposition.oneStep ((non_spine_step count before phase present notSpine).trans original)

noncomputable def fieldWalk (count : Nat) (index : Index count) (extra : Option (Option Alphabet))
    (value : Data) (input : List Alphabet) (vector result : List (Option Alphabet)) (state : Option Alphabet) :
    EvalsToInTime (machine count).step
      (config count (some (.field index .header)) (state,extra) (writeData value input) [] [] [] vector result)
      (some (config count (some (.field index .complete)) (finalState value,extra) input []
        (postorderWire value).reverse (encodeData value).reverse vector result)) (scanCost value) := by
  have walked := PrefixField.walkInto (machine count).step
    (CertificateArgumentFraming.Execution.embed (count+1) index extra vector result)
    (steps:=parser_scanning count index extra vector result) value input [] [] [] state
  simpa only [CertificateArgumentFraming.Execution.embed_config,Option.map_some,List.append_nil] using walked

noncomputable def clearPostRun (count : Nat) (index : Index count) (state : Register)
    (input post memo : List Alphabet) (vector result : List (Option Alphabet)) :
    EvalsToInTime (machine count).step
      (config count (some (.clearPost index)) state input [] post memo vector result)
      (some (config count (some (.restorePrefix index)) (none,state.2) input [] [] memo vector result))
      (post.length+1) := by
  induction post generalizing state with
  | nil =>
      exact preservedStep count (.clearPost index) (by intro i impossible;cases impossible) 
        (CertificateArgumentFraming.Execution.clear_post_nil (count+1) index state input memo vector result) rfl
  | cons head tail ih =>
      have begin := preservedStep count (.clearPost index) (by intro i impossible;cases impossible) 
        (CertificateArgumentFraming.Execution.clear_post_cons (count+1) index state head input tail memo vector result) rfl
      have rest := ih (some head,state.2)
      simpa using EvalsToInTime.trans _ 1 (tail.length+1) _ _ _ begin rest

noncomputable def restorePrefixRun (count : Nat) (index : Index count) (state : Register)
    (input post memo : List Alphabet) (vector result : List (Option Alphabet)) :
    EvalsToInTime (machine count).step
      (config count (some (.restorePrefix index)) state input [] post memo vector result)
      (some (config count (some (.copyWord index)) (none,state.2) input [] (memo.reverse++post) [] vector result))
      (memo.length+1) := by
  induction memo generalizing state post with
  | nil =>
      simpa using preservedStep count (.restorePrefix index) (by intro i impossible;cases impossible) 
        (CertificateArgumentFraming.Execution.restore_prefix_nil (count+1) index state input post vector result) rfl
  | cons head tail ih =>
      have begin := preservedStep count (.restorePrefix index) (by intro i impossible;cases impossible) 
        (CertificateArgumentFraming.Execution.restore_prefix_cons (count+1) index state head input post tail vector result) rfl
      have rest := ih (some head,state.2) (head::post)
      simpa [List.reverse_cons,List.append_assoc] using
        EvalsToInTime.trans _ 1 (tail.length+1) _ _ _ begin rest

noncomputable def copyWordRun (count : Nat) (index : Index count) (state : Register)
    (input post : List Alphabet) (vector result : List (Option Alphabet)) :
    EvalsToInTime (machine count).step
      (config count (some (.copyWord index)) state input [] post [] vector result)
      (some (config count (some (.spine (WordTemplateMachine.advance index))) (none,state.2)
        input [] [] [] (none::post.reverse.map some++vector) result)) (post.length+1) := by
  induction post generalizing state vector with
  | nil =>
      simpa using preservedStep count (.copyWord index) (by intro i impossible;cases impossible) 
        (CertificateArgumentFraming.Execution.copy_word_nil (count+1) index state input vector result) rfl
  | cons head tail ih =>
      have begin := preservedStep count (.copyWord index) (by intro i impossible;cases impossible) 
        (CertificateArgumentFraming.Execution.copy_word_cons (count+1) index state head input tail vector result) rfl
      have rest := ih (some head,state.2) (some head::vector)
      simpa [List.reverse_cons,List.map_append,List.append_assoc] using
        EvalsToInTime.trans _ 1 (tail.length+1) _ _ _ begin rest

noncomputable def restoreVectorRun (count : Nat) (state : Register)
    (vector result : List (Option Alphabet)) :
    EvalsToInTime (machine count).step
      (config count (some .restoreVector) state [] [] [] [] vector result)
      (some (config count none (none,none) [] [] [] [] [] (some 1::vector.reverse++result)))
      (vector.length+1) := by
  induction vector generalizing state result with
  | nil =>
      simpa using preservedStep count .restoreVector (by intro i impossible;cases impossible) 
        (CertificateArgumentFraming.Execution.restore_vector_nil (count+1) state result) rfl
  | cons head tail ih =>
      have begin := preservedStep count .restoreVector (by intro i impossible;cases impossible) 
        (CertificateArgumentFraming.Execution.restore_vector_cons (count+1) state head tail result) rfl
      have rest := ih (state.1,some head) (head::result)
      simpa [List.reverse_cons,List.append_assoc] using
        EvalsToInTime.trans _ 1 (tail.length+1) _ _ _ begin rest

noncomputable def fieldRun (count : Nat) (index : Index count) (extra : Option (Option Alphabet))
    (value : Data) (input : List Alphabet) (vector result : List (Option Alphabet)) (state : Option Alphabet) :
    EvalsToInTime (machine count).step
      (config count (some (.field index .header)) (state,extra) (writeData value input) [] [] [] vector result)
      (some (config count (some (.spine (WordTemplateMachine.advance index))) (none,extra)
        input [] [] [] (none::(encodeData value).reverse.map some++vector) result))
      (scanCost value+3*dataWeight value+5) := by
  have walked := fieldWalk count index extra value input vector result state
  have boundary := preservedStep count (.field index .complete) (by intro i impossible;cases impossible) 
    (CertificateArgumentFraming.Execution.field_complete_empty (count+1) index
      (finalState value,extra) input (postorderWire value).reverse (encodeData value).reverse vector result) rfl
  have returned := preservedStep count (.field index .checkTail) (by intro i impossible;cases impossible) 
    (CertificateArgumentFraming.Execution.field_return (count+1) index (none,extra)
      input (postorderWire value).reverse (encodeData value).reverse vector result) rfl
  have cleared := clearPostRun count index (none,extra) input
    (postorderWire value).reverse (encodeData value).reverse vector result
  have restored := restorePrefixRun count index (none,extra) input [] (encodeData value).reverse vector result
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at restored
  have copied := copyWordRun count index (none,extra) input (encodeData value) vector result
  have a := EvalsToInTime.trans _ (scanCost value) 1 _ _ _ walked boundary
  have b := EvalsToInTime.trans _ (1+scanCost value) 1 _ _ _ a returned
  have c := EvalsToInTime.trans _ (1+(1+scanCost value))
    ((postorderWire value).reverse.length+1) _ _ _ b cleared
  have d := EvalsToInTime.trans _ ((postorderWire value).reverse.length+1+(1+(1+scanCost value)))
    ((encodeData value).length+1) _ _ _ c restored
  have e := EvalsToInTime.trans _ ((encodeData value).length+1+((postorderWire value).reverse.length+1+(1+(1+scanCost value))))
    ((encodeData value).length+1) _ _ _ d copied
  convert e using 1
  simp only [List.length_reverse,postorderWire_length,encodeData,writeData_length,List.length_nil,Nat.add_zero]
  omega

end Mettapedia.Languages.HOLLight.ReturnedRootPrefixExtraction

namespace Mettapedia.Languages.HOLLight.ReturnedRootPrefixExtraction
open Turing StateTransition Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.GSLT.LanguageDef
open CertificateDataTraversal CertificateArgumentFraming
variable {α : Type}

def words (codec : Codec α) (selected tail : List α) : List (List Alphabet) :=
  argumentWords codec selected++[encodeWith (Codec.list codec) tail]

def prefixCost (codec : Codec α) : List α → List α → Nat
  | [],tail => scanCost ((Codec.list codec).put tail)+3*dataWeight ((Codec.list codec).put tail)+8
  | value::rest,tail => scanCost (codec.put value)+3*dataWeight (codec.put value)+6+prefixCost codec rest tail

/-- The old parser walks each selected original field and then the complete
original tail. The tail remains data; it never enters a finite register. -/
noncomputable def prefixRun (codec : Codec α) (selected tail : List α) (count : Nat) (index : Index count)
    (remaining : index.val+selected.length=count) (state : Register)
    (vector result : List (Option Alphabet)) :
    EvalsToInTime (machine count).step
      (config count (some (.spine index)) state (encodeWith (Codec.list codec) (selected++tail)) [] [] [] vector result)
      (some (config count (some .restoreVector) (none,state.2) [] [] [] []
        ((Indexed.frame (words codec selected tail)).reverse++vector) result)) (prefixCost codec selected tail) := by
  induction selected generalizing index state vector with
  | nil =>
      have cut : index.val=count := by simpa only [List.length_nil,Nat.add_zero] using remaining
      have advanced : (advance index).val=count+1 := by rw [advance_value index (by omega)];omega
      have first := StackMachineComposition.oneStep (cut_step count index cut state
        (encodeWith (Codec.list codec) tail) [] [] [] vector result)
      have field := fieldRun count index state.2 ((Codec.list codec).put tail) [] vector result state.1
      have boundary := StackMachineComposition.oneStep (end_step count (advance index) advanced (none,state.2)
        [] [] [] [] (none::(encodeWith (Codec.list codec) tail).reverse.map some++vector) result)
      have checked := preservedStep count .checkEnd (by intro i impossible;cases impossible)
        (CertificateArgumentFraming.Execution.check_end (count+1) (none,state.2)
          (none::(encodeWith (Codec.list codec) tail).reverse.map some++vector) result) rfl
      have a := EvalsToInTime.trans _ 1 (scanCost ((Codec.list codec).put tail)+3*dataWeight ((Codec.list codec).put tail)+5) _ _ _ first field
      have b := EvalsToInTime.trans _ (scanCost ((Codec.list codec).put tail)+3*dataWeight ((Codec.list codec).put tail)+5+1) 1 _ _ _ a boundary
      have c := EvalsToInTime.trans _ (1+(scanCost ((Codec.list codec).put tail)+3*dataWeight ((Codec.list codec).put tail)+5+1)) 1 _ _ _ b checked
      convert c using 1 <;> try rfl
      · simp only [words,argumentWords,List.map_nil,List.nil_append,Indexed.frame,List.flatMap_cons,List.flatMap_nil,
          List.append_nil,List.reverse_append,List.reverse_cons,List.reverse_nil,List.map_reverse,List.singleton_append]
      · simp only [prefixCost];omega
  | cons value rest ih =>
      have room : index.val<count := by simp only [List.length_cons] at remaining;omega
      have next : (advance index).val+rest.length=count := by
        rw [advance_value index (by omega)]
        simp only [List.length_cons] at remaining
        omega
      have first := StackMachineComposition.oneStep (spine_cons count index room state
        (writeData (codec.put value) (encodeWith (Codec.list codec) (rest++tail))) vector result)
      have field := fieldRun count index state.2 (codec.put value)
        (encodeWith (Codec.list codec) (rest++tail)) vector result (some 4)
      have restRun := ih (advance index) next (none,state.2)
        (none::(encodeWith codec value).reverse.map some++vector)
      have a := EvalsToInTime.trans _ 1 (scanCost (codec.put value)+3*dataWeight (codec.put value)+5) _ _ _ first field
      have b := EvalsToInTime.trans _ (scanCost (codec.put value)+3*dataWeight (codec.put value)+5+1)
        (prefixCost codec rest tail) _ _ _ a restRun
      convert b using 1 <;> try rfl
      · simp only [words,argumentWords,List.map_cons,List.cons_append,Indexed.frame,List.flatMap_cons,
          List.reverse_append,List.reverse_cons,List.nil_append,List.map_reverse,List.append_assoc]
      · simp only [prefixCost];omega

end Mettapedia.Languages.HOLLight.ReturnedRootPrefixExtraction

namespace Mettapedia.Languages.HOLLight.ReturnedRootPrefixExtraction
open Turing StateTransition Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.GSLT.LanguageDef
open CertificateDataTraversal CertificateArgumentFraming
variable {α : Type}

theorem init_eq (count : Nat) (input : List Alphabet) :
    initList (machine count) input=config count (some (.spine ⟨0,by omega⟩)) (none,none) input [] [] [] [] [] := by
  exact CertificateArgumentFraming.Execution.init_eq (count+1) input

theorem halt_eq (count : Nat) (output : List (Option Alphabet)) :
    haltList (machine count) output=config count none (none,none) [] [] [] [] [] output := by
  exact CertificateArgumentFraming.Execution.halt_eq (count+1) output

noncomputable def framedOutputs (codec : Codec α) (selected tail : List α) (count : Nat)
    (arity : selected.length=count) :
    TM2OutputsInTime (machine count) (encodeWith (Codec.list codec) (selected++tail))
      (some (statusWire (some (Indexed.frame (words codec selected tail)))))
      (prefixCost codec selected tail+(Indexed.frame (words codec selected tail)).length+1) := by
  have parsed := prefixRun codec selected tail count ⟨0,by omega⟩ (by simpa only [Nat.zero_add] using arity) (none,none) [] []
  simp only [List.append_nil] at parsed
  have finished := restoreVectorRun count (none,none) (Indexed.frame (words codec selected tail)).reverse []
  simp only [List.reverse_reverse,List.length_reverse,List.append_nil] at finished
  have joined := EvalsToInTime.trans _ (prefixCost codec selected tail)
    ((Indexed.frame (words codec selected tail)).length+1) _ _ _ parsed finished
  change EvalsToInTime _ (initList _ _) (some (haltList _ _)) _
  rw [init_eq,halt_eq]
  simpa only [statusWire,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using joined

theorem frame_length (codec : Codec α) (selected tail : List α) :
    (Indexed.frame (words codec selected tail)).length=(encodeWith (Codec.list codec) (selected++tail)).length+1 := by
  induction selected with
  | nil => simp only [words,argumentWords,List.map_nil,List.nil_append,Indexed.frame,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,List.length_append,List.length_map,List.length_cons,List.length_nil]
  | cons value rest ih =>
      have fieldSize : (encodeWith codec value).length=dataWeight (codec.put value) := by
        simp only [encodeWith,encodeData,writeData_length,List.length_nil,Nat.add_zero]
      rw [List.cons_append,CertificateArgumentFraming.Execution.encoded_cons_size]
      simp only [words,argumentWords,List.map_cons,List.cons_append,Indexed.frame,List.flatMap_cons,
        List.length_append,List.length_map,List.length_cons,List.length_nil] at ih ⊢
      omega

theorem cost_le (codec : Codec α) (selected tail : List α) :
    prefixCost codec selected tail ≤ 6*(encodeWith (Codec.list codec) (selected++tail)).length+8 := by
  induction selected with
  | nil =>
      have scan := scanCost_le ((Codec.list codec).put tail)
      simp only [prefixCost,List.nil_append,encodeWith,encodeData,writeData_length,List.length_nil,Nat.add_zero]
      omega
  | cons value rest ih =>
      have scan := scanCost_le (codec.put value)
      rw [List.cons_append,CertificateArgumentFraming.Execution.encoded_cons_size]
      simp only [prefixCost]
      omega

/-- All original scans, field copies, tail capture, status emission and scratch
cleanup satisfy a linear bound in the complete original list word. -/
noncomputable def framedOutputsLinear (codec : Codec α) (selected tail : List α) (count : Nat)
    (arity : selected.length=count) :
    TM2OutputsInTime (machine count) (encodeWith (Codec.list codec) (selected++tail))
      (some (statusWire (some (Indexed.frame (words codec selected tail)))))
      (7*(encodeWith (Codec.list codec) (selected++tail)).length+10) := by
  have executed := framedOutputs codec selected tail count arity
  have frames := frame_length codec selected tail
  have bounded := cost_le codec selected tail
  exact ⟨executed.toEvalsTo,executed.steps_le_m.trans (by omega)⟩

end Mettapedia.Languages.HOLLight.ReturnedRootPrefixExtraction

namespace Mettapedia.Languages.HOLLight.ReturnedRootPrefixExtraction
open Turing StateTransition Mettapedia.Computability
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.GSLT.LanguageDef
open CertificateDataTraversal CertificateArgumentFraming
noncomputable def rejectResultRun (count : Nat) (state : Register) (result : List (Option Alphabet)) :
    EvalsToInTime (machine count).step
      (config count (some .rejectResult) state [] [] [] [] [] result)
      (some (config count none (none, none) [] [] [] [] [] [some 0])) (result.length + 1) := by
  induction result generalizing state with
  | nil =>
      simpa using preservedStep count .rejectResult (by intro i impossible;cases impossible)
        (CertificateArgumentFraming.Execution.reject_result_nil (count+1) state) rfl
  | cons head tail ih =>
      have first := preservedStep count .rejectResult (by intro i impossible;cases impossible)
        (CertificateArgumentFraming.Execution.reject_result_cons (count+1) state head tail) rfl
      have rest := ih (state.1, some head)
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

noncomputable def rejectVectorRun (count : Nat) (state : Register) (vector result : List (Option Alphabet)) :
    EvalsToInTime (machine count).step
      (config count (some .rejectVector) state [] [] [] [] vector result)
      (some (config count none (none, none) [] [] [] [] [] [some 0])) (vector.length + result.length + 2) := by
  induction vector generalizing state with
  | nil =>
      have first := preservedStep count .rejectVector (by intro i impossible;cases impossible)
        (CertificateArgumentFraming.Execution.reject_vector_nil (count+1) state result) rfl
      have rest := rejectResultRun count (state.1, none) result
      simpa only [List.length_nil, Nat.add_zero, Nat.zero_add, Nat.add_assoc] using
        EvalsToInTime.trans _ 1 (result.length + 1) _ _ _ first rest
  | cons head tail ih =>
      have first := preservedStep count .rejectVector (by intro i impossible;cases impossible)
        (CertificateArgumentFraming.Execution.reject_vector_cons (count+1) state head tail result) rfl
      have rest := ih (state.1, some head)
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EvalsToInTime.trans _ 1 (tail.length + result.length + 2) _ _ _ first rest

noncomputable def rejectPrefixRun (count : Nat) (state : Register) (memo : List Alphabet) (vector result : List (Option Alphabet)) :
    EvalsToInTime (machine count).step
      (config count (some .rejectPrefix) state [] [] [] memo vector result)
      (some (config count none (none, none) [] [] [] [] [] [some 0])) (memo.length + vector.length + result.length + 3) := by
  induction memo generalizing state with
  | nil =>
      have first := preservedStep count .rejectPrefix (by intro i impossible;cases impossible)
        (CertificateArgumentFraming.Execution.reject_prefix_nil (count+1) state vector result) rfl
      have rest := rejectVectorRun count (none, state.2) vector result
      simpa only [List.length_nil, Nat.add_zero, Nat.zero_add, Nat.add_assoc] using
        EvalsToInTime.trans _ 1 (vector.length + result.length + 2) _ _ _ first rest
  | cons head tail ih =>
      have first := preservedStep count .rejectPrefix (by intro i impossible;cases impossible)
        (CertificateArgumentFraming.Execution.reject_prefix_cons (count+1) state head tail vector result) rfl
      have rest := ih (some head, state.2)
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EvalsToInTime.trans _ 1 (tail.length + vector.length + result.length + 3) _ _ _ first rest

noncomputable def rejectPostRun (count : Nat) (state : Register) (post memo : List Alphabet) (vector result : List (Option Alphabet)) :
    EvalsToInTime (machine count).step
      (config count (some .rejectPost) state [] [] post memo vector result)
      (some (config count none (none, none) [] [] [] [] [] [some 0])) (post.length + memo.length + vector.length + result.length + 4) := by
  induction post generalizing state with
  | nil =>
      have first := preservedStep count .rejectPost (by intro i impossible;cases impossible)
        (CertificateArgumentFraming.Execution.reject_post_nil (count+1) state memo vector result) rfl
      have rest := rejectPrefixRun count (none, state.2) memo vector result
      simpa only [List.length_nil, Nat.add_zero, Nat.zero_add, Nat.add_assoc] using
        EvalsToInTime.trans _ 1 (memo.length + vector.length + result.length + 3) _ _ _ first rest
  | cons head tail ih =>
      have first := preservedStep count .rejectPost (by intro i impossible;cases impossible)
        (CertificateArgumentFraming.Execution.reject_post_cons (count+1) state head tail memo vector result) rfl
      have rest := ih (some head, state.2)
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EvalsToInTime.trans _ 1 (tail.length + memo.length + vector.length + result.length + 4) _ _ _ first rest

noncomputable def rejectFramesRun (count : Nat) (state : Register) (frames post memo : List Alphabet) (vector result : List (Option Alphabet)) :
    EvalsToInTime (machine count).step
      (config count (some .rejectFrames) state [] frames post memo vector result)
      (some (config count none (none, none) [] [] [] [] [] [some 0])) (frames.length + post.length + memo.length + vector.length + result.length + 5) := by
  induction frames generalizing state with
  | nil =>
      have first := preservedStep count .rejectFrames (by intro i impossible;cases impossible)
        (CertificateArgumentFraming.Execution.reject_frames_nil (count+1) state post memo vector result) rfl
      have rest := rejectPostRun count (none, state.2) post memo vector result
      simpa only [List.length_nil, Nat.add_zero, Nat.zero_add, Nat.add_assoc] using
        EvalsToInTime.trans _ 1 (post.length + memo.length + vector.length + result.length + 4) _ _ _ first rest
  | cons head tail ih =>
      have first := preservedStep count .rejectFrames (by intro i impossible;cases impossible)
        (CertificateArgumentFraming.Execution.reject_frames_cons (count+1) state head tail post memo vector result) rfl
      have rest := ih (some head, state.2)
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EvalsToInTime.trans _ 1 (tail.length + post.length + memo.length + vector.length + result.length + 5) _ _ _ first rest

noncomputable def rejectInputRun (count : Nat) (state : Register) (input frames post memo : List Alphabet) (vector result : List (Option Alphabet)) :
    EvalsToInTime (machine count).step
      (config count (some .rejectInput) state input frames post memo vector result)
      (some (config count none (none, none) [] [] [] [] [] [some 0])) (input.length + frames.length + post.length + memo.length + vector.length + result.length + 6) := by
  induction input generalizing state with
  | nil =>
      have first := preservedStep count .rejectInput (by intro i impossible;cases impossible)
        (CertificateArgumentFraming.Execution.reject_input_nil (count+1) state frames post memo vector result) rfl
      have rest := rejectFramesRun count (none, state.2) frames post memo vector result
      simpa only [List.length_nil, Nat.add_zero, Nat.zero_add, Nat.add_assoc] using
        EvalsToInTime.trans _ 1 (frames.length + post.length + memo.length + vector.length + result.length + 5) _ _ _ first rest
  | cons head tail ih =>
      have first := preservedStep count .rejectInput (by intro i impossible;cases impossible)
        (CertificateArgumentFraming.Execution.reject_input_cons (count+1) state head tail frames post memo vector result) rfl
      have rest := ih (some head, state.2)
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EvalsToInTime.trans _ 1 (tail.length + frames.length + post.length + memo.length + vector.length + result.length + 6) _ _ _ first rest


end Mettapedia.Languages.HOLLight.ReturnedRootPrefixExtraction

namespace Mettapedia.Languages.HOLLight.ReturnedRootPrefixExtraction
open Turing StateTransition Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.GSLT.LanguageDef
open CertificateDataTraversal CertificateArgumentFraming
variable {α : Type}

theorem spine_refuses (count : Nat) (index : Index count) (room : index.val<count) (state : Register)
    (head : Alphabet) (input : List Alphabet) (vector result : List (Option Alphabet)) (invalid : head≠4) :
    (machine count).step (config count (some (.spine index)) state (head::input) [] [] [] vector result)=
      some (config count (some .rejectInput) (some head,state.2) input [] [] [] vector result) := by
  have notCut : index.val≠count := by omega
  have notEnd : index.val≠count+1 := by omega
  have same : body count (.spine index)=(Base count).m (.spine index) := by
    simp only [body,notCut,notEnd,↓reduceIte]
  have stepSame : (machine count).step (config count (some (.spine index)) state (head::input) [] [] [] vector result)=
      (Base count).step (config count (some (.spine index)) state (head::input) [] [] [] vector result) := by
    change some (TM2.stepAux (body count (.spine index)) state _)=some (TM2.stepAux ((Base count).m (.spine index)) state _)
    rw [same]
  rw [stepSame]
  exact CertificateArgumentFraming.Execution.spine_refuses (count+1) index state head input vector result
    (by simpa only [if_pos (by omega : index.val<count+1)] using invalid)

/-- An insufficient original list reaches the original refusal/cleanup path.
The cut count is compiled into labels; no supplied refusal flag is read. -/
noncomputable def missingRun (codec : Codec α) (values : List α) (count : Nat) (index : Index count)
    (short : index.val+values.length<count) (state : Register) (vector result : List (Option Alphabet)) :
    EvalsToInTime (machine count).step
      (config count (some (.spine index)) state (encodeWith (Codec.list codec) values) [] [] [] vector result)
      (some (config count none (none,none) [] [] [] [] [] [some 0]))
      (CertificateArgumentFraming.Execution.spineCost codec values+
        (encodeWith (Codec.list codec) values).length+vector.length+result.length+8) := by
  induction values generalizing index state vector with
  | nil =>
      have room : index.val<count := by simpa only [List.length_nil,Nat.add_zero] using short
      have first := StackMachineComposition.oneStep (spine_refuses count index room state 3 [2] vector result (by decide))
      have rest := rejectInputRun count (some 3,state.2) [2] [] [] [] vector result
      have joined := EvalsToInTime.trans _ 1 (1+0+0+0+vector.length+result.length+6) _ _ _ first rest
      change EvalsToInTime _ (config count (some (.spine index)) state [3,2] [] [] [] vector result) _ _
      exact ⟨joined.toEvalsTo,joined.steps_le_m.trans (by change _ ≤ 3+2+vector.length+result.length+8;omega)⟩
  | cons value rest ih =>
      have room : index.val<count := by simp only [List.length_cons] at short;omega
      have next : (advance index).val+rest.length<count := by
        rw [advance_value index (by omega)]
        simp only [List.length_cons] at short
        omega
      have first := StackMachineComposition.oneStep (spine_cons count index room state
        (writeData (codec.put value) (encodeWith (Codec.list codec) rest)) vector result)
      have field := fieldRun count index state.2 (codec.put value) (encodeWith (Codec.list codec) rest) vector result (some 4)
      have tail := ih (advance index) next (none,state.2)
        (none::(encodeWith codec value).reverse.map some++vector)
      have a := EvalsToInTime.trans _ 1 (scanCost (codec.put value)+3*dataWeight (codec.put value)+5) _ _ _ first field
      have b := EvalsToInTime.trans _ (scanCost (codec.put value)+3*dataWeight (codec.put value)+5+1)
        (CertificateArgumentFraming.Execution.spineCost codec rest+(encodeWith (Codec.list codec) rest).length+
          (none::(encodeWith codec value).reverse.map some++vector).length+result.length+8) _ _ _ a tail
      convert b using 1 <;> try rfl
      rw [CertificateArgumentFraming.Execution.encoded_cons_size]
      simp only [CertificateArgumentFraming.Execution.spineCost,List.length_append,List.length_cons,List.length_map,
        List.length_reverse,encodeWith,encodeData,writeData_length,List.length_nil,Nat.add_zero]
      omega

noncomputable def missingOutputs (codec : Codec α) (values : List α) (count : Nat) (short : values.length<count) :
    TM2OutputsInTime (machine count) (encodeWith (Codec.list codec) values) (some (statusWire none))
      (7*(encodeWith (Codec.list codec) values).length+8) := by
  have rejected := missingRun codec values count ⟨0,by omega⟩ (by simpa only [Nat.zero_add] using short) (none,none) [] []
  have bounded := CertificateArgumentFraming.Execution.spineCost_le codec values
  change EvalsToInTime _ (initList _ _) (some (haltList _ _)) _
  rw [init_eq,halt_eq]
  exact ⟨rejected.toEvalsTo,rejected.steps_le_m.trans (by simp only [List.length_nil,Nat.add_zero] at *;omega)⟩

end Mettapedia.Languages.HOLLight.ReturnedRootPrefixExtraction

namespace Mettapedia.Languages.HOLLight.ReturnedRootPrefixExtraction
open Turing StateTransition Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.GSLT.LanguageDef
open CertificateDataTraversal CertificateArgumentFraming
variable {α : Type}

def frameResult (codec : Codec α) (count : Nat) (values : List α) : Option (List (Option Alphabet)) :=
  if count≤values.length then some (Indexed.frame (words codec (values.take count) (values.drop count))) else none

noncomputable def totalFramedOutputs (codec : Codec α) (count : Nat) (values : List α) :
    TM2OutputsInTime (machine count) (encodeWith (Codec.list codec) values)
      (some (statusWire (frameResult codec count values))) (7*(encodeWith (Codec.list codec) values).length+10) := by
  by_cases enough : count≤values.length
  · have arity : (values.take count).length=count := by simp only [List.length_take,Nat.min_eq_left enough]
    have run := framedOutputsLinear codec (values.take count) (values.drop count) count arity
    simpa only [frameResult,if_pos enough,List.take_append_drop] using run
  · have short : values.length<count := by omega
    have run := missingOutputs codec values count short
    rw [frameResult,if_neg enough]
    exact ⟨run.toEvalsTo,run.steps_le_m.trans (by omega)⟩

/-- Static holes reverse only this rule's prefix. The final original tail is
copied from its separate field and never joins the reversed prefix. -/
def selectedIndices (count : Nat) : List (Fin (count+1)) := (List.finRange count).reverse.map Fin.castSucc

def listTemplate {arity : Nat} (indices : List (Fin arity)) : Indexed.Template Alphabet arity :=
  indices.flatMap (fun index => [.inl 4,.inr index])++[.inl 3,.inl 2]

def resultTemplate (count : Nat) : Indexed.Template Alphabet (count+1) :=
  [.inl 1,.inl 4]++listTemplate (selectedIndices count)++[.inr (Fin.last count)]

def rootFields {count : Nat} (roots : Fin count → Nat) (tail : List Nat) : Fin (count+1) → List Alphabet :=
  Fin.snoc (fun index => encodeWith Codec.nat (roots index)) (encodeWith (Codec.list Codec.nat) tail)

theorem fields_wire {count : Nat} (roots : Fin count → Nat) (tail : List Nat) :
    Indexed.argumentWire (rootFields roots tail)=Indexed.frame (words Codec.nat (List.ofFn roots) tail) := by
  simp only [Indexed.argumentWire,← List.ofFn_eq_map,rootFields]
  rw [List.ofFn_succ']
  simp only [Fin.snoc_castSucc,Fin.snoc_last,List.concat_eq_append,words,argumentWords,List.ofFn_comp']

theorem list_instantiates {arity : Nat} (indices : List (Fin arity)) (fields : Fin arity → List Alphabet) :
    Indexed.instantiate (listTemplate indices) fields=CertificateArgumentFraming.ListAssembly.wire (indices.map fields) := by
  induction indices with
  | nil => simp only [listTemplate,List.flatMap_nil,List.nil_append,List.map_nil,
      Indexed.instantiate_literal,Indexed.instantiate_nil,CertificateArgumentFraming.ListAssembly.wire_nil]
  | cons head tail ih =>
      simp only [listTemplate,List.flatMap_cons,List.append_assoc,Indexed.instantiate_append,
        Indexed.instantiate_literal,Indexed.instantiate_hole,Indexed.instantiate_nil,List.append_nil,
        List.map_cons,CertificateArgumentFraming.ListAssembly.wire_cons] at ih ⊢
      rw [ih]

theorem result_instantiates {count : Nat} (roots : Fin count → Nat) (tail : List Nat) :
    Indexed.instantiate (resultTemplate count) (rootFields roots tail)=
      (1 : Alphabet)::encodeWith (Codec.prod (Codec.list Codec.nat) (Codec.list Codec.nat))
        ((List.ofFn roots).reverse,tail) := by
  simp only [resultTemplate,Indexed.instantiate_append,Indexed.instantiate_literal,Indexed.instantiate_hole,
    Indexed.instantiate_nil,List.append_nil,list_instantiates]
  have selected : (selectedIndices count).map (rootFields roots tail)=
      ((List.ofFn roots).reverse).map (encodeWith Codec.nat) := by
    change ((List.finRange count).reverse.map Fin.castSucc).map (rootFields roots tail)=_
    rw [List.map_map,List.map_reverse]
    simp only [Function.comp_def,rootFields,Fin.snoc_castSucc]
    rw [← List.ofFn_eq_map,List.ofFn_comp']
    exact List.map_reverse.symm
  rw [selected,CertificateArgumentFraming.ListAssembly.wire_codec]
  simp only [rootFields,Fin.snoc_last,encodeWith,Codec.prod,encodeData_pair,List.cons_append,List.nil_append]

end Mettapedia.Languages.HOLLight.ReturnedRootPrefixExtraction

namespace Mettapedia.Languages.HOLLight.ReturnedRootPrefixExtraction
open Turing StateTransition Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.GSLT.LanguageDef
open CertificateArgumentFraming

abbrev payload (count : Nat) := Indexed.machine (resultTemplate count)
def accepts (cell : Option Alphabet) := decide (cell=some 1)
attribute [local implicit_reducible] Indexed.machine
local instance (count : Nat) : Inhabited ((payload count).Γ (payload count).k₀) := inferInstanceAs (Inhabited (Option Alphabet))
def dispatch (count : Nat) := StackMachineComposition.Dispatch.machine (payload count) accepts [(0 : Alphabet)]
attribute [local implicit_reducible] dispatch
local instance (count : Nat) : Fintype ((machine count).Γ (machine count).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance (count : Nat) : Inhabited ((machine count).Γ (machine count).k₁) := inferInstanceAs (Inhabited (Option Alphabet))

def rootMachine (count : Nat) := StackMachineComposition.machine (machine count) (dispatch count) (Equiv.refl (Option Alphabet))

def pairCodec := Codec.prod (Codec.list Codec.nat) (Codec.list Codec.nat)
def rootResult (count : Nat) (values : List Nat) : Option (List Nat × List Nat) :=
  if count≤values.length then some ((values.take count).reverse,values.drop count) else none

def rootWord (result : Option (List Nat × List Nat)) : List Alphabet := result.elim [0] (fun pair => 1::encodeWith pairCodec pair)
def readRoots : List Alphabet → Option (List Nat × List Nat)
  | 1::word => decodeWith pairCodec word
  | _ => none

theorem readRoots_rootWord (result : Option (List Nat × List Nat)) : readRoots (rootWord result)=result := by
  cases result with
  | none => rfl
  | some pair => exact decodeWith_encodeWith pairCodec pair

/-- Finite template overhead is charged with the original physical word. -/
def rootClock (count : Nat) (values : List Nat) :=
  7*(encodeWith (Codec.list Codec.nat) values).length+10+
    2*(statusWire (frameResult Codec.nat count values)).length+2+
      2+4*((resultTemplate count).length+1)*((statusWire (frameResult Codec.nat count values)).length+1)

noncomputable def positiveRootOutputs {count : Nat} (roots : Fin count → Nat) (tail : List Nat) :
    TM2OutputsInTime (rootMachine count) (encodeWith (Codec.list Codec.nat) (List.ofFn roots++tail))
      (some (rootWord (some ((List.ofFn roots).reverse,tail))))
      (rootClock count (List.ofFn roots++tail)) := by
  have parser := framedOutputsLinear Codec.nat (List.ofFn roots) tail count (List.length_ofFn)
  rw [← fields_wire] at parser
  have copied := Indexed.outputs (resultTemplate count) (rootFields roots tail)
  rw [result_instantiates] at copied
  have operated := StackMachineComposition.Dispatch.outputs_success (payload count) accepts [(0 : Alphabet)]
    (some 1) (Indexed.argumentWire (rootFields roots tail))
    (rootWord (some ((List.ofFn roots).reverse,tail))) _ (by decide) copied
  have joined := StackMachineComposition.outputs (machine count) (dispatch count) (Equiv.refl (Option Alphabet))
    (encodeWith (Codec.list Codec.nat) (List.ofFn roots++tail))
    (statusWire (some (Indexed.argumentWire (rootFields roots tail))))
    (rootWord (some ((List.ofFn roots).reverse,tail))) _ _ parser (by
      change TM2OutputsInTime (dispatch count) ((statusWire (some (Indexed.argumentWire (rootFields roots tail)))).map id) _ _
      simpa only [dispatch,List.map_id,statusWire] using operated)
  apply WordEqualityMachine.within joined
  have enough : count≤(List.ofFn roots++tail).length := by simp only [List.length_append,List.length_ofFn];omega
  have headTake : (List.ofFn roots).take count=List.ofFn roots := by simpa only [List.length_ofFn] using (@List.take_length Nat (List.ofFn roots))
  have headDrop : (List.ofFn roots).drop count=[] := by simpa only [List.length_ofFn] using (@List.drop_length Nat (List.ofFn roots))
  have take : (List.ofFn roots++tail).take count=List.ofFn roots := by simp only [List.take_append,List.length_ofFn,Nat.sub_self,List.take_zero,List.append_nil,headTake]
  have drop : (List.ofFn roots++tail).drop count=tail := by simp only [List.drop_append,List.length_ofFn,Nat.sub_self,List.drop_zero,headDrop,List.nil_append]
  have framed : frameResult Codec.nat count (List.ofFn roots++tail)=some (Indexed.argumentWire (rootFields roots tail)) := by
    rw [frameResult,if_pos enough,take,drop,fields_wire]
  rw [rootClock,framed]
  simp only [statusWire,List.length_cons]
  have copyBound := Nat.mul_le_mul_left (4*((resultTemplate count).length+1))
    (Nat.le_succ ((Indexed.argumentWire (rootFields roots tail)).length+1))
  simp only [Nat.succ_eq_add_one] at copyBound
  omega

noncomputable def refusedRootOutputs (count : Nat) (values : List Nat) (short : values.length<count) :
    TM2OutputsInTime (rootMachine count) (encodeWith (Codec.list Codec.nat) values) (some (rootWord none)) (rootClock count values) := by
  have parser := missingOutputs Codec.nat values count short
  have refused := StackMachineComposition.Dispatch.outputs_refused (payload count) accepts [(0 : Alphabet)]
    (some 0) [] (by decide)
  have joined := StackMachineComposition.outputs (machine count) (dispatch count) (Equiv.refl (Option Alphabet))
    (encodeWith (Codec.list Codec.nat) values) (statusWire none) (rootWord none) _ _ parser (by
      change TM2OutputsInTime (dispatch count) ((statusWire none).map id) _ _
      simpa only [dispatch,List.map_id,statusWire,rootWord,Option.elim_none] using refused)
  apply WordEqualityMachine.within joined
  have missing : frameResult Codec.nat count values=none := by rw [frameResult,if_neg (by omega : ¬count≤values.length)]
  rw [rootClock,missing]
  simp only [statusWire,List.length_cons,List.length_nil]
  omega

end Mettapedia.Languages.HOLLight.ReturnedRootPrefixExtraction

namespace Mettapedia.Languages.HOLLight.ReturnedRootPrefixExtraction
open Turing StateTransition Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.GSLT.LanguageDef
open CertificateArgumentFraming

noncomputable def rootOutputs (count : Nat) (values : List Nat) :
    TM2OutputsInTime (rootMachine count) (encodeWith (Codec.list Codec.nat) values)
      (some (rootWord (rootResult count values))) (rootClock count values) := by
  by_cases enough : count≤values.length
  · have arity : (values.take count).length=count := by simp only [List.length_take,Nat.min_eq_left enough]
    let roots := ChronologicalTaskExecution.Node.listVector (values.take count) count arity
    have vector : List.ofFn roots=values.take count := by
      rw [List.ofFn_eq_map]
      exact ChronologicalTaskExecution.Node.listVector_list _ _ _
    have positive := positiveRootOutputs roots (values.drop count)
    rw [vector,List.take_append_drop] at positive
    simpa only [rootResult,if_pos enough] using positive
  · have short : values.length<count := by omega
    simpa only [rootResult,if_neg enough] using refusedRootOutputs count values short

theorem run_root_readout (count : Nat) (values : List Nat) (word : List Alphabet)
    (finished : TM2Outputs (rootMachine count) (encodeWith (Codec.list Codec.nat) values) (some word)) :
    readRoots word=rootResult count values := by
  rw [StackMachineComposition.outputs_unique finished (rootOutputs count values).toEvalsTo,readRoots_rootWord]

theorem listTemplate_length {arity : Nat} (indices : List (Fin arity)) :
    (listTemplate indices).length=2*indices.length+2 := by
  induction indices with
  | nil => rfl
  | cons head tail ih =>
      simp only [listTemplate,List.flatMap_cons,List.append_assoc,List.length_append,List.length_cons,
        List.length_nil] at ih ⊢
      omega

theorem resultTemplate_length (count : Nat) : (resultTemplate count).length=2*count+5 := by
  simp only [resultTemplate,List.length_append,List.length_cons,List.length_nil,listTemplate_length,
    selectedIndices,List.length_map,List.length_reverse,List.length_finRange]
  omega

theorem status_length_le (count : Nat) (values : List Nat) :
    (statusWire (frameResult Codec.nat count values)).length≤
      (encodeWith (Codec.list Codec.nat) values).length+2 := by
  by_cases enough : count≤values.length
  · rw [frameResult,if_pos enough]
    simp only [statusWire,List.length_cons]
    have exactLength := frame_length Codec.nat (values.take count) (values.drop count)
    rw [List.take_append_drop] at exactLength
    omega
  · rw [frameResult,if_neg enough]
    simp only [statusWire,List.length_cons,List.length_nil]
    omega

/-- The compiled prefix length is descriptor overhead; runtime roots and their
remaining list are charged by their complete original binary word. -/
theorem rootClock_linear (count : Nat) (values : List Nat) :
    rootClock count values≤128*(count+1)*((encodeWith (Codec.list Codec.nat) values).length+1) := by
  have wireBound := status_length_le count values
  have multiplied := Nat.mul_le_mul_left (4*(2*count+6)) (Nat.add_le_add_right wireBound 1)
  rw [rootClock,resultTemplate_length]
  nlinarith

noncomputable def linearRootOutputs (count : Nat) (values : List Nat) :
    TM2OutputsInTime (rootMachine count) (encodeWith (Codec.list Codec.nat) values)
      (some (rootWord (rootResult count values)))
      (128*(count+1)*((encodeWith (Codec.list Codec.nat) values).length+1)) :=
  WordEqualityMachine.within (rootOutputs count values) (rootClock_linear count values)

open ChronologicalDriver

theorem claim_roots_split {definition : ValidatedCalculusLanguageDef}
    (checkedPrefix : Prefix definition) (values : List (Claim definition checkedPrefix)) (count : Nat) :
    rootResult count (values.map Claim.root)=
      if count≤values.length then
        some (((values.take count).reverse.map Claim.root),(values.drop count).map Claim.root)
      else none := by
  simp only [rootResult,List.length_map,← List.map_take,← List.map_drop,List.map_reverse]

/-- The exact roots supplied to the original close branch, with the unused
claim tail retained in its existing order. This does not execute emission. -/
noncomputable def controller_selected_roots (definition : ValidatedCalculusLanguageDef)
    (state : State definition) (premises : List Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    TM2OutputsInTime (rootMachine premises.length)
      (encodeWith (Codec.list Codec.nat) (state.values.map Claim.root))
      (some (rootWord (if premises.length≤state.values.length then
        some (((state.values.take premises.length).reverse.map Claim.root),
          (state.values.drop premises.length).map Claim.root) else none)))
      (128*(premises.length+1)*((encodeWith (Codec.list Codec.nat) (state.values.map Claim.root)).length+1)) := by
  simpa only [claim_roots_split] using linearRootOutputs premises.length (state.values.map Claim.root)

example : rootResult 0 [5,8]=some ([],[5,8]) := rfl
example : rootResult 3 [9,2,9,7,11]=some ([9,2,9],[7,11]) := rfl
example : rootResult 3 [1,4,2,8]=some ([2,4,1],[8]) := rfl
example : rootResult 1 []=none := rfl
example : readRoots [0]=none := rfl

end Mettapedia.Languages.HOLLight.ReturnedRootPrefixExtraction

namespace Mettapedia.Languages.HOLLight.ReturnedRootPrefixExtraction.Program
open Turing StateTransition Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.GSLT.LanguageDef
open CertificateArgumentFraming
attribute [local implicit_reducible] rootMachine dispatch machine
abbrev Key := Option (Execution.Key ⊕ Indexed.Stack)
abbrev Registers := Execution.State × (Option (Option Alphabet) × Option (Option Alphabet)) × Option (Option Alphabet)

def keys : List Key := [none,
  some (.inl Execution.inputKey),some (.inl Execution.framesKey),some (.inl Execution.postKey),
  some (.inl Execution.prefixKey),some (.inl Execution.vectorKey),some (.inl Execution.resultKey),
  some (.inr .input),some (.inr .temporary),some (.inr .output),some (.inr .result)]

theorem all_keys : ∀ key : Key,key ∈ keys := by
  intro key
  rcases key with _ | (key | key)
  · simp [keys]
  · rcases key with _ | (_ | (_ | key))
    · simp [keys,Execution.resultKey]
    · simp [keys,Execution.vectorKey]
    · simp [keys,Execution.prefixKey]
    · cases key <;> simp [keys,Execution.inputKey,Execution.framesKey,Execution.postKey]
  · cases key <;> simp [keys]

local instance (count : Nat) : BEq (rootMachine count).σ := inferInstanceAs (BEq Registers)


def prefixBody (count : Nat) : (machine count).Λ → (machine count).Stmt
  | .spine index =>
      if index.val=count then .goto fun _ => .field index .header
      else if index.val=count+1 then .goto fun _ => .checkEnd
      else OriginalChildJobs.Program.framerBody (count+1) (.spine index)
  | phase => OriginalChildJobs.Program.framerBody (count+1) phase

theorem prefixBody_exact (count : Nat) : prefixBody count=(machine count).m := by
  funext phase
  cases phase <;> simp only [prefixBody,OriginalChildJobs.Program.framerBody_exact] <;> rfl

local instance (count : Nat) : Fintype ((machine count).Γ (machine count).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance (count : Nat) : Inhabited ((machine count).Γ (machine count).k₁) := inferInstanceAs (Inhabited (Option Alphabet))
local instance (count : Nat) : Fintype ((payload count).Γ (payload count).k₀) := inferInstanceAs (Fintype (Option Alphabet))

def dispatchBody (count : Nat) : (dispatch count).Λ → (dispatch count).Stmt :=
  StackMachineComposition.Dispatch.Programs.body (Cells := Indexed.Alphabet Alphabet)
    Indexed.Stack.input Indexed.Stack.result (none : Option (Option Alphabet))
    (.emit ⟨0,by omega⟩) accepts [(0 : Alphabet)] (Indexed.program (resultTemplate count))

theorem dispatchBody_exact (count : Nat) : dispatchBody count=(dispatch count).m := by
  unfold dispatchBody
  exact (StackMachineComposition.Dispatch.Programs.body_eq (payload count) accepts [(0 : Alphabet)]).symm

def instructionBody (count : Nat) : (rootMachine count).Λ → (rootMachine count).Stmt :=
  StackMachineComposition.Programs.body Execution.resultKey Indexed.Stack.input
    StackMachineComposition.Dispatch.Phase.read (none : Option Alphabet) id
    (prefixBody count) (dispatchBody count)

theorem instructionBody_exact (count : Nat) : instructionBody count=(rootMachine count).m := by
  unfold instructionBody
  rw [prefixBody_exact,dispatchBody_exact]
  exact StackMachineComposition.body_eq (machine count) (dispatch count) (Equiv.refl (Option Alphabet))

def keyEquality : DecidableEq Key := inferInstance
local instance (count : Nat) : DecidableEq (rootMachine count).K := keyEquality

def step (count : Nat) : (rootMachine count).Cfg → Option (rootMachine count).Cfg :=
  @TM2.step (rootMachine count).K (rootMachine count).Γ (rootMachine count).Λ (rootMachine count).σ
    keyEquality (instructionBody count)

theorem step_exact (count : Nat) : step count=(rootMachine count).step := by
  unfold step
  rw [instructionBody_exact,show keyEquality=(rootMachine count).kDecidableEq from Subsingleton.elim _ _]
  rfl

abbrev inputKey (count : Nat) : (rootMachine count).K := some (.inl Execution.inputKey)
abbrev resultKey (count : Nat) : (rootMachine count).K := some (.inr Indexed.Stack.result)

def initial (count : Nat) (word : List Alphabet) : (rootMachine count).Cfg where
  l := some (.inl (.spine ⟨0,by omega⟩))
  var := ((none,none),(none,none),none)
  stk key := if same : key=inputKey count then by cases same;exact word else []

theorem initial_exact (count : Nat) (word : List Alphabet) : initial count word=initList (rootMachine count) word := by
  simp only [initial,initList]
  congr 1
  funext key
  by_cases same : key=inputKey count
  · subst key
    have original : inputKey count=(rootMachine count).k₀ := rfl
    simp only [dif_pos original]
    rfl
  · have original : key≠(rootMachine count).k₀ := same
    simp only [dif_neg same,dif_neg original]

def halted (count : Nat) (word : List Alphabet) : (rootMachine count).Cfg where
  l := none
  var := ((none,none),(none,none),none)
  stk key := if same : key=resultKey count then by cases same;exact word else []

theorem halted_exact (count : Nat) (word : List Alphabet) : halted count word=haltList (rootMachine count) word := by
  simp only [halted,haltList]
  congr 1
  funext key
  by_cases same : key=resultKey count
  · subst key
    have original : resultKey count=(rootMachine count).k₁ := rfl
    simp only [dif_pos original]
    rfl
  · have original : key≠(rootMachine count).k₁ := same
    simp only [dif_neg same,dif_neg original]

def refresh (count : Nat) (state : (rootMachine count).Cfg) : (rootMachine count).Cfg :=
  let handoff := state.stk none
  let input := state.stk (some (.inl Execution.inputKey))
  let frames := state.stk (some (.inl Execution.framesKey))
  let post := state.stk (some (.inl Execution.postKey))
  let memo := state.stk (some (.inl Execution.prefixKey))
  let vector := state.stk (some (.inl Execution.vectorKey))
  let framed := state.stk (some (.inl Execution.resultKey))
  let copyInput := state.stk (some (.inr .input))
  let copyTemporary := state.stk (some (.inr .temporary))
  let copyOutput := state.stk (some (.inr .output))
  let copyResult := state.stk (some (.inr .result))
  {state with stk := fun key => match key with
    | none => handoff
    | some (.inl none) => framed
    | some (.inl (some none)) => vector
    | some (.inl (some (some none))) => memo
    | some (.inl (some (some (some .input)))) => input
    | some (.inl (some (some (some .frames)))) => frames
    | some (.inl (some (some (some .output)))) => post
    | some (.inr .input) => copyInput
    | some (.inr .temporary) => copyTemporary
    | some (.inr .output) => copyOutput
    | some (.inr .result) => copyResult}

theorem refresh_exact (count : Nat) (state : (rootMachine count).Cfg) : refresh count state=state := by
  cases state with
  | mk label registers contents =>
      dsimp only [refresh]
      congr 1
      funext key
      rcases key with _ | (key | key)
      · rfl
      · rcases key with _ | (_ | (_ | key))
        all_goals first | rfl | (cases key <;> rfl)
      · cases key <;> rfl

def run (count : Nat) : Nat → Nat → (rootMachine count).Cfg → Option (Nat × (rootMachine count).Cfg)
  | 0,_,_ => none
  | fuel+1,used,state =>
      if state.l.isNone then some (used,state)
      else match step count state with
        | none => none
        | some next => run count fuel (used+1) (refresh count next)

theorem run_actual (count fuel used : Nat) (before : (rootMachine count).Cfg)
    {steps : Nat} {after : (rootMachine count).Cfg} (finished : run count fuel used before=some (steps,after)) :
    used≤steps ∧ (∃ path : EvalsToInTime (rootMachine count).step before (some after) (steps-used),
      path.steps=steps-used) ∧ after.l=none := by
  induction fuel generalizing used before with
  | zero => cases finished
  | succ fuel ih =>
      simp only [run,step_exact] at finished
      split at finished
      · rename_i halted
        have pair := Option.some.inj finished
        have countSame := congrArg Prod.fst pair
        have stateSame := congrArg Prod.snd pair
        change used=steps at countSame
        change before=after at stateSame
        subst steps
        subst after
        refine ⟨le_rfl,?_,Option.isNone_iff_eq_none.mp halted⟩
        rw [Nat.sub_self]
        exact ⟨EvalsToInTime.refl _ before,rfl⟩
      · cases advanced : (rootMachine count).step before with
        | none => simp only [advanced,reduceCtorEq] at finished
        | some next =>
            simp only [advanced] at finished
            rw [refresh_exact] at finished
            obtain ⟨countBound,⟨tail,tailCount⟩,stopped⟩ := ih (used+1) next finished
            let first : EvalsToInTime (rootMachine count).step before (some next) 1 :=
              ⟨⟨1,by change (some before).bind (rootMachine count).step=some next;exact advanced⟩,le_rfl⟩
            have relative : steps-used=(steps-(used+1))+1 := by omega
            refine ⟨by omega,?_,stopped⟩
            rw [relative]
            refine ⟨EvalsToInTime.trans _ 1 (steps-(used+1)) before next (some after) first tail,?_⟩
            change tail.steps+first.steps=(steps-(used+1))+1
            rw [tailCount]

def snapshot (count : Nat) (state : (rootMachine count).Cfg) : List (List (Option Alphabet)) :=
  [state.stk none,
    (state.stk (some (.inl Execution.inputKey))).map some,
    (state.stk (some (.inl Execution.framesKey))).map some,
    (state.stk (some (.inl Execution.postKey))).map some,
    (state.stk (some (.inl Execution.prefixKey))).map some,
    state.stk (some (.inl Execution.vectorKey)),state.stk (some (.inl Execution.resultKey)),
    state.stk (some (.inr .input)),state.stk (some (.inr .temporary)),
    (state.stk (some (.inr .output))).map some,(state.stk (some (.inr .result))).map some]


private theorem map_some_injective {first second : List Alphabet}
    (same : first.map some=second.map some) : first=second :=
  (List.map_inj_right (fun _ _ equal => Option.some.inj equal)).mp same

/-- Every original typed stack appears in the snapshot. Optional wrapping of
ordinary bytes is injective, including the original zero and framing symbols. -/
theorem snapshot_injective (count : Nat) (actual expected : (rootMachine count).Cfg)
    (same : snapshot count actual=snapshot count expected) : actual.stk=expected.stk := by
  funext key
  rcases key with _ | (key | key)
  · exact congrArg (fun rows => rows.getD 0 []) same
  · rcases key with _ | (_ | (_ | key))
    · exact congrArg (fun rows => rows.getD 6 []) same
    · exact congrArg (fun rows => rows.getD 5 []) same
    · exact map_some_injective (congrArg (fun rows => rows.getD 4 []) same)
    · cases key with
      | input => exact map_some_injective (congrArg (fun rows => rows.getD 1 []) same)
      | frames => exact map_some_injective (congrArg (fun rows => rows.getD 2 []) same)
      | output => exact map_some_injective (congrArg (fun rows => rows.getD 3 []) same)
  · cases key with
    | input => exact congrArg (fun rows => rows.getD 7 []) same
    | temporary => exact congrArg (fun rows => rows.getD 8 []) same
    | output => exact map_some_injective (congrArg (fun rows => rows.getD 9 []) same)
    | result => exact map_some_injective (congrArg (fun rows => rows.getD 10 []) same)

def sameStacks (count : Nat) (actual expected : (rootMachine count).Cfg) : Bool :=
  snapshot count actual == snapshot count expected

end Mettapedia.Languages.HOLLight.ReturnedRootPrefixExtraction.Program
