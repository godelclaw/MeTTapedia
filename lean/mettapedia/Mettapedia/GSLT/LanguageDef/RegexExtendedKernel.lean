import Mettapedia.GSLT.LanguageDef.RegexExtendedGraph
import Mettapedia.GSLT.LanguageDef.RegexObservationTransport

/-!
# Relocating authored regex operations into the observation kernel

Finite control indices are the actual ordered instruction rows. Group bounds,
target ownership and descending observation ranks are derived from the source
compiler. The source operation at an owned occurrence is uniquely determined
by its structural authorization derivation, independently of target decoding.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexExtendedKernel

open RegexExtendedCompilerSemantics
open RegexDependentObservation (Comparison LookKind)

def operandGroup : Instruction → Nat
  | .save _ group _ _ | .backref _ group _ _ => group
  | _ => 0

def minimumGroups (program : Program) : Nat := (program.rows.map operandGroup).foldr max 0 + 1

def groups (program : Program) (declaredCapacity : Nat) : Nat := max declaredCapacity (minimumGroups program)

private theorem member_le_maximum (values : List Nat) (value : Nat) (member : value ∈ values) :
    value ≤ values.foldr max 0 := by
  induction values with
  | nil => cases member
  | cons head tail ih =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact Nat.le_max_left _ _
      · exact (ih member).trans (Nat.le_max_right _ _)

theorem operandGroup_lt (declaredCapacity : Nat) (program : Program) (row : Instruction) (member : row ∈ program.rows) :
    operandGroup row < groups program declaredCapacity :=
  lt_of_lt_of_le (Nat.lt_succ_of_le (member_le_maximum _ _ (List.mem_map.mpr ⟨row, member, rfl⟩))) (Nat.le_max_right _ _)

def targetIndex (checked : Graph.CheckedProgram) (row : Instruction) (member : row ∈ checked.program.rows)
    (target : Address) (owned : target ∈ Graph.targets row) : Fin checked.program.rows.length :=
  Graph.relocate checked.program ⟨target, checked.targetsOwned row member target owned⟩

theorem targetIndex_address (checked : Graph.CheckedProgram) (row : Instruction)
    (member : row ∈ checked.program.rows) (target : Address) (owned : target ∈ Graph.targets row) :
    (Graph.atIndex checked.program (targetIndex checked row member target owned)).val = target :=
  congrArg Subtype.val (Graph.atIndex_relocate checked.program
    ⟨target, checked.targetsOwned row member target owned⟩)

def contains (ranges : List ScalarRange) (scalar : Nat) : Bool :=
  ranges.any (fun range => decide (range.1 ≤ scalar ∧ scalar ≤ range.2))

/-- Interpret a licensed symbolic operation, retaining its original group
identity and explicitly supplied assertion interpretation. -/
def decode (declaredCapacity : Nat) (checked : Graph.CheckedProgram) (assertions : String → Nat → Bool)
    (row : Instruction) (member : row ∈ checked.program.rows) :
    RegexDependentObservation.Instruction checked.program.rows.length (groups checked.program declaredCapacity) :=
  match row with
  | .fail _ => .dead
  | .accept _ => .accept
  | .jump origin next =>
      .jump (targetIndex checked (.jump origin next) member next (by simp [Graph.targets, ordinaryTargets]))
  | .scalar origin scalar next =>
      .consume (· == scalar)
        (targetIndex checked (.scalar origin scalar next) member next (by simp [Graph.targets, ordinaryTargets]))
  | .any origin next =>
      .consume (fun _ => true)
        (targetIndex checked (.any origin next) member next (by simp [Graph.targets, ordinaryTargets]))
  | .class_ origin ranges next =>
      .consume (contains ranges)
        (targetIndex checked (.class_ origin ranges next) member next (by simp [Graph.targets, ordinaryTargets]))
  | .assertion origin name next =>
      .assertion (assertions name)
        (targetIndex checked (.assertion origin name next) member next (by simp [Graph.targets, ordinaryTargets]))
  | .split origin first second =>
      .branch
        (targetIndex checked (.split origin first second) member first (by simp [Graph.targets, ordinaryTargets]))
        (targetIndex checked (.split origin first second) member second (by simp [Graph.targets, ordinaryTargets]))
  | .save origin group opening next =>
      let slot : Fin (groups checked.program declaredCapacity) :=
        ⟨group, operandGroup_lt declaredCapacity checked.program (.save origin group opening next) member⟩
      let next := targetIndex checked (.save origin group opening next) member next
        (by simp [Graph.targets, ordinaryTargets])
      if opening then .open slot next else .close slot next
  | .backref origin group comparison next =>
      .backref ⟨group, operandGroup_lt declaredCapacity checked.program (.backref origin group comparison next) member⟩ comparison
        (targetIndex checked (.backref origin group comparison next) member next (by simp [Graph.targets, ordinaryTargets]))
  | .look origin entry kind next =>
      .look kind
        (targetIndex checked (.look origin entry kind next) member entry (by simp [Graph.targets, ordinaryTargets]))
        (targetIndex checked (.look origin entry kind next) member next (by simp [Graph.targets, ordinaryTargets]))

def code (declaredCapacity : Nat) (checked : Graph.CheckedProgram) (assertions : String → Nat → Bool)
    (index : Fin checked.program.rows.length) :
    RegexDependentObservation.Instruction checked.program.rows.length (groups checked.program declaredCapacity) :=
  decode declaredCapacity checked assertions checked.program.rows[index.val] (List.getElem_mem index.isLt)

theorem decode_ordinary_targets (declaredCapacity : Nat) (checked : Graph.CheckedProgram) (assertions : String → Nat → Bool)
    (row : Instruction) (member : row ∈ checked.program.rows) (next : Fin checked.program.rows.length)
    (edge : next ∈ RegexDependentObservation.ordinaryTargets (decode declaredCapacity checked assertions row member)) :
    (Graph.atIndex checked.program next).val ∈ ordinaryTargets row := by
  cases row with
  | fail origin | accept origin => simp [decode, RegexDependentObservation.ordinaryTargets] at edge
  | jump origin target | scalar origin scalar target | any origin target | class_ origin ranges target | assertion origin name target | backref origin group comparison target | look origin entry kind target =>
      simp only [decode, RegexDependentObservation.ordinaryTargets, List.mem_singleton] at edge
      subst next
      simpa only [ordinaryTargets, List.mem_singleton] using targetIndex_address checked _ member target _
  | split origin first second =>
      simp only [decode, RegexDependentObservation.ordinaryTargets, List.mem_cons,
        List.not_mem_nil, or_false] at edge
      rcases edge with rfl | rfl
      · exact List.mem_cons.mpr (Or.inl (targetIndex_address checked _ member first _))
      · exact List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr (targetIndex_address checked _ member second _)))
  | save origin group opening target =>
      cases opening <;> simp only [decode, Bool.false_eq_true, ↓reduceIte,
        RegexDependentObservation.ordinaryTargets, List.mem_singleton] at edge
      all_goals
        subst next
        simpa only [ordinaryTargets, List.mem_singleton] using targetIndex_address checked _ member target _

theorem decode_look (declaredCapacity : Nat) (checked : Graph.CheckedProgram) (assertions : String → Nat → Bool)
    (row : Instruction) (member : row ∈ checked.program.rows)
    (kind : LookKind) (entry next : Fin checked.program.rows.length)
    (observed : decode declaredCapacity checked assertions row member = .look kind entry next) :
    ∃ origin body continuation, row = .look origin body kind continuation ∧
      (Graph.atIndex checked.program entry).val = body := by
  cases row <;> simp only [decode] at observed
  all_goals try contradiction
  · rename_i origin group opening target
    cases opening <;> contradiction
  · rename_i origin body actualKind continuation
    cases observed
    exact ⟨origin, body, continuation, rfl, targetIndex_address _ _ _ _ _⟩

/-- The actual relocated compiler result earns the canonical kernel's rank
certificate. No certificate fields are supplied by a caller. -/
def certificate (declaredCapacity : Nat) (pattern : Pattern) (assertions : String → Nat → Bool) :
    RegexObservationKernel.Certificate (code declaredCapacity (Graph.checkedCompile pattern) assertions) where
  rank := fun index => Graph.rank (compile pattern) (Graph.atIndex (compile pattern) index).val
  ordinary := by
    intro pc next edge
    exact Graph.compiled_ordinary_rank pattern _ (List.getElem_mem pc.isLt)
      (Graph.atIndex (compile pattern) next).val
      (decode_ordinary_targets declaredCapacity (Graph.checkedCompile pattern) assertions _ _ next edge)
  body := by
    intro pc kind entry next observed
    obtain ⟨origin, body, continuation, row, address⟩ :=
      decode_look declaredCapacity (Graph.checkedCompile pattern) assertions _ (List.getElem_mem pc.isLt) kind entry next observed
    have member : Instruction.look origin body kind continuation ∈ (compile pattern).rows := by
      rw [← row]
      exact List.getElem_mem pc.isLt
    have strict := Graph.compiled_body_rank pattern origin body continuation kind member
    have location : (Graph.atIndex (Graph.checkedCompile pattern).program pc).val = origin :=
      congrArg Instruction.address row
    exact Eq.mpr (congrArg₂ (fun first second => Graph.rank (compile pattern) first <
      Graph.rank (compile pattern) second) address location) strict

theorem authorized_at_owned (pattern : Pattern) (address : Graph.Owned (compile pattern)) :
    ∃ row, Authorizes pattern row ∧ row.address = address.val := by
  obtain ⟨row, _, member, same⟩ := Graph.lookup_defined (compile pattern) address.val address.property
  exact ⟨row, (authorizes_iff_compiled pattern row).mpr member, same⟩

/-- Structural authorization determines one source operation. The ownership
witness establishes existence; it does not define the operation's meaning. -/
noncomputable def sourceOperation (pattern : Pattern) (address : Graph.Owned (compile pattern)) : Instruction :=
  (authorized_at_owned pattern address).choose

theorem sourceOperation_authorized (pattern : Pattern) (address : Graph.Owned (compile pattern)) :
    Authorizes pattern (sourceOperation pattern address) ∧ (sourceOperation pattern address).address = address.val :=
  (authorized_at_owned pattern address).choose_spec

theorem sourceOperation_eq_row (pattern : Pattern) (index : Fin (compile pattern).rows.length) :
    sourceOperation pattern (Graph.atIndex (compile pattern) index) = (compile pattern).rows[index.val] := by
  have authorized := sourceOperation_authorized pattern (Graph.atIndex (compile pattern) index)
  exact source_operation_unique pattern _ _ authorized.1 (relocated_source_authorized pattern index) authorized.2

noncomputable def sourceCode (declaredCapacity : Nat) (pattern : Pattern) (assertions : String → Nat → Bool)
    (index : Fin (compile pattern).rows.length) :
    RegexDependentObservation.Instruction (compile pattern).rows.length (groups (compile pattern) declaredCapacity) :=
  decode declaredCapacity (Graph.checkedCompile pattern) assertions
    (sourceOperation pattern (Graph.atIndex (compile pattern) index))
    ((authorizes_iff_compiled pattern _).mp (sourceOperation_authorized pattern _).1)

theorem sourceCode_eq_code (declaredCapacity : Nat) (pattern : Pattern) (assertions : String → Nat → Bool) :
    sourceCode declaredCapacity pattern assertions = code declaredCapacity (Graph.checkedCompile pattern) assertions := by
  funext index
  simp only [sourceCode, sourceOperation_eq_row]
  rfl

theorem declared_capacity_retained (program : Program) (declaredCapacity : Nat) :
    declaredCapacity ≤ groups program declaredCapacity := Nat.le_max_left _ _

theorem source_payload_slot_bound (declaredCapacity : Nat) (pattern : Pattern) (row : Instruction)
    (source : Authorizes pattern row) : operandGroup row < groups (compile pattern) declaredCapacity :=
  operandGroup_lt declaredCapacity _ row ((authorizes_iff_compiled pattern row).mp source)

/-- Existing one-operation semantics is reused; no compiler lookup occurs
when interpreting an independently authorized source operation. -/
def perform (declaredCapacity : Nat) (checked : Graph.CheckedProgram)
    (assertions : String → Nat → Bool) {length : Nat}
    (interpretation : RegexDependentObservation.Interpretation) (input : Fin length → Nat)
    (direction : RegexDependentObservation.Direction) (row : Instruction) (member : row ∈ checked.program.rows)
    (body : LookKind → Fin checked.program.rows.length →
      RegexDependentObservation.Configuration checked.program.rows.length (groups checked.program declaredCapacity) length →
      Option (RegexDependentObservation.Winner checked.program.rows.length (groups checked.program declaredCapacity) length))
    (first : RegexDependentObservation.Configuration checked.program.rows.length (groups checked.program declaredCapacity) length) :=
  RegexObservationTrace.observedAction interpretation input direction
    (fun _ => decode declaredCapacity checked assertions row member) body first

def SourceActs (declaredCapacity : Nat) (pattern : Pattern) (assertions : String → Nat → Bool) {length : Nat}
    (interpretation : RegexDependentObservation.Interpretation) (input : Fin length → Nat)
    (direction : RegexDependentObservation.Direction)
    (body : LookKind → Fin (compile pattern).rows.length →
      RegexDependentObservation.Configuration (compile pattern).rows.length (groups (compile pattern) declaredCapacity) length →
      Option (RegexDependentObservation.Winner (compile pattern).rows.length (groups (compile pattern) declaredCapacity) length))
    (first : RegexDependentObservation.Configuration (compile pattern).rows.length (groups (compile pattern) declaredCapacity) length)
    (result : RegexObservationTrace.ObservedAction
      (RegexDependentObservation.Configuration (compile pattern).rows.length (groups (compile pattern) declaredCapacity) length)) : Prop :=
  ∃ row, ∃ source : Authorizes pattern row,
    row.address = (Graph.atIndex (compile pattern) first.pc).val ∧
    perform declaredCapacity (Graph.checkedCompile pattern) assertions interpretation input direction row
      ((authorizes_iff_compiled pattern row).mp source) body first = result

theorem observedAction_congr_at {states count length : Nat}
    (interpretation : RegexDependentObservation.Interpretation) (input : Fin length → Nat)
    (direction : RegexDependentObservation.Direction)
    (firstCode secondCode : Fin states → RegexDependentObservation.Instruction states count)
    (body : LookKind → Fin states → RegexDependentObservation.Configuration states count length →
      Option (RegexDependentObservation.Winner states count length))
    (first : RegexDependentObservation.Configuration states count length)
    (same : firstCode first.pc = secondCode first.pc) :
    RegexObservationTrace.observedAction interpretation input direction firstCode body first =
      RegexObservationTrace.observedAction interpretation input direction secondCode body first := by
  simp only [RegexObservationTrace.observedAction, RegexDependentObservation.action, same]

/-- Preservation and reflection of actual source operations, including
capture-dependent edges and completed nested observation words. The body
observer is explicit here; its recursive closure is a subsequent theorem. -/
theorem sourceActs_iff_compiled (declaredCapacity : Nat) (pattern : Pattern) (assertions : String → Nat → Bool) {length : Nat}
    (interpretation : RegexDependentObservation.Interpretation) (input : Fin length → Nat)
    (direction : RegexDependentObservation.Direction)
    (body : LookKind → Fin (compile pattern).rows.length →
      RegexDependentObservation.Configuration (compile pattern).rows.length (groups (compile pattern) declaredCapacity) length →
      Option (RegexDependentObservation.Winner (compile pattern).rows.length (groups (compile pattern) declaredCapacity) length))
    (first : RegexDependentObservation.Configuration (compile pattern).rows.length (groups (compile pattern) declaredCapacity) length)
    (result : RegexObservationTrace.ObservedAction
      (RegexDependentObservation.Configuration (compile pattern).rows.length (groups (compile pattern) declaredCapacity) length)) :
    SourceActs declaredCapacity pattern assertions interpretation input direction body first result ↔
      RegexObservationTrace.observedAction interpretation input direction
        (code declaredCapacity (Graph.checkedCompile pattern) assertions) body first = result := by
  constructor
  · rintro ⟨row, source, address, performed⟩
    have same := source_operation_unique pattern row (compile pattern).rows[first.pc.val]
      source (relocated_source_authorized pattern first.pc) address
    subst row
    exact (observedAction_congr_at interpretation input direction
      (fun _ => decode declaredCapacity (Graph.checkedCompile pattern) assertions _
        ((authorizes_iff_compiled pattern _).mp source))
      (code declaredCapacity (Graph.checkedCompile pattern) assertions) body first rfl).symm.trans performed
  · intro acted
    refine ⟨(compile pattern).rows[first.pc.val], relocated_source_authorized pattern first.pc, rfl, ?_⟩
    exact (observedAction_congr_at interpretation input direction
      (fun _ => decode declaredCapacity (Graph.checkedCompile pattern) assertions _
        ((authorizes_iff_compiled pattern _).mp (relocated_source_authorized pattern first.pc)))
      (code declaredCapacity (Graph.checkedCompile pattern) assertions) body first rfl).trans acted

noncomputable def sourceCertificate (declaredCapacity : Nat) (pattern : Pattern) (assertions : String → Nat → Bool) :
    RegexObservationKernel.Certificate (sourceCode declaredCapacity pattern assertions) := by
  rw [sourceCode_eq_code]
  exact certificate declaredCapacity pattern assertions

/-- Full nested observation transport is earned from local independent source
authorization. It retains captures and local priority words for every input,
direction and caller-supplied acceptance predicate. -/
theorem source_kernel_eq_compiled (declaredCapacity : Nat) (pattern : Pattern) (assertions : String → Nat → Bool)
    {length : Nat} (interpretation : RegexDependentObservation.Interpretation) (input : Fin length → Nat)
    (root : Fin (compile pattern).rows.length) :
    RegexObservationKernel.evaluate interpretation input (sourceCode declaredCapacity pattern assertions)
      (sourceCertificate declaredCapacity pattern assertions) root =
    RegexObservationKernel.evaluate interpretation input (code declaredCapacity (Graph.checkedCompile pattern) assertions)
      (certificate declaredCapacity pattern assertions) root :=
  RegexObservationTransport.evaluate_code_congr interpretation input _ _ _ _
    (fun pc => congrFun (sourceCode_eq_code declaredCapacity pattern assertions) pc) root

/-- The declared layout supplies the minimum carrier, including declarations
whose instructions were erased by a zero count. Actual authored output and
the full nested source-occurrence observation share the earned license. -/
theorem projected_authored_kernel (catalog : RegexClassMaterialization.Catalog) (payloadDepth : Nat)
    (policy : RegexDependentProjection.LookbehindPolicy) (state : RegexSourceProjection.State)
    (tree : CettaWire.Term) (answer : RegexDependentProjection.Output) (target : Pattern) (fuel : Nat)
    (selected : RegexDependentProjection.project (RegexDependentProjection.view? catalog payloadDepth policy)
      fuel state tree = some answer)
    (prepared : RegexDependentProjection.prepare answer = some target) :
    ∃ authored, RegexDependentAuthored.encode answer.state answer.pattern = some authored ∧
      answer.state.nextGroup ≤ groups (compile target) answer.state.nextGroup ∧
      (∀ result, DeterministicEquations.Applies RegexExtendedEquationExecution.program
        RegexExtendedEquationExecution.host "re:compile-authored" [authored] result ↔
        result = RegexExtendedAccumulatorExecution.code (compile target)) ∧
      ∀ length (interpretation : RegexDependentObservation.Interpretation) (input : Fin length → Nat)
        (assertions : String → Nat → Bool) (root : Fin (compile target).rows.length),
        RegexObservationKernel.evaluate interpretation input (sourceCode answer.state.nextGroup target assertions)
          (sourceCertificate answer.state.nextGroup target assertions) root =
        RegexObservationKernel.evaluate interpretation input
          (code answer.state.nextGroup (Graph.checkedCompile target) assertions)
          (certificate answer.state.nextGroup target assertions) root := by
  obtain ⟨authored, _, encoded, exactness⟩ := RegexDependentAuthored.projected_authored_exact
    catalog payloadDepth policy state tree answer target fuel selected prepared
  exact ⟨authored, encoded, declared_capacity_retained _ _, exactness,
    fun _ interpretation input assertions root => source_kernel_eq_compiled _ _ assertions interpretation input root⟩

namespace Controls

theorem zero_repeat_declared_slot_is_not_erased_from_carrier :
    groups (compile .epsilon) 2 = 2 ∧
    (groups (compile .epsilon) 2 = 1 → False) := by decide

theorem large_reference_id_earns_its_own_bound :
    groups (compile (.backref 8 .exact)) 2 = 9 := by decide

theorem pure_terminal_decodes_to_accept :
    code 2 (Graph.checkedCompile .epsilon) (fun _ _ => false) ⟨0, by decide⟩ = .accept := rfl

end Controls

end Mettapedia.GSLT.LanguageDef.RegexExtendedKernel
