import Mettapedia.Languages.Megalodon.SourceAdmission
import Mettapedia.Languages.Megalodon.SourceBinderRefinement
import Mettapedia.Languages.Megalodon.NativeSession
import Mettapedia.Languages.Megalodon.SourceRuleProof

/-!
# Source-safe data on the shared borrowed cursor

The source binding invariant is enforced at decoding, including the explicit
substitution operands carried by a local row. Cached judgments retain that
invariant through every pause and retry. The worker and its outcome semantics
are the same shared implementation; the guard neither searches for proofs
nor creates a second inference engine.

Native implementations may retain validated scope metadata on immutable terms
and contexts. They must not trust a flag decoded from ordinary program data.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.SourceCursor
open MathdataKernel ProofJudgment BorrowedProofCursor SourceScopeInvariant
open Mettapedia.Logic.DerivationGraph.BorrowedCursor

def JudgmentSafe (judgment : Judgment) : Prop :=
  ContextSafe judgment.context ∧ Scoped judgment.context.terms.length judgment.proposition ∧
    Protected judgment.proposition

instance judgmentSafeDecidable (judgment : Judgment) : Decidable (JudgmentSafe judgment) := by
  unfold JudgmentSafe ContextSafe
  infer_instance

def NodeSafe (node : SourceNode) : Prop := JudgmentSafe node.conclusion ∧ WitnessSafe node.request

instance nodeSafeDecidable (node : SourceNode) : Decidable (NodeSafe node) := by
  unfold NodeSafe
  infer_instance

def decode (wire : NativeSyntaxWire.Wire) : Option SourceNode := do
  let node ← NativeCursorWire.decodeNode wire
  if NodeSafe node then some node else none

theorem decode_iff (wire : NativeSyntaxWire.Wire) (node : SourceNode) :
    decode wire = some node ↔ NativeCursorWire.decodeNode wire = some node ∧ NodeSafe node := by
  cases parsed : NativeCursorWire.decodeNode wire with
  | none => simp [decode, parsed]
  | some value =>
      by_cases safe : NodeSafe value <;> simp [decode, parsed, safe]
      all_goals intro same; cases same; exact safe

def source (revision : Nat) (read : NodeId → Option NativeSyntaxWire.Wire) : Source :=
  ⟨revision, fun address => (read address).bind decode⟩

theorem source_safe {revision address : Nat} {read : NodeId → Option NativeSyntaxWire.Wire}
    {node : SourceNode} (found : (source revision read).read address = some node) : NodeSafe node := by
  obtain ⟨wire, _, decoded⟩ := Option.bind_eq_some_iff.mp found
  exact ((decode_iff wire node).mp decoded).2

def CachedSafe (state : State Judgment) : Prop := ∀ judgment ∈ state.cache, JudgmentSafe judgment

theorem start_safe (store : Source) : CachedSafe (start store) := by simp [CachedSafe, start]

theorem step_safe {environment : Environment} {fuel revision address : Nat}
    {read : NodeId → Option NativeSyntaxWire.Wire} {before after : State Judgment}
    (prior : CachedSafe before)
    (accepted : step (interface environment fuel) (source revision read) before address = some after) :
    CachedSafe after := by
  obtain ⟨node, _, found, _, _, _, _, shape⟩ :=
    step_correspondence (interface environment fuel) (source revision read) before after address accepted
  intro judgment member
  rw [shape, Array.mem_push] at member
  rcases member with old | rfl
  · exact prior judgment old
  · exact (source_safe found).1

theorem run_safe {environment : Environment} {fuel revision : Nat}
    {read : NodeId → Option NativeSyntaxWire.Wire} {before after : State Judgment} {schedule : List NodeId}
    (prior : CachedSafe before)
    (accepted : run (interface environment fuel) (source revision read) before schedule = some after) :
    CachedSafe after := by
  induction schedule generalizing before with
  | nil => cases Option.some.inj accepted; exact prior
  | cons address rest ih =>
      obtain ⟨next, first, later⟩ := Option.bind_eq_some_iff.mp accepted
      exact ih (step_safe prior first) later

theorem walk_safe (environment : Environment) (fuel revision rows : Nat)
    (read : NodeId → Option NativeSyntaxWire.Wire) (before : State Judgment) (schedule : List NodeId)
    (prior : CachedSafe before) :
    CachedSafe (ObservedCursor.walk environment fuel (source revision read) rows before schedule).checkpoint := by
  obtain ⟨_, _, _, ran⟩ := ObservedCursor.walk_partition environment fuel (source revision read) rows before schedule
  exact run_safe prior ran

theorem root_safe {state : State Judgment} (safe : CachedSafe state) {address : Nat} {judgment : Judgment}
    (found : rootAt state address = some judgment) : JudgmentSafe judgment := by
  cases indexed : indexAt state.checked address with
  | none => simp [rootAt, indexed] at found
  | some index =>
      have value : state.cache[index]? = some judgment := by simpa [rootAt, indexed] using found
      exact safe judgment (Array.mem_of_getElem? value)

def CachedSupported (environment : Environment) (state : State Judgment) : Prop :=
  ∀ judgment ∈ state.cache, Supported environment judgment

theorem start_supported (environment : Environment) (store : Source) :
    CachedSupported environment (start store) := by simp [CachedSupported, start]

theorem step_supported {environment : Environment} {fuel revision address : Nat}
    {read : NodeId → Option NativeSyntaxWire.Wire} {before after : State Judgment}
    (prior : CachedSupported environment before)
    (accepted : step (interface environment fuel) (source revision read) before address = some after) :
    CachedSupported environment after := by
  obtain ⟨node, parents, found, _, replayed, _, _, shape⟩ :=
    step_correspondence (interface environment fuel) (source revision read) before after address accepted
  obtain ⟨premises, lookup, checked, _⟩ :=
    (Mettapedia.Logic.DerivationGraph.Node.replay_eq_some_iff (interface environment fuel) before.cache after.cache
      ⟨node.conclusion, node.request, parents, node.origin⟩).mp replayed
  intro judgment member
  rw [shape, Array.mem_push] at member
  rcases member with old | rfl
  · exact prior judgment old
  · exact requirements_supported (source_safe found).2 (of_decide_eq_true checked)
      (fun premise member => prior premise
        (Mettapedia.Logic.DerivationGraph.lookupPremises_mem before.cache lookup premise member))

theorem run_supported {environment : Environment} {fuel revision : Nat}
    {read : NodeId → Option NativeSyntaxWire.Wire} {before after : State Judgment} {schedule : List NodeId}
    (prior : CachedSupported environment before)
    (accepted : run (interface environment fuel) (source revision read) before schedule = some after) :
    CachedSupported environment after := by
  induction schedule generalizing before with
  | nil => cases Option.some.inj accepted; exact prior
  | cons address rest ih =>
      obtain ⟨next, first, later⟩ := Option.bind_eq_some_iff.mp accepted
      exact ih (step_supported prior first) later

theorem walk_supported (environment : Environment) (fuel revision rows : Nat)
    (read : NodeId → Option NativeSyntaxWire.Wire) (before : State Judgment) (schedule : List NodeId)
    (prior : CachedSupported environment before) :
    CachedSupported environment (ObservedCursor.walk environment fuel (source revision read) rows before schedule).checkpoint := by
  obtain ⟨_, _, _, ran⟩ := ObservedCursor.walk_partition environment fuel (source revision read) rows before schedule
  exact run_supported prior ran

theorem root_supported {environment : Environment} {state : State Judgment}
    (supported : CachedSupported environment state) {address : Nat} {judgment : Judgment}
    (found : rootAt state address = some judgment) : Supported environment judgment := by
  cases indexed : indexAt state.checked address with
  | none => simp [rootAt, indexed] at found
  | some index =>
      have value : state.cache[index]? = some judgment := by simpa [rootAt, indexed] using found
      exact supported judgment (Array.mem_of_getElem? value)

/-- No free term variable can be captured by a hidden type region in a
retained root, including after a resource stop and a later retry. -/
theorem retained_root_uses_all_sorts {state : State Judgment} (safe : CachedSafe state)
    {address : Nat} {judgment : Judgment} (found : rootAt state address = some judgment)
    (replacement : Tm) :
    Mettapedia.GSLT.LanguageDef.SortedSignatureIndexedABT.Term.substituteTop
      SortedABTRefinement.VarSort.term (SortedABTRefinement.encode replacement)
      (SortedABTRefinement.encode judgment.proposition) =
        SortedABTRefinement.encode
          (SourceTermFragment.publicationSubstitute 0 replacement judgment.proposition) :=
  SourceBinderRefinement.protected_publication_uses_all_sorts (root_safe safe found).2.2 replacement

structure Session (environment : Environment) (revision : Nat)
    (read : NodeId → Option NativeSyntaxWire.Wire) where
  private mk ::
  native : NativeSession.Session environment (source revision read)
  environmentSafe : SourceAdmission.EnvironmentSafe environment
  cachedSafe : CachedSafe native.state
  cachedSupported : CachedSupported environment native.state

def begin (environment : Environment) (safe : SourceAdmission.EnvironmentSafe environment)
    (revision : Nat) (read : NodeId → Option NativeSyntaxWire.Wire) : Session environment revision read :=
  ⟨NativeSession.begin environment (source revision read), safe, start_safe _, start_supported _ _⟩

structure Resumed (environment : Environment) (revision : Nat)
    (read : NodeId → Option NativeSyntaxWire.Wire) where
  private mk ::
  native : NativeSession.Resumed environment (source revision read)
  environmentSafe : SourceAdmission.EnvironmentSafe environment
  cachedSafe : CachedSafe native.session.state
  cachedSupported : CachedSupported environment native.session.state

def Resumed.session {environment : Environment} {revision : Nat}
    {read : NodeId → Option NativeSyntaxWire.Wire} (result : Resumed environment revision read) :
    Session environment revision read :=
  ⟨result.native.session, result.environmentSafe, result.cachedSafe, result.cachedSupported⟩

def resume {environment : Environment} {revision : Nat} {read : NodeId → Option NativeSyntaxWire.Wire}
    (session : Session environment revision read) (normalizationBound rowBound : Nat) (schedule : List NodeId) :
    Resumed environment revision read :=
  ⟨NativeSession.resume session.native normalizationBound rowBound schedule, session.environmentSafe,
    walk_safe environment normalizationBound revision rowBound read session.native.state schedule session.cachedSafe,
    walk_supported environment normalizationBound revision rowBound read session.native.state schedule session.cachedSupported⟩

def finish {environment : Environment} {revision : Nat} {read : NodeId → Option NativeSyntaxWire.Wire}
    (result : Resumed environment revision read) (root goalBound : Nat) (proposition : Tm) :
    NativeSession.Publication environment :=
  if Protected proposition then NativeSession.finish result.native root goalBound proposition else .refused

theorem finish_accepts_iff {environment : Environment} {revision : Nat}
    {read : NodeId → Option NativeSyntaxWire.Wire} (result : Resumed environment revision read)
    (root goalBound : Nat) (proposition : Tm) :
    (finish result root goalBound proposition).isAccepted = true ↔
      Protected proposition ∧ result.native.status = .finished ∧ result.native.pending = [] ∧
        ∃ judgment, rootAt result.native.session.state root = some judgment ∧ judgment.context = ⟨0, [], []⟩ ∧
          checkProposition environment 0 [] proposition = true ∧
          normalize environment goalBound proposition = some judgment.proposition := by
  by_cases safe : Protected proposition
  · simp [finish, safe, NativeSession.finish_accepts_iff]
  · simp [finish, safe, NativeSession.Publication.isAccepted]

theorem finish_correct {environment : Environment} {revision : Nat}
    {read : NodeId → Option NativeSyntaxWire.Wire} {result : Resumed environment revision read}
    {root goalBound : Nat} {proposition : Tm} {theorem_ : NativeSession.Theorem environment}
    (accepted : finish result root goalBound proposition = .accepted theorem_) :
    SourceAdmission.EnvironmentSafe environment ∧ Protected proposition ∧
      result.native.status = .finished ∧ result.native.pending = [] ∧
      theorem_.proposition = proposition ∧ NativeSession.ValidTheorem environment proposition := by
  unfold finish at accepted
  split at accepted
  · rename_i safe
    exact ⟨result.environmentSafe, safe, NativeSession.finish_checks_whole_suffix accepted⟩
  · cases accepted

/-- Source checking keeps exactly the shared worker's unfinished suffix and
supports changing the next invocation's bounds without losing cached scope. -/
theorem resume_partition {environment : Environment} {revision : Nat}
    {read : NodeId → Option NativeSyntaxWire.Wire} (session : Session environment revision read)
    (normalizationBound rowBound : Nat) (schedule : List NodeId) :
    let result := resume session normalizationBound rowBound schedule
    ∃ checked, schedule = checked ++ result.native.pending ∧ checked.length ≤ rowBound ∧
      run (interface environment normalizationBound) (source revision read) session.native.state checked =
        some result.native.session.state :=
  NativeSession.resume_partition session.native normalizationBound rowBound schedule

namespace Controls
private def closed : Context := ⟨0, [], []⟩
private def proposition : Tm := .all .prop (.db 0)
private def ordinary : SourceNode :=
  ⟨⟨⟨0, [], [proposition]⟩, proposition⟩, .hyp 0, [], 0⟩

theorem ordinary_hypothesis_decodes : decode (NativeCursorWire.encodeNode ordinary) = some ordinary :=
  (decode_iff _ _).mpr ⟨NativeCursorWire.node_roundtrip ordinary, by decide⟩

theorem hidden_mixed_binder_operand_refused :
    decode (NativeCursorWire.encodeNode
      ⟨⟨closed, proposition⟩, .termApp (.lam .prop (.typeLam (.db 0))) .prop proposition, [], 0⟩) = none := by decide

theorem open_hypothesis_cannot_be_claimed_closed :
    decode (NativeCursorWire.encodeNode ⟨⟨closed, .db 0⟩, .hyp 0, [], 0⟩) = none := by decide
end Controls

end Mettapedia.Languages.Megalodon.SourceCursor
