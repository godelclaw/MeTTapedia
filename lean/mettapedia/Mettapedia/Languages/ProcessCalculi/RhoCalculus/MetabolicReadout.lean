import Mettapedia.Languages.ProcessCalculi.RhoCalculus.MetabolicProtocol

/-!
# Complete metabolic readout through the actual rho equations

Cell readout identifies its tail and spent head by their distinct channels,
not by the order chosen for a canonical parallel bag. Empty-stack reclaim
leaves only outputs, so no COMM can complete another structural debit.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Metabolic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Framework.ConstructorCategory
open Canonical CanonicalTyping CanonicalBag CanonicalReaction
open LanguageDefGSLT LanguageDefRewriteSystem DerivedContextualStep CanonicalStepperCompleteness
open ResourcePredation ResourceClaimHistory

universe u
variable {Head : Type u}

def outputAt (channel : Pattern) : Pattern → Option Pattern
  | .apply "POutput" [actual, contents] => if actual = channel then some contents else none
  | _ => none

def sentAt (channel process : Pattern) : List Pattern :=
  (bagContents [canonicalize process]).filterMap (outputAt channel)

private theorem canonical_body_contents (tail head : Pattern)
    (headCanonical : canonicalize head = head) :
    bagContents [canonicalize (.collection .hashBag
      [output metabolic tail, output spent head] none)] =
      sortPatterns [output metabolic (canonicalize tail), output spent head] := by
  rw [canonicalize_bag, bagContents_collapse_normalized
    (canonical_list_map [output metabolic tail, output spent head])]
  simp [canonicalizeList, canonicalize, normalizeQuote, output, metabolic, spent, pop, zero,
    headCanonical, normalizeBagElements, bagSplice]

theorem sentAt_tail (tail head : Pattern) (headCanonical : canonicalize head = head) :
    sentAt metabolic (.collection .hashBag [output metabolic tail, output spent head] none) =
      [canonicalize tail] := by
  unfold sentAt
  rw [canonical_body_contents tail head headCanonical]
  have perm := (sortPatterns_perm
    [output metabolic (canonicalize tail), output spent head]).filterMap (outputAt metabolic)
  have base : [output metabolic (canonicalize tail), output spent head].filterMap (outputAt metabolic) =
      [canonicalize tail] := by
    simp [outputAt, output, metabolic, spent, pop, zero]
  rw [base] at perm
  exact List.perm_singleton.mp perm.symm

theorem sentAt_head (tail head : Pattern) (headCanonical : canonicalize head = head) :
    sentAt spent (.collection .hashBag [output metabolic tail, output spent head] none) = [head] := by
  unfold sentAt
  rw [canonical_body_contents tail head headCanonical]
  have perm := (sortPatterns_perm
    [output metabolic (canonicalize tail), output spent head]).filterMap (outputAt spent)
  have base : [output metabolic (canonicalize tail), output spent head].filterMap (outputAt spent) = [head] := by
    simp [outputAt, output, metabolic, spent, pop, zero]
  rw [base] at perm
  exact List.perm_singleton.mp perm.symm

theorem sentAt_canonical (channel process : Pattern) :
    sentAt channel (canonicalize process) = sentAt channel process := by
  simp only [sentAt, canonicalize_idempotent]

/-- The tail and head are recovered from the actual canonical cell body.
The two channel readouts force their unique values independently of sorting. -/
inductive CanonicalPayloadReadout : Pattern → List Pattern → Prop
  | empty : CanonicalPayloadReadout zero []
  | cell (body head tail : Pattern) (heads : List Pattern)
      (tailReadout : sentAt metabolic body = [tail])
      (headReadout : sentAt spent body = [head])
      (rest : CanonicalPayloadReadout tail heads) :
      CanonicalPayloadReadout (input pop body) (head :: heads)

theorem canonical_payload_readout (encoding : Encoding Head) (stack : Stack Head) :
    CanonicalPayloadReadout (canonicalize (payload encoding stack)) (stack.heads.map encoding.code) := by
  induction stack with
  | empty => exact .empty
  | cell head tail ih =>
      have shape : canonicalize (payload encoding (.cell head tail)) =
          input pop (canonicalize (.collection .hashBag
            [output metabolic (payload encoding tail), output spent (encoding.code head)] none)) := by
        simp [payload, input, canonicalize, canonicalizeList, normalizeQuote, pop, metabolic, output, zero]
      rw [shape]
      exact .cell _ _ _ _
        ((sentAt_canonical _ _).trans (sentAt_tail _ _ (encoding.canonical head)))
        ((sentAt_canonical _ _).trans (sentAt_head _ _ (encoding.canonical head))) ih

theorem canonical_payload_readout_unique {pattern : Pattern} {first second : List Pattern}
    (left : CanonicalPayloadReadout pattern first)
    (right : CanonicalPayloadReadout pattern second) : first = second := by
  induction left generalizing second with
  | empty =>
      generalize shape : zero = pattern at right
      cases right with
      | empty => rfl
      | cell body head tail heads tailReadout headReadout rest => simp [zero, input] at shape
  | cell body head tail heads tailReadout headReadout rest ih =>
      generalize shape : input pop body = pattern at right
      cases right with
      | empty => simp [zero, input] at shape
      | cell otherBody otherHead otherTail otherHeads otherTailReadout otherHeadReadout otherRest =>
          have sameBody : body = otherBody := by simpa [input] using shape
          subst otherBody
          have sameTail : tail = otherTail := by simpa using tailReadout.symm.trans otherTailReadout
          have sameHead : head = otherHead := by simpa using headReadout.symm.trans otherHeadReadout
          subst otherTail
          subst otherHead
          exact congrArg (List.cons head) (ih otherRest)

theorem canonical_payload_complete_readout (encoding : Encoding Head) (stack : Stack Head)
    (heads : List Pattern) :
    CanonicalPayloadReadout (canonicalize (payload encoding stack)) heads ↔
      heads = stack.heads.map encoding.code :=
  ⟨fun actual => canonical_payload_readout_unique actual (canonical_payload_readout encoding stack),
    fun same => same ▸ canonical_payload_readout encoding stack⟩

theorem canonical_stack_readout_injective (encoding : Encoding Head)
    (codeInjective : Function.Injective encoding.code) {first second : Stack Head}
    (same : canonicalize (payload encoding first) = canonicalize (payload encoding second)) :
    first = second := by
  have sameHeads := canonical_payload_readout_unique (canonical_payload_readout encoding first)
    (same.symm ▸ canonical_payload_readout encoding second)
  have actualHeads := List.map_injective_iff.mpr codeInjective sameHeads
  have headsInjective : Function.Injective (Stack.heads (Head := Head)) := by
    intro left right
    induction left generalizing right with
    | empty => cases right <;> simp [Stack.heads]
    | cell head tail ih =>
        cases right with
        | empty => simp [Stack.heads]
        | cell otherHead otherTail =>
            intro same
            have parts : head = otherHead ∧ tail.heads = otherTail.heads := by simpa [Stack.heads] using same
            exact congrArg₂ Stack.cell parts.1 (ih parts.2)
  exact headsInjective actualHeads

private theorem outputs_of_parallel (parts : List RhoProcess)
    (outputs : ∀ process ∈ parts, process.1 = zero ∨ ∃ channel contents, process.1 = output channel contents)
    {pattern : Pattern} (member : pattern ∈ (fromProcess (parallel parts)).1) :
    ∃ channel contents, pattern = output channel contents := by
  rw [parallel, fromProcess_ofList_inventory] at member
  have listMember : pattern ∈ bagContents ((parts.map Subtype.val).map canonicalize) := by
    simpa using member
  obtain ⟨inSplice, nonzero⟩ := List.mem_filter.mp listMember
  obtain ⟨original, inOriginal, inOriginalSplice⟩ := List.mem_flatMap.mp inSplice
  obtain ⟨process, processMember, originalEq⟩ := List.mem_map.mp inOriginal
  obtain ⟨sourceProcess, sourceMember, processEq⟩ := List.mem_map.mp processMember
  subst process
  subst original
  rcases outputs sourceProcess sourceMember with nil | ⟨channel, contents, shape⟩
  · rw [nil] at inOriginalSplice
    have same : pattern = zero := by simpa [zero, canonicalize, canonicalizeList, bagSplice] using inOriginalSplice
    subst pattern
    simp [zero] at nonzero
  · rw [shape] at inOriginalSplice
    have same : pattern = output (canonicalize channel) (canonicalize contents) := by
      simpa [output, canonicalize, canonicalizeList, bagSplice] using inOriginalSplice
    exact ⟨_, _, same⟩

theorem empty_reclaimed_has_no_firing (encoding : Encoding Head) (record : List Head)
    (source : Configuration)
    (sourceInventory : inventory source = fromProcess (reclaimed encoding .empty 0 record)) :
    ∀ _ : ResourcePredation.Firing source, False := by
  intro firing
  have member : firing.receiver.term.1 ∈ (inventory source).1 := by
    change firing.receiver.term.1 ∈ (patterns source : Multiset Pattern)
    apply Multiset.mem_coe.mpr
    exact List.mem_map.mpr ⟨firing.receiver, List.getElem_mem firing.inputIndex.isLt, rfl⟩
  rw [sourceInventory] at member
  obtain ⟨channel, contents, shape⟩ := outputs_of_parallel _ (by
    intro process inParts
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at inParts
    rcases inParts with (rfl | rfl | rfl) | inRecord
    · exact Or.inl rfl
    · exact Or.inr ⟨pop, zero, rfl⟩
    · exact Or.inl rfl
    · obtain ⟨head, _, rfl⟩ := List.mem_map.mp inRecord
      exact Or.inr ⟨spent, encoding.code head, rfl⟩) member
  have impossible := firing.inputAt.symm.trans shape
  simp [input, output] at impossible

theorem empty_reclaimed_public_quiet (encoding : Encoding Head) (record : List Head)
    (source : Configuration)
    (sourceInventory : inventory source = fromProcess (reclaimed encoding .empty 0 record))
    {target : RhoProcess}
    (history : Relation.ReflTransGen rhoLanguageDefGSLT.Step (readout source) target) :
    target = readout source :=
  public_history_quiet_of_no_firing (empty_reclaimed_has_no_firing encoding record source sourceInventory) history

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Metabolic
