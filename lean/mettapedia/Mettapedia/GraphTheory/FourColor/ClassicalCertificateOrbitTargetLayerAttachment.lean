import Mettapedia.GraphTheory.FourColor.ClassicalCertificateIndexedLayeredKempe
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitProofDagReduction

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateOrbitTargetLayerAttachment

open ClassicalCertificateIndexedLayeredKempe
open ClassicalCertificateKempeClosure
open ClassicalCertificateOrbitProofDagReduction
open ClassicalCertificateRankedKempe
open ClassicalCertificateTraceTree

/-- Check one predicate at every occupied leaf of a target trie. -/
def allTargets (predicate : Nat → Bool) :
    ClassicalCertificateProofDagReduction.TargetTreeCode → Bool
  | .empty => true
  | .leaf target => predicate target
  | .node red blue purple =>
      allTargets predicate red &&
        (allTargets predicate blue && allTargets predicate purple)

/-- A successful all-leaf check applies to every target found by lookup. -/
theorem allTargets_of_lookup_eq_some
    (predicate : Nat → Bool)
    (tree : ClassicalCertificateProofDagReduction.TargetTreeCode)
    (hcheck : allTargets predicate tree = true)
    (word : List TraceSymbol) (target : Nat)
    (hlookup : tree.lookup word = some target) :
    predicate target = true := by
  induction tree generalizing word with
  | empty =>
      simp [ClassicalCertificateProofDagReduction.TargetTreeCode.lookup]
        at hlookup
  | leaf storedTarget =>
      cases word with
      | nil =>
          simp [ClassicalCertificateProofDagReduction.TargetTreeCode.lookup]
            at hlookup
          subst target
          simpa [allTargets] using hcheck
      | cons symbol word =>
          simp [ClassicalCertificateProofDagReduction.TargetTreeCode.lookup]
            at hlookup
  | node red blue purple ihRed ihBlue ihPurple =>
      simp only [allTargets, Bool.and_eq_true] at hcheck
      cases word with
      | nil =>
          simp [ClassicalCertificateProofDagReduction.TargetTreeCode.lookup]
            at hlookup
      | cons symbol word =>
          cases symbol with
          | red =>
              exact ihRed hcheck.1 word (by
                simpa [ClassicalCertificateProofDagReduction.TargetTreeCode.lookup]
                  using hlookup)
          | blue =>
              exact ihBlue hcheck.2.1 word (by
                simpa [ClassicalCertificateProofDagReduction.TargetTreeCode.lookup]
                  using hlookup)
          | purple =>
              exact ihPurple hcheck.2.2 word (by
                simpa [ClassicalCertificateProofDagReduction.TargetTreeCode.lookup]
                  using hlookup)

/-- Attach one old proof target to a certified layer containing the same
canonical word. -/
def targetAttachmentBoolean {length : Nat}
    (oldCode : ClassicalCertificateOrbitProofDagReduction.Code)
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (layerOf : Nat → Nat) (target : Nat) : Bool :=
  decide (target < oldCode.nodeCount) &&
    match oldCode.nodeAt? target with
    | none => false
    | some node =>
        decide (layerOf target < certificate.deltaRoots.length) &&
          certificate.acceptsAt (layerOf target)
            (ClassicalCertificateOrbitProofDagReduction.Code.nodeWord
              length node)

theorem targetAttachmentBoolean_sound {length : Nat}
    (oldCode : ClassicalCertificateOrbitProofDagReduction.Code)
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (layerOf : Nat → Nat) (target : Nat)
    (hcheck : targetAttachmentBoolean oldCode certificate layerOf target =
      true) :
    ∃ node,
      oldCode.nodeAt? target = some node ∧
        target < oldCode.nodeCount ∧
          layerOf target < certificate.deltaRoots.length ∧
            certificate.acceptsAt (layerOf target)
              (ClassicalCertificateOrbitProofDagReduction.Code.nodeWord
                length node) = true := by
  unfold targetAttachmentBoolean at hcheck
  simp only [Bool.and_eq_true] at hcheck
  have htarget : target < oldCode.nodeCount :=
    of_decide_eq_true hcheck.1
  cases hnode : oldCode.nodeAt? target with
  | none => simp [hnode] at hcheck
  | some node =>
      have hparts :
          decide (layerOf target < certificate.deltaRoots.length) = true ∧
            certificate.acceptsAt (layerOf target)
              (ClassicalCertificateOrbitProofDagReduction.Code.nodeWord
                length node) = true := by
        simpa [hnode] using hcheck.2
      exact ⟨node, rfl, htarget, of_decide_eq_true hparts.1, hparts.2⟩

/-- A checked attachment of every canonical old target to a sound new layer
replaces the old recursive proof DAG. -/
theorem targetBoolean_reduces {length : Nat}
    (oldCode : ClassicalCertificateOrbitProofDagReduction.Code)
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (layerOf : Nat → Nat)
    (family : List TraceSymbol → Prop)
    (hattachments :
      allTargets (targetAttachmentBoolean oldCode certificate layerOf)
        oldCode.contractTargets = true)
    (hlayers : ∀ layer,
      layer < certificate.deltaRoots.length →
        ∀ fixedWord : TraceWord length,
          certificate.acceptsAt layer fixedWord = true →
            KempeCoclosure family fixedWord.toList)
    (word : List TraceSymbol)
    (htarget : ClassicalCertificateOrbitProofDagReduction.targetBoolean
      length oldCode word = true) :
    KempeCoclosure family word := by
  obtain ⟨target, hlookup, htargetValid⟩ :=
    orbitTargetValid_of_targetBoolean_true length oldCode word htarget
  have hattachment := allTargets_of_lookup_eq_some
    (targetAttachmentBoolean oldCode certificate layerOf)
      oldCode.contractTargets hattachments (canonicalWord word) target hlookup
  obtain ⟨node, hnode, _htarget, hlayer, haccepted⟩ :=
    targetAttachmentBoolean_sound oldCode certificate layerOf target
      hattachment
  obtain ⟨_htargetBound, htargetLocal⟩ := htargetValid
  obtain ⟨permutation, hword⟩ :
      ∃ permutation : PermutationCode,
        (permute permutation
          (ClassicalCertificateOrbitProofDagReduction.Code.nodeWord
            length node)).toList = word := by
    simpa [hnode] using htargetLocal
  have hcoclosure := hlayers (layerOf target) hlayer
    (ClassicalCertificateOrbitProofDagReduction.Code.nodeWord length node)
      haccepted
  intro closedFamily hclosed hclosedWord
  have hinverse := (hclosed word hclosedWord).1 permutation.inverse.toEquiv
  apply hcoclosure closedFamily hclosed
  rw [← hword] at hinverse
  simpa [← toList_permute, inverse_permute] using hinverse

end ClassicalCertificateOrbitTargetLayerAttachment

end Mettapedia.GraphTheory.FourColor
