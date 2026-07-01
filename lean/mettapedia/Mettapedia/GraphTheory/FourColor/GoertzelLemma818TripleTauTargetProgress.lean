import Mettapedia.GraphTheory.FourColor.GoertzelLemma818SemanticBridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Certificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber8Certificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber10Certificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber20Block0Chunk0ComponentCertificate

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: partial `TTT` target progress

This module records the currently checked chain-level surface for the first
non-base semantic target, `TTT`/`mode09`.

It is intentionally partial.  The light fibers, three of the twelve large
fixed-input fibers, and the first slice of a fourth large fiber are certified
by explicit component/path tables.  The rest of the large-fiber layer remains
open unless a smaller transition invariant replaces it.
-/

namespace GoertzelLemma818TripleTauTargetProgress

open GoertzelLemma814
open GoertzelLemma818FrontierMode
open GoertzelLemma818RepresentativeTargets
open GoertzelLemma818SemanticBridge
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Data
open GoertzelLemma818TripleTauLargeFiber4Certificate
open GoertzelLemma818TripleTauLargeFiber8Data
open GoertzelLemma818TripleTauLargeFiber8Certificate
open GoertzelLemma818TripleTauLargeFiber10Data
open GoertzelLemma818TripleTauLargeFiber10Certificate
open GoertzelLemma818TripleTauLargeFiber20Data
open GoertzelLemma818TripleTauLargeFiber20Block0Chunk0ComponentCertificate

def tttCertifiedLargeFiberKeys : List (List LColor) :=
  [ tttLargeFiber4Key
  , tttLargeFiber8Key
  , tttLargeFiber10Key
  ]

def tttRemainingLargeFiberKeys : List (List LColor) :=
  [ [LColor.r, LColor.p, LColor.r, LColor.p]
  , [LColor.b, LColor.r, LColor.b, LColor.r]
  , [LColor.b, LColor.b, LColor.r, LColor.r]
  , [LColor.b, LColor.b, LColor.p, LColor.p]
  , [LColor.b, LColor.p, LColor.b, LColor.p]
  , [LColor.p, LColor.r, LColor.p, LColor.r]
  , [LColor.p, LColor.b, LColor.p, LColor.b]
  , [LColor.p, LColor.p, LColor.r, LColor.r]
  , [LColor.p, LColor.p, LColor.b, LColor.b]
  ]

def tttCertifiedStateCount : Nat :=
  tttLightStateCount +
    tttCertifiedLargeFiberKeys.length * tttRemainingLargeFiberSize

def tttRemainingLargeStateCount : Nat :=
  tttRemainingLargeFiberKeys.length * tttRemainingLargeFiberSize

def tttLargeFiber20FirstChunkCertifiedRows : Nat := 16

def tttCertifiedStateCountWithFiber20FirstChunk : Nat :=
  tttCertifiedStateCount + tttLargeFiber20FirstChunkCertifiedRows

def tttRemainingStateCountAfterFiber20FirstChunk : Nat :=
  tttCompositeStateCount - tttCertifiedStateCountWithFiber20FirstChunk

def tttTargetProgressCountsAudit : Bool :=
  tttLightFiberCount == 69
    && tttLightStateCount == 384
    && tttCertifiedLargeFiberKeys.length == 3
    && tttRemainingLargeFiberKeys.length == 9
    && tttCertifiedLargeFiberKeys ++ tttRemainingLargeFiberKeys ==
      tttLargeFiberKeys
    && tttCertifiedStateCount == 1920
    && tttRemainingLargeStateCount == 4608
    && tttCertifiedStateCount + tttRemainingLargeStateCount ==
      tttCompositeStateCount

theorem tttTargetProgressCountsAudit_ok :
    tttTargetProgressCountsAudit = true := by
  decide

def tttLargeFiber20FirstChunkProgressAudit : Bool :=
  tttRemainingLargeFiberKeys.contains tttLargeFiber20Key
    && tttLargeFiber20Key ==
      [LColor.r, LColor.p, LColor.r, LColor.p]
    && tttLargeFiber20Block0Chunk0Sources.length ==
      tttLargeFiber20FirstChunkCertifiedRows
    && tttCertifiedStateCountWithFiber20FirstChunk == 1936
    && tttRemainingStateCountAfterFiber20FirstChunk == 4592
    && tttLargeFiber20Block0Chunk0ComponentCertificateAudit

theorem tttLargeFiber20FirstChunkProgressAudit_ok :
    tttLargeFiber20FirstChunkProgressAudit = true := by
  decide

def tttMode09WitnessAudit : Bool :=
  semanticWitnessForMode FrontierMode.mode09 ==
      SemanticModeWitness.target RepresentativeSemanticTarget.ttt
    && targetFrontierWord RepresentativeSemanticTarget.ttt == tttFrontierWord
    && targetFrontierMode RepresentativeSemanticTarget.ttt ==
      FrontierMode.mode09
    && wordMode tttFrontierWord == some FrontierMode.mode09

theorem tttMode09WitnessAudit_ok :
    tttMode09WitnessAudit = true := by
  rfl

def tttPartialTargetCertificateAudit : Bool :=
  tttMode09WitnessAudit
    && tttTargetProgressCountsAudit
    && tttLightComponentCertificateAudit
    && tttLargeFiber4ComponentCertificateAudit
    && tttLargeFiber8ComponentCertificateAudit
    && tttLargeFiber10ComponentCertificateAudit
    && tttLargeFiber20FirstChunkProgressAudit

/--
The currently checked `TTT`/`mode09` semantic surface.

This proves only partial target progress: light fibers plus the three listed
large fibers and the first 16-row slice of the next large fiber are certified.
The rest of the fibers in `tttRemainingLargeFiberKeys` are still outside this
audit.
-/
theorem tttPartialTargetCertificateAudit_ok :
    tttPartialTargetCertificateAudit = true := by
  simp [tttPartialTargetCertificateAudit,
    tttMode09WitnessAudit_ok,
    tttTargetProgressCountsAudit_ok,
    tttLightComponentCertificateAudit_ok,
    tttLargeFiber4ComponentCertificateAudit_ok,
    tttLargeFiber8ComponentCertificateAudit_ok,
    tttLargeFiber10ComponentCertificateAudit_ok,
    tttLargeFiber20FirstChunkProgressAudit_ok]

end GoertzelLemma818TripleTauTargetProgress

end Mettapedia.GraphTheory.FourColor
