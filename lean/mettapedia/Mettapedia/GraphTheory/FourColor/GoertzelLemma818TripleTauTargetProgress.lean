import Mettapedia.GraphTheory.FourColor.GoertzelLemma818SemanticBridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Certificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber8Certificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber10Certificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber20Block0Chunk0ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber20Block0Chunk1ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber20Block0ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber20Block1ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber20Block2ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber20Block3ComponentCertificate

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: partial `TTT` target progress

This module records the currently checked chain-level surface for the first
non-base semantic target, `TTT`/`mode09`.

It is intentionally partial.  The light fibers, three of the twelve large
fixed-input fibers, and the first four blocks of a fourth large fiber are certified
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
open GoertzelLemma818TripleTauLargeFiber20Block0Chunk1ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber20Block0ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber20Block1ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber20Block2ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber20Block3ComponentCertificate

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

def tttLargeFiber20SecondChunkCertifiedRows : Nat := 16

def tttCertifiedStateCountWithFiber20FirstChunk : Nat :=
  tttCertifiedStateCount + tttLargeFiber20FirstChunkCertifiedRows

def tttRemainingStateCountAfterFiber20FirstChunk : Nat :=
  tttCompositeStateCount - tttCertifiedStateCountWithFiber20FirstChunk

def tttCertifiedStateCountWithFiber20FirstTwoChunks : Nat :=
  tttCertifiedStateCountWithFiber20FirstChunk +
    tttLargeFiber20SecondChunkCertifiedRows

def tttRemainingStateCountAfterFiber20FirstTwoChunks : Nat :=
  tttCompositeStateCount - tttCertifiedStateCountWithFiber20FirstTwoChunks

def tttLargeFiber20Block0CertifiedRows : Nat := 64

def tttCertifiedStateCountWithFiber20Block0 : Nat :=
  tttCertifiedStateCount + tttLargeFiber20Block0CertifiedRows

def tttRemainingStateCountAfterFiber20Block0 : Nat :=
  tttCompositeStateCount - tttCertifiedStateCountWithFiber20Block0

def tttLargeFiber20Block1CertifiedRows : Nat := 64

def tttCertifiedStateCountWithFiber20Block1 : Nat :=
  tttCertifiedStateCountWithFiber20Block0 + tttLargeFiber20Block1CertifiedRows

def tttRemainingStateCountAfterFiber20Block1 : Nat :=
  tttCompositeStateCount - tttCertifiedStateCountWithFiber20Block1

def tttLargeFiber20Block2CertifiedRows : Nat := 64

def tttCertifiedStateCountWithFiber20Block2 : Nat :=
  tttCertifiedStateCountWithFiber20Block1 + tttLargeFiber20Block2CertifiedRows

def tttRemainingStateCountAfterFiber20Block2 : Nat :=
  tttCompositeStateCount - tttCertifiedStateCountWithFiber20Block2

def tttLargeFiber20Block3CertifiedRows : Nat := 64

def tttCertifiedStateCountWithFiber20Block3 : Nat :=
  tttCertifiedStateCountWithFiber20Block2 + tttLargeFiber20Block3CertifiedRows

def tttRemainingStateCountAfterFiber20Block3 : Nat :=
  tttCompositeStateCount - tttCertifiedStateCountWithFiber20Block3

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

def tttLargeFiber20SecondChunkProgressAudit : Bool :=
  tttRemainingLargeFiberKeys.contains tttLargeFiber20Key
    && tttLargeFiber20Key ==
      [LColor.r, LColor.p, LColor.r, LColor.p]
    && tttLargeFiber20Block0Chunk1Sources.length ==
      tttLargeFiber20SecondChunkCertifiedRows
    && tttLargeFiber20Block0Chunk1ComponentCertificateAudit

theorem tttLargeFiber20SecondChunkProgressAudit_ok :
    tttLargeFiber20SecondChunkProgressAudit = true := by
  decide

def tttLargeFiber20FirstTwoChunksProgressAudit : Bool :=
  tttLargeFiber20FirstChunkProgressAudit
    && tttLargeFiber20SecondChunkProgressAudit
    && tttLargeFiber20FirstChunkCertifiedRows +
        tttLargeFiber20SecondChunkCertifiedRows == 32
    && tttCertifiedStateCountWithFiber20FirstTwoChunks == 1952
    && tttRemainingStateCountAfterFiber20FirstTwoChunks == 4576

theorem tttLargeFiber20FirstTwoChunksProgressAudit_ok :
    tttLargeFiber20FirstTwoChunksProgressAudit = true := by
  decide

def tttLargeFiber20Block0ProgressAudit : Bool :=
  tttRemainingLargeFiberKeys.contains tttLargeFiber20Key
    && tttLargeFiber20Key ==
      [LColor.r, LColor.p, LColor.r, LColor.p]
    && tttLargeFiber20Block0CertifiedRows == 64
    && tttCertifiedStateCountWithFiber20Block0 == 1984
    && tttRemainingStateCountAfterFiber20Block0 == 4544
    && tttLargeFiber20Block0ComponentCertificateAudit

theorem tttLargeFiber20Block0ProgressAudit_ok :
    tttLargeFiber20Block0ProgressAudit = true := by
  decide

def tttLargeFiber20Block1ProgressAudit : Bool :=
  tttLargeFiber20Block0ProgressAudit
    && tttRemainingLargeFiberKeys.contains tttLargeFiber20Key
    && tttLargeFiber20Key ==
      [LColor.r, LColor.p, LColor.r, LColor.p]
    && tttLargeFiber20Block1CertifiedRows == 64
    && tttCertifiedStateCountWithFiber20Block1 == 2048
    && tttRemainingStateCountAfterFiber20Block1 == 4480
    && tttLargeFiber20Block1ComponentCertificateAudit

theorem tttLargeFiber20Block1ProgressAudit_ok :
    tttLargeFiber20Block1ProgressAudit = true := by
  decide

def tttLargeFiber20Block2CountAudit : Bool :=
  tttRemainingLargeFiberKeys.contains tttLargeFiber20Key
    && tttLargeFiber20Key ==
      [LColor.r, LColor.p, LColor.r, LColor.p]
    && tttLargeFiber20Block2CertifiedRows == 64
    && tttCertifiedStateCountWithFiber20Block2 == 2112
    && tttRemainingStateCountAfterFiber20Block2 == 4416

theorem tttLargeFiber20Block2CountAudit_ok :
    tttLargeFiber20Block2CountAudit = true := by
  decide

def tttLargeFiber20Block2ProgressAudit : Bool :=
  tttLargeFiber20Block1ProgressAudit
    && tttLargeFiber20Block2CountAudit
    && tttLargeFiber20Block2ComponentCertificateAudit

theorem tttLargeFiber20Block2ProgressAudit_ok :
    tttLargeFiber20Block2ProgressAudit = true := by
  simp [tttLargeFiber20Block2ProgressAudit,
    tttLargeFiber20Block1ProgressAudit_ok,
    tttLargeFiber20Block2CountAudit_ok,
    tttLargeFiber20Block2ComponentCertificateAudit_ok]

def tttLargeFiber20Block3CountAudit : Bool :=
  tttRemainingLargeFiberKeys.contains tttLargeFiber20Key
    && tttLargeFiber20Key ==
      [LColor.r, LColor.p, LColor.r, LColor.p]
    && tttLargeFiber20Block3CertifiedRows == 64
    && tttCertifiedStateCountWithFiber20Block3 == 2176
    && tttRemainingStateCountAfterFiber20Block3 == 4352

theorem tttLargeFiber20Block3CountAudit_ok :
    tttLargeFiber20Block3CountAudit = true := by
  decide

def tttLargeFiber20Block3ProgressAudit : Bool :=
  tttLargeFiber20Block2ProgressAudit
    && tttLargeFiber20Block3CountAudit
    && tttLargeFiber20Block3ComponentCertificateAudit

theorem tttLargeFiber20Block3ProgressAudit_ok :
    tttLargeFiber20Block3ProgressAudit = true := by
  simp [tttLargeFiber20Block3ProgressAudit,
    tttLargeFiber20Block2ProgressAudit_ok,
    tttLargeFiber20Block3CountAudit_ok,
    tttLargeFiber20Block3ComponentCertificateAudit_ok]

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
    && tttLargeFiber20Block3ProgressAudit

/--
The currently checked `TTT`/`mode09` semantic surface.

This proves only partial target progress: light fibers plus the three listed
large fibers and the first four 64-row blocks of the next large fiber are
certified.
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
    tttLargeFiber20Block3ProgressAudit_ok]

end GoertzelLemma818TripleTauTargetProgress

end Mettapedia.GraphTheory.FourColor
