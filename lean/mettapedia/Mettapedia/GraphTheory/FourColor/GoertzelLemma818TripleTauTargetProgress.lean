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
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber20Block4ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber20Block5ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber20Block6ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber20Block7ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber20Certificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber30Certificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber36Certificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber44Certificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber50Certificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber60Certificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber70Certificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber72Certificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber76Certificate

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: `TTT` target progress

This module records the currently checked chain-level surface for the first
non-base semantic target, `TTT`/`mode09`.

The light fibers and all twelve large fixed-input fibers are certified by
explicit component/path tables.  This closes the explicit `TTT` representative
target; it is still not the all-chain `LKR_in` theorem.
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
open GoertzelLemma818TripleTauLargeFiber20Block4ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber20Block5ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber20Block6ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber20Block7ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber20Certificate
open GoertzelLemma818TripleTauLargeFiber30Data
open GoertzelLemma818TripleTauLargeFiber30Certificate
open GoertzelLemma818TripleTauLargeFiber36Data
open GoertzelLemma818TripleTauLargeFiber36Certificate
open GoertzelLemma818TripleTauLargeFiber44Data
open GoertzelLemma818TripleTauLargeFiber44Certificate
open GoertzelLemma818TripleTauLargeFiber50Data
open GoertzelLemma818TripleTauLargeFiber50Certificate
open GoertzelLemma818TripleTauLargeFiber60Data
open GoertzelLemma818TripleTauLargeFiber60Certificate
open GoertzelLemma818TripleTauLargeFiber70Data
open GoertzelLemma818TripleTauLargeFiber70Certificate
open GoertzelLemma818TripleTauLargeFiber72Data
open GoertzelLemma818TripleTauLargeFiber72Certificate
open GoertzelLemma818TripleTauLargeFiber76Data
open GoertzelLemma818TripleTauLargeFiber76Certificate

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

def tttLargeFiber20Block4CertifiedRows : Nat := 64

def tttCertifiedStateCountWithFiber20Block4 : Nat :=
  tttCertifiedStateCountWithFiber20Block3 + tttLargeFiber20Block4CertifiedRows

def tttRemainingStateCountAfterFiber20Block4 : Nat :=
  tttCompositeStateCount - tttCertifiedStateCountWithFiber20Block4

def tttLargeFiber20Block5CertifiedRows : Nat := 64

def tttCertifiedStateCountWithFiber20Block5 : Nat :=
  tttCertifiedStateCountWithFiber20Block4 + tttLargeFiber20Block5CertifiedRows

def tttRemainingStateCountAfterFiber20Block5 : Nat :=
  tttCompositeStateCount - tttCertifiedStateCountWithFiber20Block5

def tttLargeFiber20Block6CertifiedRows : Nat := 64

def tttCertifiedStateCountWithFiber20Block6 : Nat :=
  tttCertifiedStateCountWithFiber20Block5 + tttLargeFiber20Block6CertifiedRows

def tttRemainingStateCountAfterFiber20Block6 : Nat :=
  tttCompositeStateCount - tttCertifiedStateCountWithFiber20Block6

def tttLargeFiber20Block7CertifiedRows : Nat := 64

def tttCertifiedStateCountWithFiber20Block7 : Nat :=
  tttCertifiedStateCountWithFiber20Block6 + tttLargeFiber20Block7CertifiedRows

def tttRemainingStateCountAfterFiber20Block7 : Nat :=
  tttCompositeStateCount - tttCertifiedStateCountWithFiber20Block7

def tttCertifiedLargeFiberKeysAfterFiber20 : List (List LColor) :=
  tttCertifiedLargeFiberKeys ++ [tttLargeFiber20Key]

def tttRemainingLargeFiberKeysAfterFiber20 : List (List LColor) :=
  [ [LColor.b, LColor.r, LColor.b, LColor.r]
  , [LColor.b, LColor.b, LColor.r, LColor.r]
  , [LColor.b, LColor.b, LColor.p, LColor.p]
  , [LColor.b, LColor.p, LColor.b, LColor.p]
  , [LColor.p, LColor.r, LColor.p, LColor.r]
  , [LColor.p, LColor.b, LColor.p, LColor.b]
  , [LColor.p, LColor.p, LColor.r, LColor.r]
  , [LColor.p, LColor.p, LColor.b, LColor.b]
  ]

def tttCertifiedStateCountWithFiber30 : Nat :=
  tttCertifiedStateCountWithFiber20Block7 + tttRemainingLargeFiberSize

def tttRemainingStateCountAfterFiber30 : Nat :=
  tttCompositeStateCount - tttCertifiedStateCountWithFiber30

def tttCertifiedLargeFiberKeysAfterFiber30 : List (List LColor) :=
  tttCertifiedLargeFiberKeysAfterFiber20 ++ [tttLargeFiber30Key]

def tttRemainingLargeFiberKeysAfterFiber30 : List (List LColor) :=
  [ [LColor.b, LColor.b, LColor.r, LColor.r]
  , [LColor.b, LColor.b, LColor.p, LColor.p]
  , [LColor.b, LColor.p, LColor.b, LColor.p]
  , [LColor.p, LColor.r, LColor.p, LColor.r]
  , [LColor.p, LColor.b, LColor.p, LColor.b]
  , [LColor.p, LColor.p, LColor.r, LColor.r]
  , [LColor.p, LColor.p, LColor.b, LColor.b]
  ]

def tttCertifiedStateCountWithFiber36 : Nat :=
  tttCertifiedStateCountWithFiber30 + tttRemainingLargeFiberSize

def tttRemainingStateCountAfterFiber36 : Nat :=
  tttCompositeStateCount - tttCertifiedStateCountWithFiber36

def tttCertifiedLargeFiberKeysAfterFiber36 : List (List LColor) :=
  tttCertifiedLargeFiberKeysAfterFiber30 ++ [tttLargeFiber36Key]

def tttRemainingLargeFiberKeysAfterFiber36 : List (List LColor) :=
  [ [LColor.b, LColor.b, LColor.p, LColor.p]
  , [LColor.b, LColor.p, LColor.b, LColor.p]
  , [LColor.p, LColor.r, LColor.p, LColor.r]
  , [LColor.p, LColor.b, LColor.p, LColor.b]
  , [LColor.p, LColor.p, LColor.r, LColor.r]
  , [LColor.p, LColor.p, LColor.b, LColor.b]
  ]

def tttCertifiedStateCountWithFiber44 : Nat :=
  tttCertifiedStateCountWithFiber36 + tttRemainingLargeFiberSize

def tttRemainingStateCountAfterFiber44 : Nat :=
  tttCompositeStateCount - tttCertifiedStateCountWithFiber44

def tttCertifiedLargeFiberKeysAfterFiber44 : List (List LColor) :=
  tttCertifiedLargeFiberKeysAfterFiber36 ++ [tttLargeFiber44Key]

def tttRemainingLargeFiberKeysAfterFiber44 : List (List LColor) :=
  [ [LColor.b, LColor.p, LColor.b, LColor.p]
  , [LColor.p, LColor.r, LColor.p, LColor.r]
  , [LColor.p, LColor.b, LColor.p, LColor.b]
  , [LColor.p, LColor.p, LColor.r, LColor.r]
  , [LColor.p, LColor.p, LColor.b, LColor.b]
  ]

def tttCertifiedStateCountWithFiber50 : Nat :=
  tttCertifiedStateCountWithFiber44 + tttRemainingLargeFiberSize

def tttRemainingStateCountAfterFiber50 : Nat :=
  tttCompositeStateCount - tttCertifiedStateCountWithFiber50

def tttCertifiedLargeFiberKeysAfterFiber50 : List (List LColor) :=
  tttCertifiedLargeFiberKeysAfterFiber44 ++ [tttLargeFiber50Key]

def tttRemainingLargeFiberKeysAfterFiber50 : List (List LColor) :=
  [ [LColor.p, LColor.r, LColor.p, LColor.r]
  , [LColor.p, LColor.b, LColor.p, LColor.b]
  , [LColor.p, LColor.p, LColor.r, LColor.r]
  , [LColor.p, LColor.p, LColor.b, LColor.b]
  ]

def tttCertifiedStateCountWithFiber60 : Nat :=
  tttCertifiedStateCountWithFiber50 + tttRemainingLargeFiberSize

def tttRemainingStateCountAfterFiber60 : Nat :=
  tttCompositeStateCount - tttCertifiedStateCountWithFiber60

def tttCertifiedLargeFiberKeysAfterFiber60 : List (List LColor) :=
  tttCertifiedLargeFiberKeysAfterFiber50 ++ [tttLargeFiber60Key]

def tttRemainingLargeFiberKeysAfterFiber60 : List (List LColor) :=
  [ [LColor.p, LColor.b, LColor.p, LColor.b]
  , [LColor.p, LColor.p, LColor.r, LColor.r]
  , [LColor.p, LColor.p, LColor.b, LColor.b]
  ]

def tttCertifiedStateCountWithFiber70 : Nat :=
  tttCertifiedStateCountWithFiber60 + tttRemainingLargeFiberSize

def tttRemainingStateCountAfterFiber70 : Nat :=
  tttCompositeStateCount - tttCertifiedStateCountWithFiber70

def tttCertifiedLargeFiberKeysAfterFiber70 : List (List LColor) :=
  tttCertifiedLargeFiberKeysAfterFiber60 ++ [tttLargeFiber70Key]

def tttRemainingLargeFiberKeysAfterFiber70 : List (List LColor) :=
  [ [LColor.p, LColor.p, LColor.r, LColor.r]
  , [LColor.p, LColor.p, LColor.b, LColor.b]
  ]

def tttCertifiedStateCountWithFiber72 : Nat :=
  tttCertifiedStateCountWithFiber70 + tttRemainingLargeFiberSize

def tttRemainingStateCountAfterFiber72 : Nat :=
  tttCompositeStateCount - tttCertifiedStateCountWithFiber72

def tttCertifiedLargeFiberKeysAfterFiber72 : List (List LColor) :=
  tttCertifiedLargeFiberKeysAfterFiber70 ++ [tttLargeFiber72Key]

def tttRemainingLargeFiberKeysAfterFiber72 : List (List LColor) :=
  [ [LColor.p, LColor.p, LColor.b, LColor.b] ]

def tttCertifiedStateCountWithFiber76 : Nat :=
  tttCertifiedStateCountWithFiber72 + tttRemainingLargeFiberSize

def tttRemainingStateCountAfterFiber76 : Nat :=
  tttCompositeStateCount - tttCertifiedStateCountWithFiber76

def tttCertifiedLargeFiberKeysAfterFiber76 : List (List LColor) :=
  tttCertifiedLargeFiberKeysAfterFiber72 ++ [tttLargeFiber76Key]

def tttRemainingLargeFiberKeysAfterFiber76 : List (List LColor) := []

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

def tttLargeFiber20Block4CountAudit : Bool :=
  tttRemainingLargeFiberKeys.contains tttLargeFiber20Key
    && tttLargeFiber20Key ==
      [LColor.r, LColor.p, LColor.r, LColor.p]
    && tttLargeFiber20Block4CertifiedRows == 64
    && tttCertifiedStateCountWithFiber20Block4 == 2240
    && tttRemainingStateCountAfterFiber20Block4 == 4288

theorem tttLargeFiber20Block4CountAudit_ok :
    tttLargeFiber20Block4CountAudit = true := by
  decide

def tttLargeFiber20Block4ProgressAudit : Bool :=
  tttLargeFiber20Block3ProgressAudit
    && tttLargeFiber20Block4CountAudit
    && tttLargeFiber20Block4ComponentCertificateAudit

theorem tttLargeFiber20Block4ProgressAudit_ok :
    tttLargeFiber20Block4ProgressAudit = true := by
  simp [tttLargeFiber20Block4ProgressAudit,
    tttLargeFiber20Block3ProgressAudit_ok,
    tttLargeFiber20Block4CountAudit_ok,
    tttLargeFiber20Block4ComponentCertificateAudit_ok]

def tttLargeFiber20Block5CountAudit : Bool :=
  tttRemainingLargeFiberKeys.contains tttLargeFiber20Key
    && tttLargeFiber20Key ==
      [LColor.r, LColor.p, LColor.r, LColor.p]
    && tttLargeFiber20Block5CertifiedRows == 64
    && tttCertifiedStateCountWithFiber20Block5 == 2304
    && tttRemainingStateCountAfterFiber20Block5 == 4224

theorem tttLargeFiber20Block5CountAudit_ok :
    tttLargeFiber20Block5CountAudit = true := by
  decide

def tttLargeFiber20Block5ProgressAudit : Bool :=
  tttLargeFiber20Block4ProgressAudit
    && tttLargeFiber20Block5CountAudit
    && tttLargeFiber20Block5ComponentCertificateAudit

theorem tttLargeFiber20Block5ProgressAudit_ok :
    tttLargeFiber20Block5ProgressAudit = true := by
  simp [tttLargeFiber20Block5ProgressAudit,
    tttLargeFiber20Block4ProgressAudit_ok,
    tttLargeFiber20Block5CountAudit_ok,
    tttLargeFiber20Block5ComponentCertificateAudit_ok]

def tttLargeFiber20Block6CountAudit : Bool :=
  tttRemainingLargeFiberKeys.contains tttLargeFiber20Key
    && tttLargeFiber20Key ==
      [LColor.r, LColor.p, LColor.r, LColor.p]
    && tttLargeFiber20Block6CertifiedRows == 64
    && tttCertifiedStateCountWithFiber20Block6 == 2368
    && tttRemainingStateCountAfterFiber20Block6 == 4160

theorem tttLargeFiber20Block6CountAudit_ok :
    tttLargeFiber20Block6CountAudit = true := by
  decide

def tttLargeFiber20Block6ProgressAudit : Bool :=
  tttLargeFiber20Block5ProgressAudit
    && tttLargeFiber20Block6CountAudit
    && tttLargeFiber20Block6ComponentCertificateAudit

theorem tttLargeFiber20Block6ProgressAudit_ok :
    tttLargeFiber20Block6ProgressAudit = true := by
  simp [tttLargeFiber20Block6ProgressAudit,
    tttLargeFiber20Block5ProgressAudit_ok,
    tttLargeFiber20Block6CountAudit_ok,
    tttLargeFiber20Block6ComponentCertificateAudit_ok]

def tttLargeFiber20Block7CountAudit : Bool :=
  tttRemainingLargeFiberKeys.contains tttLargeFiber20Key
    && tttLargeFiber20Key ==
      [LColor.r, LColor.p, LColor.r, LColor.p]
    && tttLargeFiber20Block7CertifiedRows == 64
    && tttCertifiedStateCountWithFiber20Block7 == 2432
    && tttRemainingStateCountAfterFiber20Block7 == 4096

theorem tttLargeFiber20Block7CountAudit_ok :
    tttLargeFiber20Block7CountAudit = true := by
  decide

def tttLargeFiber20Block7ProgressAudit : Bool :=
  tttLargeFiber20Block6ProgressAudit
    && tttLargeFiber20Block7CountAudit
    && tttLargeFiber20Block7ComponentCertificateAudit

theorem tttLargeFiber20Block7ProgressAudit_ok :
    tttLargeFiber20Block7ProgressAudit = true := by
  simp [tttLargeFiber20Block7ProgressAudit,
    tttLargeFiber20Block6ProgressAudit_ok,
    tttLargeFiber20Block7CountAudit_ok,
    tttLargeFiber20Block7ComponentCertificateAudit_ok]

def tttLargeFiber20ClosedCountAudit : Bool :=
  tttCertifiedLargeFiberKeysAfterFiber20.length == 4
    && tttRemainingLargeFiberKeysAfterFiber20.length == 8
    && tttCertifiedLargeFiberKeysAfterFiber20 ++
        tttRemainingLargeFiberKeysAfterFiber20 == tttLargeFiberKeys
    && tttCertifiedStateCountWithFiber20Block7 ==
      tttLightStateCount +
        tttCertifiedLargeFiberKeysAfterFiber20.length * tttRemainingLargeFiberSize
    && tttRemainingStateCountAfterFiber20Block7 ==
      tttRemainingLargeFiberKeysAfterFiber20.length * tttRemainingLargeFiberSize
    && tttCertifiedStateCountWithFiber20Block7 +
        tttRemainingStateCountAfterFiber20Block7 == tttCompositeStateCount

theorem tttLargeFiber20ClosedCountAudit_ok :
    tttLargeFiber20ClosedCountAudit = true := by
  decide

def tttLargeFiber20ClosedProgressAudit : Bool :=
  tttLargeFiber20Block7ProgressAudit
    && tttLargeFiber20ClosedCountAudit
    && tttLargeFiber20ComponentCertificateAudit

theorem tttLargeFiber20ClosedProgressAudit_ok :
    tttLargeFiber20ClosedProgressAudit = true := by
  simp [tttLargeFiber20ClosedProgressAudit,
    tttLargeFiber20Block7ProgressAudit_ok,
    tttLargeFiber20ClosedCountAudit_ok,
    tttLargeFiber20ComponentCertificateAudit_ok]

def tttLargeFiber30ClosedCountAudit : Bool :=
  tttRemainingLargeFiberKeysAfterFiber20.contains tttLargeFiber30Key
    && tttLargeFiber30Key ==
      [LColor.b, LColor.r, LColor.b, LColor.r]
    && tttCertifiedLargeFiberKeysAfterFiber30.length == 5
    && tttRemainingLargeFiberKeysAfterFiber30.length == 7
    && tttCertifiedLargeFiberKeysAfterFiber30 ++
        tttRemainingLargeFiberKeysAfterFiber30 == tttLargeFiberKeys
    && tttCertifiedStateCountWithFiber30 == 2944
    && tttRemainingStateCountAfterFiber30 == 3584
    && tttCertifiedStateCountWithFiber30 ==
      tttLightStateCount +
        tttCertifiedLargeFiberKeysAfterFiber30.length * tttRemainingLargeFiberSize
    && tttRemainingStateCountAfterFiber30 ==
      tttRemainingLargeFiberKeysAfterFiber30.length * tttRemainingLargeFiberSize
    && tttCertifiedStateCountWithFiber30 +
        tttRemainingStateCountAfterFiber30 == tttCompositeStateCount

theorem tttLargeFiber30ClosedCountAudit_ok :
    tttLargeFiber30ClosedCountAudit = true := by
  decide

def tttLargeFiber30ClosedProgressAudit : Bool :=
  tttLargeFiber20ClosedProgressAudit
    && tttLargeFiber30ClosedCountAudit
    && tttLargeFiber30ComponentCertificateAudit

theorem tttLargeFiber30ClosedProgressAudit_ok :
    tttLargeFiber30ClosedProgressAudit = true := by
  simp [tttLargeFiber30ClosedProgressAudit,
    tttLargeFiber20ClosedProgressAudit_ok,
    tttLargeFiber30ClosedCountAudit_ok,
    tttLargeFiber30ComponentCertificateAudit_ok]

def tttLargeFiber36ClosedCountAudit : Bool :=
  tttRemainingLargeFiberKeysAfterFiber30.contains tttLargeFiber36Key
    && tttLargeFiber36Key ==
      [LColor.b, LColor.b, LColor.r, LColor.r]
    && tttCertifiedLargeFiberKeysAfterFiber36.length == 6
    && tttRemainingLargeFiberKeysAfterFiber36.length == 6
    && tttCertifiedLargeFiberKeysAfterFiber36 ++
        tttRemainingLargeFiberKeysAfterFiber36 == tttLargeFiberKeys
    && tttCertifiedStateCountWithFiber36 == 3456
    && tttRemainingStateCountAfterFiber36 == 3072
    && tttCertifiedStateCountWithFiber36 ==
      tttLightStateCount +
        tttCertifiedLargeFiberKeysAfterFiber36.length * tttRemainingLargeFiberSize
    && tttRemainingStateCountAfterFiber36 ==
      tttRemainingLargeFiberKeysAfterFiber36.length * tttRemainingLargeFiberSize
    && tttCertifiedStateCountWithFiber36 +
        tttRemainingStateCountAfterFiber36 == tttCompositeStateCount

theorem tttLargeFiber36ClosedCountAudit_ok :
    tttLargeFiber36ClosedCountAudit = true := by
  decide

def tttLargeFiber36ClosedProgressAudit : Bool :=
  tttLargeFiber30ClosedProgressAudit
    && tttLargeFiber36ClosedCountAudit
    && tttLargeFiber36ComponentCertificateAudit

theorem tttLargeFiber36ClosedProgressAudit_ok :
    tttLargeFiber36ClosedProgressAudit = true := by
  simp [tttLargeFiber36ClosedProgressAudit,
    tttLargeFiber30ClosedProgressAudit_ok,
    tttLargeFiber36ClosedCountAudit_ok,
    tttLargeFiber36ComponentCertificateAudit_ok]

def tttLargeFiber44ClosedCountAudit : Bool :=
  tttRemainingLargeFiberKeysAfterFiber36.contains tttLargeFiber44Key
    && tttLargeFiber44Key ==
      [LColor.b, LColor.b, LColor.p, LColor.p]
    && tttCertifiedLargeFiberKeysAfterFiber44.length == 7
    && tttRemainingLargeFiberKeysAfterFiber44.length == 5
    && tttCertifiedLargeFiberKeysAfterFiber44 ++
        tttRemainingLargeFiberKeysAfterFiber44 == tttLargeFiberKeys
    && tttCertifiedStateCountWithFiber44 == 3968
    && tttRemainingStateCountAfterFiber44 == 2560
    && tttCertifiedStateCountWithFiber44 ==
      tttLightStateCount +
        tttCertifiedLargeFiberKeysAfterFiber44.length * tttRemainingLargeFiberSize
    && tttRemainingStateCountAfterFiber44 ==
      tttRemainingLargeFiberKeysAfterFiber44.length * tttRemainingLargeFiberSize
    && tttCertifiedStateCountWithFiber44 +
        tttRemainingStateCountAfterFiber44 == tttCompositeStateCount

theorem tttLargeFiber44ClosedCountAudit_ok :
    tttLargeFiber44ClosedCountAudit = true := by
  decide

def tttLargeFiber44ClosedProgressAudit : Bool :=
  tttLargeFiber36ClosedProgressAudit
    && tttLargeFiber44ClosedCountAudit
    && tttLargeFiber44ComponentCertificateAudit

theorem tttLargeFiber44ClosedProgressAudit_ok :
    tttLargeFiber44ClosedProgressAudit = true := by
  simp [tttLargeFiber44ClosedProgressAudit,
    tttLargeFiber36ClosedProgressAudit_ok,
    tttLargeFiber44ClosedCountAudit_ok,
    tttLargeFiber44ComponentCertificateAudit_ok]

def tttLargeFiber50ClosedCountAudit : Bool :=
  tttRemainingLargeFiberKeysAfterFiber44.contains tttLargeFiber50Key
    && tttLargeFiber50Key ==
      [LColor.b, LColor.p, LColor.b, LColor.p]
    && tttCertifiedLargeFiberKeysAfterFiber50.length == 8
    && tttRemainingLargeFiberKeysAfterFiber50.length == 4
    && tttCertifiedLargeFiberKeysAfterFiber50 ++
        tttRemainingLargeFiberKeysAfterFiber50 == tttLargeFiberKeys
    && tttCertifiedStateCountWithFiber50 == 4480
    && tttRemainingStateCountAfterFiber50 == 2048
    && tttCertifiedStateCountWithFiber50 ==
      tttLightStateCount +
        tttCertifiedLargeFiberKeysAfterFiber50.length * tttRemainingLargeFiberSize
    && tttRemainingStateCountAfterFiber50 ==
      tttRemainingLargeFiberKeysAfterFiber50.length * tttRemainingLargeFiberSize
    && tttCertifiedStateCountWithFiber50 +
        tttRemainingStateCountAfterFiber50 == tttCompositeStateCount

theorem tttLargeFiber50ClosedCountAudit_ok :
    tttLargeFiber50ClosedCountAudit = true := by
  decide

def tttLargeFiber50ClosedProgressAudit : Bool :=
  tttLargeFiber44ClosedProgressAudit
    && tttLargeFiber50ClosedCountAudit
    && tttLargeFiber50ComponentCertificateAudit

theorem tttLargeFiber50ClosedProgressAudit_ok :
    tttLargeFiber50ClosedProgressAudit = true := by
  simp [tttLargeFiber50ClosedProgressAudit,
    tttLargeFiber44ClosedProgressAudit_ok,
    tttLargeFiber50ClosedCountAudit_ok,
    tttLargeFiber50ComponentCertificateAudit_ok]

def tttLargeFiber60ClosedCountAudit : Bool :=
  tttRemainingLargeFiberKeysAfterFiber50.contains tttLargeFiber60Key
    && tttLargeFiber60Key ==
      [LColor.p, LColor.r, LColor.p, LColor.r]
    && tttCertifiedLargeFiberKeysAfterFiber60.length == 9
    && tttRemainingLargeFiberKeysAfterFiber60.length == 3
    && tttCertifiedLargeFiberKeysAfterFiber60 ++
        tttRemainingLargeFiberKeysAfterFiber60 == tttLargeFiberKeys
    && tttCertifiedStateCountWithFiber60 == 4992
    && tttRemainingStateCountAfterFiber60 == 1536
    && tttCertifiedStateCountWithFiber60 ==
      tttLightStateCount +
        tttCertifiedLargeFiberKeysAfterFiber60.length * tttRemainingLargeFiberSize
    && tttRemainingStateCountAfterFiber60 ==
      tttRemainingLargeFiberKeysAfterFiber60.length * tttRemainingLargeFiberSize
    && tttCertifiedStateCountWithFiber60 +
        tttRemainingStateCountAfterFiber60 == tttCompositeStateCount

theorem tttLargeFiber60ClosedCountAudit_ok :
    tttLargeFiber60ClosedCountAudit = true := by
  decide

def tttLargeFiber60ClosedProgressAudit : Bool :=
  tttLargeFiber50ClosedProgressAudit
    && tttLargeFiber60ClosedCountAudit
    && tttLargeFiber60ComponentCertificateAudit

theorem tttLargeFiber60ClosedProgressAudit_ok :
    tttLargeFiber60ClosedProgressAudit = true := by
  simp [tttLargeFiber60ClosedProgressAudit,
    tttLargeFiber50ClosedProgressAudit_ok,
    tttLargeFiber60ClosedCountAudit_ok,
    tttLargeFiber60ComponentCertificateAudit_ok]

def tttLargeFiber70ClosedCountAudit : Bool :=
  tttRemainingLargeFiberKeysAfterFiber60.contains tttLargeFiber70Key
    && tttLargeFiber70Key ==
      [LColor.p, LColor.b, LColor.p, LColor.b]
    && tttCertifiedLargeFiberKeysAfterFiber70.length == 10
    && tttRemainingLargeFiberKeysAfterFiber70.length == 2
    && tttCertifiedLargeFiberKeysAfterFiber70 ++
        tttRemainingLargeFiberKeysAfterFiber70 == tttLargeFiberKeys
    && tttCertifiedStateCountWithFiber70 == 5504
    && tttRemainingStateCountAfterFiber70 == 1024
    && tttCertifiedStateCountWithFiber70 ==
      tttLightStateCount +
        tttCertifiedLargeFiberKeysAfterFiber70.length * tttRemainingLargeFiberSize
    && tttRemainingStateCountAfterFiber70 ==
      tttRemainingLargeFiberKeysAfterFiber70.length * tttRemainingLargeFiberSize
    && tttCertifiedStateCountWithFiber70 +
        tttRemainingStateCountAfterFiber70 == tttCompositeStateCount

theorem tttLargeFiber70ClosedCountAudit_ok :
    tttLargeFiber70ClosedCountAudit = true := by
  decide

def tttLargeFiber70ClosedProgressAudit : Bool :=
  tttLargeFiber60ClosedProgressAudit
    && tttLargeFiber70ClosedCountAudit
    && tttLargeFiber70ComponentCertificateAudit

theorem tttLargeFiber70ClosedProgressAudit_ok :
    tttLargeFiber70ClosedProgressAudit = true := by
  simp [tttLargeFiber70ClosedProgressAudit,
    tttLargeFiber60ClosedProgressAudit_ok,
    tttLargeFiber70ClosedCountAudit_ok,
    tttLargeFiber70ComponentCertificateAudit_ok]

def tttLargeFiber72ClosedCountAudit : Bool :=
  tttRemainingLargeFiberKeysAfterFiber70.contains tttLargeFiber72Key
    && tttLargeFiber72Key ==
      [LColor.p, LColor.p, LColor.r, LColor.r]
    && tttCertifiedLargeFiberKeysAfterFiber72.length == 11
    && tttRemainingLargeFiberKeysAfterFiber72.length == 1
    && tttCertifiedLargeFiberKeysAfterFiber72 ++
        tttRemainingLargeFiberKeysAfterFiber72 == tttLargeFiberKeys
    && tttCertifiedStateCountWithFiber72 == 6016
    && tttRemainingStateCountAfterFiber72 == 512
    && tttCertifiedStateCountWithFiber72 ==
      tttLightStateCount +
        tttCertifiedLargeFiberKeysAfterFiber72.length * tttRemainingLargeFiberSize
    && tttRemainingStateCountAfterFiber72 ==
      tttRemainingLargeFiberKeysAfterFiber72.length * tttRemainingLargeFiberSize
    && tttCertifiedStateCountWithFiber72 +
        tttRemainingStateCountAfterFiber72 == tttCompositeStateCount

theorem tttLargeFiber72ClosedCountAudit_ok :
    tttLargeFiber72ClosedCountAudit = true := by
  decide

def tttLargeFiber72ClosedProgressAudit : Bool :=
  tttLargeFiber70ClosedProgressAudit
    && tttLargeFiber72ClosedCountAudit
    && tttLargeFiber72ComponentCertificateAudit

theorem tttLargeFiber72ClosedProgressAudit_ok :
    tttLargeFiber72ClosedProgressAudit = true := by
  simp [tttLargeFiber72ClosedProgressAudit,
    tttLargeFiber70ClosedProgressAudit_ok,
    tttLargeFiber72ClosedCountAudit_ok,
    tttLargeFiber72ComponentCertificateAudit_ok]

def tttLargeFiber76ClosedCountAudit : Bool :=
  tttRemainingLargeFiberKeysAfterFiber72.contains tttLargeFiber76Key
    && tttLargeFiber76Key ==
      [LColor.p, LColor.p, LColor.b, LColor.b]
    && tttCertifiedLargeFiberKeysAfterFiber76.length == 12
    && tttRemainingLargeFiberKeysAfterFiber76.length == 0
    && tttCertifiedLargeFiberKeysAfterFiber76 ++
        tttRemainingLargeFiberKeysAfterFiber76 == tttLargeFiberKeys
    && tttCertifiedStateCountWithFiber76 == 6528
    && tttRemainingStateCountAfterFiber76 == 0
    && tttCertifiedStateCountWithFiber76 ==
      tttLightStateCount +
        tttCertifiedLargeFiberKeysAfterFiber76.length * tttRemainingLargeFiberSize
    && tttRemainingStateCountAfterFiber76 ==
      tttRemainingLargeFiberKeysAfterFiber76.length * tttRemainingLargeFiberSize
    && tttCertifiedStateCountWithFiber76 +
        tttRemainingStateCountAfterFiber76 == tttCompositeStateCount

theorem tttLargeFiber76ClosedCountAudit_ok :
    tttLargeFiber76ClosedCountAudit = true := by
  decide

def tttLargeFiber76ClosedProgressAudit : Bool :=
  tttLargeFiber72ClosedProgressAudit
    && tttLargeFiber76ClosedCountAudit
    && tttLargeFiber76ComponentCertificateAudit

theorem tttLargeFiber76ClosedProgressAudit_ok :
    tttLargeFiber76ClosedProgressAudit = true := by
  simp [tttLargeFiber76ClosedProgressAudit,
    tttLargeFiber72ClosedProgressAudit_ok,
    tttLargeFiber76ClosedCountAudit_ok,
    tttLargeFiber76ComponentCertificateAudit_ok]

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
    && tttLargeFiber20ClosedProgressAudit
    && tttLargeFiber30ClosedProgressAudit
    && tttLargeFiber36ClosedProgressAudit
    && tttLargeFiber44ClosedProgressAudit
    && tttLargeFiber50ClosedProgressAudit
    && tttLargeFiber60ClosedProgressAudit
    && tttLargeFiber70ClosedProgressAudit
    && tttLargeFiber72ClosedProgressAudit
    && tttLargeFiber76ClosedProgressAudit

/--
The currently checked `TTT`/`mode09` semantic surface.

This proves the explicit representative-target progress: the light fibers plus
all twelve large fibers are certified.  It does not prove the remaining
thirteen representative targets or all-chain `LKR_in`.
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
    tttLargeFiber20ClosedProgressAudit_ok,
    tttLargeFiber30ClosedProgressAudit_ok,
    tttLargeFiber36ClosedProgressAudit_ok,
    tttLargeFiber44ClosedProgressAudit_ok,
    tttLargeFiber50ClosedProgressAudit_ok,
    tttLargeFiber60ClosedProgressAudit_ok,
    tttLargeFiber70ClosedProgressAudit_ok,
    tttLargeFiber72ClosedProgressAudit_ok,
    tttLargeFiber76ClosedProgressAudit_ok]

def tttTargetCertificateAudit : Bool :=
  tttPartialTargetCertificateAudit

theorem tttTargetCertificateAudit_ok :
    tttTargetCertificateAudit = true := by
  simpa [tttTargetCertificateAudit] using tttPartialTargetCertificateAudit_ok

end GoertzelLemma818TripleTauTargetProgress

end Mettapedia.GraphTheory.FourColor
