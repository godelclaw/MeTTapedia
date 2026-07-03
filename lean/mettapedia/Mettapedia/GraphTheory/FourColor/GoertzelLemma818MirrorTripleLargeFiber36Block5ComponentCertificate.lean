import Mettapedia.GraphTheory.FourColor.GoertzelLemma818MirrorTripleLargeFiber36Block5PrefixComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Block5Chunk3ComponentCertificate
import Mathlib.Tactic.IntervalCases

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: fifth checked `MMM` large-fiber block

This module completes block 5 for the `MMM`/`mode05` large fixed-input fiber
with reversed key `[b,b,r,r]`.  The first three chunks are imported from the
block-5 prefix module.  The last chunk uses the same interval-membership shape
as the generated `TTT` chunk, avoiding broad traversal of the 512-row expected
list while still rechecking the row moves under the actual mirror-triple word.

This remains one checked block of one large fixed-input fiber, not the full
`MMM` target and not the all-chain `LKR_in` consequence.
-/

namespace GoertzelLemma818MirrorTripleLargeFiber36Block5ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818MirrorTripleComponentSmoke
open GoertzelLemma818MirrorTripleLargeFiber36Block1ComponentCertificate
open GoertzelLemma818MirrorTripleLargeFiber36Block5PrefixComponentCertificate
open GoertzelLemma818MirrorTripleLargeFiber36Chunk0ComponentCertificate
open GoertzelLemma818MirrorTripleLightSlices
open GoertzelLemma818TripleTauLargeFiber4Block5Chunk3ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Data
open GoertzelLemma818TripleTauLightComponentCertificate

def mmmLargeFiber36Block5Chunk3IntervalRowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber4Block5Chunk3ExpectedContains row.source &&
    tttLargeFiber4Block5Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates mmmWord s && compatibleChainStates mmmWord t &&
        chainInputKey mmmWord s == mmmLargeFiber36Key &&
          chainInputKey mmmWord t == mmmLargeFiber36Key &&
            (row.source == row.parent || chainCertifiedKempeStep mmmWord s t row.cert)

def mmmLargeFiber36Block5Chunk3IntervalRowCheck (i : Nat) : Bool :=
  mmmLargeFiber36Block5Chunk3IntervalRowValid
    (listGetD tttLargeFiber4Block5Chunk3Rows i default)

def mmmLargeFiber36Block5Chunk3IntervalRowsAudit : Bool :=
  (List.range 16).all mmmLargeFiber36Block5Chunk3IntervalRowCheck

theorem mmmLargeFiber36Block5Chunk3IntervalRowsAudit_ok :
    mmmLargeFiber36Block5Chunk3IntervalRowsAudit = true := by
  simp [mmmLargeFiber36Block5Chunk3IntervalRowsAudit,
    mmmLargeFiber36Block5Chunk3IntervalRowCheck]
  intro x hx
  interval_cases x <;> decide

def mmmLargeFiber36Block5Chunk3ComponentCertificateAudit : Bool :=
  mmmRepresentativeModeSliceAudit &&
    tttLargeFiber4CountsAudit &&
    tttLargeFiber4Block5Chunk3SourcesCheck &&
    mmmLargeFiber36Block5Chunk3IntervalRowsAudit &&
    tttLargeFiber4Block5Chunk3ParentMapAudit &&
    tttLargeFiber4Block5Chunk3ParentsAudit

theorem mmmLargeFiber36Block5Chunk3ComponentCertificateAudit_ok :
    mmmLargeFiber36Block5Chunk3ComponentCertificateAudit = true := by
  simp [mmmLargeFiber36Block5Chunk3ComponentCertificateAudit,
    mmmRepresentativeModeSliceAudit_ok,
    tttLargeFiber4CountsAudit_ok,
    tttLargeFiber4Block5Chunk3SourcesCheck_ok,
    mmmLargeFiber36Block5Chunk3IntervalRowsAudit_ok,
    tttLargeFiber4Block5Chunk3ParentMapAudit_ok,
    tttLargeFiber4Block5Chunk3ParentsAudit_ok]

def mmmLargeFiber36Block5ComponentCertificateAudit : Bool :=
  mmmLargeFiber36Block5PrefixComponentCertificateAudit &&
    mmmLargeFiber36Block5Chunk3ComponentCertificateAudit

theorem mmmLargeFiber36Block5ComponentCertificateAudit_ok :
    mmmLargeFiber36Block5ComponentCertificateAudit = true := by
  simp [mmmLargeFiber36Block5ComponentCertificateAudit,
    mmmLargeFiber36Block5PrefixComponentCertificateAudit_ok,
    mmmLargeFiber36Block5Chunk3ComponentCertificateAudit_ok]

end GoertzelLemma818MirrorTripleLargeFiber36Block5ComponentCertificate

end Mettapedia.GraphTheory.FourColor
