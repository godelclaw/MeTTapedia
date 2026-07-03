import Mettapedia.GraphTheory.FourColor.GoertzelLemma818MirrorTripleLargeFiber36Block4ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Block5Chunk0ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Block5Chunk1ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Block5Chunk2ComponentCertificate
import Mathlib.Tactic.IntervalCases

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: checked `MMM` large-fiber block-5 prefix

This module checks the first three 16-row chunks of block 5 for the
`MMM`/`mode05` large fixed-input fiber with reversed key `[b,b,r,r]`.  It
reuses completed `TTT` block-5 chunks, but rechecks them against the actual
mirror-triple word.

This is an explicit partial prefix of one large fixed-input fiber, not a full
block, not the full `MMM` target, and not the all-chain `LKR_in` consequence.
-/

namespace GoertzelLemma818MirrorTripleLargeFiber36Block5PrefixComponentCertificate

open GoertzelLemma818MirrorTripleLargeFiber36Block1ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Block5Chunk0ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Block5Chunk1ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Block5Chunk2ComponentCertificate

def mmmLargeFiber36Block5Chunk0ComponentCertificateAudit : Bool :=
  mmmLargeFiber36ChunkAudit tttLargeFiber4Block5Chunk0Rows
    tttLargeFiber4Block5Chunk0Sources

theorem mmmLargeFiber36Block5Chunk0RowsAudit_ok :
    mmmLargeFiber36ChunkRowsAudit tttLargeFiber4Block5Chunk0Rows = true := by
  simp [mmmLargeFiber36ChunkRowsAudit]
  intro x hx
  interval_cases x <;> decide

theorem mmmLargeFiber36Block5Chunk0ComponentCertificateAudit_ok :
    mmmLargeFiber36Block5Chunk0ComponentCertificateAudit = true := by
  simp [mmmLargeFiber36Block5Chunk0ComponentCertificateAudit,
    mmmLargeFiber36ChunkAudit, mmmLargeFiber36Block5Chunk0RowsAudit_ok]
  decide

def mmmLargeFiber36Block5Chunk1ComponentCertificateAudit : Bool :=
  mmmLargeFiber36ChunkAudit tttLargeFiber4Block5Chunk1Rows
    tttLargeFiber4Block5Chunk1Sources

theorem mmmLargeFiber36Block5Chunk1RowsAudit_ok :
    mmmLargeFiber36ChunkRowsAudit tttLargeFiber4Block5Chunk1Rows = true := by
  simp [mmmLargeFiber36ChunkRowsAudit]
  intro x hx
  interval_cases x <;> decide

theorem mmmLargeFiber36Block5Chunk1ComponentCertificateAudit_ok :
    mmmLargeFiber36Block5Chunk1ComponentCertificateAudit = true := by
  simp [mmmLargeFiber36Block5Chunk1ComponentCertificateAudit,
    mmmLargeFiber36ChunkAudit, mmmLargeFiber36Block5Chunk1RowsAudit_ok]
  decide

def mmmLargeFiber36Block5Chunk2ComponentCertificateAudit : Bool :=
  mmmLargeFiber36ChunkAudit tttLargeFiber4Block5Chunk2Rows
    tttLargeFiber4Block5Chunk2Sources

theorem mmmLargeFiber36Block5Chunk2RowsAudit_ok :
    mmmLargeFiber36ChunkRowsAudit tttLargeFiber4Block5Chunk2Rows = true := by
  simp [mmmLargeFiber36ChunkRowsAudit]
  intro x hx
  interval_cases x <;> decide

theorem mmmLargeFiber36Block5Chunk2ComponentCertificateAudit_ok :
    mmmLargeFiber36Block5Chunk2ComponentCertificateAudit = true := by
  simp [mmmLargeFiber36Block5Chunk2ComponentCertificateAudit,
    mmmLargeFiber36ChunkAudit, mmmLargeFiber36Block5Chunk2RowsAudit_ok]
  decide

def mmmLargeFiber36Block5PrefixComponentCertificateAudit : Bool :=
  mmmLargeFiber36Block5Chunk0ComponentCertificateAudit &&
    mmmLargeFiber36Block5Chunk1ComponentCertificateAudit &&
    mmmLargeFiber36Block5Chunk2ComponentCertificateAudit

theorem mmmLargeFiber36Block5PrefixComponentCertificateAudit_ok :
    mmmLargeFiber36Block5PrefixComponentCertificateAudit = true := by
  simp [mmmLargeFiber36Block5PrefixComponentCertificateAudit,
    mmmLargeFiber36Block5Chunk0ComponentCertificateAudit_ok,
    mmmLargeFiber36Block5Chunk1ComponentCertificateAudit_ok,
    mmmLargeFiber36Block5Chunk2ComponentCertificateAudit_ok]

end GoertzelLemma818MirrorTripleLargeFiber36Block5PrefixComponentCertificate

end Mettapedia.GraphTheory.FourColor
