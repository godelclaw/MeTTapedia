namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificatePackedRankVector

/-- Eight rank bytes are packed into each natural number.  The byte value
`255` denotes absence; all smaller values denote finite ranks. -/
structure Code where
  configCount : Nat
  vectorCount : Nat
  wordChunks : Array (Array Nat)
  deriving DecidableEq, Repr

def bytesPerWord : Nat := 8

def wordChunkSize : Nat := 128

/-- Rank vectors are padded to a word boundary.  This costs at most seven
bytes per vector and lets a response comparison fetch each packed word once. -/
def Code.wordsPerVector (code : Code) : Nat :=
  (code.configCount + bytesPerWord - 1) / bytesPerWord

def Code.wordAt? (code : Code) (index : Nat) : Option Nat :=
  (code.wordChunks[index / wordChunkSize]?).bind fun chunk =>
    chunk[index % wordChunkSize]?

def Code.vectorWordAt? (code : Code) (vector word : Nat) : Option Nat :=
  code.wordAt? (vector * code.wordsPerVector + word)

def byteAt (packed offset : Nat) : Nat :=
  Nat.land (Nat.shiftRight packed (8 * offset)) 255

def Code.rankAt? (code : Code) (vector config : Nat) : Option Nat :=
  if vector < code.vectorCount ∧ config < code.configCount then
    match code.vectorWordAt? vector (config / bytesPerWord) with
    | none => none
    | some packed =>
        let rank := byteAt packed (config % bytesPerWord)
        if rank < 255 then some rank else none
  else none

theorem Code.rankAt?_some_bounds (code : Code)
    (vector config rank : Nat)
    (hrank : code.rankAt? vector config = some rank) :
    vector < code.vectorCount ∧ config < code.configCount := by
  unfold rankAt? at hrank
  split at hrank
  · assumption
  · simp at hrank

/-- Compare the eight rank bytes in one aligned word.  Padding bytes lie past
`configCount` and are ignored. -/
def wordRespondsBoolean (code : Code) (wordOffset sourceWord responseWord : Nat) :
    Bool :=
  (List.range bytesPerWord).all fun byteOffset =>
    let config := wordOffset * bytesPerWord + byteOffset
    if config < code.configCount then
      let sourceRank := byteAt sourceWord byteOffset
      if sourceRank < 255 then
        decide (0 < sourceRank) &&
          decide (byteAt responseWord byteOffset < sourceRank)
      else true
    else true

/-- Pointwise strict response check.  Each aligned packed word is fetched
once; inactive source configurations are ignored, while every active source
rank must be positive and have a strictly lower response rank. -/
def respondsBoolean (code : Code) (source response : Nat) : Bool :=
  decide (source < code.vectorCount) &&
    (decide (response < code.vectorCount) &&
      (List.range code.wordsPerVector).all fun wordOffset =>
        match code.vectorWordAt? source wordOffset,
            code.vectorWordAt? response wordOffset with
        | some sourceWord, some responseWord =>
            wordRespondsBoolean code wordOffset sourceWord responseWord
        | _, _ => false)

theorem Code.configCount_le_wordsPerVector_mul (code : Code) :
    code.configCount ≤ code.wordsPerVector * bytesPerWord := by
  have hmod := Nat.mod_lt (code.configCount + bytesPerWord - 1)
    (by decide : 0 < bytesPerWord)
  have hdiv := Nat.div_add_mod (code.configCount + bytesPerWord - 1)
    bytesPerWord
  rw [Nat.mul_comm] at hdiv
  simp only [Code.wordsPerVector]
  omega

theorem Code.config_div_lt_wordsPerVector (code : Code) (config : Nat)
    (hconfig : config < code.configCount) :
    config / bytesPerWord < code.wordsPerVector := by
  apply (Nat.div_lt_iff_lt_mul (by decide : 0 < bytesPerWord)).2
  exact Nat.lt_of_lt_of_le hconfig code.configCount_le_wordsPerVector_mul

theorem respondsBoolean_sound (code : Code) (source response : Nat)
    (hcheck : respondsBoolean code source response = true) :
    source < code.vectorCount ∧ response < code.vectorCount ∧
      ∀ config sourceRank,
        config < code.configCount →
          code.rankAt? source config = some sourceRank →
            0 < sourceRank ∧
              ∃ responseRank,
                code.rankAt? response config = some responseRank ∧
                  responseRank < sourceRank := by
  simp only [respondsBoolean, Bool.and_eq_true] at hcheck
  have hsourceBound : source < code.vectorCount :=
    of_decide_eq_true hcheck.1
  have hresponseBound : response < code.vectorCount :=
    of_decide_eq_true hcheck.2.1
  refine ⟨hsourceBound, hresponseBound, ?_⟩
  intro config sourceRank hconfig hsource
  let wordOffset := config / bytesPerWord
  let byteOffset := config % bytesPerWord
  have hwordOffset : wordOffset < code.wordsPerVector :=
    code.config_div_lt_wordsPerVector config hconfig
  have hwordCheck := (List.all_eq_true.1 hcheck.2.2) wordOffset
    (List.mem_range.2 hwordOffset)
  cases hsourceWord : code.vectorWordAt? source wordOffset with
  | none => simp [hsourceWord] at hwordCheck
  | some sourceWord =>
      cases hresponseWord : code.vectorWordAt? response wordOffset with
      | none => simp [hsourceWord, hresponseWord] at hwordCheck
      | some responseWord =>
          simp only [hsourceWord, hresponseWord] at hwordCheck
          have hbyteOffset : byteOffset < bytesPerWord :=
            Nat.mod_lt _ (by decide)
          have hbyteCheck := (List.all_eq_true.1 hwordCheck) byteOffset
            (List.mem_range.2 hbyteOffset)
          have hconfigEq : wordOffset * bytesPerWord + byteOffset = config := by
            simpa [wordOffset, byteOffset, Nat.mul_comm] using
              (Nat.div_add_mod config bytesPerWord)
          have hsourceValue :
              (if byteAt sourceWord byteOffset < 255 then
                some (byteAt sourceWord byteOffset) else none) =
                some sourceRank := by
            simpa [Code.rankAt?, hsourceBound, hconfig, wordOffset,
              byteOffset, hsourceWord] using hsource
          split at hsourceValue
          · rename_i hsourceActive
            have hsourceRankEq : byteAt sourceWord byteOffset = sourceRank := by
              simpa using hsourceValue
            subst sourceRank
            simp [hconfigEq, hconfig, hsourceActive] at hbyteCheck
            have hresponseActive :
                byteAt responseWord byteOffset < 255 :=
              Nat.lt_trans hbyteCheck.2 hsourceActive
            refine ⟨hbyteCheck.1, byteAt responseWord byteOffset, ?_,
              hbyteCheck.2⟩
            simpa [Code.rankAt?, hresponseBound, hconfig, wordOffset,
              byteOffset, hresponseWord, hresponseActive]
          · cases hsourceValue

end ClassicalCertificatePackedRankVector

end Mettapedia.GraphTheory.FourColor
