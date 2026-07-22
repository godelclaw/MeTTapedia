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

def Code.wordAt? (code : Code) (index : Nat) : Option Nat :=
  (code.wordChunks[index / wordChunkSize]?).bind fun chunk =>
    chunk[index % wordChunkSize]?

def Code.rankAt? (code : Code) (vector config : Nat) : Option Nat :=
  if vector < code.vectorCount ∧ config < code.configCount then
    let byteIndex := vector * code.configCount + config
    match code.wordAt? (byteIndex / bytesPerWord) with
    | none => none
    | some packed =>
        let rank := (packed / 256 ^ (byteIndex % bytesPerWord)) % 256
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

/-- Pointwise strict response check.  Inactive source configurations are
ignored; every active source rank must be positive and have a strictly lower
response rank. -/
def respondsBoolean (code : Code) (source response : Nat) : Bool :=
  decide (source < code.vectorCount) &&
    (decide (response < code.vectorCount) &&
      (List.range code.configCount).all fun config =>
        match code.rankAt? source config with
        | none => true
        | some sourceRank =>
            decide (0 < sourceRank) &&
              match code.rankAt? response config with
              | none => false
              | some responseRank => decide (responseRank < sourceRank))

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
  refine ⟨of_decide_eq_true hcheck.1,
    of_decide_eq_true hcheck.2.1, ?_⟩
  intro config sourceRank hconfig hsource
  have hlocal := (List.all_eq_true.1 hcheck.2.2) config
    (List.mem_range.2 hconfig)
  simp [hsource] at hlocal
  cases hresponse : code.rankAt? response config with
  | none => simp [hresponse] at hlocal
  | some responseRank =>
      simp [hresponse] at hlocal
      exact ⟨hlocal.1, responseRank, rfl, hlocal.2⟩

end ClassicalCertificatePackedRankVector

end Mettapedia.GraphTheory.FourColor
