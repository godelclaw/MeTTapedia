import Mettapedia.GraphTheory.FourColor.ClassicalCertificateResponseDag

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateIndexedLayeredKempe

open ClassicalCertificateEvenTraceKempe
open ClassicalCertificateKempeClosure
open ClassicalCertificateRankedKempe
open ClassicalCertificateResponseDag
open ClassicalCertificateTraceDag
open ClassicalCertificateTraceTree
open ClassicalCertificateTreeRankedKempe

/-- A layered trace certificate with one globally indexed chromogram-response
dictionary.  Response ranks make the recursive decrease explicit. -/
structure Certificate (length : Nat) where
  traceCode : ClassicalCertificateTraceDag.Code
  extendableRoot : Nat
  deltaRoots : List Nat
  responseCode : ClassicalCertificateResponseDag.Code
  responseRoot : Nat

namespace Certificate

variable {length : Nat}

def rootAt (certificate : Certificate length) (rank : Nat) : Nat :=
  certificate.deltaRoots.getD rank 0

def acceptsAt (certificate : Certificate length) (rank : Nat)
    (word : TraceWord length) : Bool :=
  ClassicalCertificateTraceDag.accepts length certificate.traceCode
    (certificate.rootAt rank) word.toList

def acceptsExtendable (certificate : Certificate length)
    (word : TraceWord length) : Bool :=
  ClassicalCertificateTraceDag.accepts length certificate.traceCode
    certificate.extendableRoot word.toList

def ExtendableFamily (certificate : Certificate length)
    (word : List TraceSymbol) : Prop :=
  ∃ fixedWord : TraceWord length,
    fixedWord.toList = word ∧ certificate.acceptsExtendable fixedWord = true

/-- Find the first strictly prior layer containing a word. -/
def priorRank? (certificate : Certificate length) (layer : Nat)
    (word : TraceWord length) : Option Nat :=
  (List.range layer).find? fun rank => certificate.acceptsAt rank word

theorem priorRank?_sound (certificate : Certificate length) (layer : Nat)
    (word : TraceWord length) (rank : Nat)
    (hfound : certificate.priorRank? layer word = some rank) :
    rank < layer ∧ certificate.acceptsAt rank word = true := by
  have hselected := List.find?_some hfound
  have hmember := List.mem_of_find?_eq_some hfound
  exact ⟨List.mem_range.1 hmember, hselected⟩

/-- Search the six global color permutations for one landing in a prior
layer. -/
def previousPermutation? (certificate : Certificate length) (layer : Nat)
    (word : TraceWord length) : Option PermutationCode :=
  permutationCodes.find? fun permutation =>
    (certificate.priorRank? layer (permute permutation word)).isSome

theorem previousPermutation?_sound (certificate : Certificate length)
    (layer : Nat) (word : TraceWord length) (permutation : PermutationCode)
    (hfound : certificate.previousPermutation? layer word =
      some permutation) :
    ∃ rank, rank < layer ∧
      certificate.acceptsAt rank (permute permutation word) = true := by
  have hselected := List.find?_some hfound
  obtain ⟨rank, hrank⟩ := Option.isSome_iff_exists.1 hselected
  exact ⟨rank, certificate.priorRank?_sound layer
    (permute permutation word) rank hrank⟩

def responseValueBoolean (certificate : Certificate length)
    (value : ClassicalCertificateResponseDag.ValueCode) : Bool :=
  value.rank < certificate.deltaRoots.length &&
    certificate.acceptsAt value.rank
      (decodedTraceWord length value.wordCode)

/-- Validate every stored response once, independently of the source words
that subsequently reuse it. -/
def responseChunkBoolean (certificate : Certificate length)
    (chunk : Nat) : Bool :=
  (List.range ClassicalCertificateResponseDag.chunkSize).all fun offset =>
    let index := chunk * ClassicalCertificateResponseDag.chunkSize + offset
    match ClassicalCertificateResponseDag.valueAt?
        certificate.responseCode index with
    | some value => certificate.responseValueBoolean value
    | none => true

def responseTableBoolean (certificate : Certificate length) : Bool :=
  (List.range certificate.responseCode.values.size).all
    certificate.responseChunkBoolean

theorem responseTableBoolean_sound (certificate : Certificate length)
    (htable : certificate.responseTableBoolean = true)
    (index : Nat) (hindex : index <
      ClassicalCertificateResponseDag.valueBound certificate.responseCode)
    (value : ClassicalCertificateResponseDag.ValueCode)
    (hvalue : ClassicalCertificateResponseDag.valueAt?
      certificate.responseCode index = some value) :
    value.rank < certificate.deltaRoots.length ∧
      certificate.acceptsAt value.rank
        (decodedTraceWord length value.wordCode) = true := by
  have hchunk : index / ClassicalCertificateResponseDag.chunkSize <
      certificate.responseCode.values.size := by
    have hpositive : 0 < ClassicalCertificateResponseDag.chunkSize := by
      decide
    exact (Nat.div_lt_iff_lt_mul hpositive).2 (by
      simpa [ClassicalCertificateResponseDag.valueBound,
        Nat.mul_comm] using hindex)
  have hchunkValid := (List.all_eq_true.1 htable)
    (index / ClassicalCertificateResponseDag.chunkSize)
      (List.mem_range.2 hchunk)
  have hoffset : index % ClassicalCertificateResponseDag.chunkSize <
      ClassicalCertificateResponseDag.chunkSize :=
    Nat.mod_lt _ (by decide)
  have hvalid := (List.all_eq_true.1 hchunkValid)
    (index % ClassicalCertificateResponseDag.chunkSize)
      (List.mem_range.2 hoffset)
  have hindexEq : index / ClassicalCertificateResponseDag.chunkSize *
        ClassicalCertificateResponseDag.chunkSize +
          index % ClassicalCertificateResponseDag.chunkSize = index :=
    by simpa [Nat.mul_comm] using
      Nat.div_add_mod index ClassicalCertificateResponseDag.chunkSize
  simp [hindexEq, hvalue, responseValueBoolean] at hvalid
  exact ⟨hvalid.1, hvalid.2⟩

def responseWord (certificate : Certificate length) (gram : GramWord length) :
    TraceWord length :=
  match ClassicalCertificateResponseDag.lookup certificate.responseCode
      certificate.responseRoot gram.toList with
  | some index =>
      match ClassicalCertificateResponseDag.valueAt?
          certificate.responseCode index with
      | some value => decodedTraceWord length value.wordCode
      | none => decodedTraceWord length 0
  | none => decodedTraceWord length 0

def ruleBoolean (certificate : Certificate length) (layer : Nat)
    (word : TraceWord length) : Bool :=
  if certificate.acceptsExtendable word then true
  else
    match certificate.previousPermutation? layer word with
    | some _ => true
    | none =>
        (matchingGramWords word).all fun gram =>
          match ClassicalCertificateResponseDag.lookup
              certificate.responseCode certificate.responseRoot gram.toList with
          | some index =>
              if index < ClassicalCertificateResponseDag.valueBound
                  certificate.responseCode then
                match ClassicalCertificateResponseDag.valueAt?
                    certificate.responseCode index with
                | some value =>
                    value.rank < layer &&
                      chromogramMatches []
                        (decodedTraceWord length value.wordCode).toList
                        gram.toList
                | none => false
              else false
          | none => false

def layerBoolean (certificate : Certificate length) (layer : Nat) : Bool :=
  (ClassicalCertificateTraceDag.acceptedWords length certificate.traceCode
    (certificate.rootAt layer)).all (certificate.ruleBoolean layer)

def checker (certificate : Certificate length) : Bool :=
  certificate.responseTableBoolean &&
    (List.range certificate.deltaRoots.length).all
      certificate.layerBoolean

private def gramWordOfMatch (word : TraceWord length) (gram : Chromogram)
    (hmatch : Matches word.toList gram) : GramWord length :=
  ⟨gram, hmatch.length_eq.symm.trans word.2⟩

/-- One indexed layer rule composes with derivations from all strictly lower
layers. -/
theorem derivation_of_ruleBoolean (certificate : Certificate length)
    (htable : certificate.responseTableBoolean = true) (layer : Nat)
    (priorSound : ∀ rank, rank < layer → ∀ word : TraceWord length,
      certificate.acceptsAt rank word = true →
        CoclosureDerivation certificate.ExtendableFamily word.toList)
    (word : TraceWord length)
    (hrule : certificate.ruleBoolean layer word = true) :
    CoclosureDerivation certificate.ExtendableFamily word.toList := by
  unfold ruleBoolean at hrule
  split at hrule
  · rename_i hextendable
    exact .member ⟨word, rfl, hextendable⟩
  · rename_i hnotExtendable
    cases hpermutation : certificate.previousPermutation? layer word with
    | some permutation =>
        obtain ⟨rank, hrank, haccepted⟩ :=
          certificate.previousPermutation?_sound layer word permutation
            hpermutation
        exact .permutation permutation.toEquiv (by
          simpa using priorSound rank hrank (permute permutation word)
            haccepted)
    | none =>
        have hchecks :
            (matchingGramWords word).all (fun gram =>
              match ClassicalCertificateResponseDag.lookup
                  certificate.responseCode certificate.responseRoot
                    gram.toList with
              | some index =>
                  if index < ClassicalCertificateResponseDag.valueBound
                      certificate.responseCode then
                    match ClassicalCertificateResponseDag.valueAt?
                        certificate.responseCode index with
                    | some value =>
                        value.rank < layer &&
                          chromogramMatches []
                            (decodedTraceWord length value.wordCode).toList
                            gram.toList
                    | none => false
                  else false
              | none => false) = true := by
          simpa [hpermutation] using hrule
        let nextWord : ∀ gram, Matches word.toList gram →
            List TraceSymbol := fun gram hmatch =>
          (certificate.responseWord
            (gramWordOfMatch word gram hmatch)).toList
        have hresponse : ∀ gram (hmatch : Matches word.toList gram),
            ∃ rank, rank < layer ∧
              certificate.acceptsAt rank
                (certificate.responseWord
                  (gramWordOfMatch word gram hmatch)) = true ∧
              Matches (nextWord gram hmatch) gram := by
          intro gram hmatch
          let fixedGram := gramWordOfMatch word gram hmatch
          have hmem : fixedGram ∈ matchingGramWords word :=
            mem_matchingGramWords word fixedGram hmatch
          have hgramCheck := (List.all_eq_true.1 hchecks) fixedGram hmem
          cases hlookup : ClassicalCertificateResponseDag.lookup
              certificate.responseCode certificate.responseRoot
                fixedGram.toList with
          | none => simp [hlookup] at hgramCheck
          | some index =>
              by_cases hindex : index <
                  ClassicalCertificateResponseDag.valueBound
                    certificate.responseCode
              · cases hvalue : ClassicalCertificateResponseDag.valueAt?
                    certificate.responseCode index with
                | none => simp [hlookup, hindex, hvalue] at hgramCheck
                | some value =>
                    have hcheck' : decide (value.rank < layer) = true ∧
                        chromogramMatches []
                          (decodedTraceWord length value.wordCode).toList
                            fixedGram.toList = true := by
                      simpa [hlookup, hindex, hvalue] using hgramCheck
                    have hrank : value.rank < layer :=
                      of_decide_eq_true hcheck'.1
                    have hstored :=
                      certificate.responseTableBoolean_sound htable index
                        hindex value hvalue
                    have hresponseEq : certificate.responseWord fixedGram =
                        decodedTraceWord length value.wordCode := by
                      simp [responseWord, hlookup, hvalue]
                    refine ⟨value.rank, hrank, ?_, ?_⟩
                    · change certificate.acceptsAt value.rank
                          (certificate.responseWord fixedGram) = true
                      rw [hresponseEq]
                      exact hstored.2
                    · change Matches
                          (certificate.responseWord fixedGram).toList gram
                      rw [hresponseEq]
                      simpa [Matches, fixedGram, gramWordOfMatch] using
                        hcheck'.2
              · simp [hlookup, hindex] at hgramCheck
        refine .chromograms nextWord ?_ ?_
        · intro gram hmatch
          exact (hresponse gram hmatch).choose_spec.2.2
        · intro gram hmatch
          obtain ⟨rank, hrank, haccepted, hmatches⟩ :=
            hresponse gram hmatch
          simpa [nextWord] using priorSound rank hrank
            (certificate.responseWord
              (gramWordOfMatch word gram hmatch)) haccepted

/-- The indexed checker assembles all certified layers into finite Kempe
co-closure derivations. -/
theorem derivation_at_rank_of_checker_true
    (certificate : Certificate length)
    (hchecker : certificate.checker = true) (layer : Nat)
    (hlayer : layer < certificate.deltaRoots.length)
    (word : TraceWord length)
    (haccepted : certificate.acceptsAt layer word = true) :
    CoclosureDerivation certificate.ExtendableFamily word.toList := by
  have hparts : certificate.responseTableBoolean = true ∧
      (List.range certificate.deltaRoots.length).all
        certificate.layerBoolean = true := by
    simpa [checker] using hchecker
  induction layer using Nat.strong_induction_on generalizing word with
  | h layer ih =>
      have hlayerCheck := (List.all_eq_true.1 hparts.2) layer
        (List.mem_range.2 hlayer)
      have hrule := (List.all_eq_true.1 hlayerCheck) word
        ((ClassicalCertificateTraceDag.mem_acceptedWords_iff_accepts
          certificate.traceCode (certificate.rootAt layer) word).2 haccepted)
      apply certificate.derivation_of_ruleBoolean hparts.1 layer
        (word := word) (hrule := hrule)
      intro rank hrank priorWord hpriorAccepted
      exact ih rank hrank (Nat.lt_trans hrank hlayer) priorWord
        hpriorAccepted

theorem kempeCoclosure_at_rank_of_checker_true
    (certificate : Certificate length)
    (hchecker : certificate.checker = true) (layer : Nat)
    (hlayer : layer < certificate.deltaRoots.length)
    (word : TraceWord length)
    (haccepted : certificate.acceptsAt layer word = true) :
    KempeCoclosure certificate.ExtendableFamily word.toList :=
  (certificate.derivation_at_rank_of_checker_true hchecker layer hlayer word
    haccepted).sound

end Certificate

end ClassicalCertificateIndexedLayeredKempe

end Mettapedia.GraphTheory.FourColor
