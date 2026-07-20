import Mettapedia.GraphTheory.FourColor.ClassicalCertificateIndexedLayeredKempe
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateResponseTree

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateTreeIndexedLayeredKempe

open ClassicalCertificateIndexedLayeredKempe
open ClassicalCertificateKempeClosure
open ClassicalCertificateRankedKempe
open ClassicalCertificateResponseDag
open ClassicalCertificateResponseTree
open ClassicalCertificateTraceDag
open ClassicalCertificateTraceTree

variable {length : Nat}

def responseWord (certificate :
    ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (tree : ClassicalCertificateResponseTree.Tree)
    (gram : GramWord length) : TraceWord length :=
  match ClassicalCertificateResponseTree.lookup tree gram.toList with
  | some index =>
      match ClassicalCertificateResponseDag.valueAt?
          certificate.responseCode index with
      | some value => decodedTraceWord length value.wordCode
      | none => decodedTraceWord length 0
  | none => decodedTraceWord length 0

def ruleBoolean (certificate :
    ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (tree : ClassicalCertificateResponseTree.Tree) (layer : Nat)
    (word : TraceWord length) : Bool :=
  if certificate.acceptsExtendable word then true
  else
    match certificate.previousPermutation? layer word with
    | some _ => true
    | none =>
        (matchingGramWords word).all fun gram =>
          match ClassicalCertificateResponseTree.lookup tree gram.toList with
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

def layerBoolean (certificate :
    ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (tree : ClassicalCertificateResponseTree.Tree) (layer : Nat) : Bool :=
  (ClassicalCertificateTraceDag.acceptedWords length certificate.traceCode
    (certificate.rootAt layer)).all (ruleBoolean certificate tree layer)

def sourceBoolean (certificate :
    ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (tree : ClassicalCertificateResponseTree.Tree) : Bool :=
  (List.range certificate.deltaRoots.length).all
    (layerBoolean certificate tree)

private def gramWordOfMatch (word : TraceWord length) (gram : Chromogram)
    (hmatch : Matches word.toList gram) : GramWord length :=
  ⟨gram, hmatch.length_eq.symm.trans word.2⟩

/-- A direct-tree source rule composes with all strictly lower layers. -/
theorem derivation_of_ruleBoolean (certificate :
    ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (tree : ClassicalCertificateResponseTree.Tree)
    (htable : certificate.responseTableBoolean = true) (layer : Nat)
    (priorSound : ∀ rank, rank < layer → ∀ word : TraceWord length,
      certificate.acceptsAt rank word = true →
        CoclosureDerivation certificate.ExtendableFamily word.toList)
    (word : TraceWord length)
    (hrule : ruleBoolean certificate tree layer word = true) :
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
              match ClassicalCertificateResponseTree.lookup tree
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
          (responseWord certificate tree
            (gramWordOfMatch word gram hmatch)).toList
        have hresponse : ∀ gram (hmatch : Matches word.toList gram),
            ∃ rank, rank < layer ∧
              certificate.acceptsAt rank
                (responseWord certificate tree
                  (gramWordOfMatch word gram hmatch)) = true ∧
              Matches (nextWord gram hmatch) gram := by
          intro gram hmatch
          let fixedGram := gramWordOfMatch word gram hmatch
          have hmem : fixedGram ∈ matchingGramWords word :=
            mem_matchingGramWords word fixedGram hmatch
          have hgramCheck := (List.all_eq_true.1 hchecks) fixedGram hmem
          cases hlookup : ClassicalCertificateResponseTree.lookup tree
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
                    have hstored := certificate.responseTableBoolean_sound
                      htable index hindex value hvalue
                    have hresponseEq :
                        responseWord certificate tree fixedGram =
                          decodedTraceWord length value.wordCode := by
                      simp [responseWord, hlookup, hvalue]
                    refine ⟨value.rank, hrank, ?_, ?_⟩
                    · change certificate.acceptsAt value.rank
                          (responseWord certificate tree fixedGram) = true
                      rw [hresponseEq]
                      exact hstored.2
                    · change Matches
                          (responseWord certificate tree fixedGram).toList gram
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
            (responseWord certificate tree
              (gramWordOfMatch word gram hmatch)) haccepted

/-- The direct-tree source audit and the separately validated response table
assemble into ordinary Kempe co-closure derivations. -/
theorem derivation_at_rank_of_checks
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (tree : ClassicalCertificateResponseTree.Tree)
    (htable : certificate.responseTableBoolean = true)
    (hsource : sourceBoolean certificate tree = true)
    (layer : Nat) (hlayer : layer < certificate.deltaRoots.length)
    (word : TraceWord length)
    (haccepted : certificate.acceptsAt layer word = true) :
    CoclosureDerivation certificate.ExtendableFamily word.toList := by
  induction layer using Nat.strong_induction_on generalizing word with
  | h layer ih =>
      have hlayerCheck := (List.all_eq_true.1 hsource) layer
        (List.mem_range.2 hlayer)
      have hrule := (List.all_eq_true.1 hlayerCheck) word
        ((ClassicalCertificateTraceDag.mem_acceptedWords_iff_accepts
          certificate.traceCode (certificate.rootAt layer) word).2 haccepted)
      apply derivation_of_ruleBoolean certificate tree htable layer
        (word := word) (hrule := hrule)
      intro rank hrank priorWord hpriorAccepted
      exact ih rank hrank (Nat.lt_trans hrank hlayer) priorWord
        hpriorAccepted

theorem kempeCoclosure_at_rank_of_checks
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (tree : ClassicalCertificateResponseTree.Tree)
    (htable : certificate.responseTableBoolean = true)
    (hsource : sourceBoolean certificate tree = true)
    (layer : Nat) (hlayer : layer < certificate.deltaRoots.length)
    (word : TraceWord length)
    (haccepted : certificate.acceptsAt layer word = true) :
    KempeCoclosure certificate.ExtendableFamily word.toList :=
  (derivation_at_rank_of_checks certificate tree htable hsource layer hlayer
    word haccepted).sound

end ClassicalCertificateTreeIndexedLayeredKempe

end Mettapedia.GraphTheory.FourColor
