import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitResponseMatching
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitResponseTable
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateTraceResponseProductSound

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateOrbitLayeredKempe

open ClassicalCertificateIndexedLayeredKempe
open ClassicalCertificateKempeClosure
open ClassicalCertificateOrbitResponseMatching
open ClassicalCertificateOrbitResponseTable
open ClassicalCertificateRankedKempe
open ClassicalCertificateResponseDag
open ClassicalCertificateTraceResponseProduct
open ClassicalCertificateTraceResponseProductSound
open ClassicalCertificateTraceTree

variable {length : Nat}

private def gramWordOfMatch (word : TraceWord length) (gram : Chromogram)
    (hmatch : Matches word.toList gram) : GramWord length :=
  ⟨gram, hmatch.length_eq.symm.trans word.2⟩

/-- The three independent certificate factors combine at one source word:
the product supplies a lower rank, the response trie supplies the same-fiber
spelling, and the orbit table supplies membership after one global color
permutation. -/
theorem responseWord_of_layerBoolean
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (hmatching : ClassicalCertificateOrbitResponseMatching.checker
      certificate = true)
    (hvalues : responseValueTableBoolean certificate = true)
    (layer : Nat)
    (hlayer : ClassicalCertificateTraceResponseProduct.layerBoolean
      certificate layer = true)
    (word : TraceWord length)
    (haccepted : certificate.acceptsAt layer word = true)
    (gram : Chromogram) (hmatch : Matches word.toList gram) :
    ∃ rank permutation,
      rank < layer ∧
      Matches
        (certificate.responseWord
          (gramWordOfMatch word gram hmatch)).toList gram ∧
      certificate.acceptsAt rank
        (permute permutation
          (certificate.responseWord
            (gramWordOfMatch word gram hmatch))) = true := by
  let fixedGram := gramWordOfMatch word gram hmatch
  have hfixedGramList : fixedGram.toList = gram := rfl
  have hgramLength : gram.length = length := by
    simpa [fixedGram, gramWordOfMatch] using fixedGram.2
  have hproduct : productBoolean certificate layer length
      (certificate.rootAt layer) (some certificate.responseRoot) [] = true := by
    simpa [ClassicalCertificateTraceResponseProduct.layerBoolean] using hlayer
  obtain ⟨index, value, hlookup, hindex, hvalue, hrank⟩ :=
    productBoolean_response certificate layer length
      (certificate.rootAt layer) (some certificate.responseRoot) []
        word.toList gram word.2 hgramLength hproduct haccepted hmatch
  have hlookup' : ClassicalCertificateResponseDag.lookup
      certificate.responseCode certificate.responseRoot gram = some index := by
    simpa [responseLookup?] using hlookup
  have hresponseEq : certificate.responseWord fixedGram =
      ClassicalCertificateResponseDag.decodedTraceWord
        length value.wordCode := by
    unfold Certificate.responseWord
    rw [hfixedGramList, hlookup']
    simp [hvalue]
  have hsameFiber : Matches
      (ClassicalCertificateResponseDag.decodedTraceWord
        length value.wordCode).toList gram :=
    ClassicalCertificateOrbitResponseMatching.checker_sound certificate
      hmatching gram hgramLength index value hlookup' hvalue
  obtain ⟨permutation, hpermutation⟩ :=
    responseValueTableBoolean_sound certificate hvalues index hindex value
      hvalue
  refine ⟨value.rank, permutation, hrank, ?_, ?_⟩
  · rw [hresponseEq]
    exact hsameFiber
  · rw [hresponseEq]
    exact hpermutation

/-- Orbit-reduced product layers still assemble into ordinary finite Kempe
co-closure derivations.  Rank zero is the extendable language; every positive
rank uses all matching planar chromograms and descends strictly. -/
theorem derivation_at_rank
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (hbase : certificate.rootAt 0 = certificate.extendableRoot)
    (hmatching : ClassicalCertificateOrbitResponseMatching.checker
      certificate = true)
    (hvalues : responseValueTableBoolean certificate = true)
    (hlayers : ∀ layer, 0 < layer →
      layer < certificate.deltaRoots.length →
      ClassicalCertificateTraceResponseProduct.layerBoolean
        certificate layer = true)
    (layer : Nat) (hlayer : layer < certificate.deltaRoots.length)
    (word : TraceWord length)
    (haccepted : certificate.acceptsAt layer word = true) :
    CoclosureDerivation certificate.ExtendableFamily word.toList := by
  induction layer using Nat.strong_induction_on generalizing word with
  | h layer ih =>
      cases layer with
      | zero =>
          apply CoclosureDerivation.member
          exact ⟨word, rfl, by
            simpa [Certificate.acceptsAt, Certificate.acceptsExtendable,
              hbase] using haccepted⟩
      | succ priorLayer =>
          have hlayerPositive : 0 < priorLayer + 1 := Nat.succ_pos _
          have hlayerBoolean := hlayers (priorLayer + 1) hlayerPositive hlayer
          let nextWord : ∀ gram, Matches word.toList gram →
              List TraceSymbol := fun gram hmatch =>
            (certificate.responseWord
              (gramWordOfMatch word gram hmatch)).toList
          apply CoclosureDerivation.chromograms nextWord
          · intro gram hmatch
            obtain ⟨rank, permutation, hrank, hsameFiber, hacceptedNext⟩ :=
              responseWord_of_layerBoolean certificate hmatching hvalues
                (priorLayer + 1) hlayerBoolean word haccepted gram hmatch
            simpa [nextWord] using hsameFiber
          · intro gram hmatch
            obtain ⟨rank, permutation, hrank, hsameFiber, hacceptedNext⟩ :=
              responseWord_of_layerBoolean certificate hmatching hvalues
                (priorLayer + 1) hlayerBoolean word haccepted gram hmatch
            have hnext := ih rank hrank (Nat.lt_trans hrank hlayer)
              (permute permutation
                (certificate.responseWord
                  (gramWordOfMatch word gram hmatch))) hacceptedNext
            exact CoclosureDerivation.permutation permutation.toEquiv (by
              simpa [nextWord] using hnext)

theorem kempeCoclosure_at_rank
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (hbase : certificate.rootAt 0 = certificate.extendableRoot)
    (hmatching : ClassicalCertificateOrbitResponseMatching.checker
      certificate = true)
    (hvalues : responseValueTableBoolean certificate = true)
    (hlayers : ∀ layer, 0 < layer →
      layer < certificate.deltaRoots.length →
      ClassicalCertificateTraceResponseProduct.layerBoolean
        certificate layer = true)
    (layer : Nat) (hlayer : layer < certificate.deltaRoots.length)
    (word : TraceWord length)
    (haccepted : certificate.acceptsAt layer word = true) :
    KempeCoclosure certificate.ExtendableFamily word.toList :=
  (derivation_at_rank certificate hbase hmatching hvalues hlayers layer hlayer
    word haccepted).sound

end ClassicalCertificateOrbitLayeredKempe

end Mettapedia.GraphTheory.FourColor
