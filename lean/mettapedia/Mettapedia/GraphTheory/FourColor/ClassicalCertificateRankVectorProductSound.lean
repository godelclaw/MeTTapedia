import Mettapedia.GraphTheory.FourColor.ClassicalCertificateRankVectorProduct
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateTraceResponseProductSound

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateRankVectorProductSound

open ClassicalCertificateKempeClosure
open ClassicalCertificatePackedRankVector
open ClassicalCertificateRankVectorDag
open ClassicalCertificateRankVectorProduct
open ClassicalCertificateRankedKempe
open ClassicalCertificateTraceTree

variable {length : Nat}

set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000

/-- Selecting one word/chromogram transition selects the corresponding
conjunct of the rank-vector product recursion. -/
private theorem productBoolean_red_child
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length)
    (remaining sourceRoot red blue purple : Nat)
    (responseRoot : Option Nat) (stack nextStack : List Bool)
    (step : ChromogramStep)
    (hstack : ¬stack.length > remaining + 1)
    (hsource : certificate.traceCode.nodeAt sourceRoot =
      TraceNodeCode.node red blue purple)
    (hadvance : chromogramAdvance stack .red step = some nextStack)
    (hproduct : productBoolean certificate (remaining + 1) sourceRoot
      responseRoot stack = true) :
    productBoolean certificate remaining red
      (certificate.responseCode.child? responseRoot step) nextStack = true := by
  cases step <;> cases stack with
  | nil =>
      simp [chromogramAdvance] at hadvance <;>
        subst nextStack <;>
        simp [productBoolean, hsource] at hproduct <;>
        aesop
  | cons head tail =>
      have htail : ¬remaining < tail.length := by
        simp only [List.length_cons] at hstack
        omega
      cases head <;>
        simp [chromogramAdvance] at hadvance <;>
        subst nextStack <;>
        simp [productBoolean, htail, hsource] at hproduct <;>
        aesop

private theorem productBoolean_blue_child
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length)
    (remaining sourceRoot red blue purple : Nat)
    (responseRoot : Option Nat) (stack nextStack : List Bool)
    (step : ChromogramStep)
    (hstack : ¬stack.length > remaining + 1)
    (hsource : certificate.traceCode.nodeAt sourceRoot =
      TraceNodeCode.node red blue purple)
    (hadvance : chromogramAdvance stack .blue step = some nextStack)
    (hproduct : productBoolean certificate (remaining + 1) sourceRoot
      responseRoot stack = true) :
    productBoolean certificate remaining blue
      (certificate.responseCode.child? responseRoot step) nextStack = true := by
  cases step <;> cases stack with
  | nil =>
      simp [chromogramAdvance] at hadvance <;>
        subst nextStack <;>
        simp [productBoolean, hsource] at hproduct <;>
        aesop
  | cons head tail =>
      have htail : ¬remaining < tail.length := by
        simp only [List.length_cons] at hstack
        omega
      cases head <;>
        simp [chromogramAdvance] at hadvance <;>
        subst nextStack <;>
        simp [productBoolean, htail, hsource] at hproduct <;>
        aesop

private theorem productBoolean_purple_child
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length)
    (remaining sourceRoot red blue purple : Nat)
    (responseRoot : Option Nat) (stack nextStack : List Bool)
    (step : ChromogramStep)
    (hstack : ¬stack.length > remaining + 1)
    (hsource : certificate.traceCode.nodeAt sourceRoot =
      TraceNodeCode.node red blue purple)
    (hadvance : chromogramAdvance stack .purple step = some nextStack)
    (hproduct : productBoolean certificate (remaining + 1) sourceRoot
      responseRoot stack = true) :
    productBoolean certificate remaining purple
      (certificate.responseCode.child? responseRoot step) nextStack = true := by
  cases step <;> cases stack with
  | nil =>
      simp [chromogramAdvance] at hadvance <;>
        subst nextStack <;>
        simp [productBoolean, hsource] at hproduct <;>
        aesop
  | cons head tail =>
      have htail : ¬remaining < tail.length := by
        simp only [List.length_cons] at hstack
        omega
      cases head <;>
        simp [chromogramAdvance] at hadvance <;>
        subst nextStack <;>
        simp [productBoolean, htail, hsource] at hproduct <;>
        aesop

/-- Every accepted source/chromogram path in a successful product reaches a
response vector satisfying the packed pointwise descent check. -/
theorem productBoolean_response
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length)
    (remaining sourceRoot sourceVector : Nat)
    (responseRoot : Option Nat) (stack : List Bool)
    (word : List TraceSymbol) (gram : Chromogram)
    (hwordLength : word.length = remaining)
    (hgramLength : gram.length = remaining)
    (hproduct : productBoolean certificate remaining sourceRoot
      responseRoot stack = true)
    (haccepted : certificate.traceCode.lookup remaining sourceRoot word =
      some sourceVector)
    (hmatch : chromogramMatches stack word gram = true) :
    ∃ responseVector,
      certificate.responseCode.lookup? responseRoot gram =
        some responseVector ∧
      respondsBoolean certificate.ranks sourceVector responseVector = true := by
  induction remaining generalizing sourceRoot responseRoot stack word gram with
  | zero =>
      cases word with
      | cons symbol word => simp at hwordLength
      | nil =>
          cases gram with
          | cons step gram => simp at hgramLength
          | nil =>
              have hstack : stack = [] := by
                cases stack <;> simp_all [chromogramMatches]
              subst stack
              cases hsource : certificate.traceCode.nodeAt sourceRoot with
              | empty => simp [TraceCode.lookup, hsource] at haccepted
              | node red blue purple =>
                  simp [TraceCode.lookup, hsource] at haccepted
              | leaf storedSourceVector =>
                  have hsourceVector : storedSourceVector = sourceVector := by
                    simpa [TraceCode.lookup, hsource] using haccepted
                  subst storedSourceVector
                  simp only [productBoolean, hsource] at hproduct
                  cases responseRoot with
                  | none => simp [responseLeafBoolean] at hproduct
                  | some responseRoot =>
                      cases hresponse : certificate.responseCode.nodeAt
                          responseRoot with
                      | empty =>
                          simp [responseLeafBoolean, hresponse] at hproduct
                      | node push skip popSame popOpposite =>
                          simp [responseLeafBoolean, hresponse] at hproduct
                      | leaf responseVector =>
                          exact ⟨responseVector,
                            by simp [ResponseCode.lookup?, ResponseCode.lookup,
                              hresponse],
                            by simpa [responseLeafBoolean, hresponse] using
                              hproduct⟩
  | succ remaining ih =>
      cases word with
      | nil => simp at hwordLength
      | cons symbol word =>
          cases gram with
          | nil => simp at hgramLength
          | cons step gram =>
              have hwordTail : word.length = remaining :=
                Nat.succ.inj hwordLength
              have hgramTail : gram.length = remaining :=
                Nat.succ.inj hgramLength
              have hstack : ¬stack.length > remaining + 1 := by
                have hbound :=
                  ClassicalCertificateTraceResponseProductSound.stack_length_le_of_chromogramMatches
                    hmatch
                simp only [List.length_cons] at hbound
                omega
              cases hsource : certificate.traceCode.nodeAt sourceRoot with
              | empty => simp [TraceCode.lookup, hsource] at haccepted
              | leaf rankVector =>
                  simp [TraceCode.lookup, hsource] at haccepted
              | node red blue purple =>
                  cases symbol with
                  | red =>
                      have htailAccepted :
                          certificate.traceCode.lookup remaining red word =
                            some sourceVector := by
                        simpa [TraceCode.lookup, hsource] using haccepted
                      cases hadvance : chromogramAdvance stack .red step with
                      | none => simp [chromogramMatches, hadvance] at hmatch
                      | some nextStack =>
                          have htailMatch : chromogramMatches nextStack word
                              gram = true := by
                            simpa [chromogramMatches, hadvance] using hmatch
                          have htailProduct := productBoolean_red_child
                            certificate remaining sourceRoot red blue purple
                              responseRoot stack nextStack step hstack hsource
                                hadvance hproduct
                          obtain ⟨responseVector, hlookup, hresponds⟩ :=
                            ih red (certificate.responseCode.child?
                              responseRoot step) nextStack word gram hwordTail
                                hgramTail htailProduct htailAccepted htailMatch
                          exact ⟨responseVector, by simpa using hlookup,
                            hresponds⟩
                  | blue =>
                      have htailAccepted :
                          certificate.traceCode.lookup remaining blue word =
                            some sourceVector := by
                        simpa [TraceCode.lookup, hsource] using haccepted
                      cases hadvance : chromogramAdvance stack .blue step with
                      | none => simp [chromogramMatches, hadvance] at hmatch
                      | some nextStack =>
                          have htailMatch : chromogramMatches nextStack word
                              gram = true := by
                            simpa [chromogramMatches, hadvance] using hmatch
                          have htailProduct := productBoolean_blue_child
                            certificate remaining sourceRoot red blue purple
                              responseRoot stack nextStack step hstack hsource
                                hadvance hproduct
                          obtain ⟨responseVector, hlookup, hresponds⟩ :=
                            ih blue (certificate.responseCode.child?
                              responseRoot step) nextStack word gram hwordTail
                                hgramTail htailProduct htailAccepted htailMatch
                          exact ⟨responseVector, by simpa using hlookup,
                            hresponds⟩
                  | purple =>
                      have htailAccepted :
                          certificate.traceCode.lookup remaining purple word =
                            some sourceVector := by
                        simpa [TraceCode.lookup, hsource] using haccepted
                      cases hadvance : chromogramAdvance stack .purple step with
                      | none => simp [chromogramMatches, hadvance] at hmatch
                      | some nextStack =>
                          have htailMatch : chromogramMatches nextStack word
                              gram = true := by
                            simpa [chromogramMatches, hadvance] using hmatch
                          have htailProduct := productBoolean_purple_child
                            certificate remaining sourceRoot red blue purple
                              responseRoot stack nextStack step hstack hsource
                                hadvance hproduct
                          obtain ⟨responseVector, hlookup, hresponds⟩ :=
                            ih purple (certificate.responseCode.child?
                              responseRoot step) nextStack word gram hwordTail
                                hgramTail htailProduct htailAccepted htailMatch
                          exact ⟨responseVector, by simpa using hlookup,
                            hresponds⟩

/-- A checked rank-vector product supplies a strictly lower response rank for
every active configuration and every matching chromogram. -/
theorem certificate_response_rank_lt_of_checker_true
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length)
    (hchecker : certificate.checker = true)
    (word : TraceWord length) (sourceVector config sourceRank : Nat)
    (haccepted : certificate.traceCode.lookup length certificate.sourceRoot
      word.toList = some sourceVector)
    (hconfig : config < certificate.ranks.configCount)
    (hsourceRank : certificate.ranks.rankAt? sourceVector config =
      some sourceRank)
    (gram : GramWord length)
    (hmatch : Matches word.toList gram.toList) :
    0 < sourceRank ∧
      ∃ responseVector responseRank,
        certificate.responseCode.lookup certificate.responseRoot gram.toList =
          some responseVector ∧
        certificate.ranks.rankAt? responseVector config = some responseRank ∧
        responseRank < sourceRank := by
  obtain ⟨responseVector, hlookup, hresponds⟩ :=
    productBoolean_response certificate length certificate.sourceRoot
      sourceVector (some certificate.responseRoot) [] word.toList gram.toList
        word.2 gram.2 hchecker haccepted hmatch
  have hlocal := respondsBoolean_sound certificate.ranks sourceVector
    responseVector hresponds
  obtain ⟨hpositive, responseRank, hresponseRank, hlower⟩ :=
    hlocal.2.2 config sourceRank hconfig hsourceRank
  exact ⟨hpositive, responseVector, responseRank,
    by simpa [ResponseCode.lookup?] using hlookup,
    hresponseRank, hlower⟩

end ClassicalCertificateRankVectorProductSound

end Mettapedia.GraphTheory.FourColor
