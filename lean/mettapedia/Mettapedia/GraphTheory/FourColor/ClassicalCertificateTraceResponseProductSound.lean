import Mettapedia.GraphTheory.FourColor.ClassicalCertificateTraceResponseProduct

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateTraceResponseProductSound

open ClassicalCertificateIndexedLayeredKempe
open ClassicalCertificateKempeClosure
open ClassicalCertificateRankedKempe
open ClassicalCertificateResponseDag
open ClassicalCertificateTraceDag
open ClassicalCertificateTraceResponseProduct
open ClassicalCertificateTraceTree

variable {length : Nat}

/-- Optional-root lookup, matching the optional response state used by the
source/response product. -/
def responseLookup? (code : ClassicalCertificateResponseDag.Code) :
    Option Nat → Chromogram → Option Nat
  | none, _ => none
  | some root, gram => ClassicalCertificateResponseDag.lookup code root gram

@[simp] theorem responseLookup?_cons
    (code : ClassicalCertificateResponseDag.Code) (root : Option Nat)
    (step : ChromogramStep) (gram : Chromogram) :
    responseLookup? code root (step :: gram) =
      responseLookup? code (responseChild? code root step) gram := by
  cases root with
  | none => rfl
  | some root =>
      cases hnode : ClassicalCertificateResponseDag.nodeAt code root <;>
        simp [responseLookup?, responseChild?,
          ClassicalCertificateResponseDag.lookup, hnode]

/-- A stack that can still close over a matching suffix has at most one open
entry per remaining symbol. -/
theorem stack_length_le_of_chromogramMatches
    {stack : List Bool} {word : List TraceSymbol} {gram : Chromogram}
    (hmatch : chromogramMatches stack word gram = true) :
    stack.length ≤ word.length := by
  induction word generalizing stack gram with
  | nil =>
      cases gram <;> cases stack <;>
        simp_all [chromogramMatches]
  | cons symbol word ih =>
      cases gram with
      | nil => simp [chromogramMatches] at hmatch
      | cons step gram =>
          cases hadvance : chromogramAdvance stack symbol step with
          | none => simp [chromogramMatches, hadvance] at hmatch
          | some nextStack =>
              have htail : chromogramMatches nextStack word gram = true := by
                simpa [chromogramMatches, hadvance] using hmatch
              have hbound := ih htail
              cases symbol <;> cases step <;> cases stack with
              | nil =>
                  simp [chromogramAdvance] at hadvance <;>
                    subst nextStack <;>
                    simp only [List.length_cons, List.length_nil] at hbound ⊢ <;>
                    omega
              | cons head tail =>
                  cases head <;>
                    simp [chromogramAdvance] at hadvance <;>
                    subst nextStack <;>
                    simp only [List.length_cons] at hbound ⊢ <;>
                    omega

/-- Selecting one word/chromogram transition selects the corresponding
conjunct of the product recursion. -/
private theorem productBoolean_red_child
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (layer remaining sourceRoot red blue purple : Nat)
    (responseRoot : Option Nat) (stack nextStack : List Bool)
    (step : ChromogramStep)
    (hstack : ¬stack.length > remaining + 1)
    (hsource : ClassicalCertificateTraceDag.nodeAt certificate.traceCode
      sourceRoot = .node red blue purple)
    (hadvance : chromogramAdvance stack .red step = some nextStack)
    (hproduct : productBoolean certificate layer (remaining + 1) sourceRoot
      responseRoot stack = true) :
    productBoolean certificate layer remaining red
      (responseChild? certificate.responseCode responseRoot step)
      nextStack = true := by
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
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (layer remaining sourceRoot red blue purple : Nat)
    (responseRoot : Option Nat) (stack nextStack : List Bool)
    (step : ChromogramStep)
    (hstack : ¬stack.length > remaining + 1)
    (hsource : ClassicalCertificateTraceDag.nodeAt certificate.traceCode
      sourceRoot = .node red blue purple)
    (hadvance : chromogramAdvance stack .blue step = some nextStack)
    (hproduct : productBoolean certificate layer (remaining + 1) sourceRoot
      responseRoot stack = true) :
    productBoolean certificate layer remaining blue
      (responseChild? certificate.responseCode responseRoot step)
      nextStack = true := by
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
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (layer remaining sourceRoot red blue purple : Nat)
    (responseRoot : Option Nat) (stack nextStack : List Bool)
    (step : ChromogramStep)
    (hstack : ¬stack.length > remaining + 1)
    (hsource : ClassicalCertificateTraceDag.nodeAt certificate.traceCode
      sourceRoot = .node red blue purple)
    (hadvance : chromogramAdvance stack .purple step = some nextStack)
    (hproduct : productBoolean certificate layer (remaining + 1) sourceRoot
      responseRoot stack = true) :
    productBoolean certificate layer remaining purple
      (responseChild? certificate.responseCode responseRoot step)
      nextStack = true := by
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

/-- A successful product traversal gives a genuine response leaf of strictly
smaller rank for every accepted source word in every matching chromogram
fiber.  Response-word semantics are deliberately factored into a separate
table theorem, so this result checks dictionary coverage only once. -/
theorem productBoolean_response
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (layer remaining sourceRoot : Nat) (responseRoot : Option Nat)
    (stack : List Bool) (word : List TraceSymbol) (gram : Chromogram)
    (hwordLength : word.length = remaining)
    (hgramLength : gram.length = remaining)
    (hproduct : productBoolean certificate layer remaining sourceRoot
      responseRoot stack = true)
    (haccepted : ClassicalCertificateTraceDag.accepts remaining
      certificate.traceCode sourceRoot word = true)
    (hmatch : chromogramMatches stack word gram = true) :
    ∃ index value,
      responseLookup? certificate.responseCode responseRoot gram = some index ∧
      index < ClassicalCertificateResponseDag.valueBound
        certificate.responseCode ∧
      ClassicalCertificateResponseDag.valueAt?
        certificate.responseCode index = some value ∧
      value.rank < layer := by
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
              cases hsource : ClassicalCertificateTraceDag.nodeAt
                  certificate.traceCode sourceRoot with
              | empty => simp [ClassicalCertificateTraceDag.accepts,
                  hsource] at haccepted
              | node red blue purple =>
                  simp [ClassicalCertificateTraceDag.accepts,
                    hsource] at haccepted
              | leaf =>
                  simp only [productBoolean, hsource] at hproduct
                  cases responseRoot with
                  | none => simp [responseLeafBoolean] at hproduct
                  | some responseRoot =>
                      cases hresponse : ClassicalCertificateResponseDag.nodeAt
                          certificate.responseCode responseRoot with
                      | empty => simp [responseLeafBoolean, hresponse] at hproduct
                      | node push skip popSame popOpposite =>
                          simp [responseLeafBoolean, hresponse] at hproduct
                      | leaf index =>
                          by_cases hindex : index <
                              ClassicalCertificateResponseDag.valueBound
                                certificate.responseCode
                          · cases hvalue : ClassicalCertificateResponseDag.valueAt?
                                certificate.responseCode index with
                            | none =>
                                simp [responseLeafBoolean, hresponse, hindex,
                                  hvalue] at hproduct
                            | some value =>
                                have hrank : value.rank < layer := by
                                  apply of_decide_eq_true
                                  simpa [responseLeafBoolean, hresponse, hindex,
                                    hvalue] using hproduct
                                exact ⟨index, value,
                                  by simp [responseLookup?,
                                    ClassicalCertificateResponseDag.lookup,
                                    hresponse],
                                  hindex, hvalue, hrank⟩
                          · simp [responseLeafBoolean, hresponse, hindex]
                              at hproduct
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
                have hbound := stack_length_le_of_chromogramMatches hmatch
                simp only [List.length_cons] at hbound
                omega
              cases hsource : ClassicalCertificateTraceDag.nodeAt
                  certificate.traceCode sourceRoot with
              | empty =>
                  simp [ClassicalCertificateTraceDag.accepts, hsource]
                    at haccepted
              | leaf =>
                  simp [ClassicalCertificateTraceDag.accepts, hsource]
                    at haccepted
              | node red blue purple =>
                  cases symbol with
                  | red =>
                      have htailAccepted :
                          ClassicalCertificateTraceDag.accepts remaining
                            certificate.traceCode red word = true := by
                        simpa [ClassicalCertificateTraceDag.accepts, hsource]
                          using haccepted
                      cases hadvance : chromogramAdvance stack .red step with
                      | none =>
                          simp [chromogramMatches, hadvance] at hmatch
                      | some nextStack =>
                          have htailMatch : chromogramMatches nextStack word
                              gram = true := by
                            simpa [chromogramMatches, hadvance] using hmatch
                          have htailProduct := productBoolean_red_child
                            certificate layer remaining sourceRoot red blue
                              purple responseRoot stack nextStack step hstack
                                hsource hadvance hproduct
                          obtain ⟨index, value, hlookup, hindex, hvalue,
                              hrank⟩ := ih red
                            (responseChild? certificate.responseCode responseRoot
                              step) nextStack word gram hwordTail hgramTail
                                htailProduct htailAccepted htailMatch
                          exact ⟨index, value, by simpa using hlookup,
                            hindex, hvalue, hrank⟩
                  | blue =>
                      have htailAccepted :
                          ClassicalCertificateTraceDag.accepts remaining
                            certificate.traceCode blue word = true := by
                        simpa [ClassicalCertificateTraceDag.accepts, hsource]
                          using haccepted
                      cases hadvance : chromogramAdvance stack .blue step with
                      | none =>
                          simp [chromogramMatches, hadvance] at hmatch
                      | some nextStack =>
                          have htailMatch : chromogramMatches nextStack word
                              gram = true := by
                            simpa [chromogramMatches, hadvance] using hmatch
                          have htailProduct := productBoolean_blue_child
                            certificate layer remaining sourceRoot red blue
                              purple responseRoot stack nextStack step hstack
                                hsource hadvance hproduct
                          obtain ⟨index, value, hlookup, hindex, hvalue,
                              hrank⟩ := ih blue
                            (responseChild? certificate.responseCode responseRoot
                              step) nextStack word gram hwordTail hgramTail
                                htailProduct htailAccepted htailMatch
                          exact ⟨index, value, by simpa using hlookup,
                            hindex, hvalue, hrank⟩
                  | purple =>
                      have htailAccepted :
                          ClassicalCertificateTraceDag.accepts remaining
                            certificate.traceCode purple word = true := by
                        simpa [ClassicalCertificateTraceDag.accepts, hsource]
                          using haccepted
                      cases hadvance : chromogramAdvance stack .purple step with
                      | none =>
                          simp [chromogramMatches, hadvance] at hmatch
                      | some nextStack =>
                          have htailMatch : chromogramMatches nextStack word
                              gram = true := by
                            simpa [chromogramMatches, hadvance] using hmatch
                          have htailProduct := productBoolean_purple_child
                            certificate layer remaining sourceRoot red blue
                              purple responseRoot stack nextStack step hstack
                                hsource hadvance hproduct
                          obtain ⟨index, value, hlookup, hindex, hvalue,
                              hrank⟩ := ih purple
                            (responseChild? certificate.responseCode responseRoot
                              step) nextStack word gram hwordTail hgramTail
                                htailProduct htailAccepted htailMatch
                          exact ⟨index, value, by simpa using hlookup,
                            hindex, hvalue, hrank⟩

end ClassicalCertificateTraceResponseProductSound

end Mettapedia.GraphTheory.FourColor
