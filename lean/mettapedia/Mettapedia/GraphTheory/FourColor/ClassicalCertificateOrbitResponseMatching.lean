import Mettapedia.GraphTheory.FourColor.ClassicalCertificateIndexedLayeredKempe

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateOrbitResponseMatching

open ClassicalCertificateIndexedLayeredKempe
open ClassicalCertificateKempeClosure
open ClassicalCertificateResponseDag

variable {length : Nat}

/-- Check the semantic spelling attached to every response-dictionary leaf
below one node.  The reversed prefix makes each recursive extension constant
time; only leaves reverse it to recover the chromogram in traversal order. -/
def matchingBoolean
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length) :
    Nat → Nat → Chromogram → Bool
  | 0, root, reversePrefix =>
      match ClassicalCertificateResponseDag.nodeAt
          certificate.responseCode root with
      | .leaf index =>
          if index < ClassicalCertificateResponseDag.valueBound
              certificate.responseCode then
            match ClassicalCertificateResponseDag.valueAt?
                certificate.responseCode index with
            | some value =>
                chromogramMatches []
                  (ClassicalCertificateResponseDag.decodedTraceWord
                    length value.wordCode).toList reversePrefix.reverse
            | none => false
          else false
      | _ => true
  | remaining + 1, root, reversePrefix =>
      match ClassicalCertificateResponseDag.nodeAt
          certificate.responseCode root with
      | .node push skip popSame popOpposite =>
          matchingBoolean certificate remaining push
              (.push :: reversePrefix) &&
            matchingBoolean certificate remaining skip
              (.skip :: reversePrefix) &&
            matchingBoolean certificate remaining popSame
              (.popSame :: reversePrefix) &&
            matchingBoolean certificate remaining popOpposite
              (.popOpposite :: reversePrefix)
      | _ => true

def checker
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length) :
    Bool :=
  matchingBoolean certificate length certificate.responseRoot []

/-- A checked response trie spells, at every reachable leaf, a word in the
same chromogram fiber as the key leading to that leaf. -/
theorem matchingBoolean_sound
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (remaining root : Nat) (reversePrefix gram : Chromogram)
    (index : Nat) (value : ClassicalCertificateResponseDag.ValueCode)
    (hcheck : matchingBoolean certificate remaining root reversePrefix = true)
    (hlength : gram.length = remaining)
    (hlookup : ClassicalCertificateResponseDag.lookup
      certificate.responseCode root gram = some index)
    (hvalue : ClassicalCertificateResponseDag.valueAt?
      certificate.responseCode index = some value) :
    chromogramMatches []
      (ClassicalCertificateResponseDag.decodedTraceWord
        length value.wordCode).toList
      (reversePrefix.reverse ++ gram) = true := by
  induction remaining generalizing root reversePrefix gram with
  | zero =>
      have hgram : gram = [] := by simpa using hlength
      subst gram
      cases hnode : ClassicalCertificateResponseDag.nodeAt
          certificate.responseCode root with
      | empty =>
          simp [ClassicalCertificateResponseDag.lookup, hnode] at hlookup
      | node push skip popSame popOpposite =>
          simp [ClassicalCertificateResponseDag.lookup, hnode] at hlookup
      | leaf storedIndex =>
          have hindexEq : storedIndex = index := by
            have hsome : some storedIndex = some index := by
              simpa [ClassicalCertificateResponseDag.lookup, hnode] using
                hlookup
            exact Option.some.inj hsome
          subst storedIndex
          by_cases hbound : index <
              ClassicalCertificateResponseDag.valueBound
                certificate.responseCode
          · simpa [matchingBoolean, hnode, hbound, hvalue] using hcheck
          · simp [matchingBoolean, hnode, hbound] at hcheck
  | succ remaining ih =>
      cases gram with
      | nil => simp at hlength
      | cons step gram =>
          have htailLength : gram.length = remaining :=
            Nat.succ.inj hlength
          cases hnode : ClassicalCertificateResponseDag.nodeAt
              certificate.responseCode root with
          | empty =>
              simp [ClassicalCertificateResponseDag.lookup, hnode] at hlookup
          | leaf storedIndex =>
              simp [ClassicalCertificateResponseDag.lookup, hnode] at hlookup
          | node push skip popSame popOpposite =>
              have htailCheck : matchingBoolean certificate remaining
                  (ClassicalCertificateResponseDag.child push skip popSame
                    popOpposite step) (step :: reversePrefix) = true := by
                cases step <;>
                  simp_all [matchingBoolean, hnode,
                    ClassicalCertificateResponseDag.child]
              have htailLookup : ClassicalCertificateResponseDag.lookup
                  certificate.responseCode
                    (ClassicalCertificateResponseDag.child push skip popSame
                      popOpposite step) gram = some index := by
                simpa [ClassicalCertificateResponseDag.lookup, hnode] using
                  hlookup
              have htailSound := ih
                (ClassicalCertificateResponseDag.child push skip popSame
                  popOpposite step) (step :: reversePrefix) gram htailCheck
                    htailLength htailLookup
              simpa using htailSound

theorem checker_sound
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (hchecker : checker certificate = true)
    (gram : Chromogram) (hgramLength : gram.length = length)
    (index : Nat) (value : ClassicalCertificateResponseDag.ValueCode)
    (hlookup : ClassicalCertificateResponseDag.lookup
      certificate.responseCode certificate.responseRoot gram = some index)
    (hvalue : ClassicalCertificateResponseDag.valueAt?
      certificate.responseCode index = some value) :
    Matches
      (ClassicalCertificateResponseDag.decodedTraceWord
        length value.wordCode).toList gram := by
  simpa [checker, Matches] using
    matchingBoolean_sound certificate length certificate.responseRoot [] gram
      index value hchecker hgramLength hlookup hvalue

end ClassicalCertificateOrbitResponseMatching

end Mettapedia.GraphTheory.FourColor
