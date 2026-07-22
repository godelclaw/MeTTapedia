import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitResponseMatching

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateOrbitResponseMatchingAggregate

open ClassicalCertificateIndexedLayeredKempe
open ClassicalCertificateKempeClosure
open ClassicalCertificateOrbitResponseMatching
open ClassicalCertificateResponseDag

variable {length : Nat}

/-- An empty response-dictionary branch has no spelling obligation. -/
theorem matchingBoolean_of_empty
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (remaining root : Nat) (reversePrefix : Chromogram)
    (hnode : ClassicalCertificateResponseDag.nodeAt
      certificate.responseCode root = .empty) :
    matchingBoolean certificate remaining root reversePrefix = true := by
  cases remaining <;> simp [matchingBoolean, hnode]

/-- One response-dictionary node combines exactly its four independently
checked child branches. -/
theorem matchingBoolean_succ_of_node
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (remaining root : Nat) (reversePrefix : Chromogram)
    (push skip popSame popOpposite : Nat)
    (hnode : ClassicalCertificateResponseDag.nodeAt
      certificate.responseCode root =
        .node push skip popSame popOpposite)
    (hpush : matchingBoolean certificate remaining push
      (.push :: reversePrefix) = true)
    (hskip : matchingBoolean certificate remaining skip
      (.skip :: reversePrefix) = true)
    (hpopSame : matchingBoolean certificate remaining popSame
      (.popSame :: reversePrefix) = true)
    (hpopOpposite : matchingBoolean certificate remaining popOpposite
      (.popOpposite :: reversePrefix) = true) :
    matchingBoolean certificate (remaining + 1) root reversePrefix = true := by
  simp [matchingBoolean, hnode, hpush, hskip, hpopSame, hpopOpposite]

end ClassicalCertificateOrbitResponseMatchingAggregate

end Mettapedia.GraphTheory.FourColor
