import KrennCollapseComponentContainmentCertificateSegment00

/-!
A kernel-checked mutation gate for the component label carried by a concrete
containment certificate.

The masks and witnesses below are the first certificate in segment zero.
Only its component label is changed, from component 38 to component 26.
The unchanged witness list has fourteen entries, whereas component 26 has
fifty-four generators, so the aligned certificate validity predicate rejects
the mutation.
-/

namespace Krenn.CollapseComponentContainmentMutationGate

open Krenn.CollapseComponentContainment

/-- A deliberately malformed copy of the first segment-zero certificate:
only the in-range component label has been changed. -/
def malformed : StratumCertificate :=
  { stratum :=
      { activeMask := 0
        zeroMask := 18079727
        component := 26 }
    witnesses :=
      [.killed 17 (some 0), .killed 12 (some 5), .killed 8 (some 9),
       .killed 3 (some 14), .killed 24 (some 14), .killed 20 (some 9),
       .killed 16 (some 15), .killed 15 none, .killed 11 (some 10),
       .killed 10 none, .killed 7 none, .killed 6 none, .killed 2 none,
       .killed 1 none] }

/-- The component-only mutation is rejected by the finite validity
predicate itself. -/
theorem malformed_rejected : ¬ malformed.Valid := by
  decide

/-- A stronger component-label mutation: row 32 has the same number of
generators as row 38, so rejection cannot follow from list length alone. -/
def malformedSameLength : StratumCertificate :=
  { stratum :=
      { activeMask := 0
        zeroMask := 18079727
        component := 32 }
    witnesses :=
      [.killed 17 (some 0), .killed 12 (some 5), .killed 8 (some 9),
       .killed 3 (some 14), .killed 24 (some 14), .killed 20 (some 9),
       .killed 16 (some 15), .killed 15 none, .killed 11 (some 10),
       .killed 10 none, .killed 7 none, .killed 6 none, .killed 2 none,
       .killed 1 none] }

/-- Component identity is checked by witness content, not merely by arity. -/
theorem malformed_same_length_rejected : ¬ malformedSameLength.Valid := by
  decide

end Krenn.CollapseComponentContainmentMutationGate

#print axioms Krenn.CollapseComponentContainmentMutationGate.malformed_rejected
#print axioms
  Krenn.CollapseComponentContainmentMutationGate.malformed_same_length_rejected
