import Mettapedia.GraphTheory.FourColor.CAP5BoundaryWord

/-!
# Y-cap boundary words on the five-ring

Besides the pentagon cap, the smaller disc completions available at a cyclic
five-edge-cut include the five Y-caps: one cubic vertex carrying three of
the ports and a direct cap joining the remaining two adjacent ports.  This
file records their boundary-word layer:

* the exact support of the Y-cap whose direct cap joins ports `i, i+1`;
* the `{3,1,1}` rigidity: over nonzero words with odd colour counts, the cap
  equality alone already characterizes the support — the three vertex ports
  are automatically a proper Tait triple;
* supports of Y-caps whose cap pairs are separated are disjoint.  This is
  why only three CONSECUTIVE Y-caps, together with the pentagon, drive the
  trivial-five-cut analysis: separated cap equalities would force colour
  counts `{2,2,1}`, which contradicts odd counts.
-/

namespace Mettapedia.GraphTheory.FourColor

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The exact boundary support of the Y-cap whose direct cap joins ports
`i` and `i + 1`: those two ports agree and are nonzero, and the three ports
on the cubic vertex form a proper Tait triple. -/
def CAP5YCapSupport (i : Fin 5) (w : CAP5BoundaryWord) : Prop :=
  w i = w (i + 1) ∧ w i ≠ 0 ∧
    IsTaitColorTriple (w (i + 2)) (w (i + 3)) (w (i + 4))

instance (i : Fin 5) (w : CAP5BoundaryWord) :
    Decidable (CAP5YCapSupport i w) := by
  unfold CAP5YCapSupport IsTaitColorTriple
  infer_instance

private instance : DecidablePred (Odd : Nat → Prop) := fun n =>
  decidable_of_iff (n % 2 = 1) Nat.odd_iff.symm

private instance (w : CAP5BoundaryWord) :
    Decidable (CAP5BoundaryWordIsNonzero w) := by
  unfold CAP5BoundaryWordIsNonzero
  infer_instance

private instance (w : CAP5BoundaryWord) :
    Decidable (CAP5BoundaryWordHasOddColorCounts w) := by
  unfold CAP5BoundaryWordHasOddColorCounts
  infer_instance

/-- Over admissible boundary words the cap equality alone characterizes the
Y-cap support: nonzero colours with odd counts force the three remaining
ports to carry the three distinct nonzero colours. -/
theorem cap5YCapSupport_iff_cap_eq :
    ∀ w : CAP5BoundaryWord, ∀ i : Fin 5,
      CAP5BoundaryWordIsNonzero w →
      CAP5BoundaryWordHasOddColorCounts w →
      (CAP5YCapSupport i w ↔ w i = w (i + 1)) := by
  decide

/-- Y-cap supports with separated cap pairs are disjoint: two disjoint cap
equalities would force colour counts `{2,2,1}`, contradicting odd counts. -/
theorem not_cap5YCapSupport_separated :
    ∀ w : CAP5BoundaryWord, ∀ i : Fin 5,
      CAP5BoundaryWordIsNonzero w →
      CAP5BoundaryWordHasOddColorCounts w →
      ¬ (CAP5YCapSupport i w ∧ CAP5YCapSupport (i + 2) w) := by
  decide

/-- Adjacent Y-cap supports meet exactly in the majority-run words. -/
theorem cap5YCapSupport_adjacent_iff_run :
    ∀ w : CAP5BoundaryWord, ∀ i : Fin 5,
      CAP5BoundaryWordIsNonzero w →
      CAP5BoundaryWordHasOddColorCounts w →
      ((CAP5YCapSupport i w ∧ CAP5YCapSupport (i + 1) w) ↔
        (w i = w (i + 1) ∧ w (i + 1) = w (i + 2))) := by
  decide

end Mettapedia.GraphTheory.FourColor
