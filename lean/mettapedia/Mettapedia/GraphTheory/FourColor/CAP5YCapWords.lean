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

/-! ## The menu-preserving reflection and colour equivariance -/

/-- The reflection `i ↦ 3 - i` of the five ports.  It fixes the middle Y-cap
pair `(1,2)`, swaps the cap pairs `(0,1)` and `(2,3)`, and preserves the
pentagon support, so it is the reflection symmetry of the trivial-five-cut
menu `{P5, Y₀, Y₁, Y₂}`. -/
def cap5ReflectBoundaryWord (w : CAP5BoundaryWord) : CAP5BoundaryWord :=
  fun i => w (3 - i)

/-- Reflect an internal 5-cycle colouring compatibly: edge `j` of the
reflected word was edge `2 - j` of the original. -/
def cap5ReflectInternalCycleColoring
    (x : CAP5InternalCycleColoring) : CAP5InternalCycleColoring :=
  fun j => x (2 - j)

theorem isTaitColorTriple_swap_last {a b c : Color}
    (h : IsTaitColorTriple a b c) : IsTaitColorTriple a c b := by
  obtain ⟨ha, hb, hc, hab, hac, hbc⟩ := h
  exact ⟨ha, hc, hb, hac, hab, fun hcb => hbc hcb.symm⟩

/-- Reflection transports pentagon extensions, with the reflected internal
colouring as explicit witness. -/
theorem cap5ExtendsAcrossCycleWith_reflect
    {w : CAP5BoundaryWord} {x : CAP5InternalCycleColoring}
    (h : CAP5ExtendsAcrossCycleWith w x) :
    CAP5ExtendsAcrossCycleWith (cap5ReflectBoundaryWord w)
      (cap5ReflectInternalCycleColoring x) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  exact ⟨isTaitColorTriple_swap_last h3, isTaitColorTriple_swap_last h2,
    isTaitColorTriple_swap_last h1, isTaitColorTriple_swap_last h0,
    isTaitColorTriple_swap_last h4⟩

theorem cap5WordExtendsAcrossCycle_reflect {w : CAP5BoundaryWord}
    (h : CAP5WordExtendsAcrossCycle w) :
    CAP5WordExtendsAcrossCycle (cap5ReflectBoundaryWord w) := by
  obtain ⟨x, hx⟩ := h
  exact ⟨cap5ReflectInternalCycleColoring x, cap5ExtendsAcrossCycleWith_reflect hx⟩

/-- Reflection carries the Y-cap support at `i` to the one at `2 - i`. -/
theorem cap5YCapSupport_reflect :
    ∀ (w : CAP5BoundaryWord) (i : Fin 5),
      (CAP5YCapSupport i (cap5ReflectBoundaryWord w) ↔
        CAP5YCapSupport (2 - i) w) := by
  decide

/-- A colour equivalence fixing `0` preserves each Y-cap support. -/
theorem cap5YCapSupport_map_equiv_of_map_zero {σ : Color ≃ Color}
    (hσ0 : σ 0 = 0) (i : Fin 5) {w : CAP5BoundaryWord}
    (h : CAP5YCapSupport i w) :
    CAP5YCapSupport i (cap5MapBoundaryWord σ w) := by
  obtain ⟨hcap, hnz, htriple⟩ := h
  refine ⟨?_, ?_, isTaitColorTriple_map_equiv_of_map_zero hσ0 htriple⟩
  · simp [cap5MapBoundaryWord, hcap]
  · intro hzero
    exact hnz (σ.injective (by simpa [cap5MapBoundaryWord, hσ0] using hzero))

end Mettapedia.GraphTheory.FourColor
