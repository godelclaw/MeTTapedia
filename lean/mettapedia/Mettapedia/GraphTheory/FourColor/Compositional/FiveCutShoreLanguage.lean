import Mettapedia.GraphTheory.FourColor.Compositional.FiveCutWordHeart
import Mettapedia.GraphTheory.FourColor.Compositional.FiveCutWordHeartProof
import Mettapedia.GraphTheory.FourColor.Compositional.BoundaryColorOrbit

/-!
# The boundary language of one shore of a five-edge cut

The word-level heart of the trivial-five-cut theorem consumes an abstract
`BoundaryLanguage`: admissible words, closed under global zero-fixing colour
equivalences, and chain-closed under involutive noncrossing boundary mates.
This file constructs that language for a physical shore: the value-level
boundary support of a finite cubic port tangle read in cyclic coordinates.

* admissibility comes from properness and open cut parity;
* colour closure comes from relabelling the realizing colouring;
* chain closure comes from the physical bichromatic mate and the
  component-union switch theorem, with noncrossing supplied by the caller
  (on an exact cyclic five-edge cut it is the physical noncrossing
  theorem).

Together with `exists_common_word` this reduces the five-cut theorem to the
menu obligations: each shore's language must meet the pentagon support and
three consecutive Y-cap supports.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace Compositional

namespace FiveCutShoreLanguage

open BoundaryColorOrbit
open BoundaryKempeSwitch
open CyclicBoundaryMatching
open FiveCutWordHeart
open GoertzelV24HexagonPairingTargetAwareBoundary
open GoertzelV24PortTangleCommonKempeWeb
open GoertzelV24PortTangleCutParity
open GoertzelV24PortTangleGluing
open GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24PortTanglePhysicalKempeClosure

set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

/-! ## Finite colour lemmas -/

private instance : DecidableEq Color := inferInstance

private instance : DecidablePred (Odd : Nat → Prop) := fun n =>
  decidable_of_iff (n % 2 = 1) Nat.odd_iff.symm

private instance (w : CAP5BoundaryWord) :
    Decidable (CAP5BoundaryWordHasOddColorCounts w) := by
  unfold CAP5BoundaryWordHasOddColorCounts; infer_instance

/-- A nonzero five-letter colour word with zero total colour has odd colour
counts. -/
private theorem cap5OddCounts_of_sum :
    ∀ w : CAP5BoundaryWord, (∀ i, w i ≠ 0) →
      w 0 + w 1 + w 2 + w 3 + w 4 = 0 →
      CAP5BoundaryWordHasOddColorCounts w := by
  decide

/-- Two distinct nonzero colours are the colours of a Tait colour pair, in
one of the two orders. -/
private theorem exists_taitColorPair :
    ∀ x y : Color, x ≠ 0 → y ≠ 0 → x ≠ y →
      ∃ pair : TaitColorPair,
        (pair.colors.1 = x ∧ pair.colors.2 = y) ∨
        (pair.colors.1 = y ∧ pair.colors.2 = x) := by
  decide

private theorem colorSwap_comm :
    ∀ a b c : Color, Color.swap a b c = Color.swap b a c := by
  decide

/-! ## The shore language -/

universe u v

variable {V I P : Type u}
  [Fintype V] [Fintype I] [Fintype P]
  [DecidableEq V] [DecidableEq I] [DecidableEq P]

/-- The value-level boundary language of one shore: colour words realized by
some proper colouring of the tangle, read in the chosen cyclic boundary
coordinates. -/
def shoreLanguage (order : Fin 5 ≃ P) (T : PortTangle V I P) :
    CAP5BoundaryWord → Prop :=
  fun w => ∃ boundary ∈ supportInCoordinates order T,
    ∀ i, (boundary i).1 = w i

/-- The boundary word of a realizing colouring, in coordinates, projects to
the language word. -/
theorem shoreLanguage_of_coloring
    (order : Fin 5 ≃ P) {T : PortTangle V I P}
    (coloring : Coloring T) (hproper : IsProper coloring) :
    shoreLanguage order T
      (fun i => (properBoundaryWordInCoordinates order coloring hproper i).1) :=
  ⟨properBoundaryWordInCoordinates order coloring hproper,
    properBoundaryWordInCoordinates_mem_support order T coloring hproper,
    fun _ => rfl⟩

/-- **The physical shore language is a boundary language.**  Cubicity gives
parity, relabelling gives colour closure, and the physical bichromatic mate
with the component-union switch theorem gives chain closure; noncrossing of
the mate is the caller's geometric input. -/
theorem boundaryLanguage_shoreLanguage
    (order : Fin 5 ≃ P) (T : PortTangle V I P) (hcubic : IsCubic T)
    (hnc : ∀ (coloring : Coloring T) (hproper : IsProper coloring)
        (pair : TaitColorPair),
        IsNoncrossingMatching
          (physicalMateInCoordinates order T hcubic coloring hproper pair)) :
    BoundaryLanguage (shoreLanguage order T) := by
  constructor
  · -- admissibility: nonzero letters and odd colour counts
    rintro w ⟨boundary, hmem, hval⟩
    have hnonzero : ∀ i, w i ≠ 0 := fun i => hval i ▸ (boundary i).2
    refine ⟨hnonzero, ?_⟩
    have hzero := taitSupport_subset_zeroSum T hcubic hmem
    have hsum : (∑ port : P, (boundary (order.symm port)).1) = 0 := hzero
    have hreindex : (∑ port : P, (boundary (order.symm port)).1) =
        ∑ i : Fin 5, (boundary i).1 :=
      Equiv.sum_comp order.symm (fun i => (boundary i).1)
    have hvals : (∑ i : Fin 5, (boundary i).1) = ∑ i : Fin 5, w i := by
      exact Finset.sum_congr rfl fun i _ => hval i
    rw [hreindex, hvals, Fin.sum_univ_five] at hsum
    exact cap5OddCounts_of_sum w hnonzero hsum
  · -- colour closure: relabel the realizing colouring
    rintro σ hσ w ⟨boundary, hmem, hval⟩
    refine ⟨relabelBoundaryWord σ hσ boundary,
      (relabelBoundaryWord_mem_supportInCoordinates_iff
        order T σ hσ boundary).2 hmem, ?_⟩
    intro i
    show σ (boundary i).1 = cap5MapBoundaryWord σ w i
    rw [cap5MapBoundaryWord, hval i]
  · -- chain closure: the physical bichromatic mate
    rintro w ⟨boundary, hmem, hval⟩ x y hx hy hxy
    obtain ⟨pair, hpair⟩ := exists_taitColorPair x y hx hy hxy
    obtain ⟨⟨coloring, hproper, hword⟩⟩ := hmem
    have hcolor : ∀ i : Fin 5, coloring.color (Sum.inr (order i)) = w i := by
      intro i
      have hp := congrFun hword (order i)
      change coloring.color (Sum.inr (order i)) =
        (boundary (order.symm (order i))).1 at hp
      rw [hp, Equiv.symm_apply_apply, hval i]
    have hboundaryEq :
        properBoundaryWordInCoordinates order coloring hproper = boundary := by
      funext i
      apply Subtype.ext
      show coloring.color (Sum.inr (order i)) = (boundary i).1
      rw [hcolor i, hval i]
    have hswapEq : ∀ c : Color,
        Color.swap pair.colors.1 pair.colors.2 c = cap5SwapColor x y c := by
      intro c
      rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2, cap5SwapColor_eq_colorSwap]
      · rw [h1, h2, cap5SwapColor_eq_colorSwap, colorSwap_comm]
    have hactiveIff : ∀ i : Fin 5,
        pairActiveDart coloring pair (Sum.inr (order i)) ↔
          (w i = x ∨ w i = y) := by
      intro i
      show pairActiveColor pair (coloring.color (Sum.inr (order i))) ↔ _
      rw [hcolor i]
      change (w i = pair.colors.1 ∨ w i = pair.colors.2) ↔ _
      rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
      · rw [h1, h2]
        exact or_comm
    refine ⟨physicalMateInCoordinates order T hcubic coloring hproper pair,
      ?_, ?_, hnc coloring hproper pair, ?_⟩
    · -- involutive
      intro i
      show order.symm (physicalMate T hcubic coloring hproper pair
        (order (order.symm (physicalMate T hcubic coloring hproper pair
          (order i))))) = i
      rw [Equiv.apply_symm_apply,
        physicalMate_involutive T hcubic coloring hproper pair,
        Equiv.symm_apply_apply]
    · -- activity characterization
      intro i
      rw [← hactiveIff i]
      constructor
      · intro hne
        by_contra hinactive
        apply hne
        show order.symm (physicalMate T hcubic coloring hproper pair
          (order i)) = i
        rw [physicalMate_eq_self_of_inactive T hcubic coloring hproper pair
          (order i) hinactive, Equiv.symm_apply_apply]
      · intro hactive hEq
        apply physicalMate_ne_of_active T hcubic coloring hproper pair
          (order i) hactive
        have hEq' : order.symm (physicalMate T hcubic coloring hproper pair
            (order i)) = i := hEq
        have := congrArg order hEq'
        rwa [Equiv.apply_symm_apply] at this
    · -- component-union switches stay in the language
      intro Tset hclosed
      have hinv : ∀ i : Fin 5,
          physicalMateInCoordinates order T hcubic coloring hproper pair
            (physicalMateInCoordinates order T hcubic coloring hproper pair
              i) = i := by
        intro i
        show order.symm (physicalMate T hcubic coloring hproper pair
          (order (order.symm (physicalMate T hcubic coloring hproper pair
            (order i))))) = i
        rw [Equiv.apply_symm_apply,
          physicalMate_involutive T hcubic coloring hproper pair,
          Equiv.symm_apply_apply]
      have hunion : ∀ i : Fin 5, i ∈ Tset ↔
          physicalMateInCoordinates order T hcubic coloring hproper pair i ∈
            Tset := by
        intro i
        constructor
        · exact hclosed i
        · intro hmate
          have := hclosed _ hmate
          rwa [hinv i] at this
      have hswitch := switchBoundaryWord_mem_supportInCoordinates
        order T hcubic coloring hproper pair Tset hunion
      rw [hboundaryEq] at hswitch
      refine ⟨switchBoundaryWord boundary pair Tset, hswitch, ?_⟩
      intro i
      show (switchBoundaryWord boundary pair Tset i).1 =
        cap5BoundarySwap x y Tset w i
      by_cases hmemT : i ∈ Tset
      · simp only [switchBoundaryWord, cap5BoundarySwap, hmemT, if_pos]
        rw [hswapEq, hval i]
      · simp only [switchBoundaryWord, cap5BoundarySwap, hmemT, if_neg,
          not_false_iff]
        exact hval i

/-! ## The heart, instantiated on two shores -/

variable {V' I' P' : Type u}
  [Fintype V'] [Fintype I'] [Fintype P']
  [DecidableEq V'] [DecidableEq I'] [DecidableEq P']

/-- **Two physical shores meeting the menu share a boundary word.**  The
five-cut heart `exists_common_word`, instantiated at two shore languages. -/
theorem exists_common_shore_word
    (orderA : Fin 5 ≃ P) (TA : PortTangle V I P) (hcubicA : IsCubic TA)
    (hncA : ∀ (coloring : Coloring TA) (hproper : IsProper coloring)
        (pair : TaitColorPair),
        IsNoncrossingMatching
          (physicalMateInCoordinates orderA TA hcubicA coloring hproper pair))
    (orderB : Fin 5 ≃ P') (TB : PortTangle V' I' P') (hcubicB : IsCubic TB)
    (hncB : ∀ (coloring : Coloring TB) (hproper : IsProper coloring)
        (pair : TaitColorPair),
        IsNoncrossingMatching
          (physicalMateInCoordinates orderB TB hcubicB coloring hproper pair))
    (hAP5 : ∃ w, shoreLanguage orderA TA w ∧ CAP5WordExtendsAcrossCycle w)
    (hAY0 : ∃ w, shoreLanguage orderA TA w ∧ CAP5YCapSupport 0 w)
    (hAY1 : ∃ w, shoreLanguage orderA TA w ∧ CAP5YCapSupport 1 w)
    (hAY2 : ∃ w, shoreLanguage orderA TA w ∧ CAP5YCapSupport 2 w)
    (hBP5 : ∃ w, shoreLanguage orderB TB w ∧ CAP5WordExtendsAcrossCycle w)
    (hBY0 : ∃ w, shoreLanguage orderB TB w ∧ CAP5YCapSupport 0 w)
    (hBY1 : ∃ w, shoreLanguage orderB TB w ∧ CAP5YCapSupport 1 w)
    (hBY2 : ∃ w, shoreLanguage orderB TB w ∧ CAP5YCapSupport 2 w) :
    ∃ w, shoreLanguage orderA TA w ∧ shoreLanguage orderB TB w :=
  exists_common_word
    (boundaryLanguage_shoreLanguage orderA TA hcubicA hncA)
    (boundaryLanguage_shoreLanguage orderB TB hcubicB hncB)
    hAP5 hAY0 hAY1 hAY2 hBP5 hBY0 hBY1 hBY2

end FiveCutShoreLanguage

end Compositional

end Mettapedia.GraphTheory.FourColor
