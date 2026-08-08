import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebBoundaryData

/-!
# Exact good-word endpoint counts for the v24 closed web

The source's good five-edge word has color multiplicities `(3,1,1)`, up to
cyclic rotation and a relabeling of the three nonzero Tait colors.  This
module proves that statement at the existing `CAP5BoundaryWord` interface
and turns it into exact endpoint counts for the three bichromatic graphs.

No assertion about the outer word or about how endpoints are paired into
strands is made here.  Those are consequences of the later closed-web
component census, not of inner-word goodness alone.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebGoodWordCounts

open GoertzelV24ClosedWebBoundaryData

/-- The cyclic index permutation used by `cap5RotateBoundaryWord`. -/
def cap5RotationIndexEquiv : Equiv.Perm (Fin 5) where
  toFun := cap5RotateBoundaryPreimageIndex
  invFun
    | 0 => 4
    | 1 => 0
    | 2 => 1
    | 3 => 2
    | 4 => 3
  left_inv index := by fin_cases index <;> rfl
  right_inv index := by fin_cases index <;> rfl

@[simp] theorem cap5RotateBoundaryWord_apply
    (word : CAP5BoundaryWord) (index : Fin 5) :
    cap5RotateBoundaryWord word index = word (cap5RotationIndexEquiv index) := by
  fin_cases index <;> rfl

/-- A cyclic rotation preserves every color multiplicity. -/
theorem cap5BoundaryColorCount_rotate
    (word : CAP5BoundaryWord) (color : Color) :
    cap5BoundaryColorCount (cap5RotateBoundaryWord word) color =
      cap5BoundaryColorCount word color := by
  unfold cap5BoundaryColorCount
  apply Finset.card_bij
      (fun index _hindex => cap5RotationIndexEquiv index)
  · intro index hindex
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hindex ⊢
    simpa using hindex
  · intro first _hfirst second _hsecond heq
    exact cap5RotationIndexEquiv.injective heq
  · intro index hindex
    refine ⟨cap5RotationIndexEquiv.symm index, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        cap5RotateBoundaryWord_apply]
      simpa using hindex
    · exact cap5RotationIndexEquiv.apply_symm_apply index

/-- Any finite cyclic rotation preserves every color multiplicity. -/
theorem cap5BoundaryColorCount_rotateN
    (steps : Nat) (word : CAP5BoundaryWord) (color : Color) :
    cap5BoundaryColorCount (cap5RotateBoundaryWordN steps word) color =
      cap5BoundaryColorCount word color := by
  induction steps with
  | zero => rfl
  | succ steps inductionHypothesis =>
      rw [cap5RotateBoundaryWordN, cap5BoundaryColorCount_rotate,
        inductionHypothesis]

/-- The explicit normal-form good word has multiplicities `(3,1,1)`. -/
theorem cap5BoundaryWord311Of_colorCounts
    {majority singletonFirst singletonSecond : Color}
    (htriple : IsTaitColorTriple majority singletonFirst singletonSecond) :
    cap5BoundaryColorCount
        (cap5BoundaryWord311Of majority singletonFirst singletonSecond)
        majority = 3 ∧
      cap5BoundaryColorCount
        (cap5BoundaryWord311Of majority singletonFirst singletonSecond)
        singletonFirst = 1 ∧
      cap5BoundaryColorCount
        (cap5BoundaryWord311Of majority singletonFirst singletonSecond)
        singletonSecond = 1 := by
  rcases htriple with
    ⟨hmajorityZero, hfirstZero, hsecondZero,
      hmajorityFirst, hmajoritySecond, hfirstSecond⟩
  have hmajoritySupport :
      Finset.univ.filter
          (fun index : Fin 5 =>
            cap5BoundaryWord311Of majority singletonFirst singletonSecond index =
              majority) =
        ({0, 1, 2} : Finset (Fin 5)) := by
    ext index
    fin_cases index <;>
      simp [cap5BoundaryWord311Of, hmajorityFirst.symm,
        hmajoritySecond.symm]
  have hfirstSupport :
      Finset.univ.filter
          (fun index : Fin 5 =>
            cap5BoundaryWord311Of majority singletonFirst singletonSecond index =
              singletonFirst) =
        ({3} : Finset (Fin 5)) := by
    ext index
    fin_cases index <;>
      simp [cap5BoundaryWord311Of, hmajorityFirst, hfirstSecond.symm]
  have hsecondSupport :
      Finset.univ.filter
          (fun index : Fin 5 =>
            cap5BoundaryWord311Of majority singletonFirst singletonSecond index =
              singletonSecond) =
        ({4} : Finset (Fin 5)) := by
    ext index
    fin_cases index <;>
      simp [cap5BoundaryWord311Of, hmajoritySecond, hfirstSecond]
  constructor
  · rw [cap5BoundaryColorCount, hmajoritySupport]
    decide
  constructor
  · rw [cap5BoundaryColorCount, hfirstSupport]
    simp
  · rw [cap5BoundaryColorCount, hsecondSupport]
    simp

/-- A good colored-block witness yields explicit names for the majority and
the two singleton colors together with their exact counts. -/
theorem exists_exact_colorCounts_of_coloredBlock311
    {word : CAP5BoundaryWord}
    (hgood : CAP5BoundaryWordHasColoredBlock311 word) :
    ∃ majority singletonFirst singletonSecond : Color,
      IsTaitColorTriple majority singletonFirst singletonSecond ∧
      cap5BoundaryColorCount word majority = 3 ∧
      cap5BoundaryColorCount word singletonFirst = 1 ∧
      cap5BoundaryColorCount word singletonSecond = 1 := by
  rcases hgood with
    ⟨majority, singletonFirst, singletonSecond, htriple, steps, rfl⟩
  refine ⟨majority, singletonFirst, singletonSecond, htriple, ?_⟩
  simpa only [cap5BoundaryColorCount_rotateN] using
    cap5BoundaryWord311Of_colorCounts htriple

/-- The boundary positions carrying one fixed color. -/
def cap5ColorSupport (color : Color) (word : CAP5BoundaryWord) :
    Finset (Fin 5) :=
  Finset.univ.filter fun index => word index = color

@[simp] theorem cap5ColorSupport_card
    (color : Color) (word : CAP5BoundaryWord) :
    (cap5ColorSupport color word).card =
      cap5BoundaryColorCount word color :=
  rfl

/-- The active support of a pair is the union of its monochromatic
supports. -/
theorem cap5ActiveSupport_eq_union_colorSupports
    (first second : Color) (word : CAP5BoundaryWord) :
    cap5ActiveSupport first second word =
      cap5ColorSupport first word ∪ cap5ColorSupport second word := by
  ext index
  simp [cap5ActiveSupport, cap5ColorSupport]

/-- Distinct colors have disjoint boundary supports. -/
theorem cap5ColorSupport_disjoint
    {first second : Color} (hne : first ≠ second)
    (word : CAP5BoundaryWord) :
    Disjoint (cap5ColorSupport first word)
      (cap5ColorSupport second word) := by
  rw [Finset.disjoint_left]
  intro index hfirst hsecond
  have hfirstColor : word index = first := by
    simpa [cap5ColorSupport] using hfirst
  have hsecondColor : word index = second := by
    simpa [cap5ColorSupport] using hsecond
  exact hne (hfirstColor.symm.trans hsecondColor)

/-- Exact pair-support cardinality is the sum of the two color counts. -/
theorem cap5ActiveSupport_card_eq_add_colorCounts
    {first second : Color} (hne : first ≠ second)
    (word : CAP5BoundaryWord) :
    (cap5ActiveSupport first second word).card =
      cap5BoundaryColorCount word first +
        cap5BoundaryColorCount word second := by
  rw [cap5ActiveSupport_eq_union_colorSupports,
    Finset.card_union_of_disjoint (cap5ColorSupport_disjoint hne word)]
  rfl

/-- At a good word, the two singleton colors select exactly two inner
boundary endpoints, while either majority/singleton pair selects four. -/
theorem exists_exact_pairEndpointCounts_of_coloredBlock311
    {word : CAP5BoundaryWord}
    (hgood : CAP5BoundaryWordHasColoredBlock311 word) :
    ∃ majority singletonFirst singletonSecond : Color,
      IsTaitColorTriple majority singletonFirst singletonSecond ∧
      (cap5ActiveSupport singletonFirst singletonSecond word).card = 2 ∧
      (cap5ActiveSupport majority singletonFirst word).card = 4 ∧
      (cap5ActiveSupport majority singletonSecond word).card = 4 := by
  rcases exists_exact_colorCounts_of_coloredBlock311 hgood with
    ⟨majority, singletonFirst, singletonSecond, htriple,
      hmajorityCount, hfirstCount, hsecondCount⟩
  have hmajorityFirst : majority ≠ singletonFirst :=
    htriple.2.2.2.1
  have hmajoritySecond : majority ≠ singletonSecond :=
    htriple.2.2.2.2.1
  have hfirstSecond : singletonFirst ≠ singletonSecond :=
    htriple.2.2.2.2.2
  refine ⟨majority, singletonFirst, singletonSecond, htriple, ?_, ?_, ?_⟩
  · rw [cap5ActiveSupport_card_eq_add_colorCounts hfirstSecond,
      hfirstCount, hsecondCount]
  · rw [cap5ActiveSupport_card_eq_add_colorCounts hmajorityFirst,
      hmajorityCount, hfirstCount]
  · rw [cap5ActiveSupport_card_eq_add_colorCounts hmajoritySecond,
      hmajorityCount, hsecondCount]

/-- Boundary-data specialization: source-level goodness of the actual inner
edge word gives the exact `(2,4,4)` selected endpoint counts. -/
theorem AnnularBoundaryData.exists_innerPairEndpointCounts_of_goodWord
    {V : Type*} {G : SimpleGraph V} {outerCount : Nat}
    (data : AnnularBoundaryData G outerCount)
    (C : G.EdgeColoring Color)
    (hgood : CAP5BoundaryWordHasColoredBlock311
      (data.innerBoundaryWord C)) :
    ∃ majority singletonFirst singletonSecond : Color,
      IsTaitColorTriple majority singletonFirst singletonSecond ∧
      (cap5ActiveSupport singletonFirst singletonSecond
        (data.innerBoundaryWord C)).card = 2 ∧
      (cap5ActiveSupport majority singletonFirst
        (data.innerBoundaryWord C)).card = 4 ∧
      (cap5ActiveSupport majority singletonSecond
        (data.innerBoundaryWord C)).card = 4 :=
  exists_exact_pairEndpointCounts_of_coloredBlock311 hgood

end GoertzelV24ClosedWebGoodWordCounts

end Mettapedia.GraphTheory.FourColor
