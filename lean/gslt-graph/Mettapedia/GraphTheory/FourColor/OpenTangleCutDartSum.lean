import Mettapedia.GraphTheory.FourColor.OpenTangleSmallCutReplacement

/-!
# Cut sizes from interior darts

Each interior edge contributes its two darts. This identifies the actual
multigraph cut count with half the symmetric dart sum, avoiding a second
choice of edge identifiers when computing serial-tangle transfers.
-/

namespace Mettapedia.GraphTheory.FourColor.OpenTangleCutDartSum

open GoertzelV24OpenTangleComposition GoertzelV24CompositeSeamMultigraph
open BoundarySmallCutProfile

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V I B : Type*} [Fintype I] [DecidableEq I]

instance sideEdgeFintype (T : OpenTangleData V I B) : Fintype (SideEdge T) := by
  unfold SideEdge
  infer_instance

/-- A chosen dart and its mate enumerate each interior edge exactly twice. -/
def dartEquiv (T : OpenTangleData V I B) : SideEdge T × Bool ≃ I where
  toFun x := if x.2 then x.1.2.choose else T.interiorAlpha x.1.2.choose
  invFun d := (sideEdgeOf T d, decide (d = (sideEdgeOf T d).2.choose))
  left_inv := by
    rintro ⟨e, b⟩
    cases b <;> simp only [Bool.false_eq_true, if_false, if_true]
    · simp only [sideEdgeOf_alpha, sideEdgeOf_choose, T.interiorAlpha_fixfree,
        decide_false]
    · simp only [sideEdgeOf_choose, decide_true]
  right_inv := by
    intro d
    by_cases h : d = (sideEdgeOf T d).2.choose
    · have ht : decide (d = (sideEdgeOf T d).2.choose) = true := by simpa using h
      simp only [ht, if_true]
      exact h.symm
    · simp only [h, decide_false, Bool.false_eq_true, if_false]
      rcases choose_sideEdgeOf T d with hd | hd
      · exact (h hd.symm).elim
      · rw [hd, T.interiorAlpha_involutive]

def bit (a b : Bool) : Nat := if a = b then 0 else 1

theorem bit_symm (a b : Bool) : bit a b = bit b a := by cases a <;> cases b <;> rfl

theorem twice_cutSize (T : OpenTangleData V I B) (s : V → Bool) :
    2 * cutSize (sideMultigraph T) s =
      ∑ d : I, bit (s (T.interiorVert d)) (s (T.interiorVert (T.interiorAlpha d))) := by
  have h := Fintype.sum_equiv (dartEquiv T)
    (fun x => bit (s (T.interiorVert (dartEquiv T x)))
      (s (T.interiorVert (T.interiorAlpha (dartEquiv T x)))))
    (fun d => bit (s (T.interiorVert d)) (s (T.interiorVert (T.interiorAlpha d))))
    (fun _ => rfl)
  rw [← h, Fintype.sum_prod_type]
  unfold cutSize
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  simp only [Fintype.sum_bool, dartEquiv, Equiv.coe_fn_mk, Bool.false_eq_true, if_false, if_true,
    T.interiorAlpha_involutive]
  change 2 * bit (s (T.interiorVert e.2.choose)) (s (T.interiorVert (T.interiorAlpha e.2.choose))) = _
  rw [bit_symm (s (T.interiorVert (T.interiorAlpha e.2.choose))), two_mul]

end
end Mettapedia.GraphTheory.FourColor.OpenTangleCutDartSum
