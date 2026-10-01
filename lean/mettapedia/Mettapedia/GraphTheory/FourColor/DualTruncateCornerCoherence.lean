import Mettapedia.GraphTheory.FourColor.DualTruncateCornerSemantics

/-!
# The precise condition for collapsing corners to source vertex colours

An exact corner state may vary around a source vertex. Its cyclic difference
is preserved across source edge reversal. Vanishing of every difference,
together with genuine cyclic vertex rotations, is exactly the condition
for a compatible three-vertex source witness. This condition is additional
mathematics, not a consequence of target Tait colourability alone.
-/

namespace Mettapedia.GraphTheory.FourColor.DualTruncateCornerCoherence

open DualTruncateColoring DualTruncateCornerSemantics

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (RS : RotationSystem V E)

def Coherent (q : RS.D → Color) : Prop :=
  ∀ d e, RS.vertOf d = RS.vertOf e → q d = q e

def difference (q : RS.D → Color) (d : RS.D) : Color := q d + q (RS.rho d)

/-- A target cross edge retains this difference at both source endpoints. -/
theorem difference_alpha {q : RS.D → Color} (hq : Valid RS q) (d : RS.D) :
    difference RS q (RS.alpha d) = difference RS q d := by
  have h := hq.2.2 d
  simp only [DualTruncateCornerSemantics.Balanced, RotationSystem.phi_apply,
    RS.alpha_involutive] at h
  have exchange (a b c e : Color) (h : a+b = c+e) : c+b = a+e := by
    revert a b c e
    decide +kernel
  exact exchange _ _ _ _ h

theorem difference_zero_of_coherent {q : RS.D → Color} (h : Coherent RS q) (d : RS.D) :
    difference RS q d = 0 := by
  unfold difference
  rw [h d (RS.rho d) (RS.vert_rho d).symm, color_add_self]

theorem coherent_of_difference_zero {q : RS.D → Color}
    (hrotation : ∀ d e, RS.vertOf d = RS.vertOf e → RS.rho.SameCycle d e)
    (hz : ∀ d, difference RS q d = 0) : Coherent RS q := by
  have step (d) : q (RS.rho d) = q d :=
    ((add_eq_zero_iff_eq _ _).mp (hz d)).symm
  have powers (n : ℕ) (d : RS.D) : q ((RS.rho ^ n) d) = q d := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, step, ih]
  intro d e hv
  obtain ⟨n,hn⟩ := (hrotation d e hv).exists_nat_pow_eq
  have he : q e = q d := by simpa only [hn] using powers n d
  exact he.symm

def vertexColour (q : RS.D → Color) (v : V) : Color :=
  if h : ∃ d, RS.vertOf d = v then q h.choose else red

theorem vertexColour_dart {q : RS.D → Color} (h : Coherent RS q) (d : RS.D) :
    vertexColour RS q (RS.vertOf d) = q d := by
  have hex : ∃ e, RS.vertOf e = RS.vertOf d := ⟨d,rfl⟩
  simp only [vertexColour, dite_eq_left hex]
  exact h _ d hex.choose_spec

def sourceColouring (q : RS.D → Color) (hq : Valid RS q) (h : Coherent RS q) :
    ThreeVertexColoring RS where
  colour := vertexColour RS q
  nonzero v := by
    unfold vertexColour
    split
    · exact hq.1 _
    · exact red_ne_zero
  proper d := by
    rw [vertexColour_dart RS h d, vertexColour_dart RS h (RS.alpha d)]
    have he : q (RS.phi d) = q (RS.alpha d) :=
      h _ _ (RS.vert_phi_eq_vert_alpha d)
    exact fun hn => hq.2.1 d (hn.trans he.symm)

/-- The source witness agrees with every retained corner, rather than
merely showing that some source colouring exists. -/
theorem source_witness_iff (q : RS.D → Color) (hq : Valid RS q) :
    (∃ c : ThreeVertexColoring RS, ∀ d, c.colour (RS.vertOf d) = q d) ↔ Coherent RS q := by
  constructor
  · rintro ⟨c,hc⟩ d e hv
    rw [← hc d, ← hc e, hv]
  · intro h
    exact ⟨sourceColouring RS q hq h, vertexColour_dart RS h⟩

/-- Genuine cyclic vertex rotations make the zero-difference test exact. -/
theorem source_witness_iff_difference_zero (q : RS.D → Color) (hq : Valid RS q)
    (hrotation : ∀ d e, RS.vertOf d = RS.vertOf e → RS.rho.SameCycle d e) :
    (∃ c : ThreeVertexColoring RS, ∀ d, c.colour (RS.vertOf d) = q d) ↔
      ∀ d, difference RS q d = 0 := by
  rw [source_witness_iff RS q hq]
  exact ⟨fun h d => difference_zero_of_coherent RS h d,
    coherent_of_difference_zero RS hrotation⟩

end
end Mettapedia.GraphTheory.FourColor.DualTruncateCornerCoherence
