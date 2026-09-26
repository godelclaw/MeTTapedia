import Mettapedia.GraphTheory.FourColor.CAP5BoundaryWord
import Mettapedia.GraphTheory.FourColor.ZigzagRingTangle

/-!
# One-sided support descent for pentagon-capped zigzag tubes

Adding a five-port zigzag ring strictly enlarges the pentagon's boundary
support. Equality of supports therefore cannot remove the first ring, whereas
support inclusion can. The inclusion persists through every number of rings
by monotonicity of composition. Ring acceptance here is the Tait-colouring
relation of the physical two-sided open tangle.

These are colouring statements. Applying them to a closed embedded tube
also requires a compatible boundary order and the structural and strict-size
hypotheses of physical replacement. No assertion of universal tube supply is
made here.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelV24PentagonTubeSupportInclusion

open ZigzagRing

/-- Boundary colourings realized by the five-cycle cap. -/
def capSupport : Set CAP5BoundaryWord := {w | CAP5WordExtendsAcrossCycle w}

/-- Relational composition with the physical five-port zigzag ring. -/
def appendRingSupport (S : Set CAP5BoundaryWord) : Set CAP5BoundaryWord :=
  {w | ∃ x ∈ S, (ring 5).AcceptsBoundaryWords x w}

theorem appendRingSupport_mono {S T : Set CAP5BoundaryWord} (h : S ⊆ T) :
    appendRingSupport S ⊆ appendRingSupport T := by
  rintro w ⟨x, hx, hring⟩
  exact ⟨x, h hx, hring⟩

private theorem canonical_ring (a b c : Color) (h : IsTaitColorTriple a b c) :
    (ring 5).AcceptsBoundaryWords
      (cap5BoundaryWord311Of a c b) (cap5BoundaryWord311Of a b c) := by
  apply (accepts_iff 5 _ _).2
  refine ⟨(fun i => if i.val < 3 then c else a), ?_, ?_⟩
  · constructor <;> intro i <;> fin_cases i <;>
      revert a b c <;> unfold IsTaitColorTriple <;> decide +kernel
  · funext i
    fin_cases i <;> revert a b c <;> unfold IsTaitColorTriple <;> decide +kernel

private theorem ring_rotate {x y : CAP5BoundaryWord}
    (h : (ring 5).AcceptsBoundaryWords x y) :
    (ring 5).AcceptsBoundaryWords
      (cap5RotateBoundaryWord x) (cap5RotateBoundaryWord y) := by
  obtain ⟨a, ha, rfl⟩ := (accepts_iff 5 x y).1 h
  apply (accepts_iff 5 _ _).2
  refine ⟨cap5RotateBoundaryWord a, ?_, ?_⟩
  · constructor
    · intro i
      fin_cases i <;> exact ha.x_ne_zero _
    · intro i
      fin_cases i <;> exact ha.a_ne_zero _
    · intro i
      fin_cases i <;> exact ha.a_ne_x _
    · intro i
      fin_cases i
      · exact ha.a_ne_b 1
      · exact ha.a_ne_b 2
      · exact ha.a_ne_b 3
      · exact ha.a_ne_b 4
      · exact ha.a_ne_b 0
  · funext i
    fin_cases i <;> rfl

/-- Every cap boundary colouring also extends through a cap and one ring. -/
theorem capSupport_subset_appendRing : capSupport ⊆ appendRingSupport capSupport := by
  intro w hw
  obtain ⟨a, b, c, htriple, n, rfl⟩ :=
    cap5BoundaryWordHasColoredBlock311_of_extendsAcrossCycle hw
  clear hw
  have hswap : IsTaitColorTriple a c b := by
    rcases htriple with ⟨ha, hb, hc, hab, hac, hbc⟩
    exact ⟨ha, hc, hb, hac, hab, hbc.symm⟩
  refine ⟨cap5RotateBoundaryWordN n (cap5BoundaryWord311Of a c b),
    cap5WordExtendsAcrossCycle_rotateN
      (cap5BoundaryWord311Of_extendsAcrossCycle hswap), ?_⟩
  induction n with
  | zero => exact canonical_ring a b c htriple
  | succ n ih => exact ring_rotate ih

/-- A word excluded by the cap is admitted after one ring. -/
theorem badWord_mem_appendRing : cap5BadBoundaryWord2111 ∈ appendRingSupport capSupport := by
  refine ⟨cap5BoundaryWord311Of red blue purple,
    cap5BoundaryWord311Of_extendsAcrossCycle isTaitColorTriple_red_blue_purple, ?_⟩
  apply (accepts_iff 5 _ _).2
  refine ⟨(fun i => if i.val < 4 then purple else red), ?_, ?_⟩
  · constructor <;> intro i <;> fin_cases i <;> decide +kernel
  · funext i
    fin_cases i <;> decide +kernel

/-- The first ring is a strict support enlargement, so an equality-based
replacement test rejects this valid one-sided colour extension. -/
theorem capSupport_ssubset_appendRing : capSupport ⊂ appendRingSupport capSupport := by
  refine ⟨capSupport_subset_appendRing, ?_⟩
  intro hback
  exact not_cap5BadBoundaryWord2111_extendsAcrossCycle (hback badWord_mem_appendRing)

/-- Support after any finite number of physical ring compositions. -/
def tubeSupport : Nat → Set CAP5BoundaryWord
  | 0 => capSupport
  | n + 1 => appendRingSupport (tubeSupport n)

theorem tubeSupport_subset_succ (n : Nat) : tubeSupport n ⊆ tubeSupport (n + 1) := by
  induction n with
  | zero => exact capSupport_subset_appendRing
  | succ n ih => exact appendRingSupport_mono ih

/-- Every pentagon-capped tube admits all the cap's boundary colourings. -/
theorem capSupport_subset_tubeSupport (n : Nat) : capSupport ⊆ tubeSupport n := by
  induction n with
  | zero => exact Set.Subset.refl _
  | succ n ih => exact ih.trans (tubeSupport_subset_succ n)

end GoertzelV24PentagonTubeSupportInclusion
end Mettapedia.GraphTheory.FourColor
