import MettapediaFourColor.D3009Colouring

/-!
# Compatible sectors and a failed closure on the actual wheel source

The positive example is a full source colouring, so its two sector histories
stitch into a genuine colouring. The negative example fixes a proper boundary
colouring for which both sectors have histories, but the complete cyclic
choice is impossible. It refutes independent sector inhabitation as a repair
criterion; it does not refute exterior recolouring or D-reducibility.
-/

namespace FourColor.D3009ColouringExample

open Color D3009Colouring CyclicColourRoute

def full : D3009Wheel.input.graph.Coloring Color :=
  .mk ![c0,c1,c0,c1,c0,c1,c0,c1,c0,c1,c0,c2,c3,c0,c2,c2,c3,c1,c3,c2,c3]
    (by decide +kernel)

def good : boundaryGraph.Coloring Color :=
  .mk (fun b => full (b.castAdd 8)) (fun {_ _} h => full.valid h)

theorem stitched : ∃ z a b,
    (WheelColouringGSLT.semantics (by decide : 2 ≤ 7) touch good z).Supports
      (route 0 3) a b ∧
    (WheelColouringGSLT.semantics (by decide : 2 ≤ 7) touch good z).Supports
      (route 3 4) b a :=
  (two_sectors_iff good).mp ⟨full, fun _ => rfl⟩

def bad : boundaryGraph.Coloring Color :=
  .mk ![c0,c1,c0,c1,c0,c1,c0,c1,c0,c1,c0,c1,c3] (by decide +kernel)

theorem touches_both : ∀ i : Fin 7, ∃ a b : Fin 13,
    touch i a ∧ bad a = c0 ∧ touch i b ∧ bad b = c1 := by decide +kernel

theorem odd_cycle : ¬ ∃ f : Fin 7 → Fin 2,
    ∀ i, f i ≠ f (next (by decide) i) := by decide +kernel

theorem bad_no_witness :
    ¬ Nonempty (WheelColouring.Witness (next (by decide)) touch bad) := by
  rintro ⟨w⟩
  have two (i : Fin 7) : w.rim i = c2 ∨ w.rim i = c3 := by
    obtain ⟨a, b, ha, ca, hb, cb⟩ := touches_both i
    have na := w.boundary_ne i a ha
    have nb := w.boundary_ne i b hb
    rw [ca] at na
    rw [cb] at nb
    cases h : w.rim i <;> simp_all
  let f : Fin 7 → Fin 2 := fun i => if w.rim i = c2 then 0 else 1
  have reflects (i j : Fin 7) : f i = f j → w.rim i = w.rim j := by
    rcases two i with hi | hi <;> rcases two j with hj | hj <;> simp [f, hi, hj]
  apply odd_cycle
  exact ⟨f, fun i equal => w.rim_ne i (reflects i _ equal)⟩

theorem bad_no_extension :
    ¬ ∃ k : D3009Wheel.input.graph.Coloring Color,
      ∀ b : Fin 13, k (b.castAdd 8) = bad b := by
  rw [D3009Colouring.extends_iff]
  exact bad_no_witness

theorem first_sector :
    (WheelColouringGSLT.semantics (by decide : 2 ≤ 7) touch bad c0).Supports
      (route 0 3) c2 c3 := by
  apply (supports_iff
    (fun i => WheelColouringGSLT.row touch bad c0 ⟨i % 7, Nat.mod_lt _ (by decide)⟩)
    0 3 c2 c3).mpr
  exact ⟨![c2,c3,c2,c3], rfl, rfl, by decide +kernel⟩

theorem second_sector :
    (WheelColouringGSLT.semantics (by decide : 2 ≤ 7) touch bad c0).Supports
      (route 3 4) c3 c3 := by
  apply (supports_iff
    (fun i => WheelColouringGSLT.row touch bad c0 ⟨i % 7, Nat.mod_lt _ (by decide)⟩)
    3 4 c3 c3).mpr
  exact ⟨![c3,c2,c3,c2,c3], rfl, rfl, by decide +kernel⟩

/-- Both histories exist and meet at one seam, but their other seam cannot close. -/
theorem incompatible_sectors :
    ¬ ∃ z a b,
      (WheelColouringGSLT.semantics (by decide : 2 ≤ 7) touch bad z).Supports
        (route 0 3) a b ∧
      (WheelColouringGSLT.semantics (by decide : 2 ≤ 7) touch bad z).Supports
        (route 3 4) b a := by
  rw [← two_sectors_iff bad]
  exact bad_no_extension

end FourColor.D3009ColouringExample
