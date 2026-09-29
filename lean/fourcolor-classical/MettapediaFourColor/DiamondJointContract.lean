import MettapediaFourColor.DiamondContract

/-!
# Elimination of the jointly contracted diamond interior

The two contracted insertion triangles are joined by an edge of the internal
diamond. Their common colours must differ. Eliminating the interior leaves
six boundary colours with explicit inequalities, and any such boundary data
reconstruct a contract colouring. The formula uses addition in the Klein
four-group to recover the remaining two interior colours.
-/

namespace FourColor.DiamondJointContract

open Color DiamondConfigurations DiamondContract

/-- The six colours observed after contracting both insertion triangles. -/
def Admissible (a b x y z w : Color) : Prop :=
  a ≠ b ∧ x ≠ a ∧ z ≠ b ∧ y ≠ a ∧ y ≠ b ∧ w ≠ a ∧ w ≠ b

instance (a b x y z w : Color) : Decidable (Admissible a b x y z w) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def boundary (a b x y z w : Color) : List Color := [a, x, a, y, b, z, b, w]

/-- The last two interior colours are the fourth colours of their triangles. -/
def reconstruct (a b x y z w : Color) (v : Fin 12) : Color :=
  match v.val with
  | 0 | 2 | 8 => b
  | 1 => z
  | 3 => w
  | 4 | 6 | 10 => a
  | 5 => x
  | 7 => y
  | 9 => a + b + w
  | _ => a + b + y

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
-- Check the local four-colour identities against the fifty literal darts.
theorem reconstruct_valid : ∀ a b x y z w, Admissible a b x y z w →
    ∀ d, reconstruct a b x y z w (vertex004 (table004.map.edge d)) =
      reconstruct a b x y z w (vertex004 d) ↔ d ∈ table004.map.insertE darts004 := by
  decide +kernel

def assignment (a b x y z w : Color) (h : Admissible a b x y z w) :
    faces004.ContractAssignment darts004 :=
  ⟨reconstruct a b x y z w, reconstruct_valid a b x y z w h⟩

theorem reconstruct_boundary (a b x y z w : Color) :
    boundary004.reverse.map (reconstruct a b x y z w) = boundary a b x y z w := rfl

private theorem edge_eq (k : faces004.ContractAssignment darts004) (d : Fin 50)
    (h : d ∈ table004.map.insertE darts004) :
    k.val (vertex004 (table004.map.edge d)) = k.val (vertex004 d) :=
  (k.property d).mpr h

private theorem edge_ne (k : faces004.ContractAssignment darts004) (d : Fin 50)
    (h : d ∉ table004.map.insertE darts004) :
    k.val (vertex004 (table004.map.edge d)) ≠ k.val (vertex004 d) :=
  fun he => h ((k.property d).mp he)

/-- All actual contract witnesses have precisely the six-colour boundary form. -/
theorem eliminate (k : faces004.ContractAssignment darts004) :
    Admissible (k.val 4) (k.val 0) (k.val 5) (k.val 7) (k.val 1) (k.val 3) ∧
    boundary004.reverse.map k.val =
      boundary (k.val 4) (k.val 0) (k.val 5) (k.val 7) (k.val 1) (k.val 3) := by
  have h4 : k.val 4 = k.val 10 := edge_eq k 13 (by decide +kernel)
  have h6 : k.val 10 = k.val 6 := edge_eq k 24 (by decide +kernel)
  have h0 : k.val 0 = k.val 8 := edge_eq k 33 (by decide +kernel)
  have h2 : k.val 8 = k.val 2 := edge_eq k 38 (by decide +kernel)
  have hab : k.val 8 ≠ k.val 10 := edge_ne k 49 (by decide +kernel)
  have hx : k.val 5 ≠ k.val 4 := edge_ne k 5 (by decide +kernel)
  have hz : k.val 1 ≠ k.val 0 := edge_ne k 31 (by decide +kernel)
  have hya : k.val 7 ≠ k.val 6 := edge_ne k 21 (by decide +kernel)
  have hyb : k.val 7 ≠ k.val 0 := edge_ne k 17 (by decide +kernel)
  have hwa : k.val 3 ≠ k.val 4 := edge_ne k 7 (by decide +kernel)
  have hwb : k.val 3 ≠ k.val 2 := edge_ne k 11 (by decide +kernel)
  constructor
  · exact ⟨by simpa only [h4, h0] using hab.symm, hx, hz,
      by simpa only [h4, h6] using hya, hyb, hwa,
      by simpa only [h0, h2] using hwb⟩
  · change [k.val 4, k.val 5, k.val 6, k.val 7, k.val 0, k.val 1, k.val 2, k.val 3] = _
    simp only [boundary, h4, h6, h0, h2]

/-- Exact boundary elimination, with a constructive return direction. -/
theorem contractTrace_iff (et : List Color) :
    (cfmap cf004).map.CcRingTrace (cfcontract cf004) (cfring cf004).reverse et ↔
      ∃ a b x y z w, Admissible a b x y z w ∧ et = trace (boundary a b x y z w) := by
  rw [contractTrace004]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k.val 4, k.val 0, k.val 5, k.val 7, k.val 1, k.val 3,
      (eliminate k).1, congrArg trace (eliminate k).2⟩
  · rintro ⟨a, b, x, y, z, w, h, rfl⟩
    exact ⟨assignment a b x y z w h, rfl⟩

end FourColor.DiamondJointContract
