import Mettapedia.GraphTheory.FourColor.DualTruncateColoring
import Mettapedia.GraphTheory.FourColor.GoertzelV24FiniteTransitionWeakSelfLoop

/-!
# Compact certificates for literal cubic rotations

The three positions at a vertex carry its supplied cyclic neighbour order.
Flat little-endian tables retain edge identities, opposite positions and one
representative of every edge. Local checks establish the rotation-system
axioms without recomputing every edge fibre by a global search. Bounds and
the equality to the supplied neighbour table are checked explicitly.
-/

namespace Mettapedia.GraphTheory.FourColor.CubicRotationByteCertificate

open GoertzelV24FiniteTransitionWeakSelfLoop

abbrev Position (n : Nat) := Fin n × Fin 3

def index {n : Nat} (d : Position n) : Nat := 3 * d.1.val + d.2.val

def position (n : Nat) [NeZero n] (i : Nat) : Position n :=
  (Fin.ofNat n (i / 3), Fin.ofNat 3 i)

/-- Small flat pages avoid repeated reduction through a large array literal. -/
structure Table where
  size : Nat
  pages : Nat → ByteArray

def Table.read (t : Table) (i : Nat) : Nat :=
  readU16LE (t.pages (i / 64)) (i % 64)

def Table.WellFormed (t : Table) (entries : Nat) : Prop :=
  t.size = entries ∧
    ∀ i : Fin entries, 2 * (i.val % 64) + 1 < (t.pages (i.val / 64)).size

instance (t : Table) (entries : Nat) : Decidable (t.WellFormed entries) := by
  unfold Table.WellFormed
  infer_instance

/-- Flat tables describe one supplied cyclic order, not a searched embedding. -/
structure Code (n m : Nat) where
  neighbours : Table
  edges : Table
  mates : Table
  representatives : Table

namespace Code

variable {n m : Nat} [NeZero n] [NeZero m] (c : Code n m)

def mate (d : Position n) : Position n := position n (c.mates.read (index d))
def edge (d : Position n) : Fin m := Fin.ofNat m (c.edges.read (index d))
def representative (e : Fin m) : Position n :=
  position n (c.representatives.read e.val)

def WellFormed : Prop :=
  c.neighbours.WellFormed (3 * n) ∧ c.edges.WellFormed (3 * n) ∧
  c.mates.WellFormed (3 * n) ∧ c.representatives.WellFormed m ∧
  (∀ d : Position n, c.neighbours.read (index d) < n ∧
    c.edges.read (index d) < m ∧ c.mates.read (index d) < 3 * n) ∧
  (∀ e : Fin m, c.representatives.read e.val < 3 * n)

/-- Each decoded edge has exactly the two certified opposite positions. -/
def Valid : Prop :=
  c.WellFormed ∧
  (∀ d, c.mate (c.mate d) = d) ∧
  (∀ d, d.1 ≠ (c.mate d).1) ∧
  (∀ d, c.edge (c.mate d) = c.edge d) ∧
  (∀ e, c.edge (c.representative e) = e) ∧
  (∀ d, d = c.representative (c.edge d) ∨
    d = c.mate (c.representative (c.edge d))) ∧
  (∀ d, c.neighbours.read (index d) = (c.mate d).1.val) ∧
  (∀ (v : Fin n) (i j : Fin 3), i ≠ j →
    c.neighbours.read (index (v, i)) ≠ c.neighbours.read (index (v, j)))

instance : Decidable c.Valid := by unfold Valid WellFormed; infer_instance

def alpha (h : c.Valid) : Equiv.Perm (Position n) where
  toFun := c.mate
  invFun := c.mate
  left_inv := h.2.1
  right_inv := h.2.1

def rho : Equiv.Perm (Position n) where
  toFun d := (d.1, d.2 + 1)
  invFun d := (d.1, d.2 - 1)
  left_inv := by rintro ⟨v, i⟩; simp
  right_inv := by rintro ⟨v, i⟩; simp

theorem fibre (h : c.Valid) (e : Fin m) :
    Finset.univ.filter (fun d => c.edge d = e) =
      {c.representative e, c.mate (c.representative e)} := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hd
    simpa [hd] using h.2.2.2.2.2.1 d
  · rintro (rfl | rfl)
    · exact h.2.2.2.2.1 e
    · exact (h.2.2.2.1 _).trans (h.2.2.2.2.1 e)

/-- The decoder constructs genuine edge fibres and the literal vertex order. -/
abbrev rotation (h : c.Valid) : RotationSystem (Fin n) (Fin m) where
  D := Position n
  edgeOf := c.edge
  vertOf := Prod.fst
  alpha := c.alpha h
  rho := rho
  alpha_involutive := h.2.1
  alpha_fixfree := by
    intro d hd
    exact h.2.2.1 d (congrArg Prod.fst hd).symm
  edge_alpha := h.2.2.2.1
  edge_fiber_two := by
    intro e
    rw [fibre c h e]
    have hn : c.representative e ≠ c.mate (c.representative e) := by
      intro hd
      exact h.2.2.1 _ (congrArg Prod.fst hd)
    simp [hn]
  vert_rho := by intro d; rfl
  outer := (Fin.ofNat n 0, 0)
  no_self_loops := h.2.2.1

theorem cubic (h : c.Valid) : (c.rotation h).IsCubic := by
  intro v
  have hstar : (c.rotation h).dartsAt v =
      ({(v, 0), (v, 1), (v, 2)} : Finset (Position n)) := by
    ext d
    rcases d with ⟨w, i⟩
    fin_cases i <;> simp [RotationSystem.dartsAt, rotation]
  rw [hstar]
  simp

/-- The observed opposite vertex is exactly the supplied neighbour entry. -/
theorem neighbour_fidelity (h : c.Valid) (d : Position n) :
    (c.rotation h).vertOf ((c.rotation h).alpha d) =
      Fin.ofNat n (c.neighbours.read (index d)) := by
  change (c.mate d).1 = _
  apply Fin.ext
  simp only [Fin.ofNat, ← h.2.2.2.2.2.2.1 d]
  exact (Nat.mod_eq_of_lt (h.1.2.2.2.2.1 d).1).symm

end Code

/-- A checked vertex word is an actual input to the uniform reconstruction. -/
def wordColour (word : ByteArray) (v : Nat) : Color :=
  match (word.get! v).toNat with
  | 1 => red
  | 2 => blue
  | _ => purple

def ProperWord {n m : Nat} [NeZero n] [NeZero m]
    (c : Code n m) (word : ByteArray) : Prop :=
  word.size = n ∧
  (∀ v : Fin n, 1 ≤ (word.get! v.val).toNat ∧ (word.get! v.val).toNat ≤ 3) ∧
  (∀ d : Position n, wordColour word d.1.val ≠ wordColour word (c.mate d).1.val)

instance {n m : Nat} [NeZero n] [NeZero m] (c : Code n m) (word : ByteArray) :
    Decidable (ProperWord c word) := by unfold ProperWord; infer_instance

theorem wordColour_nonzero (word : ByteArray) (v : Nat) : wordColour word v ≠ 0 := by
  unfold wordColour
  split <;> simp [red, blue, purple]

def threeVertexColoring {n m : Nat} [NeZero n] [NeZero m]
    (c : Code n m) (h : c.Valid) (word : ByteArray) (hw : ProperWord c word) :
    DualTruncateColoring.ThreeVertexColoring (c.rotation h) where
  colour v := wordColour word v.val
  nonzero v := wordColour_nonzero word v.val
  proper := hw.2.2

end Mettapedia.GraphTheory.FourColor.CubicRotationByteCertificate
