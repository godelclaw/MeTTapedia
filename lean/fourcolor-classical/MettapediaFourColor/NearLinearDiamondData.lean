import MettapediaFourColor.DiamondConfigurations

/-!
# The first two configurations of the near-linear catalogue

The source strings reproduce D0000.conf and D0001.conf at revision
c2ce7a96e35256201526e2abb51a39d04a588b53 of
https://github.com/near-linear-4ct/reducible-configurations.
The data are copyright (c) 2026 Yuta Inoue, MIT licensed; the notice and the
unaltered files are retained in tools/fourcolor/near-linear.

The format lists the number of vertices, the ring size, and the cyclic
neighbours of each internal vertex. Ring labels are consecutive, starting at
one. The free completion adds the ring edges. Every field used below is
validated by kernel computation. Boundary stars are supplied explicitly and
checked against the exact reference embeddings, as are all internal stars.
-/

namespace FourColor.NearLinearDiamondData

open DiamondConfigurations ConfigurationTable

private def finishToken (token : Option ℕ) (row : List ℕ) : List ℕ :=
  match token with
  | none => row
  | some n => n :: row

private def finishRow (row : List ℕ) (out : List (List ℕ)) : List (List ℕ) :=
  if row.isEmpty then out else row.reverse :: out

/-- Structural ASCII parser; an unrecognized byte causes failure. -/
private def scanRows : List ℕ → Option ℕ → List ℕ → List (List ℕ) →
    Option (List (List ℕ))
  | [], token, row, out => some (finishRow (finishToken token row) out).reverse
  | c :: cs, token, row, out =>
    if 48 ≤ c ∧ c ≤ 57 then
      scanRows cs (some (10 * token.getD 0 + (c - 48))) row out
    else if c = 32 ∨ c = 9 ∨ c = 13 then
      scanRows cs none (finishToken token row) out
    else if c = 10 then
      scanRows cs none [] (finishRow (finishToken token row) out)
    else none

/-- Parse natural-number rows by kernel-reducible byte inspection. -/
def parseRows (source : String) : Option (List (List ℕ)) :=
  scanRows ((List.range source.toUTF8.size).map fun i =>
    (source.toUTF8[i]?.getD 0).toNat) none [] []

def rows (source : String) : List (List ℕ) := (parseRows source).getD []

def coreRow (source : String) (i : ℕ) : List ℕ := (rows source).getD (i + 1) []

/-- All labelled internal rows and their advertised degrees are checked. -/
def WellFormed (source : String) (n r : ℕ) : Prop :=
  (parseRows source).isSome = true ∧
  (rows source).headD [] = [n, r] ∧
  (rows source).length = n - r + 1 ∧ 3 ≤ r ∧ r ≤ n ∧
  ∀ i : Fin (n - r),
    (coreRow source i).getD 0 0 = r + i.val + 1 ∧
    (coreRow source i).getD 1 0 = ((coreRow source i).drop 2).length ∧
    ((coreRow source i).drop 2).Nodup ∧
    ∀ w ∈ (coreRow source i).drop 2, 1 ≤ w ∧ w ≤ n ∧ w ≠ r + i.val + 1

instance (source : String) (n r : ℕ) : Decidable (WellFormed source n r) := by
  unfold WellFormed
  infer_instance

structure Input (n r : ℕ) where
  source : String
  valid : WellFormed source n r

namespace Input

variable {n r : ℕ} (input : Input n r)

def neighbors (v : Fin n) : List ℕ :=
  if r ≤ v.val then (coreRow input.source (v.val - r)).drop 2 else []

def ringEdge (v w : Fin n) : Prop :=
  v.val < r ∧ w.val < r ∧ ((v.val + 1) % r = w.val ∨ (w.val + 1) % r = v.val)

/-- The listed internal incidences and the consecutive ring edges. -/
def graph : SimpleGraph (Fin n) where
  Adj v w := v ≠ w ∧
    (ringEdge (r := r) v w ∨ w.val + 1 ∈ input.neighbors v ∨ v.val + 1 ∈ input.neighbors w)
  symm := ⟨by
    rintro v w ⟨hne, h | h | h⟩
    · exact ⟨hne.symm, Or.inl ⟨h.2.1, h.1, h.2.2.symm⟩⟩
    · exact ⟨hne.symm, Or.inr (Or.inr h)⟩
    · exact ⟨hne.symm, Or.inr (Or.inl h)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance : DecidableRel input.graph.Adj := by
  intro v w
  unfold graph ringEdge
  infer_instance

def boundary : List (Fin n) :=
  (List.finRange r).map fun i => ⟨i.val, lt_of_lt_of_le i.isLt input.valid.2.2.2.2.1⟩

def internalStar [NeZero n] (v : Fin n) : List (Fin n) :=
  (input.neighbors v).map fun w => ⟨(w - 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩

end Input

def input0000 : Input 10 6 where
  source := "10 6\n7 5 4 5 10 8 3\n8 5 3 7 10 9 2\n9 5 2 8 10 6 1\n10 5 6 9 8 7 5\n"
  valid := by decide +kernel

def input0001 : Input 11 7 where
  source := "11 7\n8 5 2 11 9 7 1\n9 6 6 7 8 11 10 5\n10 5 4 5 9 11 3\n11 5 3 10 9 8 2\n"
  valid := by decide +kernel

/-- Boundary stars are given in the same orientation as the source core rows. -/
def stars0000 (v : Fin 10) : List (Fin 10) :=
  if h : v.val < 6 then
    ![[1, 8, 5], [0, 2, 7, 8], [3, 6, 7, 1], [4, 6, 2],
      [3, 5, 9, 6], [0, 8, 9, 4]] ⟨v.val, h⟩
  else input0000.internalStar v

def stars0001 (v : Fin 11) : List (Fin 11) :=
  if h : v.val < 7 then
    ![[1, 7, 6], [0, 2, 10, 7], [3, 9, 10, 1], [4, 9, 2],
      [5, 8, 9, 3], [6, 8, 4], [5, 0, 7, 8]] ⟨v.val, h⟩
  else input0001.internalStar v

def vertex0000 : Fin 10 ≃ Fin 10 where
  toFun := ![5, 0, 1, 2, 3, 4, 7, 6, 9, 8]
  invFun := ![1, 2, 3, 4, 5, 0, 7, 6, 9, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def vertex0001 : Fin 11 ≃ Fin 11 where
  toFun := ![3, 4, 5, 6, 0, 1, 2, 8, 7, 10, 9]
  invFun := ![4, 5, 6, 0, 1, 2, 3, 8, 7, 10, 9]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

set_option maxRecDepth 32768 in
def iso0000 : input0000.graph ≃g graph001 where
  toEquiv := vertex0000
  map_rel_iff' := by decide +kernel

set_option maxRecDepth 32768 in
def iso0001 : input0001.graph ≃g graph002 where
  toEquiv := vertex0001
  map_rel_iff' := by decide +kernel

set_option maxRecDepth 32768 in
theorem rotation0000 : ∀ v : Fin 10, ∃ shift : Fin 6,
    stars001 (iso0000 v) = ((stars0000 v).map iso0000).rotate shift.val := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem rotation0001 : ∀ v : Fin 11, ∃ shift : Fin 7,
    stars002 (iso0001 v) = ((stars0001 v).map iso0001).rotate shift.val := by
  decide +kernel

theorem degree0000 : ∀ i : Fin 4,
    (coreRow input0000.source i).getD 1 0 = degree001 (iso0000 (i.natAdd 6)) := by
  decide +kernel

theorem degree0001 : ∀ i : Fin 4,
    (coreRow input0001.source i).getD 1 0 = degree002 (iso0001 (i.natAdd 7)) := by
  decide +kernel

theorem boundary0000 : (input0000.boundary.map iso0000).rotate 5 = boundary001.reverse := by
  decide +kernel

theorem boundary0001 : (input0001.boundary.map iso0001).rotate 4 = boundary002.reverse := by
  decide +kernel

end FourColor.NearLinearDiamondData
