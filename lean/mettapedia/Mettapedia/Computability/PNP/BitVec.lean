/-!
# PNP bit-vector basics

Shared finite Boolean vectors used by the PNP obstruction library.
-/

namespace Mettapedia.Computability.PNP

/-- Length-`n` bit-vectors, represented extensionally as Boolean functions on `Fin n`. -/
abbrev BitVec (n : Nat) := Fin n → Bool

/-- The all-false bit-vector. -/
def zeroVec {n : Nat} : BitVec n := fun _ => false

/-- Bitwise exclusive-or, used by the post-switch right-hand-side update. -/
def vvToggle {n : Nat} (a b : BitVec n) : BitVec n :=
  fun i => Bool.xor (b i) (a i)

/-- A bit-vector with at least one true coordinate. -/
def nonzeroColumn {n : Nat} (a : BitVec n) : Prop :=
  Exists fun i => a i = true

/-- Toggle one coordinate of a bit-vector. -/
def toggleBit {n : Nat} (x : BitVec n) (i : Fin n) : BitVec n :=
  fun j => if j = i then !(x i) else x j

/-- The bit-vector supported on one coordinate. -/
def singletonVec {n : Nat} (i : Fin n) : BitVec n :=
  fun j => decide (j = i)

/-- The bit-vector supported on two coordinates. -/
def pairVec {n : Nat} (i j : Fin n) : BitVec n :=
  fun t => decide (t = i ∨ t = j)

/-- The bit-vector with a single true coordinate at `0`, available for positive widths. -/
def headOneVec {n : Nat} (hn : 0 < n) : BitVec n :=
  fun i => decide (i = ⟨0, hn⟩)

@[simp] theorem toggleBit_apply_same {n : Nat} (x : BitVec n) (i : Fin n) :
    toggleBit x i i = !(x i) := by
  simp [toggleBit]

@[simp] theorem toggleBit_apply_of_ne {n : Nat} (x : BitVec n) {i j : Fin n}
    (hij : j ≠ i) :
    toggleBit x i j = x j := by
  simp [toggleBit, hij]

theorem toggleBit_ne_self {n : Nat} (x : BitVec n) (i : Fin n) :
    toggleBit x i ≠ x := by
  intro h
  have hi := congrFun h i
  cases hxi : x i <;> simp [toggleBit, hxi] at hi

@[simp] theorem singletonVec_apply_self {n : Nat} (i : Fin n) :
    singletonVec i i = true := by
  simp [singletonVec]

@[simp] theorem singletonVec_apply_of_ne {n : Nat} {i j : Fin n} (hij : j ≠ i) :
    singletonVec i j = false := by
  simp [singletonVec, hij]

theorem singletonVec_ne_zeroVec {n : Nat} (i : Fin n) :
    singletonVec i ≠ zeroVec := by
  intro h
  have hi : singletonVec i i = false := by
    simpa [zeroVec] using congrFun h i
  simp [singletonVec] at hi

theorem singletonVec_ne_singletonVec {n : Nat} {i j : Fin n} (hij : i ≠ j) :
    singletonVec i ≠ singletonVec j := by
  intro h
  have hi : singletonVec i i = singletonVec j i := congrFun h i
  simp [singletonVec, hij] at hi

theorem pairVec_ne_zeroVec {n : Nat} {i j : Fin n} (hij : i ≠ j) :
    pairVec i j ≠ zeroVec := by
  intro h
  have hi : pairVec i j i = false := by
    simpa [zeroVec] using congrFun h i
  simp [pairVec, hij] at hi

@[simp] theorem headOneVec_head {n : Nat} (hn : 0 < n) :
    headOneVec hn ⟨0, hn⟩ = true := by
  simp [headOneVec]

@[simp] theorem headOneVec_zeroVec_ne {n : Nat} (hn : 0 < n) :
    headOneVec hn ≠ zeroVec := by
  intro h
  have : headOneVec hn ⟨0, hn⟩ = false := by
    simpa [zeroVec] using congrFun h ⟨0, hn⟩
  simp [headOneVec] at this

end Mettapedia.Computability.PNP
