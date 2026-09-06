/-!
# Generic transfer semantics for zigzag rings

The computable transition and stabilisation predicate are retained from the
lab development. Concrete width-five/six tables and their decision proofs
remain on the lab branch; the generic state and tangle consumers need none
of those computations. No stabilisation instance is asserted in this module.
-/

namespace TubeRingOrbit

/-- digit `i` of `w` in base 3 -/
def digit (w i : Nat) : Nat := (w / 3 ^ i) % 3

/-- colour at position `i` chosen by bit `i` of `m`: the smaller (bit 0) or larger
    (bit 1) colour different from `x_i` -/
def pick (x m i : Nat) : Nat :=
  let xi := digit x i
  let lo := if xi = 0 then 1 else 0
  let hi := if xi = 2 then 1 else 2
  if (m / 2 ^ i) % 2 = 1 then hi else lo

/-- the `a`-word for mask `m`, positions `0..n-1` -/
def aWord (x m : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => aWord x m n + pick x m n * 3 ^ n

/-- out-word digits for positions `0..n-1`; `none` if some `a_i = b_i` -/
def outAux (k x a : Nat) : Nat → Option Nat
  | 0 => some 0
  | n + 1 =>
    match outAux k x a n with
    | none => none
    | some y =>
      let ai := digit a n
      let inext := (n + 1) % k
      let bi := 3 - digit x inext - digit a inext
      if ai = bi then none else some (y + (3 - ai - bi) * 3 ^ n)

def outWord (k x a : Nat) : Option Nat := outAux k x a k

/-- out-word set of in-word `x` over masks `0..n-1`, as a bitmask -/
def stepMask (k x : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    let acc := stepMask k x n
    match outWord k x (aWord x n k) with
    | some y => acc ||| (1 <<< y)
    | none => acc

/-- number of positions `< n` whose digit is `c` -/
def count (w c : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => count w c n + (if digit w n = c then 1 else 0)

/-- parity-legal: the three colour counts have the same parity -/
def legal (k w : Nat) : Bool :=
  (count w 0 k % 2 == count w 1 k % 2) && (count w 1 k % 2 == count w 2 k % 2)

def legalWords (k : Nat) : List Nat := (List.range (3 ^ k)).filter (legal k)

/-- the ring relation as a table indexed by word numeral, all `3^k` words -/
def computedTable (k : Nat) : List Nat :=
  (List.range (3 ^ k)).map fun x => stepMask k x (2 ^ k)

/-- push a set of in-words (bitmask) through one ring, using a table -/
def stepSet (S : Nat) : List Nat → Nat → Nat
  | [], _ => 0
  | t :: ts, w => (if (S >>> w) % 2 = 1 then t else 0) ||| stepSet S ts (w + 1)

def iterSet (tab : List Nat) : Nat → Nat → Nat
  | 0, S => S
  | n + 1, S => iterSet tab n (stepSet S tab 0)

/-- for every singleton word (legal or not), `k` rings equal `k-1` rings -/
def stabilizesWith (k : Nat) (tab : List Nat) : Bool :=
  (List.range (3 ^ k)).all fun w => iterSet tab k (1 <<< w) == iterSet tab (k - 1) (1 <<< w)

def stabilizes (k : Nat) : Bool := stabilizesWith k (computedTable k)

end TubeRingOrbit
