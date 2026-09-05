import Mettapedia.GraphTheory.FourColor.PresentedClosedForm

/-!
# A vertex-ordered enumerator for presented tangles (computable part)

Given a presentation and an in-word, the enumerator processes the vertices in
order, keeping every partial assignment of edge and out-port digits that is
proper on the vertices seen so far, branching on the unassigned slots of each
vertex.  The complete assignments give the accepted out-words as a bitmask.
Correctness against `Pres.accepts_iff` is the next seal; this file is the
program and its cross-check on the thickness-2 rung against the lab's table.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace TubeSlab
namespace Presented

/-- a partial assignment: edge digits and out-port digits, `none` = unassigned -/
structure PA (N k : Nat) where
  e : Fin N → Option (Fin 3)
  o : Fin k → Option (Fin 3)

namespace PA

variable {N k : Nat}

def empty : PA N k := ⟨fun _ => none, fun _ => none⟩

/-- the digit of a slot under an in-word and a partial assignment -/
def look (x : Fin k → Fin 3) (σ : PA N k) : Slot N k → Option (Fin 3)
  | Slot.edge e => σ.e e
  | Slot.inp i => some (x i)
  | Slot.out i => σ.o i

/-- set a slot's digit (in-ports are never set) -/
def set (σ : PA N k) : Slot N k → Fin 3 → PA N k
  | Slot.edge e, d => ⟨Function.update σ.e e (some d), σ.o⟩
  | Slot.inp _, _ => σ
  | Slot.out i, d => ⟨σ.e, Function.update σ.o i (some d)⟩

/-- all ways to assign an unassigned slot -/
def branch (x : Fin k → Fin 3) (σ : PA N k) (s : Slot N k) : List (PA N k) :=
  match σ.look x s with
  | some _ => [σ]
  | none => [σ.set s 0, σ.set s 1, σ.set s 2]

/-- the three slot digits of a vertex are pairwise distinct -/
def properAt (x : Fin k → Fin 3) (σ : PA N k) (s0 s1 s2 : Slot N k) : Bool :=
  match σ.look x s0, σ.look x s1, σ.look x s2 with
  | some a, some b, some c => a != b && a != c && b != c
  | _, _, _ => false

end PA

namespace Pres

variable {V N k : Nat} (P : Pres V N k)

/-- process one vertex: branch on its unassigned slots, keep the proper assignments -/
def stepVertex (x : Fin k → Fin 3) (v : Fin V) (σs : List (PA N k)) : List (PA N k) :=
  σs.flatMap fun σ =>
    (PA.branch x σ (P.tri v 0)).flatMap fun σ1 =>
      (PA.branch x σ1 (P.tri v 1)).flatMap fun σ2 =>
        (PA.branch x σ2 (P.tri v 2)).filter fun σ3 =>
          PA.properAt x σ3 (P.tri v 0) (P.tri v 1) (P.tri v 2)

/-- process a list of vertices -/
def runVertices (x : Fin k → Fin 3) : List (Fin V) → List (PA N k) → List (PA N k)
  | [], σs => σs
  | v :: vs, σs => runVertices x vs (P.stepVertex x v σs)

/-- the out-word numeral of a complete assignment (unassigned out-ports read as 0) -/
def outNumeral (σ : PA N k) : Nat :=
  (List.finRange k).foldr (fun i acc => acc * 3 + ((σ.o i).getD 0).val) 0

/-- the in-word of a numeral -/
def inWord (X : Nat) : Fin k → Fin 3 := fun i => ⟨(X / 3 ^ (i : Nat)) % 3, Nat.mod_lt _ (by omega)⟩

/-- **the enumerator**: the mask of accepted out-words for in-word `X` -/
def enumMask (X : Nat) : Nat :=
  (P.runVertices (inWord X) (List.finRange V) [PA.empty]).foldl
    (fun acc σ => acc ||| (1 <<< outNumeral σ)) 0

end Pres

/-! ## The thickness-2 rung as a presentation, and the cross-check -/

namespace RungPres

open Slot

/-- vertices `c, d1, e1, d2, e2, c'`; edges `0..4` along the path; in-ports `0,1,2,3` at
`c, d1, d2, c'`; out-ports at `c, e1, e2, c'` -/
def tri : Fin 6 → Fin 3 → Slot 5 4
  | 0, 0 => inp 0 | 0, 1 => out 0 | 0, 2 => edge 0
  | 1, 0 => edge 0 | 1, 1 => edge 1 | 1, 2 => inp 1
  | 2, 0 => edge 1 | 2, 1 => edge 2 | 2, 2 => out 1
  | 3, 0 => edge 2 | 3, 1 => edge 3 | 3, 2 => inp 2
  | 4, 0 => edge 3 | 4, 1 => edge 4 | 4, 2 => out 2
  | 5, 0 => edge 4 | 5, 1 => inp 3 | 5, 2 => out 3

def endPos : Fin 5 → Bool → Pos 6
  | 0, false => (0, 2) | 0, true => (1, 0)
  | 1, false => (1, 1) | 1, true => (2, 0)
  | 2, false => (2, 1) | 2, true => (3, 0)
  | 3, false => (3, 1) | 3, true => (4, 0)
  | 4, false => (4, 1) | 4, true => (5, 0)

def inPos : Fin 4 → Pos 6
  | 0 => (0, 0) | 1 => (1, 2) | 2 => (3, 2) | 3 => (5, 1)

def outPos : Fin 4 → Pos 6
  | 0 => (0, 1) | 1 => (2, 2) | 2 => (4, 2) | 3 => (5, 2)

def P : Pres 6 5 4 := ⟨tri, endPos, inPos, outPos⟩

theorem valid : P.Valid := by decide

end RungPres

end Presented
end TubeSlab
end Mettapedia.GraphTheory.FourColor
