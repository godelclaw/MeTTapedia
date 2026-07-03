import Mathlib.Data.List.Basic
import Mathlib.Data.List.Perm.Subperm

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.14: finite `LKR_in` audit

This module formalizes the finite local check from Goertzel's Lemma 8.14 for
the canonical three-cell collar gadget.  The gadget has internal vertices
`F0..F5`, boundary stubs `B0..B7`, internal tree
`F1-F0-F2-F4-F5` with leaf `F3`, and fixed input stubs `B0..B3`.

The definitions below are intentionally finite and concrete: a coloring state
is one of the proper 3-edge-colorings of this fixed tree gadget, Kempe steps
are switches on two-color components disjoint from the input stubs, and
`tauLKRInAudit` checks that every fixed-input fiber is connected.
-/

namespace GoertzelLemma814

/-- The three nonzero edge colors used in the local gadget. -/
inductive LColor
  | r
  | b
  | p
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr, Inhabited

def colors : List LColor :=
  [LColor.r, LColor.b, LColor.p]

def colorPairs : List (LColor × LColor) :=
  [(LColor.r, LColor.b), (LColor.r, LColor.p), (LColor.b, LColor.p)]

def colorEq (x y : LColor) : Bool :=
  if x = y then true else false

def colorInPair (x a c : LColor) : Bool :=
  colorEq x a || colorEq x c

def swapColor (a c x : LColor) : LColor :=
  if x = a then c else if x = c then a else x

/-- The ordered pair of the two colors different from `x`. -/
def otherPair : LColor → LColor × LColor
  | LColor.r => (LColor.b, LColor.p)
  | LColor.b => (LColor.r, LColor.p)
  | LColor.p => (LColor.r, LColor.b)

def orderedOtherPair (x : LColor) (swap : Bool) : LColor × LColor :=
  let q := otherPair x
  if swap then (q.2, q.1) else q

/-- Edges of the canonical three-cell gadget.  Stub names denote the edge
incident to that boundary stub. -/
inductive TauEdge
  | F1F0
  | F0F2
  | F2F3
  | F2F4
  | F4F5
  | B0
  | B1
  | B2
  | B3
  | B4
  | B5
  | B6
  | B7
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr, Inhabited

def tauEdges : List TauEdge :=
  [ TauEdge.F1F0
  , TauEdge.F0F2
  , TauEdge.F2F3
  , TauEdge.F2F4
  , TauEdge.F4F5
  , TauEdge.B0
  , TauEdge.B1
  , TauEdge.B2
  , TauEdge.B3
  , TauEdge.B4
  , TauEdge.B5
  , TauEdge.B6
  , TauEdge.B7
  ]

def tauInputEdges : List TauEdge :=
  [TauEdge.B0, TauEdge.B1, TauEdge.B2, TauEdge.B3]

/-- Internal vertices of the canonical three-cell gadget. -/
inductive TauVertex
  | F0
  | F1
  | F2
  | F3
  | F4
  | F5
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr, Inhabited

def tauVertices : List TauVertex :=
  [TauVertex.F0, TauVertex.F1, TauVertex.F2, TauVertex.F3, TauVertex.F4, TauVertex.F5]

def incidentEdges : TauVertex → List TauEdge
  | TauVertex.F0 => [TauEdge.B0, TauEdge.F1F0, TauEdge.F0F2]
  | TauVertex.F1 => [TauEdge.B1, TauEdge.B2, TauEdge.F1F0]
  | TauVertex.F2 => [TauEdge.F0F2, TauEdge.F2F3, TauEdge.F2F4]
  | TauVertex.F3 => [TauEdge.B3, TauEdge.B4, TauEdge.F2F3]
  | TauVertex.F4 => [TauEdge.F2F4, TauEdge.F4F5, TauEdge.B7]
  | TauVertex.F5 => [TauEdge.F4F5, TauEdge.B5, TauEdge.B6]

def shareInternalVertex (e f : TauEdge) : Bool :=
  if e = f then
    false
  else
    tauVertices.any fun v => (incidentEdges v).contains e && (incidentEdges v).contains f

/-- A distinct ordered triple of colors at the central vertex `F2`. -/
structure F2Triple where
  e02 : LColor
  e23 : LColor
  e24 : LColor
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr, Inhabited

def f2Triples : List F2Triple :=
  [ ⟨LColor.r, LColor.b, LColor.p⟩
  , ⟨LColor.r, LColor.p, LColor.b⟩
  , ⟨LColor.b, LColor.r, LColor.p⟩
  , ⟨LColor.b, LColor.p, LColor.r⟩
  , ⟨LColor.p, LColor.r, LColor.b⟩
  , ⟨LColor.p, LColor.b, LColor.r⟩
  ]

/--
A proper coloring of `tau`, represented by the finite choices left after
properness at every internal cubic vertex is imposed.

For any central ordered triple `(F0F2, F2F3, F2F4)`, the edge `F1F0` is one of
the two colors different from `F0F2`; each remaining boundary pair is then an
ordered pair of the two colors not used by its adjacent internal edge.
-/
structure TauState where
  f2 : F2Triple
  e10UsesE23 : Bool
  b1b2Swap : Bool
  b3b4Swap : Bool
  f4Swap : Bool
  b5b6Swap : Bool
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr, Inhabited

def bools : List Bool :=
  [false, true]

def bindList (xs : List α) (f : α → List β) : List β :=
  xs.foldr (fun x acc => f x ++ acc) []

def allTauStates : List TauState :=
  bindList f2Triples fun f2 =>
  bindList bools fun e10UsesE23 =>
  bindList bools fun b1b2Swap =>
  bindList bools fun b3b4Swap =>
  bindList bools fun f4Swap =>
  bools.map fun b5b6Swap =>
    { f2 := f2
      e10UsesE23 := e10UsesE23
      b1b2Swap := b1b2Swap
      b3b4Swap := b3b4Swap
      f4Swap := f4Swap
      b5b6Swap := b5b6Swap }

def TauState.e10 (s : TauState) : LColor :=
  if s.e10UsesE23 then s.f2.e23 else s.f2.e24

def TauState.b0 (s : TauState) : LColor :=
  if s.e10UsesE23 then s.f2.e24 else s.f2.e23

def TauState.e45 (s : TauState) : LColor :=
  (orderedOtherPair s.f2.e24 s.f4Swap).1

def TauState.b7 (s : TauState) : LColor :=
  (orderedOtherPair s.f2.e24 s.f4Swap).2

def TauState.color (s : TauState) : TauEdge → LColor
  | TauEdge.F1F0 => s.e10
  | TauEdge.F0F2 => s.f2.e02
  | TauEdge.F2F3 => s.f2.e23
  | TauEdge.F2F4 => s.f2.e24
  | TauEdge.F4F5 => s.e45
  | TauEdge.B0 => s.b0
  | TauEdge.B1 => (orderedOtherPair s.e10 s.b1b2Swap).1
  | TauEdge.B2 => (orderedOtherPair s.e10 s.b1b2Swap).2
  | TauEdge.B3 => (orderedOtherPair s.f2.e23 s.b3b4Swap).1
  | TauEdge.B4 => (orderedOtherPair s.f2.e23 s.b3b4Swap).2
  | TauEdge.B5 => (orderedOtherPair s.e45 s.b5b6Swap).1
  | TauEdge.B6 => (orderedOtherPair s.e45 s.b5b6Swap).2
  | TauEdge.B7 => s.b7

def pairwiseDistinct3 (x y z : LColor) : Bool :=
  !colorEq x y && !colorEq x z && !colorEq y z

def properAt (s : TauState) (v : TauVertex) : Bool :=
  match incidentEdges v with
  | [e₀, e₁, e₂] => pairwiseDistinct3 (s.color e₀) (s.color e₁) (s.color e₂)
  | _ => false

def tauProperState (s : TauState) : Bool :=
  tauVertices.all (properAt s)

def edgeInPair (s : TauState) (a c : LColor) (e : TauEdge) : Bool :=
  colorInPair (s.color e) a c

def addIfFresh [BEq α] (xs : List α) (x : α) : List α :=
  if xs.contains x then xs else xs ++ [x]

def appendFresh [BEq α] (xs ys : List α) : List α :=
  ys.foldl addIfFresh xs

def nextComponentLayer (s : TauState) (a c : LColor) (seen : List TauEdge) : List TauEdge :=
  tauEdges.filter fun e =>
    edgeInPair s a c e &&
      !seen.contains e &&
      seen.any (shareInternalVertex e)

def closeComponent (s : TauState) (a c : LColor) : Nat → List TauEdge → List TauEdge
  | 0, seen => seen
  | n + 1, seen =>
      let layer := nextComponentLayer s a c seen
      closeComponent s a c n (appendFresh seen layer)

def tauComponent (s : TauState) (a c : LColor) (seed : TauEdge) : List TauEdge :=
  if edgeInPair s a c seed then
    closeComponent s a c tauEdges.length [seed]
  else
    []

def componentAvoidsInputs (component : List TauEdge) : Bool :=
  !component.any (fun e => tauInputEdges.contains e)

def switchedColor (s : TauState) (component : List TauEdge) (a c : LColor) (e : TauEdge) : LColor :=
  if component.contains e then swapColor a c (s.color e) else s.color e

def agreesWithSwitch (s t : TauState) (component : List TauEdge) (a c : LColor) : Bool :=
  tauEdges.all fun e => colorEq (t.color e) (switchedColor s component a c e)

def singleKempeStep (s t : TauState) : Bool :=
  colorPairs.any fun pair =>
    let a := pair.1
    let c := pair.2
    tauEdges.any fun seed =>
      let component := tauComponent s a c seed
      !component.isEmpty && componentAvoidsInputs component && agreesWithSwitch s t component a c

def sameInput (s t : TauState) : Bool :=
  tauInputEdges.all fun e => colorEq (s.color e) (t.color e)

structure KempeMove where
  a : LColor
  c : LColor
  seed : TauEdge
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr, Inhabited

structure IndexedPathStep where
  move : KempeMove
  target : Nat
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr, Inhabited

structure IndexedPathRow where
  representative : Nat
  steps : List IndexedPathStep
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr, Inhabited

def mv (a c : LColor) (seed : TauEdge) : KempeMove :=
  { a := a, c := c, seed := seed }

def step (move : KempeMove) (target : Nat) : IndexedPathStep :=
  { move := move, target := target }

def row (representative : Nat) (steps : List IndexedPathStep) : IndexedPathRow :=
  { representative := representative, steps := steps }

def mkTauState (f2 : F2Triple)
    (e10UsesE23 b1b2Swap b3b4Swap f4Swap b5b6Swap : Bool) : TauState :=
  { f2 := f2
    e10UsesE23 := e10UsesE23
    b1b2Swap := b1b2Swap
    b3b4Swap := b3b4Swap
    f4Swap := f4Swap
    b5b6Swap := b5b6Swap }

def f2_rbp : F2Triple := ⟨LColor.r, LColor.b, LColor.p⟩
def f2_rpb : F2Triple := ⟨LColor.r, LColor.p, LColor.b⟩
def f2_brp : F2Triple := ⟨LColor.b, LColor.r, LColor.p⟩
def f2_bpr : F2Triple := ⟨LColor.b, LColor.p, LColor.r⟩
def f2_prb : F2Triple := ⟨LColor.p, LColor.r, LColor.b⟩
def f2_pbr : F2Triple := ⟨LColor.p, LColor.b, LColor.r⟩

def stateAt : Nat → TauState
  | 0 => mkTauState f2_rbp false false false false false
  | 1 => mkTauState f2_rbp false false false false true
  | 2 => mkTauState f2_rbp false false false true false
  | 3 => mkTauState f2_rbp false false false true true
  | 4 => mkTauState f2_rbp false false true false false
  | 5 => mkTauState f2_rbp false false true false true
  | 6 => mkTauState f2_rbp false false true true false
  | 7 => mkTauState f2_rbp false false true true true
  | 8 => mkTauState f2_rbp false true false false false
  | 9 => mkTauState f2_rbp false true false false true
  | 10 => mkTauState f2_rbp false true false true false
  | 11 => mkTauState f2_rbp false true false true true
  | 12 => mkTauState f2_rbp false true true false false
  | 13 => mkTauState f2_rbp false true true false true
  | 14 => mkTauState f2_rbp false true true true false
  | 15 => mkTauState f2_rbp false true true true true
  | 16 => mkTauState f2_rbp true false false false false
  | 17 => mkTauState f2_rbp true false false false true
  | 18 => mkTauState f2_rbp true false false true false
  | 19 => mkTauState f2_rbp true false false true true
  | 20 => mkTauState f2_rbp true false true false false
  | 21 => mkTauState f2_rbp true false true false true
  | 22 => mkTauState f2_rbp true false true true false
  | 23 => mkTauState f2_rbp true false true true true
  | 24 => mkTauState f2_rbp true true false false false
  | 25 => mkTauState f2_rbp true true false false true
  | 26 => mkTauState f2_rbp true true false true false
  | 27 => mkTauState f2_rbp true true false true true
  | 28 => mkTauState f2_rbp true true true false false
  | 29 => mkTauState f2_rbp true true true false true
  | 30 => mkTauState f2_rbp true true true true false
  | 31 => mkTauState f2_rbp true true true true true
  | 32 => mkTauState f2_rpb false false false false false
  | 33 => mkTauState f2_rpb false false false false true
  | 34 => mkTauState f2_rpb false false false true false
  | 35 => mkTauState f2_rpb false false false true true
  | 36 => mkTauState f2_rpb false false true false false
  | 37 => mkTauState f2_rpb false false true false true
  | 38 => mkTauState f2_rpb false false true true false
  | 39 => mkTauState f2_rpb false false true true true
  | 40 => mkTauState f2_rpb false true false false false
  | 41 => mkTauState f2_rpb false true false false true
  | 42 => mkTauState f2_rpb false true false true false
  | 43 => mkTauState f2_rpb false true false true true
  | 44 => mkTauState f2_rpb false true true false false
  | 45 => mkTauState f2_rpb false true true false true
  | 46 => mkTauState f2_rpb false true true true false
  | 47 => mkTauState f2_rpb false true true true true
  | 48 => mkTauState f2_rpb true false false false false
  | 49 => mkTauState f2_rpb true false false false true
  | 50 => mkTauState f2_rpb true false false true false
  | 51 => mkTauState f2_rpb true false false true true
  | 52 => mkTauState f2_rpb true false true false false
  | 53 => mkTauState f2_rpb true false true false true
  | 54 => mkTauState f2_rpb true false true true false
  | 55 => mkTauState f2_rpb true false true true true
  | 56 => mkTauState f2_rpb true true false false false
  | 57 => mkTauState f2_rpb true true false false true
  | 58 => mkTauState f2_rpb true true false true false
  | 59 => mkTauState f2_rpb true true false true true
  | 60 => mkTauState f2_rpb true true true false false
  | 61 => mkTauState f2_rpb true true true false true
  | 62 => mkTauState f2_rpb true true true true false
  | 63 => mkTauState f2_rpb true true true true true
  | 64 => mkTauState f2_brp false false false false false
  | 65 => mkTauState f2_brp false false false false true
  | 66 => mkTauState f2_brp false false false true false
  | 67 => mkTauState f2_brp false false false true true
  | 68 => mkTauState f2_brp false false true false false
  | 69 => mkTauState f2_brp false false true false true
  | 70 => mkTauState f2_brp false false true true false
  | 71 => mkTauState f2_brp false false true true true
  | 72 => mkTauState f2_brp false true false false false
  | 73 => mkTauState f2_brp false true false false true
  | 74 => mkTauState f2_brp false true false true false
  | 75 => mkTauState f2_brp false true false true true
  | 76 => mkTauState f2_brp false true true false false
  | 77 => mkTauState f2_brp false true true false true
  | 78 => mkTauState f2_brp false true true true false
  | 79 => mkTauState f2_brp false true true true true
  | 80 => mkTauState f2_brp true false false false false
  | 81 => mkTauState f2_brp true false false false true
  | 82 => mkTauState f2_brp true false false true false
  | 83 => mkTauState f2_brp true false false true true
  | 84 => mkTauState f2_brp true false true false false
  | 85 => mkTauState f2_brp true false true false true
  | 86 => mkTauState f2_brp true false true true false
  | 87 => mkTauState f2_brp true false true true true
  | 88 => mkTauState f2_brp true true false false false
  | 89 => mkTauState f2_brp true true false false true
  | 90 => mkTauState f2_brp true true false true false
  | 91 => mkTauState f2_brp true true false true true
  | 92 => mkTauState f2_brp true true true false false
  | 93 => mkTauState f2_brp true true true false true
  | 94 => mkTauState f2_brp true true true true false
  | 95 => mkTauState f2_brp true true true true true
  | 96 => mkTauState f2_bpr false false false false false
  | 97 => mkTauState f2_bpr false false false false true
  | 98 => mkTauState f2_bpr false false false true false
  | 99 => mkTauState f2_bpr false false false true true
  | 100 => mkTauState f2_bpr false false true false false
  | 101 => mkTauState f2_bpr false false true false true
  | 102 => mkTauState f2_bpr false false true true false
  | 103 => mkTauState f2_bpr false false true true true
  | 104 => mkTauState f2_bpr false true false false false
  | 105 => mkTauState f2_bpr false true false false true
  | 106 => mkTauState f2_bpr false true false true false
  | 107 => mkTauState f2_bpr false true false true true
  | 108 => mkTauState f2_bpr false true true false false
  | 109 => mkTauState f2_bpr false true true false true
  | 110 => mkTauState f2_bpr false true true true false
  | 111 => mkTauState f2_bpr false true true true true
  | 112 => mkTauState f2_bpr true false false false false
  | 113 => mkTauState f2_bpr true false false false true
  | 114 => mkTauState f2_bpr true false false true false
  | 115 => mkTauState f2_bpr true false false true true
  | 116 => mkTauState f2_bpr true false true false false
  | 117 => mkTauState f2_bpr true false true false true
  | 118 => mkTauState f2_bpr true false true true false
  | 119 => mkTauState f2_bpr true false true true true
  | 120 => mkTauState f2_bpr true true false false false
  | 121 => mkTauState f2_bpr true true false false true
  | 122 => mkTauState f2_bpr true true false true false
  | 123 => mkTauState f2_bpr true true false true true
  | 124 => mkTauState f2_bpr true true true false false
  | 125 => mkTauState f2_bpr true true true false true
  | 126 => mkTauState f2_bpr true true true true false
  | 127 => mkTauState f2_bpr true true true true true
  | 128 => mkTauState f2_prb false false false false false
  | 129 => mkTauState f2_prb false false false false true
  | 130 => mkTauState f2_prb false false false true false
  | 131 => mkTauState f2_prb false false false true true
  | 132 => mkTauState f2_prb false false true false false
  | 133 => mkTauState f2_prb false false true false true
  | 134 => mkTauState f2_prb false false true true false
  | 135 => mkTauState f2_prb false false true true true
  | 136 => mkTauState f2_prb false true false false false
  | 137 => mkTauState f2_prb false true false false true
  | 138 => mkTauState f2_prb false true false true false
  | 139 => mkTauState f2_prb false true false true true
  | 140 => mkTauState f2_prb false true true false false
  | 141 => mkTauState f2_prb false true true false true
  | 142 => mkTauState f2_prb false true true true false
  | 143 => mkTauState f2_prb false true true true true
  | 144 => mkTauState f2_prb true false false false false
  | 145 => mkTauState f2_prb true false false false true
  | 146 => mkTauState f2_prb true false false true false
  | 147 => mkTauState f2_prb true false false true true
  | 148 => mkTauState f2_prb true false true false false
  | 149 => mkTauState f2_prb true false true false true
  | 150 => mkTauState f2_prb true false true true false
  | 151 => mkTauState f2_prb true false true true true
  | 152 => mkTauState f2_prb true true false false false
  | 153 => mkTauState f2_prb true true false false true
  | 154 => mkTauState f2_prb true true false true false
  | 155 => mkTauState f2_prb true true false true true
  | 156 => mkTauState f2_prb true true true false false
  | 157 => mkTauState f2_prb true true true false true
  | 158 => mkTauState f2_prb true true true true false
  | 159 => mkTauState f2_prb true true true true true
  | 160 => mkTauState f2_pbr false false false false false
  | 161 => mkTauState f2_pbr false false false false true
  | 162 => mkTauState f2_pbr false false false true false
  | 163 => mkTauState f2_pbr false false false true true
  | 164 => mkTauState f2_pbr false false true false false
  | 165 => mkTauState f2_pbr false false true false true
  | 166 => mkTauState f2_pbr false false true true false
  | 167 => mkTauState f2_pbr false false true true true
  | 168 => mkTauState f2_pbr false true false false false
  | 169 => mkTauState f2_pbr false true false false true
  | 170 => mkTauState f2_pbr false true false true false
  | 171 => mkTauState f2_pbr false true false true true
  | 172 => mkTauState f2_pbr false true true false false
  | 173 => mkTauState f2_pbr false true true false true
  | 174 => mkTauState f2_pbr false true true true false
  | 175 => mkTauState f2_pbr false true true true true
  | 176 => mkTauState f2_pbr true false false false false
  | 177 => mkTauState f2_pbr true false false false true
  | 178 => mkTauState f2_pbr true false false true false
  | 179 => mkTauState f2_pbr true false false true true
  | 180 => mkTauState f2_pbr true false true false false
  | 181 => mkTauState f2_pbr true false true false true
  | 182 => mkTauState f2_pbr true false true true false
  | 183 => mkTauState f2_pbr true false true true true
  | 184 => mkTauState f2_pbr true true false false false
  | 185 => mkTauState f2_pbr true true false false true
  | 186 => mkTauState f2_pbr true true false true false
  | 187 => mkTauState f2_pbr true true false true true
  | 188 => mkTauState f2_pbr true true true false false
  | 189 => mkTauState f2_pbr true true true false true
  | 190 => mkTauState f2_pbr true true true true false
  | 191 => mkTauState f2_pbr true true true true true
  | _ => default
def indexInStateSpace (i : Nat) : Bool :=
  i < 192

def specifiedKempeStep (s t : TauState) (move : KempeMove) : Bool :=
  let component := tauComponent s move.a move.c move.seed
  !component.isEmpty &&
    componentAvoidsInputs component &&
    agreesWithSwitch s t component move.a move.c

def validIndexedPathSteps : Nat → List IndexedPathStep → Nat → Bool
  | current, [], representative => current == representative
  | current, next :: rest, representative =>
      indexInStateSpace next.target &&
        specifiedKempeStep (stateAt current) (stateAt next.target) next.move &&
        validIndexedPathSteps next.target rest representative

def validIndexedPathRow (source : Nat) (r : IndexedPathRow) : Bool :=
  indexInStateSpace source &&
    indexInStateSpace r.representative &&
    sameInput (stateAt source) (stateAt r.representative) &&
    r.steps.length <= 2 &&
    validIndexedPathSteps source r.steps r.representative

def validIndexedRowsFrom : Nat → List IndexedPathRow → Bool
  | _, [] => true
  | source, r :: rs => validIndexedPathRow source r && validIndexedRowsFrom (source + 1) rs

def lemma814PathCertificate : List IndexedPathRow :=
[
  row 0 [],
  row 0 [step (mv LColor.b LColor.p TauEdge.B5) 0],
  row 0 [step (mv LColor.r LColor.b TauEdge.F4F5) 0],
  row 0 [step (mv LColor.r LColor.b TauEdge.F4F5) 1, step (mv LColor.b LColor.p TauEdge.B5) 0],
  row 4 [],
  row 4 [step (mv LColor.b LColor.p TauEdge.B5) 4],
  row 4 [step (mv LColor.r LColor.b TauEdge.F4F5) 4],
  row 4 [step (mv LColor.r LColor.b TauEdge.F4F5) 5, step (mv LColor.b LColor.p TauEdge.B5) 4],
  row 8 [],
  row 8 [step (mv LColor.b LColor.p TauEdge.B5) 8],
  row 8 [step (mv LColor.r LColor.b TauEdge.F4F5) 8],
  row 8 [step (mv LColor.r LColor.b TauEdge.F4F5) 9, step (mv LColor.b LColor.p TauEdge.B5) 8],
  row 12 [],
  row 12 [step (mv LColor.b LColor.p TauEdge.B5) 12],
  row 12 [step (mv LColor.r LColor.b TauEdge.F4F5) 12],
  row 12 [step (mv LColor.r LColor.b TauEdge.F4F5) 13, step (mv LColor.b LColor.p TauEdge.B5) 12],
  row 16 [],
  row 16 [step (mv LColor.b LColor.p TauEdge.B5) 16],
  row 16 [step (mv LColor.r LColor.b TauEdge.F4F5) 16],
  row 16 [step (mv LColor.r LColor.b TauEdge.F4F5) 17, step (mv LColor.b LColor.p TauEdge.B5) 16],
  row 20 [],
  row 20 [step (mv LColor.b LColor.p TauEdge.B5) 20],
  row 20 [step (mv LColor.r LColor.b TauEdge.F4F5) 20],
  row 20 [step (mv LColor.r LColor.b TauEdge.F4F5) 21, step (mv LColor.b LColor.p TauEdge.B5) 20],
  row 24 [],
  row 24 [step (mv LColor.b LColor.p TauEdge.B5) 24],
  row 24 [step (mv LColor.r LColor.b TauEdge.F4F5) 24],
  row 24 [step (mv LColor.r LColor.b TauEdge.F4F5) 25, step (mv LColor.b LColor.p TauEdge.B5) 24],
  row 28 [],
  row 28 [step (mv LColor.b LColor.p TauEdge.B5) 28],
  row 28 [step (mv LColor.r LColor.b TauEdge.F4F5) 28],
  row 28 [step (mv LColor.r LColor.b TauEdge.F4F5) 29, step (mv LColor.b LColor.p TauEdge.B5) 28],
  row 16 [step (mv LColor.b LColor.p TauEdge.F2F3) 16],
  row 16 [step (mv LColor.b LColor.p TauEdge.F2F3) 17, step (mv LColor.b LColor.p TauEdge.B5) 16],
  row 16 [step (mv LColor.b LColor.p TauEdge.F2F3) 18, step (mv LColor.r LColor.b TauEdge.F4F5) 16],
  row 16 [step (mv LColor.r LColor.p TauEdge.F4F5) 32, step (mv LColor.b LColor.p TauEdge.F2F3) 16],
  row 36 [],
  row 36 [step (mv LColor.b LColor.p TauEdge.B5) 36],
  row 36 [step (mv LColor.r LColor.p TauEdge.F4F5) 37, step (mv LColor.b LColor.p TauEdge.B5) 36],
  row 36 [step (mv LColor.r LColor.p TauEdge.F4F5) 36],
  row 24 [step (mv LColor.b LColor.p TauEdge.F2F3) 24],
  row 24 [step (mv LColor.b LColor.p TauEdge.F2F3) 25, step (mv LColor.b LColor.p TauEdge.B5) 24],
  row 24 [step (mv LColor.b LColor.p TauEdge.F2F3) 26, step (mv LColor.r LColor.b TauEdge.F4F5) 24],
  row 24 [step (mv LColor.r LColor.p TauEdge.F4F5) 40, step (mv LColor.b LColor.p TauEdge.F2F3) 24],
  row 44 [],
  row 44 [step (mv LColor.b LColor.p TauEdge.B5) 44],
  row 44 [step (mv LColor.r LColor.p TauEdge.F4F5) 45, step (mv LColor.b LColor.p TauEdge.B5) 44],
  row 44 [step (mv LColor.r LColor.p TauEdge.F4F5) 44],
  row 0 [step (mv LColor.b LColor.p TauEdge.F2F3) 0],
  row 0 [step (mv LColor.b LColor.p TauEdge.F2F3) 1, step (mv LColor.b LColor.p TauEdge.B5) 0],
  row 0 [step (mv LColor.b LColor.p TauEdge.F2F3) 2, step (mv LColor.r LColor.b TauEdge.F4F5) 0],
  row 0 [step (mv LColor.r LColor.p TauEdge.F4F5) 48, step (mv LColor.b LColor.p TauEdge.F2F3) 0],
  row 52 [],
  row 52 [step (mv LColor.b LColor.p TauEdge.B5) 52],
  row 52 [step (mv LColor.r LColor.p TauEdge.F4F5) 53, step (mv LColor.b LColor.p TauEdge.B5) 52],
  row 52 [step (mv LColor.r LColor.p TauEdge.F4F5) 52],
  row 8 [step (mv LColor.b LColor.p TauEdge.F2F3) 8],
  row 8 [step (mv LColor.b LColor.p TauEdge.F2F3) 9, step (mv LColor.b LColor.p TauEdge.B5) 8],
  row 8 [step (mv LColor.b LColor.p TauEdge.F2F3) 10, step (mv LColor.r LColor.b TauEdge.F4F5) 8],
  row 8 [step (mv LColor.r LColor.p TauEdge.F4F5) 56, step (mv LColor.b LColor.p TauEdge.F2F3) 8],
  row 60 [],
  row 60 [step (mv LColor.b LColor.p TauEdge.B5) 60],
  row 60 [step (mv LColor.r LColor.p TauEdge.F4F5) 61, step (mv LColor.b LColor.p TauEdge.B5) 60],
  row 60 [step (mv LColor.r LColor.p TauEdge.F4F5) 60],
  row 64 [],
  row 64 [step (mv LColor.b LColor.p TauEdge.B5) 64],
  row 64 [step (mv LColor.r LColor.b TauEdge.F4F5) 64],
  row 64 [step (mv LColor.r LColor.b TauEdge.F4F5) 65, step (mv LColor.b LColor.p TauEdge.B5) 64],
  row 68 [],
  row 68 [step (mv LColor.b LColor.p TauEdge.B5) 68],
  row 68 [step (mv LColor.r LColor.b TauEdge.F4F5) 68],
  row 68 [step (mv LColor.r LColor.b TauEdge.F4F5) 69, step (mv LColor.b LColor.p TauEdge.B5) 68],
  row 72 [],
  row 72 [step (mv LColor.b LColor.p TauEdge.B5) 72],
  row 72 [step (mv LColor.r LColor.b TauEdge.F4F5) 72],
  row 72 [step (mv LColor.r LColor.b TauEdge.F4F5) 73, step (mv LColor.b LColor.p TauEdge.B5) 72],
  row 76 [],
  row 76 [step (mv LColor.b LColor.p TauEdge.B5) 76],
  row 76 [step (mv LColor.r LColor.b TauEdge.F4F5) 76],
  row 76 [step (mv LColor.r LColor.b TauEdge.F4F5) 77, step (mv LColor.b LColor.p TauEdge.B5) 76],
  row 80 [],
  row 80 [step (mv LColor.b LColor.p TauEdge.B5) 80],
  row 80 [step (mv LColor.r LColor.b TauEdge.F4F5) 80],
  row 80 [step (mv LColor.r LColor.b TauEdge.F4F5) 81, step (mv LColor.b LColor.p TauEdge.B5) 80],
  row 84 [],
  row 84 [step (mv LColor.b LColor.p TauEdge.B5) 84],
  row 84 [step (mv LColor.r LColor.b TauEdge.F4F5) 84],
  row 84 [step (mv LColor.r LColor.b TauEdge.F4F5) 85, step (mv LColor.b LColor.p TauEdge.B5) 84],
  row 88 [],
  row 88 [step (mv LColor.b LColor.p TauEdge.B5) 88],
  row 88 [step (mv LColor.r LColor.b TauEdge.F4F5) 88],
  row 88 [step (mv LColor.r LColor.b TauEdge.F4F5) 89, step (mv LColor.b LColor.p TauEdge.B5) 88],
  row 92 [],
  row 92 [step (mv LColor.b LColor.p TauEdge.B5) 92],
  row 92 [step (mv LColor.r LColor.b TauEdge.F4F5) 92],
  row 92 [step (mv LColor.r LColor.b TauEdge.F4F5) 93, step (mv LColor.b LColor.p TauEdge.B5) 92],
  row 96 [],
  row 96 [step (mv LColor.r LColor.p TauEdge.B5) 96],
  row 96 [step (mv LColor.b LColor.p TauEdge.F4F5) 96],
  row 96 [step (mv LColor.b LColor.p TauEdge.F4F5) 97, step (mv LColor.r LColor.p TauEdge.B5) 96],
  row 80 [step (mv LColor.r LColor.p TauEdge.F2F3) 82, step (mv LColor.r LColor.b TauEdge.F4F5) 80],
  row 80 [step (mv LColor.b LColor.p TauEdge.F4F5) 103, step (mv LColor.r LColor.p TauEdge.F2F3) 80],
  row 80 [step (mv LColor.r LColor.p TauEdge.F2F3) 81, step (mv LColor.b LColor.p TauEdge.B5) 80],
  row 80 [step (mv LColor.r LColor.p TauEdge.F2F3) 80],
  row 104 [],
  row 104 [step (mv LColor.r LColor.p TauEdge.B5) 104],
  row 104 [step (mv LColor.b LColor.p TauEdge.F4F5) 104],
  row 104 [step (mv LColor.b LColor.p TauEdge.F4F5) 105, step (mv LColor.r LColor.p TauEdge.B5) 104],
  row 88 [step (mv LColor.r LColor.p TauEdge.F2F3) 90, step (mv LColor.r LColor.b TauEdge.F4F5) 88],
  row 88 [step (mv LColor.b LColor.p TauEdge.F4F5) 111, step (mv LColor.r LColor.p TauEdge.F2F3) 88],
  row 88 [step (mv LColor.r LColor.p TauEdge.F2F3) 89, step (mv LColor.b LColor.p TauEdge.B5) 88],
  row 88 [step (mv LColor.r LColor.p TauEdge.F2F3) 88],
  row 112 [],
  row 112 [step (mv LColor.r LColor.p TauEdge.B5) 112],
  row 112 [step (mv LColor.b LColor.p TauEdge.F4F5) 112],
  row 112 [step (mv LColor.b LColor.p TauEdge.F4F5) 113, step (mv LColor.r LColor.p TauEdge.B5) 112],
  row 64 [step (mv LColor.r LColor.p TauEdge.F2F3) 66, step (mv LColor.r LColor.b TauEdge.F4F5) 64],
  row 64 [step (mv LColor.b LColor.p TauEdge.F4F5) 119, step (mv LColor.r LColor.p TauEdge.F2F3) 64],
  row 64 [step (mv LColor.r LColor.p TauEdge.F2F3) 65, step (mv LColor.b LColor.p TauEdge.B5) 64],
  row 64 [step (mv LColor.r LColor.p TauEdge.F2F3) 64],
  row 120 [],
  row 120 [step (mv LColor.r LColor.p TauEdge.B5) 120],
  row 120 [step (mv LColor.b LColor.p TauEdge.F4F5) 120],
  row 120 [step (mv LColor.b LColor.p TauEdge.F4F5) 121, step (mv LColor.r LColor.p TauEdge.B5) 120],
  row 72 [step (mv LColor.r LColor.p TauEdge.F2F3) 74, step (mv LColor.r LColor.b TauEdge.F4F5) 72],
  row 72 [step (mv LColor.b LColor.p TauEdge.F4F5) 127, step (mv LColor.r LColor.p TauEdge.F2F3) 72],
  row 72 [step (mv LColor.r LColor.p TauEdge.F2F3) 73, step (mv LColor.b LColor.p TauEdge.B5) 72],
  row 72 [step (mv LColor.r LColor.p TauEdge.F2F3) 72],
  row 128 [],
  row 128 [step (mv LColor.b LColor.p TauEdge.B5) 128],
  row 128 [step (mv LColor.r LColor.p TauEdge.F4F5) 129, step (mv LColor.b LColor.p TauEdge.B5) 128],
  row 128 [step (mv LColor.r LColor.p TauEdge.F4F5) 128],
  row 132 [],
  row 132 [step (mv LColor.b LColor.p TauEdge.B5) 132],
  row 132 [step (mv LColor.r LColor.p TauEdge.F4F5) 133, step (mv LColor.b LColor.p TauEdge.B5) 132],
  row 132 [step (mv LColor.r LColor.p TauEdge.F4F5) 132],
  row 136 [],
  row 136 [step (mv LColor.b LColor.p TauEdge.B5) 136],
  row 136 [step (mv LColor.r LColor.p TauEdge.F4F5) 137, step (mv LColor.b LColor.p TauEdge.B5) 136],
  row 136 [step (mv LColor.r LColor.p TauEdge.F4F5) 136],
  row 140 [],
  row 140 [step (mv LColor.b LColor.p TauEdge.B5) 140],
  row 140 [step (mv LColor.r LColor.p TauEdge.F4F5) 141, step (mv LColor.b LColor.p TauEdge.B5) 140],
  row 140 [step (mv LColor.r LColor.p TauEdge.F4F5) 140],
  row 144 [],
  row 144 [step (mv LColor.b LColor.p TauEdge.B5) 144],
  row 144 [step (mv LColor.r LColor.p TauEdge.F4F5) 145, step (mv LColor.b LColor.p TauEdge.B5) 144],
  row 144 [step (mv LColor.r LColor.p TauEdge.F4F5) 144],
  row 148 [],
  row 148 [step (mv LColor.b LColor.p TauEdge.B5) 148],
  row 148 [step (mv LColor.r LColor.p TauEdge.F4F5) 149, step (mv LColor.b LColor.p TauEdge.B5) 148],
  row 148 [step (mv LColor.r LColor.p TauEdge.F4F5) 148],
  row 152 [],
  row 152 [step (mv LColor.b LColor.p TauEdge.B5) 152],
  row 152 [step (mv LColor.r LColor.p TauEdge.F4F5) 153, step (mv LColor.b LColor.p TauEdge.B5) 152],
  row 152 [step (mv LColor.r LColor.p TauEdge.F4F5) 152],
  row 156 [],
  row 156 [step (mv LColor.b LColor.p TauEdge.B5) 156],
  row 156 [step (mv LColor.r LColor.p TauEdge.F4F5) 157, step (mv LColor.b LColor.p TauEdge.B5) 156],
  row 156 [step (mv LColor.r LColor.p TauEdge.F4F5) 156],
  row 160 [],
  row 160 [step (mv LColor.r LColor.p TauEdge.B5) 160],
  row 160 [step (mv LColor.b LColor.p TauEdge.F4F5) 160],
  row 160 [step (mv LColor.b LColor.p TauEdge.F4F5) 161, step (mv LColor.r LColor.p TauEdge.B5) 160],
  row 148 [step (mv LColor.r LColor.b TauEdge.F2F3) 148],
  row 148 [step (mv LColor.r LColor.b TauEdge.F2F3) 149, step (mv LColor.b LColor.p TauEdge.B5) 148],
  row 148 [step (mv LColor.b LColor.p TauEdge.F4F5) 164, step (mv LColor.r LColor.b TauEdge.F2F3) 148],
  row 148 [step (mv LColor.r LColor.b TauEdge.F2F3) 151, step (mv LColor.r LColor.p TauEdge.F4F5) 148],
  row 168 [],
  row 168 [step (mv LColor.r LColor.p TauEdge.B5) 168],
  row 168 [step (mv LColor.b LColor.p TauEdge.F4F5) 168],
  row 168 [step (mv LColor.b LColor.p TauEdge.F4F5) 169, step (mv LColor.r LColor.p TauEdge.B5) 168],
  row 156 [step (mv LColor.r LColor.b TauEdge.F2F3) 156],
  row 156 [step (mv LColor.r LColor.b TauEdge.F2F3) 157, step (mv LColor.b LColor.p TauEdge.B5) 156],
  row 156 [step (mv LColor.b LColor.p TauEdge.F4F5) 172, step (mv LColor.r LColor.b TauEdge.F2F3) 156],
  row 156 [step (mv LColor.r LColor.b TauEdge.F2F3) 159, step (mv LColor.r LColor.p TauEdge.F4F5) 156],
  row 176 [],
  row 176 [step (mv LColor.r LColor.p TauEdge.B5) 176],
  row 176 [step (mv LColor.b LColor.p TauEdge.F4F5) 176],
  row 176 [step (mv LColor.b LColor.p TauEdge.F4F5) 177, step (mv LColor.r LColor.p TauEdge.B5) 176],
  row 132 [step (mv LColor.r LColor.b TauEdge.F2F3) 132],
  row 132 [step (mv LColor.r LColor.b TauEdge.F2F3) 133, step (mv LColor.b LColor.p TauEdge.B5) 132],
  row 132 [step (mv LColor.b LColor.p TauEdge.F4F5) 180, step (mv LColor.r LColor.b TauEdge.F2F3) 132],
  row 132 [step (mv LColor.r LColor.b TauEdge.F2F3) 135, step (mv LColor.r LColor.p TauEdge.F4F5) 132],
  row 184 [],
  row 184 [step (mv LColor.r LColor.p TauEdge.B5) 184],
  row 184 [step (mv LColor.b LColor.p TauEdge.F4F5) 184],
  row 184 [step (mv LColor.b LColor.p TauEdge.F4F5) 185, step (mv LColor.r LColor.p TauEdge.B5) 184],
  row 140 [step (mv LColor.r LColor.b TauEdge.F2F3) 140],
  row 140 [step (mv LColor.r LColor.b TauEdge.F2F3) 141, step (mv LColor.b LColor.p TauEdge.B5) 140],
  row 140 [step (mv LColor.b LColor.p TauEdge.F4F5) 188, step (mv LColor.r LColor.b TauEdge.F2F3) 140],
  row 140 [step (mv LColor.r LColor.b TauEdge.F2F3) 143, step (mv LColor.r LColor.p TauEdge.F4F5) 140]
]

def rowAt (i : Nat) : IndexedPathRow :=
  lemma814PathCertificate.getD i default

def representativeAt (i : Nat) : Nat :=
  (rowAt i).representative

def representativeCoherenceAudit : Bool :=
  (List.range 192).all fun i =>
    (List.range 192).all fun j =>
      !sameInput (stateAt i) (stateAt j) || representativeAt i == representativeAt j

def lemma814PathCertificateAudit : Bool :=
  lemma814PathCertificate.length == 192 &&
    validIndexedRowsFrom 0 lemma814PathCertificate &&
    representativeCoherenceAudit

/--
Finite certificate for `LKR_in`: each listed state has a verified path of at
most two input-disjoint Kempe switches to the representative of its fixed-input
fiber, and states with the same input have the same representative.
-/
def tauLKRInAudit : Bool :=
  lemma814PathCertificateAudit


def tauStateSpaceAudit : Bool :=
  allTauStates.length == 192 &&
    allTauStates.eraseDups.length == allTauStates.length &&
    allTauStates.all tauProperState

/-- Vertices including boundary stubs, used for the finite transparency audit. -/
inductive TauEndpoint
  | F0
  | F1
  | F2
  | F3
  | F4
  | F5
  | B0
  | B1
  | B2
  | B3
  | B4
  | B5
  | B6
  | B7
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr, Inhabited

def tauEndpoints : List TauEndpoint :=
  [ TauEndpoint.F0
  , TauEndpoint.F1
  , TauEndpoint.F2
  , TauEndpoint.F3
  , TauEndpoint.F4
  , TauEndpoint.F5
  , TauEndpoint.B0
  , TauEndpoint.B1
  , TauEndpoint.B2
  , TauEndpoint.B3
  , TauEndpoint.B4
  , TauEndpoint.B5
  , TauEndpoint.B6
  , TauEndpoint.B7
  ]

def isInternalEndpoint : TauEndpoint → Bool
  | TauEndpoint.F0 => true
  | TauEndpoint.F1 => true
  | TauEndpoint.F2 => true
  | TauEndpoint.F3 => true
  | TauEndpoint.F4 => true
  | TauEndpoint.F5 => true
  | TauEndpoint.B0 => false
  | TauEndpoint.B1 => false
  | TauEndpoint.B2 => false
  | TauEndpoint.B3 => false
  | TauEndpoint.B4 => false
  | TauEndpoint.B5 => false
  | TauEndpoint.B6 => false
  | TauEndpoint.B7 => false

def edgeEndpoints : TauEdge → TauEndpoint × TauEndpoint
  | TauEdge.F1F0 => (TauEndpoint.F1, TauEndpoint.F0)
  | TauEdge.F0F2 => (TauEndpoint.F0, TauEndpoint.F2)
  | TauEdge.F2F3 => (TauEndpoint.F2, TauEndpoint.F3)
  | TauEdge.F2F4 => (TauEndpoint.F2, TauEndpoint.F4)
  | TauEdge.F4F5 => (TauEndpoint.F4, TauEndpoint.F5)
  | TauEdge.B0 => (TauEndpoint.F0, TauEndpoint.B0)
  | TauEdge.B1 => (TauEndpoint.F1, TauEndpoint.B1)
  | TauEdge.B2 => (TauEndpoint.F1, TauEndpoint.B2)
  | TauEdge.B3 => (TauEndpoint.F3, TauEndpoint.B3)
  | TauEdge.B4 => (TauEndpoint.F3, TauEndpoint.B4)
  | TauEdge.B5 => (TauEndpoint.F5, TauEndpoint.B5)
  | TauEdge.B6 => (TauEndpoint.F5, TauEndpoint.B6)
  | TauEdge.B7 => (TauEndpoint.F4, TauEndpoint.B7)

def edgeTouchesEndpoint (e : TauEdge) (v : TauEndpoint) : Bool :=
  let p := edgeEndpoints e
  p.1 == v || p.2 == v

def degreeInComponent (component : List TauEdge) (v : TauEndpoint) : Nat :=
  (component.filter fun e => edgeTouchesEndpoint e v).length

def componentEndpoints (component : List TauEdge) : List TauEndpoint :=
  component.foldl
    (fun acc e =>
      let p := edgeEndpoints e
      addIfFresh (addIfFresh acc p.1) p.2)
    []

def boundaryDegreeOneCount (component : List TauEdge) : Nat :=
  (tauEndpoints.filter fun v =>
    !isInternalEndpoint v && degreeInComponent component v == 1).length

def internalDegreesOk (component : List TauEdge) : Bool :=
  tauEndpoints.all fun v =>
    !isInternalEndpoint v || degreeInComponent component v == 0 || degreeInComponent component v == 2

def connectedComponentIsTree (component : List TauEdge) : Bool :=
  component.length + 1 == (componentEndpoints component).length

def transparentComponent (component : List TauEdge) : Bool :=
  !component.isEmpty &&
    internalDegreesOk component &&
    boundaryDegreeOneCount component == 2 &&
    connectedComponentIsTree component

def tauTreeTransparencyAtIndex (i : Nat) : Bool :=
  colorPairs.all fun pair =>
    tauEdges.all fun seed =>
      let component := tauComponent (stateAt i) pair.1 pair.2 seed
      component.isEmpty || transparentComponent component

def tauTreeTransparencyRangeAudit (start len : Nat) : Bool :=
  (List.range len).all (fun k => tauTreeTransparencyAtIndex (start + k))

/-- The finite tree-transparency audit corresponding to Lemma 8.15. -/
def tauTreeTransparencyAudit : Bool :=
  tauTreeTransparencyRangeAudit 0 64 &&
    tauTreeTransparencyRangeAudit 64 64 &&
    tauTreeTransparencyRangeAudit 128 64

/--
Finite check for Lemma 8.14 on the canonical gadget.  This is the exact Lean
predicate that must reduce to `true`: the state space has 192 proper states,
and the indexed path certificate verifies `LKR_in` by paths of length at most
two to fixed-input representatives.
-/
def lemma814_tau_lkrIn_finiteCheck : Bool :=
  tauStateSpaceAudit && tauLKRInAudit

set_option maxRecDepth 4096 in
theorem tauStateSpaceAudit_ok :
    tauStateSpaceAudit = true := by
  decide

set_option maxRecDepth 4096 in
theorem lemma814PathCertificate_length_ok :
    (lemma814PathCertificate.length == 192) = true := by
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem lemma814PathCertificate_rows_ok :
    validIndexedRowsFrom 0 lemma814PathCertificate = true := by
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem representativeCoherenceAudit_ok :
    representativeCoherenceAudit = true := by
  decide

theorem lemma814PathCertificateAudit_ok :
    lemma814PathCertificateAudit = true := by
  simp [lemma814PathCertificateAudit, lemma814PathCertificate_length_ok,
    lemma814PathCertificate_rows_ok, representativeCoherenceAudit_ok]

/-- Lemma 8.14, closed by the finite state-space and indexed path certificate. -/
theorem lemma814_tau_lkrIn_audit :
    lemma814_tau_lkrIn_finiteCheck = true := by
  simp [lemma814_tau_lkrIn_finiteCheck, tauStateSpaceAudit_ok, tauLKRInAudit,
    lemma814PathCertificateAudit_ok]

/-- The mirror gadget has the same incidence tree; reflection changes only the planar order. -/
def mirrorTauLKRInAudit : Bool :=
  tauLKRInAudit

/-- The mirror check is definitionally the same incidence check. -/
theorem lemma814_mirror_lkrIn_same_check :
    mirrorTauLKRInAudit = tauLKRInAudit :=
  rfl

/--
Finite check for Lemma 8.15: every two-color component in every listed
coloring of the tree gadget is a boundary-to-boundary path.
-/
def lemma815_tau_tree_transparency_finiteCheck : Bool :=
  tauTreeTransparencyAudit

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem tauTreeTransparencyRange_0_64_ok :
    tauTreeTransparencyRangeAudit 0 64 = true := by
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem tauTreeTransparencyRange_64_64_ok :
    tauTreeTransparencyRangeAudit 64 64 = true := by
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem tauTreeTransparencyRange_128_64_ok :
    tauTreeTransparencyRangeAudit 128 64 = true := by
  decide

/--
Lemma 8.15 finite audit: every two-color component in every canonical
three-cell gadget coloring is a boundary-to-boundary tree path.
-/
theorem lemma815_tau_tree_transparency_audit :
    lemma815_tau_tree_transparency_finiteCheck = true := by
  unfold lemma815_tau_tree_transparency_finiteCheck tauTreeTransparencyAudit
  rw [tauTreeTransparencyRange_0_64_ok]
  rw [tauTreeTransparencyRange_64_64_ok]
  rw [tauTreeTransparencyRange_128_64_ok]
  rfl

/--
The output stubs of an upstream `τ` when composing two canonical gadgets along
the interface used in Lemma 8.18.
-/
def tauOutputEdges : List TauEdge :=
  [TauEdge.B4, TauEdge.B5, TauEdge.B6, TauEdge.B7]

def tauOutputFootprint (component : List TauEdge) : List TauEdge :=
  tauOutputEdges.filter fun e => component.contains e

/-- Interface color agreement for the serial gluing
`X.B4..X.B7 = Y.B0..Y.B3`. -/
def tauInterfaceColorAgrees (x y : TauState) : Bool :=
  colorEq (x.color TauEdge.B4) (y.color TauEdge.B0) &&
    colorEq (x.color TauEdge.B5) (y.color TauEdge.B1) &&
    colorEq (x.color TauEdge.B6) (y.color TauEdge.B2) &&
    colorEq (x.color TauEdge.B7) (y.color TauEdge.B3)

/--
The exact downstream-preparation condition used in Lemma 8.18's Step 1 for a
single downstream `τ`: with the downstream input colors fixed, some extension
must pair the two named input stubs in the chosen two-color component.

By Lemma 8.14, existence of such an extension would be enough to reach it by a
Kempe word disjoint from the downstream input stubs.  The obstruction below
shows that the existence premise itself can fail.
-/
def downstreamInputPairCanBePrepared (y : TauState) (a c : LColor)
    (u v : TauEdge) : Bool :=
  allTauStates.any fun y' =>
    sameInput y' y && (tauComponent y' a c u).contains v

/--
Finite obstruction to the pointwise preparation step in Lemma 8.18.

Take an upstream `τ` in state `6` and a downstream `τ` in state `176`, glued
along `B4..B7 = B0..B3`.  The upstream `{r,b}`-component seeded at `B5`
is input-disjoint and has interface footprint exactly `{B5,B7}`.  Lemma 8.18's
proof then asks the downstream side to preserve its input colors while pairing
the corresponding downstream input stubs `{B1,B3}` in the `{r,b}`-subgraph.
The final conjunct checks that no downstream extension with those fixed input
colors has that pairing.

This is not a counterexample to `LKR_in` for the two-gadget composite; it is a
checked failure of the pointwise lift-preparation claim used in the manuscript
proof of Lemma 8.18.
-/
def lemma818_pointwiseLiftCounterexampleCheck : Bool :=
  let x := stateAt 6
  let y := stateAt 176
  let component := tauComponent x LColor.r LColor.b TauEdge.B5
  tauInterfaceColorAgrees x y &&
    componentAvoidsInputs component &&
    tauOutputFootprint component == [TauEdge.B5, TauEdge.B7] &&
    colorInPair (y.color TauEdge.B1) LColor.r LColor.b &&
    colorInPair (y.color TauEdge.B3) LColor.r LColor.b &&
    !downstreamInputPairCanBePrepared y LColor.r LColor.b TauEdge.B1 TauEdge.B3

set_option maxRecDepth 4096

/--
Lemma 8.18 as written cannot be closed from Lemmas 8.14 and 8.15 alone:
the downstream pairing-preparation step invoked for a lifted upstream switch
has this finite `τ → τ` obstruction.
-/
theorem lemma818_pointwise_lift_preparation_obstruction :
    lemma818_pointwiseLiftCounterexampleCheck = true := by
  decide

/-!
## Gate-1 direct composite `LKR_in` audit

The obstruction above refutes the manuscript's pointwise preparation argument,
not composite reachability itself.  The definitions below model serial chains
of `τ` and its reflected ordered-stub version and test the composite fixed-input
Kempe graph directly.
-/

inductive TauOrient
  | normal
  | mirror
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr, Inhabited

def tauOrientInputOrder : TauOrient → List TauEdge
  | TauOrient.normal => [TauEdge.B0, TauEdge.B1, TauEdge.B2, TauEdge.B3]
  | TauOrient.mirror => [TauEdge.B3, TauEdge.B2, TauEdge.B1, TauEdge.B0]

def tauOrientOutputOrder : TauOrient → List TauEdge
  | TauOrient.normal => [TauEdge.B4, TauEdge.B5, TauEdge.B6, TauEdge.B7]
  | TauOrient.mirror => [TauEdge.B7, TauEdge.B6, TauEdge.B5, TauEdge.B4]

def listGetD (xs : List α) (i : Nat) (fallback : α) : α :=
  match xs, i with
  | [], _ => fallback
  | x :: _, 0 => x
  | _ :: rest, n + 1 => listGetD rest n fallback

def indexOfAux [BEq α] (needle : α) : List α → Nat → Option Nat
  | [], _ => none
  | x :: xs, n => if x == needle then some n else indexOfAux needle xs (n + 1)

def indexOf? [BEq α] (xs : List α) (needle : α) : Option Nat :=
  indexOfAux needle xs 0

theorem indexOfAux_eq_none_of_contains_false {α : Type} [BEq α] [LawfulBEq α]
    (needle : α) :
    ∀ (xs : List α) (n : Nat), xs.contains needle = false →
      indexOfAux needle xs n = none
  | [], _, _ => rfl
  | x :: xs, n, hcontains => by
      unfold indexOfAux
      by_cases hx : (x == needle) = true
      · have hxEq : x = needle := beq_iff_eq.mp hx
        have hmem : needle ∈ x :: xs := by
          simp [hxEq]
        have htrue : (x :: xs).contains needle = true :=
          List.contains_iff_mem.mpr hmem
        rw [hcontains] at htrue
        cases htrue
      · have htail : xs.contains needle = false := by
          cases htailEq : xs.contains needle with
          | false =>
              rfl
          | true =>
              have hmemTail : needle ∈ xs :=
                List.contains_iff_mem.mp htailEq
              have hmem : needle ∈ x :: xs :=
                List.mem_cons_of_mem x hmemTail
              have htrue : (x :: xs).contains needle = true :=
                List.contains_iff_mem.mpr hmem
              rw [hcontains] at htrue
              cases htrue
        have hxFalse : (x == needle) = false := by
          cases hxEq : x == needle with
          | false =>
              rfl
          | true =>
              exact False.elim (hx hxEq)
        simp only [hxFalse, Bool.false_eq_true, ↓reduceIte]
        exact indexOfAux_eq_none_of_contains_false needle xs (n + 1) htail

theorem indexOf?_eq_none_of_contains_false {α : Type} [BEq α] [LawfulBEq α]
    (xs : List α) (needle : α)
    (hcontains : xs.contains needle = false) :
    indexOf? xs needle = none := by
  unfold indexOf?
  exact indexOfAux_eq_none_of_contains_false needle xs 0 hcontains

def tauOrientAt (orients : List TauOrient) (i : Nat) : TauOrient :=
  listGetD orients i TauOrient.normal

def chainStateAt (states : List TauState) (i : Nat) : TauState :=
  listGetD states i default

def tauStateColorAt (states : List TauState) (i : Nat) (e : TauEdge) : LColor :=
  (chainStateAt states i).color e

structure ChainEdge where
  occ : Nat
  edge : TauEdge
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr, Inhabited

inductive ChainEndpoint
  | internal (occ : Nat) (v : TauEndpoint)
  | boundary (occ : Nat) (v : TauEndpoint)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr, Inhabited

def tauStubInternalEndpoint : TauEdge → TauEndpoint
  | TauEdge.B0 => TauEndpoint.F0
  | TauEdge.B1 => TauEndpoint.F1
  | TauEdge.B2 => TauEndpoint.F1
  | TauEdge.B3 => TauEndpoint.F3
  | TauEdge.B4 => TauEndpoint.F3
  | TauEdge.B5 => TauEndpoint.F5
  | TauEdge.B6 => TauEndpoint.F5
  | TauEdge.B7 => TauEndpoint.F4
  | e => (edgeEndpoints e).1

def chainInputOrder (orients : List TauOrient) : List TauEdge :=
  tauOrientInputOrder (tauOrientAt orients 0)

def chainOutputOrder (orients : List TauOrient) (i : Nat) : List TauEdge :=
  tauOrientOutputOrder (tauOrientAt orients i)

def chainIsGluedInput (orients : List TauOrient) (i : Nat) (e : TauEdge) : Bool :=
  i > 0 && (tauOrientInputOrder (tauOrientAt orients i)).contains e

def chainIsGluedOutput (orients : List TauOrient) (i : Nat) (e : TauEdge) : Bool :=
  i + 1 < orients.length && (tauOrientOutputOrder (tauOrientAt orients i)).contains e

def chainIsRepresentativeEdge (orients : List TauOrient) (ge : ChainEdge) : Bool :=
  !(chainIsGluedInput orients ge.occ ge.edge)

def chainCanonicalEdge (orients : List TauOrient) (ge : ChainEdge) : ChainEdge :=
  if ge.occ > 0 then
    match indexOf? (tauOrientInputOrder (tauOrientAt orients ge.occ)) ge.edge with
    | some k =>
        { occ := ge.occ - 1
          edge := listGetD (chainOutputOrder orients (ge.occ - 1)) k TauEdge.B4 }
    | none => ge
  else
    ge

def chainLocalEdges (orients : List TauOrient) : List ChainEdge :=
  bindList (List.range orients.length) fun i =>
    tauEdges.map fun e => ({ occ := i, edge := e } : ChainEdge)

def chainEdges (orients : List TauOrient) : List ChainEdge :=
  (chainLocalEdges orients).filter (chainIsRepresentativeEdge orients)

def chainEdgeColor (states : List TauState) (ge : ChainEdge) : LColor :=
  tauStateColorAt states ge.occ ge.edge

def tauEndpointToChainEndpoint (i : Nat) (v : TauEndpoint) : ChainEndpoint :=
  if isInternalEndpoint v then ChainEndpoint.internal i v else ChainEndpoint.boundary i v

def chainEdgeEndpoints (orients : List TauOrient) (ge : ChainEdge) :
    ChainEndpoint × ChainEndpoint :=
  if chainIsGluedOutput orients ge.occ ge.edge then
    match indexOf? (tauOrientOutputOrder (tauOrientAt orients ge.occ)) ge.edge with
    | some k =>
        let nextInput := listGetD
          (tauOrientInputOrder (tauOrientAt orients (ge.occ + 1))) k TauEdge.B0
        ( ChainEndpoint.internal ge.occ (tauStubInternalEndpoint ge.edge)
        , ChainEndpoint.internal (ge.occ + 1) (tauStubInternalEndpoint nextInput) )
    | none =>
        let p := edgeEndpoints ge.edge
        (tauEndpointToChainEndpoint ge.occ p.1, tauEndpointToChainEndpoint ge.occ p.2)
  else
    let p := edgeEndpoints ge.edge
    (tauEndpointToChainEndpoint ge.occ p.1, tauEndpointToChainEndpoint ge.occ p.2)

def chainEdgesShareEndpoint (orients : List TauOrient) (e f : ChainEdge) : Bool :=
  if e == f then
    false
  else
    let ep := chainEdgeEndpoints orients e
    let fp := chainEdgeEndpoints orients f
    ep.1 == fp.1 || ep.1 == fp.2 || ep.2 == fp.1 || ep.2 == fp.2

def chainEdgeInPair (states : List TauState) (a c : LColor) (e : ChainEdge) : Bool :=
  colorInPair (chainEdgeColor states e) a c

def nextChainComponentLayer (orients : List TauOrient) (states : List TauState)
    (a c : LColor) (seen : List ChainEdge) : List ChainEdge :=
  (chainEdges orients).filter fun e =>
    chainEdgeInPair states a c e &&
      !seen.contains e &&
      seen.any (chainEdgesShareEndpoint orients e)

def closeChainComponent (orients : List TauOrient) (states : List TauState)
    (a c : LColor) : Nat → List ChainEdge → List ChainEdge
  | 0, seen => seen
  | n + 1, seen =>
      let layer := nextChainComponentLayer orients states a c seen
      closeChainComponent orients states a c n (appendFresh seen layer)

def chainComponent (orients : List TauOrient) (states : List TauState)
    (a c : LColor) (seed : ChainEdge) : List ChainEdge :=
  if chainEdgeInPair states a c seed then
    closeChainComponent orients states a c (chainEdges orients).length [seed]
  else
    []

def chainOuterInputEdges (orients : List TauOrient) : List ChainEdge :=
  (chainInputOrder orients).map fun e => ({ occ := 0, edge := e } : ChainEdge)

def chainComponentAvoidsInputs (orients : List TauOrient) (component : List ChainEdge) : Bool :=
  !component.any (fun e => (chainOuterInputEdges orients).contains e)

def chainSwitchedColor (orients : List TauOrient) (states : List TauState)
    (component : List ChainEdge) (a c : LColor) (ge : ChainEdge) : LColor :=
  let canonical := chainCanonicalEdge orients ge
  if component.contains canonical then swapColor a c (chainEdgeColor states canonical)
  else chainEdgeColor states canonical

def chainAgreesWithSwitch (orients : List TauOrient) (s t : List TauState)
    (component : List ChainEdge) (a c : LColor) : Bool :=
  (chainLocalEdges orients).all fun ge =>
    colorEq (chainEdgeColor t ge) (chainSwitchedColor orients s component a c ge)

def chainSingleKempeStep (orients : List TauOrient) (s t : List TauState) : Bool :=
  colorPairs.any fun pair =>
    let a := pair.1
    let c := pair.2
    (chainEdges orients).any fun seed =>
      let component := chainComponent orients s a c seed
      !component.isEmpty && chainComponentAvoidsInputs orients component &&
        chainAgreesWithSwitch orients s t component a c

structure ChainMove where
  a : LColor
  c : LColor
  seed : ChainEdge
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr, Inhabited

def chainSpecifiedKempeStep (orients : List TauOrient) (s t : List TauState)
    (move : ChainMove) : Bool :=
  let component := chainComponent orients s move.a move.c move.seed
  !component.isEmpty && chainComponentAvoidsInputs orients component &&
    chainAgreesWithSwitch orients s t component move.a move.c

def compatibleAdjacent (leftOrient rightOrient : TauOrient) (x y : TauState) : Bool :=
  (List.zip (tauOrientOutputOrder leftOrient) (tauOrientInputOrder rightOrient)).all fun pair =>
    colorEq (x.color pair.1) (y.color pair.2)

def compatibleChainStates (orients : List TauOrient) (states : List TauState) : Bool :=
  states.length == orients.length &&
    (List.range (orients.length - 1)).all fun i =>
      compatibleAdjacent (tauOrientAt orients i) (tauOrientAt orients (i + 1))
        (chainStateAt states i) (chainStateAt states (i + 1))

theorem chainEdgeColor_chainCanonicalEdge_of_compatible
    {orients : List TauOrient} {states : List TauState}
    (hcompatible : compatibleChainStates orients states = true)
    (ge : ChainEdge)
    (hocc : ge.occ < orients.length) :
    chainEdgeColor states (chainCanonicalEdge orients ge) =
      chainEdgeColor states ge := by
  cases ge with
  | mk occ edge =>
      have hoccNat : occ < orients.length := by
        simpa using hocc
      by_cases hpos : occ > 0
      · have hAdjAll :
            (List.range (orients.length - 1)).all (fun i =>
              compatibleAdjacent (tauOrientAt orients i)
                (tauOrientAt orients (i + 1))
                (chainStateAt states i) (chainStateAt states (i + 1))) =
                true := by
          unfold compatibleChainStates at hcompatible
          simp only [Bool.and_eq_true] at hcompatible
          exact hcompatible.2
        have hprevMem : occ - 1 ∈ List.range (orients.length - 1) := by
          simp
          omega
        have hstep :
            compatibleAdjacent (tauOrientAt orients (occ - 1))
              (tauOrientAt orients ((occ - 1) + 1))
              (chainStateAt states (occ - 1))
              (chainStateAt states ((occ - 1) + 1)) = true :=
          (List.all_eq_true.mp hAdjAll) (occ - 1) hprevMem
        have hsucc : (occ - 1) + 1 = occ := by omega
        cases hleft : tauOrientAt orients (occ - 1) <;>
          cases hright : tauOrientAt orients occ <;>
          cases edge <;>
          simp [chainCanonicalEdge, chainEdgeColor, chainOutputOrder,
            tauStateColorAt, listGetD, hpos, hsucc, hleft, hright,
            indexOf?, indexOfAux, tauOrientInputOrder,
            tauOrientOutputOrder, compatibleAdjacent, colorEq] at hstep ⊢ <;>
          tauto
      · have hzero : occ = 0 := by omega
        simp [chainCanonicalEdge, hzero]

def extendChainStates (orients : List TauOrient) (prefixes : List (List TauState))
    (nextIndex : Nat) : List (List TauState) :=
  bindList prefixes fun accStates =>
    let prevOrient := tauOrientAt orients (nextIndex - 1)
    let nextOrient := tauOrientAt orients nextIndex
    let prevState := chainStateAt accStates (nextIndex - 1)
    (allTauStates.filter fun nextState =>
      compatibleAdjacent prevOrient nextOrient prevState nextState).map fun nextState =>
        accStates ++ [nextState]

def buildChainStatesFrom (orients : List TauOrient) :
    Nat → List (List TauState) → List (List TauState)
  | 0, prefixes => prefixes
  | n + 1, prefixes =>
      let nextIndex := orients.length - (n + 1)
      buildChainStatesFrom orients n (extendChainStates orients prefixes nextIndex)

def buildChainStatesFromIndex (orients : List TauOrient) :
    Nat → Nat → List (List TauState) → List (List TauState)
  | _, 0, prefixes => prefixes
  | nextIndex, n + 1, prefixes =>
      buildChainStatesFromIndex orients (nextIndex + 1) n
        (extendChainStates orients prefixes nextIndex)

def allChainStates (orients : List TauOrient) : List (List TauState) :=
  match orients with
  | [] => [[]]
  | _ :: rest =>
      let starts := allTauStates.map fun s => [s]
      buildChainStatesFrom orients rest.length starts

theorem mem_bindList_iff {α β : Type} {xs : List α} {f : α → List β} {y : β} :
    y ∈ bindList xs f ↔ ∃ x, x ∈ xs ∧ y ∈ f x := by
  induction xs with
  | nil =>
      simp [bindList]
  | cons x xs ih =>
      simp [bindList, or_and_right, exists_or]

theorem listGetD_append_length {α : Type} (xs : List α) (x fallback : α) :
    listGetD (xs ++ [x]) xs.length fallback = x := by
  induction xs with
  | nil =>
      rfl
  | cons _ rest ih =>
      simp [listGetD, ih]

theorem listGetD_append_left {α : Type}
    (xs ys : List α) (fallback : α) {idx : Nat}
    (hidx : idx < xs.length) :
    listGetD (xs ++ ys) idx fallback = listGetD xs idx fallback := by
  induction xs generalizing idx with
  | nil =>
      cases hidx
  | cons _ rest ih =>
      cases idx with
      | zero =>
          rfl
      | succ idx =>
          simp [listGetD]
          exact ih (Nat.succ_lt_succ_iff.mp hidx)

theorem tauOrientAt_append_left
    (orients suffix : List TauOrient) {idx : Nat}
    (hidx : idx < orients.length) :
    tauOrientAt (orients ++ suffix) idx = tauOrientAt orients idx := by
  simp [tauOrientAt, listGetD_append_left orients suffix TauOrient.normal hidx]

theorem chainStateAt_append_length
    (acc : List TauState) (next : TauState) (idx : Nat)
    (hidx : acc.length = idx) :
    chainStateAt (acc ++ [next]) idx = next := by
  subst idx
  simp [chainStateAt, listGetD_append_length]

theorem chainStateAt_append_left
    (acc : List TauState) (next : TauState) {idx : Nat}
    (hidx : idx < acc.length) :
    chainStateAt (acc ++ [next]) idx = chainStateAt acc idx := by
  simp [chainStateAt, listGetD_append_left acc [next] default hidx]

def chainPrefixCompatibleAt
    (orients : List TauOrient) (states : List TauState)
    (nextIndex : Nat) : Prop :=
  states.length = nextIndex ∧
    (List.range (nextIndex - 1)).all (fun i =>
      compatibleAdjacent (tauOrientAt orients i) (tauOrientAt orients (i + 1))
        (chainStateAt states i) (chainStateAt states (i + 1))) = true

theorem chainPrefixCompatibleAt_full
    {orients : List TauOrient} {states : List TauState}
    (h : chainPrefixCompatibleAt orients states orients.length) :
    compatibleChainStates orients states = true := by
  rcases h with ⟨hlen, hadj⟩
  unfold compatibleChainStates
  simp [hlen, hadj]

theorem chainPrefixCompatibleAt_singleton
    (orients : List TauOrient) (state : TauState) :
    chainPrefixCompatibleAt orients [state] 1 := by
  simp [chainPrefixCompatibleAt]

theorem chainPrefixCompatibleAt_extend
    {orients : List TauOrient} {acc : List TauState} {next : TauState}
    {nextIndex : Nat}
    (hpos : 0 < nextIndex)
    (hprefix : chainPrefixCompatibleAt orients acc nextIndex)
    (hcomp : compatibleAdjacent
      (tauOrientAt orients (nextIndex - 1)) (tauOrientAt orients nextIndex)
      (chainStateAt acc (nextIndex - 1)) next = true) :
    chainPrefixCompatibleAt orients (acc ++ [next]) (nextIndex + 1) := by
  rcases hprefix with ⟨hlen, hadj⟩
  constructor
  · simp [hlen]
  · rw [List.all_eq_true]
    intro i hi
    have hiLt : i < nextIndex := by
      simpa using (List.mem_range.mp hi)
    by_cases hiOld : i < nextIndex - 1
    · rw [List.all_eq_true] at hadj
      have hOld := hadj i (List.mem_range.mpr hiOld)
      have hiAcc : i < acc.length := by
        omega
      have hiSuccAcc : i + 1 < acc.length := by
        omega
      simpa [chainStateAt_append_left acc next hiAcc,
        chainStateAt_append_left acc next hiSuccAcc] using hOld
    · have hiLast : i = nextIndex - 1 := by
        omega
      subst i
      have hprev : nextIndex - 1 < acc.length := by
        omega
      have hnext : chainStateAt (acc ++ [next]) nextIndex = next := by
        exact chainStateAt_append_length acc next nextIndex hlen
      have hprevEq :
          chainStateAt (acc ++ [next]) (nextIndex - 1) =
            chainStateAt acc (nextIndex - 1) :=
        chainStateAt_append_left acc next hprev
      have hsucc : (nextIndex - 1) + 1 = nextIndex := by
        omega
      simpa [hprevEq, hnext, hsucc] using hcomp

theorem extendChainStates_prefixCompatible
    {orients : List TauOrient} {prefixes : List (List TauState)}
    {nextIndex : Nat}
    (hpos : 0 < nextIndex)
    (hprefixes : ∀ states, states ∈ prefixes →
      chainPrefixCompatibleAt orients states nextIndex) :
    ∀ states, states ∈ extendChainStates orients prefixes nextIndex →
      chainPrefixCompatibleAt orients states (nextIndex + 1) := by
  intro states hmem
  unfold extendChainStates at hmem
  rw [mem_bindList_iff] at hmem
  rcases hmem with ⟨acc, hacc, hstates⟩
  rw [List.mem_map] at hstates
  rcases hstates with ⟨next, hnext, rfl⟩
  rw [List.mem_filter] at hnext
  rcases hnext with ⟨_, hcomp⟩
  exact chainPrefixCompatibleAt_extend hpos (hprefixes acc hacc) hcomp

theorem extendChainStates_mem_split
    {orients : List TauOrient} {prefixes : List (List TauState)}
    {nextIndex : Nat} {states : List TauState}
    (hmem : states ∈ extendChainStates orients prefixes nextIndex) :
    ∃ acc next,
      acc ∈ prefixes ∧
        next ∈ allTauStates ∧
        compatibleAdjacent
          (tauOrientAt orients (nextIndex - 1)) (tauOrientAt orients nextIndex)
          (chainStateAt acc (nextIndex - 1)) next = true ∧
        states = acc ++ [next] := by
  unfold extendChainStates at hmem
  rw [mem_bindList_iff] at hmem
  rcases hmem with ⟨acc, hacc, hstates⟩
  rw [List.mem_map] at hstates
  rcases hstates with ⟨next, hnext, rfl⟩
  rw [List.mem_filter] at hnext
  exact ⟨acc, next, hacc, hnext.1, hnext.2, rfl⟩

theorem extendChainStates_mem_of_split
    {orients : List TauOrient} {prefixes : List (List TauState)}
    {nextIndex : Nat} {acc : List TauState} {next : TauState}
    (hacc : acc ∈ prefixes)
    (hnext : next ∈ allTauStates)
    (hcomp : compatibleAdjacent
      (tauOrientAt orients (nextIndex - 1)) (tauOrientAt orients nextIndex)
      (chainStateAt acc (nextIndex - 1)) next = true) :
    acc ++ [next] ∈ extendChainStates orients prefixes nextIndex := by
  unfold extendChainStates
  rw [mem_bindList_iff]
  refine ⟨acc, hacc, ?_⟩
  rw [List.mem_map]
  refine ⟨next, ?_, rfl⟩
  rw [List.mem_filter]
  exact ⟨hnext, hcomp⟩

theorem extendChainStates_mem_prefix
    {orients : List TauOrient} {prefixes : List (List TauState)}
    {nextIndex : Nat} {states : List TauState}
    (hlen : ∀ acc, acc ∈ prefixes → acc.length = nextIndex)
    (hmem : states ∈ extendChainStates orients prefixes nextIndex) :
    states.take nextIndex ∈ prefixes := by
  rcases extendChainStates_mem_split
      (orients := orients) (prefixes := prefixes) (nextIndex := nextIndex)
      hmem with ⟨acc, next, hacc, _hnext, _hcomp, hstates⟩
  subst states
  have htake : (acc ++ [next]).take nextIndex = acc := by
    rw [← hlen acc hacc]
    simp
  simpa [htake] using hacc

theorem extendChainStates_append_left
    (orients suffix : List TauOrient) (prefixes : List (List TauState))
    {nextIndex : Nat}
    (hpos : 0 < nextIndex)
    (hidx : nextIndex < orients.length) :
    extendChainStates (orients ++ suffix) prefixes nextIndex =
      extendChainStates orients prefixes nextIndex := by
  have hprev : nextIndex - 1 < orients.length := by
    omega
  simp [extendChainStates,
    tauOrientAt_append_left (orients := orients) (suffix := suffix)
      (idx := nextIndex) hidx,
    tauOrientAt_append_left (orients := orients) (suffix := suffix)
      (idx := nextIndex - 1) hprev]

theorem buildChainStatesFrom_eq_fromIndex
    {orients : List TauOrient} {n : Nat} {prefixes : List (List TauState)}
    (hn : n ≤ orients.length) :
    buildChainStatesFrom orients n prefixes =
      buildChainStatesFromIndex orients (orients.length - n) n prefixes := by
  induction n generalizing prefixes with
  | zero =>
      rfl
  | succ n ih =>
      unfold buildChainStatesFrom
      unfold buildChainStatesFromIndex
      rw [ih (prefixes :=
        extendChainStates orients prefixes (orients.length - (n + 1)))
        (by omega)]
      congr
      omega

theorem buildChainStatesFromIndex_append_singleton_last_aux
    (orients : List TauOrient) (next : TauOrient)
    (prefixes : List (List TauState))
    (start k : Nat)
    (hpos : 0 < start)
    (hlen : start + k = orients.length) :
    buildChainStatesFromIndex (orients ++ [next]) start (k + 1) prefixes =
      extendChainStates (orients ++ [next])
        (buildChainStatesFromIndex orients start k prefixes) orients.length := by
  induction k generalizing start prefixes with
  | zero =>
      have hstart : start = orients.length := by
        omega
      subst start
      rfl
  | succ k ih =>
      have hidx : start < orients.length := by
        omega
      have hlen' : start + 1 + k = orients.length := by
        omega
      have hExt :
          extendChainStates (orients ++ [next]) prefixes start =
            extendChainStates orients prefixes start :=
        extendChainStates_append_left orients [next] prefixes hpos hidx
      simpa [buildChainStatesFromIndex, hExt] using
        ih (prefixes := extendChainStates orients prefixes start)
          (start := start + 1) (by omega) hlen'

theorem buildChainStatesFrom_prefixCompatible_full
    (orients : List TauOrient) (n : Nat)
    (prefixes : List (List TauState))
    (hn : n < orients.length)
    (hprefixes : ∀ states, states ∈ prefixes →
      chainPrefixCompatibleAt orients states (orients.length - n)) :
    ∀ states, states ∈ buildChainStatesFrom orients n prefixes →
      chainPrefixCompatibleAt orients states orients.length := by
  induction n generalizing prefixes with
  | zero =>
      simpa [buildChainStatesFrom] using hprefixes
  | succ n ih =>
      intro states hmem
      unfold buildChainStatesFrom at hmem
      let nextIndex := orients.length - (n + 1)
      have hpos : 0 < nextIndex := by
        simp [nextIndex]
        omega
      have hExt : ∀ states, states ∈ extendChainStates orients prefixes nextIndex →
          chainPrefixCompatibleAt orients states (orients.length - n) := by
        intro states hstates
        have hraw := extendChainStates_prefixCompatible
          (orients := orients) (prefixes := prefixes) (nextIndex := nextIndex)
          hpos (by
            intro s hs
            simpa [nextIndex] using hprefixes s hs) states hstates
        have hidx : nextIndex + 1 = orients.length - n := by
          simp [nextIndex]
          omega
        simpa [hidx] using hraw
      exact ih (extendChainStates orients prefixes nextIndex) (by omega)
        hExt states hmem

theorem allChainStates_compatible (orients : List TauOrient) :
    (allChainStates orients).all (compatibleChainStates orients) = true := by
  cases orients with
  | nil =>
      decide
  | cons orient rest =>
      rw [List.all_eq_true]
      intro states hmem
      have hprefix := buildChainStatesFrom_prefixCompatible_full
        (orient :: rest) rest.length (allTauStates.map fun s => [s])
        (by simp)
        (by
          intro states hstates
          rw [List.mem_map] at hstates
          rcases hstates with ⟨state, _hstate, rfl⟩
          have hlen : (orient :: rest).length - rest.length = 1 := by
            simp
          simpa [hlen] using
            chainPrefixCompatibleAt_singleton (orient :: rest) state)
        states hmem
      exact chainPrefixCompatibleAt_full hprefix

theorem allChainStates_mem_length
    {orients : List TauOrient} {states : List TauState}
    (hmem : states ∈ allChainStates orients) :
    states.length = orients.length := by
  have hAll := allChainStates_compatible orients
  rw [List.all_eq_true] at hAll
  have hcomp := hAll states hmem
  unfold compatibleChainStates at hcomp
  have hparts :
      (states.length == orients.length) = true ∧
        (List.range (orients.length - 1)).all (fun i =>
          compatibleAdjacent (tauOrientAt orients i)
            (tauOrientAt orients (i + 1))
            (chainStateAt states i) (chainStateAt states (i + 1))) = true := by
    simpa [Bool.and_eq_true] using hcomp
  exact beq_iff_eq.mp hparts.1

theorem allChainStates_append_singleton_eq_extend
    (orients : List TauOrient) (next : TauOrient)
    (hne : orients ≠ []) :
    allChainStates (orients ++ [next]) =
      extendChainStates (orients ++ [next]) (allChainStates orients)
        orients.length := by
  cases orients with
  | nil =>
      exact False.elim (hne rfl)
  | cons orient rest =>
      have hApp :
          allChainStates ((orient :: rest) ++ [next]) =
            buildChainStatesFromIndex ((orient :: rest) ++ [next]) 1
              (orient :: rest).length (allTauStates.map fun s => [s]) := by
        simpa [allChainStates] using
          (buildChainStatesFrom_eq_fromIndex
            (orients := (orient :: rest) ++ [next])
            (n := (orient :: rest).length)
            (prefixes := allTauStates.map fun s => [s]) (by simp))
      have hOrig :
          allChainStates (orient :: rest) =
            buildChainStatesFromIndex (orient :: rest) 1 rest.length
              (allTauStates.map fun s => [s]) := by
        simpa [allChainStates] using
          (buildChainStatesFrom_eq_fromIndex
            (orients := orient :: rest)
            (n := rest.length)
            (prefixes := allTauStates.map fun s => [s]) (by simp))
      have hAux :
          buildChainStatesFromIndex ((orient :: rest) ++ [next]) 1
              (orient :: rest).length (allTauStates.map fun s => [s]) =
            extendChainStates ((orient :: rest) ++ [next])
              (buildChainStatesFromIndex (orient :: rest) 1 rest.length
                (allTauStates.map fun s => [s]))
              (orient :: rest).length := by
        simpa using
          (buildChainStatesFromIndex_append_singleton_last_aux
            (orients := orient :: rest) (next := next)
            (prefixes := allTauStates.map fun s => [s])
            (start := 1) (k := rest.length) (by omega) (by simp [Nat.add_comm]))
      calc
        allChainStates ((orient :: rest) ++ [next])
            = buildChainStatesFromIndex ((orient :: rest) ++ [next]) 1
                (orient :: rest).length (allTauStates.map fun s => [s]) := hApp
        _ = extendChainStates ((orient :: rest) ++ [next])
              (buildChainStatesFromIndex (orient :: rest) 1 rest.length
                (allTauStates.map fun s => [s]))
              (orient :: rest).length := hAux
        _ = extendChainStates ((orient :: rest) ++ [next])
              (allChainStates (orient :: rest)) (orient :: rest).length := by
                rw [← hOrig]

theorem allChainStates_append_singleton_mem_split
    {orients : List TauOrient} {next : TauOrient}
    {states : List TauState}
    (hne : orients ≠ [])
    (hmem : states ∈ allChainStates (orients ++ [next])) :
    ∃ pref last,
      pref ∈ allChainStates orients ∧
        last ∈ allTauStates ∧
        compatibleAdjacent
          (tauOrientAt (orients ++ [next]) (orients.length - 1))
          (tauOrientAt (orients ++ [next]) orients.length)
          (chainStateAt pref (orients.length - 1)) last = true ∧
        states = pref ++ [last] := by
  have hEq := allChainStates_append_singleton_eq_extend orients next hne
  rw [hEq] at hmem
  exact extendChainStates_mem_split
    (orients := orients ++ [next])
    (prefixes := allChainStates orients)
    (nextIndex := orients.length)
    hmem

theorem allChainStates_append_singleton_mem_of_split
    {orients : List TauOrient} {next : TauOrient}
    {pref : List TauState} {last : TauState}
    (hne : orients ≠ [])
    (hpref : pref ∈ allChainStates orients)
    (hlast : last ∈ allTauStates)
    (hcompatible : compatibleAdjacent
      (tauOrientAt (orients ++ [next]) (orients.length - 1))
      (tauOrientAt (orients ++ [next]) orients.length)
      (chainStateAt pref (orients.length - 1)) last = true) :
    pref ++ [last] ∈ allChainStates (orients ++ [next]) := by
  have hEq := allChainStates_append_singleton_eq_extend orients next hne
  rw [hEq]
  exact extendChainStates_mem_of_split
    (orients := orients ++ [next])
    (prefixes := allChainStates orients)
    (nextIndex := orients.length)
    hpref hlast hcompatible

theorem allChainStates_append_singleton_mem_prefix
    {orients : List TauOrient} {next : TauOrient}
    {states : List TauState}
    (hne : orients ≠ [])
    (hmem : states ∈ allChainStates (orients ++ [next])) :
    states.take orients.length ∈ allChainStates orients := by
  have hEq := allChainStates_append_singleton_eq_extend orients next hne
  rw [hEq] at hmem
  exact extendChainStates_mem_prefix
    (orients := orients ++ [next])
    (prefixes := allChainStates orients)
    (nextIndex := orients.length)
    (states := states)
    (by
      intro acc hacc
      exact allChainStates_mem_length hacc)
    hmem

def colorAssignments4 : List (List LColor) :=
  bindList colors fun c₀ =>
  bindList colors fun c₁ =>
  bindList colors fun c₂ =>
  colors.map fun c₃ => [c₀, c₁, c₂, c₃]

def chainInputKey (orients : List TauOrient) (states : List TauState) : List LColor :=
  (chainInputOrder orients).map fun e => tauStateColorAt states 0 e

theorem chainInputKey_append_prefix_take
    (orients : List TauOrient) (next : TauOrient)
    (states : List TauState)
    (hne : orients ≠ []) :
    chainInputKey orients (states.take orients.length) =
      chainInputKey (orients ++ [next]) states := by
  cases orients with
  | nil =>
      exact False.elim (hne rfl)
  | cons orient rest =>
      cases states <;> rfl

def chainFiberFrom (orients : List TauOrient) (statesList : List (List TauState))
    (key : List LColor) : List (List TauState) :=
  statesList.filter fun states => chainInputKey orients states == key

def chainClosureStep (orients : List TauOrient) (fiber seen : List (List TauState)) :
    List (List TauState) :=
  fiber.foldl
    (fun acc candidate =>
      if acc.any (fun current => chainSingleKempeStep orients current candidate) then
        addIfFresh acc candidate
      else
        acc)
    seen

def closeChainFiber (orients : List TauOrient) (fiber : List (List TauState)) :
    Nat → List (List TauState) → List (List TauState)
  | 0, seen => seen
  | n + 1, seen =>
      let seen' := chainClosureStep orients fiber seen
      if seen'.length == seen.length then seen' else closeChainFiber orients fiber n seen'

def chainFiberConnected (orients : List TauOrient) (fiber : List (List TauState)) : Bool :=
  match fiber with
  | [] => true
  | root :: _ =>
      let closure := closeChainFiber orients fiber fiber.length [root]
      fiber.all fun state => closure.contains state

theorem bool_false_of_not_true {b : Bool} (h : ¬ b = true) : b = false := by
  cases hb : b
  · rfl
  · exact False.elim (h hb)

theorem mem_addIfFresh_of_mem {α : Type} [BEq α]
    {xs : List α} {x y : α} (h : x ∈ xs) :
    x ∈ addIfFresh xs y := by
  unfold addIfFresh
  split
  · exact h
  · simp [h]

theorem mem_addIfFresh_self {α : Type} [BEq α] [LawfulBEq α]
    (xs : List α) (x : α) :
    x ∈ addIfFresh xs x := by
  unfold addIfFresh
  by_cases hc : xs.contains x = true
  · simp only [hc, if_true]
    exact List.contains_iff_mem.mp hc
  · have hfalse : xs.contains x = false := bool_false_of_not_true hc
    simp only [hfalse, Bool.false_eq_true, if_false]
    exact List.mem_append_right xs (by simp)

theorem list_any_true_of_mem {α : Type} {xs : List α} {x : α} {p : α → Bool}
    (hmem : x ∈ xs) (hp : p x = true) :
    xs.any p = true := by
  rw [List.any_eq_true]
  exact ⟨x, hmem, hp⟩

theorem tauEdges_mem (edge : TauEdge) :
    edge ∈ tauEdges := by
  cases edge <;> simp [tauEdges]

theorem chainLocalEdges_mem_of_occ_edge
    (orients : List TauOrient) (i : Nat) (edge : TauEdge)
    (hi : i < orients.length) :
    ({ occ := i, edge := edge } : ChainEdge) ∈ chainLocalEdges orients := by
  unfold chainLocalEdges
  rw [mem_bindList_iff]
  refine ⟨i, List.mem_range.mpr hi, ?_⟩
  exact List.mem_map.mpr ⟨edge, tauEdges_mem edge, rfl⟩

theorem chainLocalEdges_mem_occ_lt
    {orients : List TauOrient} {ge : ChainEdge}
    (hmem : ge ∈ chainLocalEdges orients) :
    ge.occ < orients.length := by
  unfold chainLocalEdges at hmem
  rw [mem_bindList_iff] at hmem
  rcases hmem with ⟨i, hi, hmap⟩
  rw [List.mem_range] at hi
  rcases List.mem_map.mp hmap with ⟨edge, _hedge, hgeEq⟩
  rw [← hgeEq]
  exact hi

theorem chainEdges_contains_of_occ_edge_and_representative
    (orients : List TauOrient) (i : Nat) (edge : TauEdge)
    (hi : i < orients.length)
    (hrep : chainIsRepresentativeEdge orients
      ({ occ := i, edge := edge } : ChainEdge) = true) :
    (chainEdges orients).contains
      ({ occ := i, edge := edge } : ChainEdge) = true := by
  apply List.contains_iff_mem.mpr
  unfold chainEdges
  rw [List.mem_filter]
  exact ⟨chainLocalEdges_mem_of_occ_edge orients i edge hi, hrep⟩

theorem mem_appendFresh_left {α : Type} [BEq α]
    {xs ys : List α} {x : α} (h : x ∈ xs) :
    x ∈ appendFresh xs ys := by
  unfold appendFresh
  induction ys generalizing xs with
  | nil =>
      simpa using h
  | cons _ ys ih =>
      simp only [List.foldl_cons]
      exact ih (mem_addIfFresh_of_mem h)

theorem mem_appendFresh_right {α : Type} [BEq α] [LawfulBEq α]
    {xs ys : List α} {x : α} (h : x ∈ ys) :
    x ∈ appendFresh xs ys := by
  unfold appendFresh
  induction ys generalizing xs with
  | nil =>
      cases h
  | cons z zs ih =>
      simp only [List.foldl_cons]
      simp only [List.mem_cons] at h
      rcases h with hx | htail
      · subst z
        exact mem_appendFresh_left (mem_addIfFresh_self xs x)
      · exact ih (xs := addIfFresh xs z) htail

theorem closeChainComponent_mem_of_seen
    (orients : List TauOrient) (states : List TauState)
    (a c : LColor) (n : Nat) {seen : List ChainEdge} {edge : ChainEdge}
    (h : edge ∈ seen) :
    edge ∈ closeChainComponent orients states a c n seen := by
  induction n generalizing seen with
  | zero =>
      simpa [closeChainComponent] using h
  | succ _ ih =>
      simp only [closeChainComponent]
      exact ih (mem_appendFresh_left h)

theorem closeChainComponent_mem_mono_succ
    (orients : List TauOrient) (states : List TauState)
    (a c : LColor) (n : Nat) (seen : List ChainEdge)
    {edge : ChainEdge}
    (h : edge ∈ closeChainComponent orients states a c n seen) :
    edge ∈ closeChainComponent orients states a c (n + 1) seen := by
  induction n generalizing seen with
  | zero =>
      exact closeChainComponent_mem_of_seen orients states a c 1
        (by simpa [closeChainComponent] using h)
  | succ n ih =>
      simp only [closeChainComponent] at h ⊢
      exact ih (appendFresh seen
        (nextChainComponentLayer orients states a c seen)) h

theorem closeChainComponent_mem_mono_add
    (orients : List TauOrient) (states : List TauState)
    (a c : LColor) (n m : Nat) (seen : List ChainEdge)
    {edge : ChainEdge}
    (h : edge ∈ closeChainComponent orients states a c n seen) :
    edge ∈ closeChainComponent orients states a c (n + m) seen := by
  induction m with
  | zero =>
      simpa using h
  | succ m ih =>
      change edge ∈ closeChainComponent orients states a c ((n + m) + 1) seen
      exact closeChainComponent_mem_mono_succ
        orients states a c (n + m) seen ih

theorem chainComponent_seed_mem_of_nonempty
    (orients : List TauOrient) (states : List TauState)
    (move : ChainMove)
    (hNonempty :
      (!(chainComponent orients states move.a move.c move.seed).isEmpty) = true) :
    move.seed ∈ chainComponent orients states move.a move.c move.seed := by
  by_cases hpair : chainEdgeInPair states move.a move.c move.seed = true
  · simp [chainComponent, hpair, closeChainComponent_mem_of_seen]
  · have hempty :
        chainComponent orients states move.a move.c move.seed = [] := by
      simp [chainComponent, hpair]
    simp [hempty] at hNonempty

theorem chainSpecifiedKempeStep_seed_not_outer_input
    (orients : List TauOrient) (s t : List TauState) (move : ChainMove)
    (hstep : chainSpecifiedKempeStep orients s t move = true) :
    (chainOuterInputEdges orients).contains move.seed = false := by
  unfold chainSpecifiedKempeStep at hstep
  simp only [Bool.and_eq_true] at hstep
  rcases hstep with ⟨⟨hNonempty, hAvoid⟩, _hAgree⟩
  have hseedMem :
      move.seed ∈ chainComponent orients s move.a move.c move.seed :=
    chainComponent_seed_mem_of_nonempty orients s move hNonempty
  by_cases hcontains : (chainOuterInputEdges orients).contains move.seed = true
  · have hany :
        (chainComponent orients s move.a move.c move.seed).any
          (fun e => (chainOuterInputEdges orients).contains e) = true :=
      list_any_true_of_mem hseedMem hcontains
    unfold chainComponentAvoidsInputs at hAvoid
    rw [hany] at hAvoid
    cases hAvoid
  · exact bool_false_of_not_true hcontains

theorem chainEdges_singleton_seed_occ_zero
    (orient : TauOrient) (seed : ChainEdge)
    (hseed : (chainEdges [orient]).contains seed = true) :
    seed.occ = 0 := by
  have hmem : seed ∈ chainEdges [orient] := List.contains_iff_mem.mp hseed
  unfold chainEdges at hmem
  rw [List.mem_filter] at hmem
  have hlocal := hmem.1
  unfold chainLocalEdges at hlocal
  rw [mem_bindList_iff] at hlocal
  rcases hlocal with ⟨i, hi, hmap⟩
  rw [List.mem_range] at hi
  have hi0 : i = 0 := by
    cases i with
    | zero =>
        rfl
    | succ _ =>
        simp at hi
  rcases List.mem_map.mp hmap with ⟨edge, _hedge, hseedEq⟩
  rw [← hseedEq, hi0]

theorem tauOrientInputOrder_contains_edge_false_of_chainOuterInput_false_singleton
    (orient : TauOrient) (seed : ChainEdge)
    (hocc : seed.occ = 0)
    (houter : (chainOuterInputEdges [orient]).contains seed = false) :
    (tauOrientInputOrder orient).contains seed.edge = false := by
  cases seed with
  | mk occ edge =>
      simp at hocc
      subst occ
      cases orient <;> cases edge <;>
        simp [chainOuterInputEdges, chainInputOrder, tauOrientAt,
          tauOrientInputOrder, listGetD] at houter ⊢

theorem mem_addIfFresh_source_or_eq {α : Type} [BEq α] [LawfulBEq α]
    (xs : List α) (x y : α) (h : y ∈ addIfFresh xs x) :
    y ∈ xs ∨ y = x := by
  unfold addIfFresh at h
  by_cases hc : xs.contains x = true
  · simp only [hc, if_true] at h
    exact Or.inl h
  · have hfalse : xs.contains x = false := bool_false_of_not_true hc
    simp only [hfalse, Bool.false_eq_true, if_false] at h
    rw [List.mem_append] at h
    rcases h with hxs | hsingle
    · exact Or.inl hxs
    · simp at hsingle
      exact Or.inr hsingle

theorem list_any_false_of_forall_mem {α : Type} {xs : List α} {p : α → Bool}
    (h : ∀ x, x ∈ xs → p x = false) :
    xs.any p = false := by
  rw [List.any_eq_false]
  intro x hx hp
  have hfalse := h x hx
  rw [hfalse] at hp
  cases hp

theorem mem_appendFresh_source_or_mem {α : Type} [BEq α] [LawfulBEq α]
    (xs ys : List α) {x : α} (h : x ∈ appendFresh xs ys) :
    x ∈ xs ∨ x ∈ ys := by
  unfold appendFresh at h
  induction ys generalizing xs with
  | nil =>
      simp at h
      exact Or.inl h
  | cons y ys ih =>
      simp only [List.foldl_cons] at h
      rcases ih (addIfFresh xs y) h with hsource | htail
      · rcases mem_addIfFresh_source_or_eq xs y x hsource with hxs | hxy
        · exact Or.inl hxs
        · subst hxy
          exact Or.inr (by simp)
      · exact Or.inr (by simp [htail])

theorem nextChainComponentLayer_mem_mono_seen
    (orients : List TauOrient) (states : List TauState)
    (a c : LColor) {seen₁ seen₂ : List ChainEdge}
    (hsub : ∀ edge, edge ∈ seen₁ → edge ∈ seen₂)
    {edge : ChainEdge}
    (hmem : edge ∈ nextChainComponentLayer orients states a c seen₁) :
    edge ∈ seen₂ ∨
      edge ∈ nextChainComponentLayer orients states a c seen₂ := by
  have hfilter := hmem
  unfold nextChainComponentLayer at hfilter
  rw [List.mem_filter] at hfilter
  rcases hfilter with ⟨hchain, hpred⟩
  simp only [Bool.and_eq_true] at hpred
  rcases hpred with ⟨⟨hpair, _hfresh₁⟩, hshare₁⟩
  by_cases hseen₂ : edge ∈ seen₂
  · exact Or.inl hseen₂
  · have hcontains₂ : seen₂.contains edge = false :=
      bool_false_of_not_true (by
        intro hcontains
        exact hseen₂ (List.contains_iff_mem.mp hcontains))
    have hfresh₂ : (!seen₂.contains edge) = true := by
      rw [hcontains₂]
      rfl
    have hshare₂ :
        seen₂.any (chainEdgesShareEndpoint orients edge) = true := by
      rw [List.any_eq_true] at hshare₁
      rcases hshare₁ with ⟨other, hother, hshare⟩
      exact list_any_true_of_mem (hsub other hother) hshare
    exact Or.inr (by
      unfold nextChainComponentLayer
      rw [List.mem_filter]
      exact ⟨hchain, by
        rw [hpair, hfresh₂, hshare₂]
        rfl⟩)

theorem closeChainComponent_mem_mono_seen
    (orients : List TauOrient) (states : List TauState)
    (a c : LColor) (n : Nat) {seen₁ seen₂ : List ChainEdge}
    (hsub : ∀ edge, edge ∈ seen₁ → edge ∈ seen₂)
    {edge : ChainEdge}
    (hmem : edge ∈ closeChainComponent orients states a c n seen₁) :
    edge ∈ closeChainComponent orients states a c n seen₂ := by
  induction n generalizing seen₁ seen₂ with
  | zero =>
      exact hsub edge (by simpa [closeChainComponent] using hmem)
  | succ n ih =>
      simp only [closeChainComponent] at hmem ⊢
      apply ih
      · intro other hother
        rcases mem_appendFresh_source_or_mem seen₁
            (nextChainComponentLayer orients states a c seen₁) hother with
          hseen | hlayer
        · exact mem_appendFresh_left (hsub other hseen)
        · rcases nextChainComponentLayer_mem_mono_seen
              orients states a c (seen₁ := seen₁) (seen₂ := seen₂)
              hsub hlayer with
            hseen₂ | hlayer₂
          · exact mem_appendFresh_left hseen₂
          · exact mem_appendFresh_right hlayer₂
      · exact hmem

theorem closeChainComponent_lift_property
    (orients : List TauOrient) (states : List TauState)
    (a c : LColor) (n : Nat) (seen : List ChainEdge)
    (P : ChainEdge → Prop)
    (hseen : ∀ edge, edge ∈ seen → P edge)
    (hstep : ∀ seen' edge,
      (∀ other, other ∈ seen' → P other) →
      edge ∈ nextChainComponentLayer orients states a c seen' →
      P edge) :
    ∀ edge,
      edge ∈ closeChainComponent orients states a c n seen → P edge := by
  induction n generalizing seen with
  | zero =>
      intro edge hmem
      exact hseen edge (by simpa [closeChainComponent] using hmem)
  | succ n ih =>
      intro edge hmem
      simp only [closeChainComponent] at hmem
      let layer := nextChainComponentLayer orients states a c seen
      have hseen' : ∀ edge, edge ∈ appendFresh seen layer → P edge := by
        intro other hother
        rcases mem_appendFresh_source_or_mem seen layer hother with
          hold | hlayer
        · exact hseen other hold
        · exact hstep seen other hseen hlayer
      exact ih (appendFresh seen layer) hseen' edge hmem

theorem closeChainComponent_mem_comp
    (orients : List TauOrient) (states : List TauState)
    (a c : LColor) (m n : Nat) (seen : List ChainEdge)
    {edge : ChainEdge}
    (h : edge ∈ closeChainComponent orients states a c n
      (closeChainComponent orients states a c m seen)) :
    edge ∈ closeChainComponent orients states a c (m + n) seen := by
  induction m generalizing seen with
  | zero =>
      simpa [closeChainComponent] using h
  | succ m ih =>
      simp only [closeChainComponent] at h
      have hrec := ih (seen := appendFresh seen
        (nextChainComponentLayer orients states a c seen)) h
      have hnat : m + 1 + n = (m + n) + 1 := by omega
      rw [hnat]
      simp only [closeChainComponent]
      exact hrec

theorem closeChainComponent_mem_nextLayer_close
    (orients : List TauOrient) (states : List TauState)
    (a c : LColor) (m : Nat) (seen : List ChainEdge)
    {edge : ChainEdge}
    (h : edge ∈ nextChainComponentLayer orients states a c
      (closeChainComponent orients states a c m seen)) :
    edge ∈ closeChainComponent orients states a c (m + 1) seen := by
  apply closeChainComponent_mem_comp
    (orients := orients) (states := states) (a := a) (c := c)
    (m := m) (n := 1) (seen := seen)
  simp only [closeChainComponent]
  exact mem_appendFresh_right h

theorem contains_map_injective_eq {α β : Type}
    [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (hinj : Function.Injective f) (xs : List α) (x : α) :
    (xs.map f).contains (f x) = xs.contains x := by
  by_cases hx : x ∈ xs
  · have hxs : xs.contains x = true := List.contains_iff_mem.mpr hx
    have hmap : (xs.map f).contains (f x) = true :=
      List.contains_iff_mem.mpr (List.mem_map.mpr ⟨x, hx, rfl⟩)
    rw [hmap, hxs]
  · have hxs : xs.contains x = false :=
      bool_false_of_not_true (by
        intro hcontains
        exact hx (List.contains_iff_mem.mp hcontains))
    have hnotMap : ¬ f x ∈ xs.map f := by
      intro hmem
      rcases List.mem_map.mp hmem with ⟨y, hy, hfy⟩
      exact hx (by simpa [hinj hfy] using hy)
    have hmap : (xs.map f).contains (f x) = false :=
      bool_false_of_not_true (by
        intro hcontains
        exact hnotMap (List.contains_iff_mem.mp hcontains))
    rw [hmap, hxs]

theorem map_addIfFresh_injective {α β : Type}
    [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (hinj : Function.Injective f)
    (xs : List α) (x : α) :
    (addIfFresh xs x).map f = addIfFresh (xs.map f) (f x) := by
  unfold addIfFresh
  by_cases hx : x ∈ xs
  · have hmap : f x ∈ xs.map f := List.mem_map.mpr ⟨x, hx, rfl⟩
    simp [hx, hmap]
  · have hnotMap : ¬ f x ∈ xs.map f := by
      intro hmem
      rcases List.mem_map.mp hmem with ⟨y, hy, hfy⟩
      exact hx (by simpa [hinj hfy] using hy)
    simp [hx, hnotMap]

theorem map_appendFresh_injective {α β : Type}
    [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (hinj : Function.Injective f)
    (xs ys : List α) :
    (appendFresh xs ys).map f = appendFresh (xs.map f) (ys.map f) := by
  unfold appendFresh
  induction ys generalizing xs with
  | nil =>
      simp
  | cons y ys ih =>
      simp only [List.foldl_cons, List.map_cons]
      calc
        (List.foldl addIfFresh (addIfFresh xs y) ys).map f =
            List.foldl addIfFresh ((addIfFresh xs y).map f) (ys.map f) := by
              exact ih (addIfFresh xs y)
        _ = List.foldl addIfFresh (addIfFresh (xs.map f) (f y)) (ys.map f) := by
              rw [map_addIfFresh_injective f hinj xs y]

theorem nextChainComponentLayer_mem_chainEdges
    (orients : List TauOrient) (states : List TauState)
    (a c : LColor) (seen : List ChainEdge)
    {edge : ChainEdge}
    (hmem : edge ∈ nextChainComponentLayer orients states a c seen) :
    edge ∈ chainEdges orients := by
  unfold nextChainComponentLayer at hmem
  exact (List.mem_filter.mp hmem).1

theorem closeChainComponent_mem_seen_or_chainEdges
    (orients : List TauOrient) (states : List TauState)
    (a c : LColor) (n : Nat) (seen : List ChainEdge)
    {edge : ChainEdge}
    (hmem : edge ∈ closeChainComponent orients states a c n seen) :
    edge ∈ seen ∨ edge ∈ chainEdges orients := by
  induction n generalizing seen with
  | zero =>
      simpa [closeChainComponent] using (Or.inl hmem)
  | succ _ ih =>
      simp only [closeChainComponent] at hmem
      let layer := nextChainComponentLayer orients states a c seen
      have hrec :
          edge ∈ appendFresh seen layer ∨ edge ∈ chainEdges orients :=
        ih (appendFresh seen layer) hmem
      rcases hrec with hseenLayer | hchain
      · rcases mem_appendFresh_source_or_mem seen layer hseenLayer with
          hseen | hlayer
        · exact Or.inl hseen
        · exact Or.inr
            (nextChainComponentLayer_mem_chainEdges
              orients states a c seen hlayer)
      · exact Or.inr hchain

theorem chainComponent_mem_chainEdges
    (orients : List TauOrient) (states : List TauState)
    (a c : LColor) (seed : ChainEdge)
    (hseed : seed ∈ chainEdges orients)
    {edge : ChainEdge}
    (hmem : edge ∈ chainComponent orients states a c seed) :
    edge ∈ chainEdges orients := by
  by_cases hpair : chainEdgeInPair states a c seed = true
  · have hmem' :
        edge ∈ closeChainComponent orients states a c
          (chainEdges orients).length [seed] := by
      simpa [chainComponent, hpair] using hmem
    rcases closeChainComponent_mem_seen_or_chainEdges
        orients states a c (chainEdges orients).length [seed] hmem' with
      hseen | hchain
    · simp at hseen
      subst hseen
      exact hseed
    · exact hchain
  · have hempty :
        chainComponent orients states a c seed = [] := by
      simp [chainComponent, hpair]
    rw [hempty] at hmem
    cases hmem

theorem chainComponent_mem_occ_zero_of_singleton
    (orient : TauOrient) (states : List TauState)
    (a c : LColor) (seed edge : ChainEdge)
    (hseed : (chainEdges [orient]).contains seed = true)
    (hmem : edge ∈ chainComponent [orient] states a c seed) :
    edge.occ = 0 := by
  have hseedMem : seed ∈ chainEdges [orient] :=
    List.contains_iff_mem.mp hseed
  have hedgeMem :
      edge ∈ chainEdges [orient] :=
    chainComponent_mem_chainEdges [orient] states a c seed hseedMem hmem
  unfold chainEdges at hedgeMem
  have hlocal : edge ∈ chainLocalEdges [orient] :=
    (List.mem_filter.mp hedgeMem).1
  have hoccLt := chainLocalEdges_mem_occ_lt hlocal
  have hoccLtOne : edge.occ < 1 := by
    simpa using hoccLt
  omega

theorem chainComponentAvoidsInputs_contains_false
    (orients : List TauOrient) (component : List ChainEdge)
    {edge : ChainEdge}
    (hAvoid : chainComponentAvoidsInputs orients component = true)
    (hmem : edge ∈ component) :
    (chainOuterInputEdges orients).contains edge = false := by
  by_cases hcontains : (chainOuterInputEdges orients).contains edge = true
  · have hany :
        component.any (fun e => (chainOuterInputEdges orients).contains e) =
          true :=
      list_any_true_of_mem hmem hcontains
    unfold chainComponentAvoidsInputs at hAvoid
    rw [hany] at hAvoid
    cases hAvoid
  · exact bool_false_of_not_true hcontains

theorem addIfFresh_nodup {α : Type} [BEq α] [LawfulBEq α]
    (xs : List α) (x : α) (hxs : xs.Nodup) :
    (addIfFresh xs x).Nodup := by
  unfold addIfFresh
  by_cases hc : xs.contains x = true
  · simp only [hc, if_true]
    exact hxs
  · have hfalse : xs.contains x = false := bool_false_of_not_true hc
    have hxnot : x ∉ xs := by
      intro hx
      exact hc (List.contains_iff_mem.mpr hx)
    simp only [hfalse, Bool.false_eq_true, if_false]
    simp [List.nodup_append, hxs]
    intro a ha heq
    subst heq
    exact hxnot ha

theorem addIfFresh_length_le {α : Type} [BEq α] [LawfulBEq α]
    (xs : List α) (x : α) :
    xs.length ≤ (addIfFresh xs x).length := by
  by_cases hx : x ∈ xs <;> simp [addIfFresh, hx]

theorem addIfFresh_length_lt_of_fresh {α : Type} [BEq α] [LawfulBEq α]
    (xs : List α) (x : α) (hfresh : x ∉ xs) :
    xs.length < (addIfFresh xs x).length := by
  simp [addIfFresh, hfresh]

theorem appendFresh_length_le {α : Type} [BEq α] [LawfulBEq α]
    (xs ys : List α) :
    xs.length ≤ (appendFresh xs ys).length := by
  unfold appendFresh
  induction ys generalizing xs with
  | nil =>
      simp
  | cons y ys ih =>
      simp only [List.foldl_cons]
      exact Nat.le_trans (addIfFresh_length_le xs y)
        (ih (addIfFresh xs y))

theorem appendFresh_length_lt_of_mem_fresh {α : Type}
    [BEq α] [LawfulBEq α]
    {xs ys : List α} {x : α}
    (hmem : x ∈ ys) (hfresh : x ∉ xs) :
    xs.length < (appendFresh xs ys).length := by
  unfold appendFresh
  induction ys generalizing xs with
  | nil =>
      cases hmem
  | cons y ys ih =>
      simp only [List.foldl_cons]
      simp only [List.mem_cons] at hmem
      rcases hmem with hxy | htail
      · subst y
        exact Nat.lt_of_lt_of_le
          (addIfFresh_length_lt_of_fresh xs x hfresh)
          (appendFresh_length_le (addIfFresh xs x) ys)
      · by_cases hxadd : x ∈ addIfFresh xs y
        · rcases mem_addIfFresh_source_or_eq xs y x hxadd with hxsrc | hxeq
          · exact False.elim (hfresh hxsrc)
          · subst x
            exact Nat.lt_of_lt_of_le
              (addIfFresh_length_lt_of_fresh xs y (by
                intro hy
                exact hfresh hy))
              (appendFresh_length_le (addIfFresh xs y) ys)
        · exact Nat.lt_of_le_of_lt
            (addIfFresh_length_le xs y)
            (ih (xs := addIfFresh xs y) htail hxadd)

theorem appendFresh_length_lt_of_mem_not_mem {α : Type}
    [BEq α] [LawfulBEq α] {xs ys : List α} {x : α}
    (hmem : x ∈ appendFresh xs ys) (hfresh : x ∉ xs) :
    xs.length < (appendFresh xs ys).length := by
  rcases mem_appendFresh_source_or_mem xs ys hmem with hxsrc | hxys
  · exact False.elim (hfresh hxsrc)
  · exact appendFresh_length_lt_of_mem_fresh hxys hfresh

theorem appendFresh_nodup {α : Type} [BEq α] [LawfulBEq α]
    {xs ys : List α} (hxs : xs.Nodup) :
    (appendFresh xs ys).Nodup := by
  unfold appendFresh
  induction ys generalizing xs with
  | nil =>
      simpa using hxs
  | cons y ys ih =>
      simp only [List.foldl_cons]
      exact ih (addIfFresh_nodup xs y hxs)

theorem appendFresh_subset_of_subset_right {α : Type}
    [BEq α] [LawfulBEq α] {xs ys zs : List α}
    (hxs : xs ⊆ zs) (hys : ys ⊆ zs) :
    appendFresh xs ys ⊆ zs := by
  intro x hx
  rcases mem_appendFresh_source_or_mem xs ys hx with hxsrc | hxys
  · exact hxs hxsrc
  · exact hys hxys

theorem nextChainComponentLayer_subset_chainEdges
    (orients : List TauOrient) (states : List TauState)
    (a c : LColor) (seen : List ChainEdge) :
    nextChainComponentLayer orients states a c seen ⊆ chainEdges orients := by
  intro edge hmem
  exact nextChainComponentLayer_mem_chainEdges orients states a c seen hmem

theorem nextChainComponentLayer_mem_not_seen
    (orients : List TauOrient) (states : List TauState)
    (a c : LColor) {seen : List ChainEdge} {edge : ChainEdge}
    (hmem : edge ∈ nextChainComponentLayer orients states a c seen) :
    edge ∉ seen := by
  intro hseen
  unfold nextChainComponentLayer at hmem
  rw [List.mem_filter] at hmem
  rcases hmem with ⟨_hchain, hpred⟩
  simp only [Bool.and_eq_true] at hpred
  rcases hpred with ⟨⟨_hpair, hfresh⟩, _hshare⟩
  have hcontains : seen.contains edge = true := List.contains_iff_mem.mpr hseen
  rw [hcontains] at hfresh
  cases hfresh

theorem closeChainComponent_nodup
    (orients : List TauOrient) (states : List TauState)
    (a c : LColor) (n : Nat) {seen : List ChainEdge}
    (hseen : seen.Nodup) :
    (closeChainComponent orients states a c n seen).Nodup := by
  induction n generalizing seen with
  | zero =>
      simpa [closeChainComponent] using hseen
  | succ _ ih =>
      simp only [closeChainComponent]
      exact ih (appendFresh_nodup hseen)

theorem closeChainComponent_subset_chainEdges
    (orients : List TauOrient) (states : List TauState)
    (a c : LColor) (n : Nat) {seen : List ChainEdge}
    (hseen : seen ⊆ chainEdges orients) :
    closeChainComponent orients states a c n seen ⊆ chainEdges orients := by
  induction n generalizing seen with
  | zero =>
      intro edge hmem
      exact hseen (by simpa [closeChainComponent] using hmem)
  | succ _ ih =>
      simp only [closeChainComponent]
      apply ih
      exact appendFresh_subset_of_subset_right hseen
        (nextChainComponentLayer_subset_chainEdges orients states a c seen)

theorem closeChainComponent_length_le_chainEdges
    (orients : List TauOrient) (states : List TauState)
    (a c : LColor) (n : Nat) {seen : List ChainEdge}
    (hseenNodup : seen.Nodup)
    (hseenSub : seen ⊆ chainEdges orients) :
    (closeChainComponent orients states a c n seen).length ≤
      (chainEdges orients).length := by
  exact List.Subperm.length_le
    (List.subperm_of_subset
      (closeChainComponent_nodup orients states a c n hseenNodup)
      (closeChainComponent_subset_chainEdges orients states a c n hseenSub))

theorem closeChainComponent_length_ge_of_new
    (orients : List TauOrient) (states : List TauState)
    (a c : LColor) :
    ∀ (n : Nat) (seen : List ChainEdge) {edge : ChainEdge},
      edge ∈ closeChainComponent orients states a c (n + 1) seen →
        edge ∉ closeChainComponent orients states a c n seen →
          seen.length + (n + 1) ≤
            (closeChainComponent orients states a c (n + 1) seen).length
  | 0, seen, edge, hmem, hnot => by
      have hmem' : edge ∈ appendFresh seen
          (nextChainComponentLayer orients states a c seen) := by
        simpa [closeChainComponent] using hmem
      have hnot' : edge ∉ seen := by
        intro hseen
        exact hnot (by simpa [closeChainComponent] using hseen)
      have hlt := appendFresh_length_lt_of_mem_not_mem hmem' hnot'
      simpa [closeChainComponent] using (Nat.succ_le_iff.mpr hlt)
  | n + 1, seen, edge, hmem, hnot => by
      let layer := nextChainComponentLayer orients states a c seen
      let seen' := appendFresh seen layer
      have hmem' :
          edge ∈ closeChainComponent orients states a c (n + 1) seen' := by
        simpa [closeChainComponent, layer, seen'] using hmem
      have hnot' :
          edge ∉ closeChainComponent orients states a c n seen' := by
        intro hedge
        exact hnot (by simpa [closeChainComponent, layer, seen'] using hedge)
      have ih := closeChainComponent_length_ge_of_new orients states a c
        n seen' hmem' hnot'
      have hLayerNe : layer ≠ [] := by
        intro hnil
        have hmemPrev :
            edge ∈ closeChainComponent orients states a c (n + 1) seen := by
          simpa [closeChainComponent, layer, seen', hnil, appendFresh]
            using hmem
        exact hnot hmemPrev
      rcases List.exists_mem_of_ne_nil layer hLayerNe with ⟨z, hz⟩
      have hnotSeen : z ∉ seen :=
        nextChainComponentLayer_mem_not_seen orients states a c hz
      have hgrow : seen.length + 1 ≤ seen'.length := by
        have hlt := appendFresh_length_lt_of_mem_fresh (xs := seen)
          (ys := layer) hz hnotSeen
        have hle : seen.length + 1 ≤ (appendFresh seen layer).length :=
          Nat.succ_le_iff.mpr hlt
        simpa [seen'] using hle
      have htarget :
          seen.length + ((n + 1) + 1) ≤ seen'.length + (n + 1) := by
        omega
      exact Nat.le_trans htarget ih

theorem closeChainComponent_bounded_saturation
    (orients : List TauOrient) (states : List TauState)
    (a c : LColor) {seen : List ChainEdge}
    (hseenNodup : seen.Nodup)
    (hseenSub : seen ⊆ chainEdges orients)
    {edge : ChainEdge}
    (hmem : edge ∈ closeChainComponent orients states a c
      ((chainEdges orients).length + 1) seen) :
    edge ∈ closeChainComponent orients states a c
      (chainEdges orients).length seen := by
  by_contra hnot
  have hge := closeChainComponent_length_ge_of_new orients states a c
    (chainEdges orients).length seen hmem hnot
  have hle := closeChainComponent_length_le_chainEdges
    orients states a c ((chainEdges orients).length + 1)
    hseenNodup hseenSub
  omega

theorem chainComponent_nextLayer_empty
    (orients : List TauOrient) (states : List TauState)
    (a c : LColor) (seed : ChainEdge)
    (hseed : seed ∈ chainEdges orients)
    {edge : ChainEdge}
    (hmem : edge ∈ nextChainComponentLayer orients states a c
      (chainComponent orients states a c seed)) :
    False := by
  by_cases hpair : chainEdgeInPair states a c seed = true
  · have hmemClose : edge ∈ nextChainComponentLayer orients states a c
        (closeChainComponent orients states a c
          (chainEdges orients).length [seed]) := by
      simpa [chainComponent, hpair] using hmem
    have hmemSucc : edge ∈ closeChainComponent orients states a c
        ((chainEdges orients).length + 1) [seed] := by
      exact closeChainComponent_mem_nextLayer_close orients states a c
        (chainEdges orients).length [seed] hmemClose
    have hmemSat : edge ∈ closeChainComponent orients states a c
        (chainEdges orients).length [seed] := by
      apply closeChainComponent_bounded_saturation
      · simp
      · intro x hx
        simp at hx
        subst x
        exact hseed
      · exact hmemSucc
    exact nextChainComponentLayer_mem_not_seen orients states a c
      hmemClose hmemSat
  · have hempty : chainComponent orients states a c seed = [] := by
      simp [chainComponent, hpair]
    unfold nextChainComponentLayer at hmem
    rw [hempty] at hmem
    simp at hmem

theorem list_length_beq_false_of_nodup_subset_new {α : Type} [DecidableEq α]
    (xs ys : List α) (y : α) (hxs : xs.Nodup) (hsub : xs ⊆ ys)
    (hy : y ∈ ys) (hnot : y ∉ xs) :
    (ys.length == xs.length) = false := by
  by_cases hbeq : (ys.length == xs.length) = true
  · have hlen : ys.length = xs.length := by
      simpa using hbeq
    have hsp : List.Subperm xs ys := List.subperm_of_subset hxs hsub
    have hperm : List.Perm xs ys :=
      List.Subperm.perm_of_length_le hsp (by simp [hlen])
    have hyx : y ∈ xs := (List.Perm.mem_iff hperm).mpr hy
    exact False.elim (hnot hyx)
  · exact bool_false_of_not_true hbeq

theorem list_length_beq_one_false_of_two_mem {α : Type}
    [DecidableEq α] (xs : List α) (x y : α)
    (hx : x ∈ xs) (hy : y ∈ xs) (hne : x ≠ y) :
    (xs.length == 1) = false := by
  cases xs with
  | nil => cases hx
  | cons a rest =>
      cases rest with
      | nil =>
          simp only [List.mem_cons, List.not_mem_nil] at hx hy
          rcases hx with rfl | hxfalse
          · rcases hy with rfl | hyfalse
            · exact False.elim (hne rfl)
            · cases hyfalse
          · cases hxfalse
      | cons _ _ =>
          rfl

theorem chainClosureStep_append (orients : List TauOrient)
    (pref suffix seen : List (List TauState)) :
    chainClosureStep orients (pref ++ suffix) seen =
      chainClosureStep orients suffix (chainClosureStep orients pref seen) := by
  simp [chainClosureStep, List.foldl_append]

theorem chainClosureStep_mem_of_seen (orients : List TauOrient)
    (fiber seen : List (List TauState)) (x : List TauState)
    (h : x ∈ seen) :
    x ∈ chainClosureStep orients fiber seen := by
  unfold chainClosureStep
  induction fiber generalizing seen with
  | nil =>
      simpa using h
  | cons candidate rest ih =>
      simp only [List.foldl_cons]
      apply ih
      by_cases hc :
          (seen.any fun current => chainSingleKempeStep orients current candidate) = true
      · simp only [hc, if_true]
        exact mem_addIfFresh_of_mem h
      · have hfalse :
            (seen.any fun current => chainSingleKempeStep orients current candidate) =
              false :=
          bool_false_of_not_true hc
        simp only [hfalse, Bool.false_eq_true, if_false]
        exact h

theorem chainClosureStep_lift_property (orients : List TauOrient)
    (fiber seen : List (List TauState)) (P : List TauState → Prop)
    (hseen : ∀ x, x ∈ seen → P x)
    (hstep : ∀ current target,
      P current →
      target ∈ fiber →
      chainSingleKempeStep orients current target = true →
      P target) :
    ∀ x, x ∈ chainClosureStep orients fiber seen → P x := by
  induction fiber generalizing seen with
  | nil =>
      intro x hx
      simpa [chainClosureStep] using hseen x hx
  | cons candidate rest ih =>
      intro x hx
      unfold chainClosureStep at hx
      simp only [List.foldl_cons] at hx
      let nextSeen :=
        if (seen.any fun current =>
            chainSingleKempeStep orients current candidate) then
          addIfFresh seen candidate
        else
          seen
      have hnextSeen : ∀ w, w ∈ nextSeen → P w := by
        intro w hw
        by_cases hany :
            (seen.any fun current =>
              chainSingleKempeStep orients current candidate) = true
        · have hw' : w ∈ addIfFresh seen candidate := by
            simpa [nextSeen, hany] using hw
          rcases mem_addIfFresh_source_or_eq seen candidate w hw' with hwSeen | hwCandidate
          ·
              exact hseen w hwSeen
          ·
              subst hwCandidate
              rw [List.any_eq_true] at hany
              rcases hany with ⟨current, hcurrentSeen, hcurrentStep⟩
              exact hstep current w (hseen current hcurrentSeen)
                (by simp) hcurrentStep
        · have hfalse :
              (seen.any fun current =>
                chainSingleKempeStep orients current candidate) = false :=
            bool_false_of_not_true hany
          exact hseen w (by simpa [nextSeen, hfalse] using hw)
      exact ih nextSeen hnextSeen (by
        intro current target hcurrent htarget hsingle
        exact hstep current target hcurrent
          (List.mem_cons_of_mem candidate htarget) hsingle)
        x (by simpa [chainClosureStep, nextSeen] using hx)

theorem chainClosureStep_nodup (orients : List TauOrient)
    (fiber seen : List (List TauState)) (hseen : seen.Nodup) :
    (chainClosureStep orients fiber seen).Nodup := by
  unfold chainClosureStep
  induction fiber generalizing seen with
  | nil =>
      simpa using hseen
  | cons candidate rest ih =>
      simp only [List.foldl_cons]
      by_cases hc :
          (seen.any fun current => chainSingleKempeStep orients current candidate) = true
      · simp only [hc, if_true]
        exact ih (addIfFresh seen candidate) (addIfFresh_nodup seen candidate hseen)
      · have hfalse :
            (seen.any fun current => chainSingleKempeStep orients current candidate) =
              false :=
          bool_false_of_not_true hc
        simp only [hfalse, Bool.false_eq_true, if_false]
        exact ih seen hseen

theorem chainClosureStep_cons_mem_of_seen_step (orients : List TauOrient)
    (target : List TauState) (rest seen : List (List TauState))
    (current : List TauState) (hcurrent : current ∈ seen)
    (hstep : chainSingleKempeStep orients current target = true) :
    target ∈ chainClosureStep orients (target :: rest) seen := by
  unfold chainClosureStep
  simp only [List.foldl_cons]
  have hany : (seen.any fun cur => chainSingleKempeStep orients cur target) = true :=
    list_any_true_of_mem hcurrent hstep
  apply chainClosureStep_mem_of_seen
  simp only [hany, if_true]
  exact mem_addIfFresh_self seen target

theorem chainClosureStep_mem_of_seen_step (orients : List TauOrient)
    (fiber seen : List (List TauState)) (current target : List TauState)
    (htarget : target ∈ fiber) (hcurrent : current ∈ seen)
    (hstep : chainSingleKempeStep orients current target = true) :
    target ∈ chainClosureStep orients fiber seen := by
  unfold chainClosureStep
  induction fiber generalizing seen current with
  | nil =>
      cases htarget
  | cons candidate rest ih =>
      simp only [List.foldl_cons]
      let newSeen : List (List TauState) :=
        if (seen.any fun cur => chainSingleKempeStep orients cur candidate) = true then
          addIfFresh seen candidate
        else seen
      change target ∈ List.foldl
        (fun acc cand =>
          if (acc.any fun cur => chainSingleKempeStep orients cur cand) = true then
            addIfFresh acc cand
          else acc)
        newSeen rest
      by_cases heq : candidate = target
      · have hany :
            (seen.any fun cur => chainSingleKempeStep orients cur candidate) = true := by
          rw [heq]
          exact list_any_true_of_mem hcurrent hstep
        have hnew : target ∈ newSeen := by
          simp only [newSeen, hany, if_true]
          rw [heq]
          exact mem_addIfFresh_self seen target
        change target ∈ chainClosureStep orients rest newSeen
        exact chainClosureStep_mem_of_seen orients rest newSeen target hnew
      · have htail : target ∈ rest := by
          cases htarget with
          | head hhead => contradiction
          | tail _ htail => exact htail
        have hcurrent' : current ∈ newSeen := by
          by_cases hc :
              (seen.any fun cur => chainSingleKempeStep orients cur candidate) = true
          · simp only [newSeen, hc, if_true]
            exact mem_addIfFresh_of_mem hcurrent
          · have hfalse :
                (seen.any fun cur => chainSingleKempeStep orients cur candidate) =
                  false :=
              bool_false_of_not_true hc
            simp only [newSeen, hfalse, Bool.false_eq_true, if_false]
            exact hcurrent
        change target ∈ chainClosureStep orients rest newSeen
        exact ih newSeen current htail hcurrent' hstep

theorem chainClosureStep_mem_seen_or_fiber (orients : List TauOrient)
    (fiber seen : List (List TauState)) (x : List TauState)
    (h : x ∈ chainClosureStep orients fiber seen) :
    x ∈ seen ∨ x ∈ fiber := by
  unfold chainClosureStep at h
  induction fiber generalizing seen with
  | nil =>
      simp at h
      exact Or.inl h
  | cons candidate rest ih =>
      simp only [List.foldl_cons] at h
      by_cases hc :
          (seen.any fun current => chainSingleKempeStep orients current candidate) = true
      · simp only [hc, if_true] at h
        rcases ih (addIfFresh seen candidate) h with hnew | hrest
        · rcases mem_addIfFresh_source_or_eq seen candidate x hnew with hseen | rfl
          · exact Or.inl hseen
          · exact Or.inr (by simp)
        · exact Or.inr (by simp [hrest])
      · have hfalse :
            (seen.any fun current => chainSingleKempeStep orients current candidate) =
              false :=
          bool_false_of_not_true hc
        simp only [hfalse, Bool.false_eq_true, if_false] at h
        rcases ih seen h with hseen | hrest
        · exact Or.inl hseen
        · exact Or.inr (by simp [hrest])

theorem chainClosureStep_not_mem_of_not_mem_seen_not_mem_fiber
    (orients : List TauOrient) (fiber seen : List (List TauState)) (x : List TauState)
    (hseen : x ∉ seen) (hfiber : x ∉ fiber) :
    x ∉ chainClosureStep orients fiber seen := by
  intro hx
  rcases chainClosureStep_mem_seen_or_fiber orients fiber seen x hx with hxseen | hxfiber
  · exact hseen hxseen
  · exact hfiber hxfiber

theorem chainClosureStep_cons_not_mem_target_of_no_step
    (orients : List TauOrient) (target : List TauState)
    (rest seen : List (List TauState))
    (hany : (seen.any fun cur => chainSingleKempeStep orients cur target) = false)
    (hseen : target ∉ seen) (hrest : target ∉ rest) :
    target ∉ chainClosureStep orients (target :: rest) seen := by
  unfold chainClosureStep
  simp only [List.foldl_cons, hany, Bool.false_eq_true, if_false]
  exact chainClosureStep_not_mem_of_not_mem_seen_not_mem_fiber
    orients rest seen target hseen hrest

theorem chainClosureStep_mem_seen_of_stop (orients : List TauOrient)
    (fiber seen : List (List TauState)) (x : List TauState)
    (hseen : seen.Nodup)
    (hstop : ((chainClosureStep orients fiber seen).length == seen.length) = true)
    (hx : x ∈ chainClosureStep orients fiber seen) :
    x ∈ seen := by
  have hlen : (chainClosureStep orients fiber seen).length = seen.length := by
    simpa using hstop
  have hsub : seen ⊆ chainClosureStep orients fiber seen := by
    intro y hy
    exact chainClosureStep_mem_of_seen orients fiber seen y hy
  have hsp : List.Subperm seen (chainClosureStep orients fiber seen) :=
    List.subperm_of_subset hseen hsub
  have hperm : List.Perm seen (chainClosureStep orients fiber seen) :=
    List.Subperm.perm_of_length_le hsp (by simp [hlen])
  exact (List.Perm.mem_iff hperm).mpr hx

theorem closeChainFiber_mem_of_seen (orients : List TauOrient)
    (fiber : List (List TauState)) (n : Nat) (seen : List (List TauState))
    (x : List TauState) (h : x ∈ seen) :
    x ∈ closeChainFiber orients fiber n seen := by
  induction n generalizing seen with
  | zero =>
      simpa [closeChainFiber] using h
  | succ n ih =>
      simp only [closeChainFiber]
      let seen' := chainClosureStep orients fiber seen
      have hx' : x ∈ seen' := chainClosureStep_mem_of_seen orients fiber seen x h
      by_cases hstop : ((seen'.length == seen.length) = true)
      · simp only [seen', hstop, if_true]
        exact hx'
      · have hfalse : (seen'.length == seen.length) = false :=
          bool_false_of_not_true hstop
        simp only [seen', hfalse, Bool.false_eq_true, if_false]
        exact ih seen' hx'

theorem closeChainFiber_lift_property (orients : List TauOrient)
    (fiber : List (List TauState)) (n : Nat) (seen : List (List TauState))
    (P : List TauState → Prop)
    (hseen : ∀ x, x ∈ seen → P x)
    (hstep : ∀ current target,
      P current →
      target ∈ fiber →
      chainSingleKempeStep orients current target = true →
      P target) :
    ∀ x, x ∈ closeChainFiber orients fiber n seen → P x := by
  induction n generalizing seen with
  | zero =>
      intro x hx
      simpa [closeChainFiber] using hseen x hx
  | succ n ih =>
      intro x hx
      simp only [closeChainFiber] at hx
      let seen' := chainClosureStep orients fiber seen
      have hseen' : ∀ y, y ∈ seen' → P y :=
        chainClosureStep_lift_property orients fiber seen P hseen hstep
      by_cases hstop : (seen'.length == seen.length) = true
      · simp only [seen', hstop, if_true] at hx
        exact hseen' x hx
      · have hfalse : (seen'.length == seen.length) = false :=
          bool_false_of_not_true hstop
        simp only [seen', hfalse, Bool.false_eq_true, if_false] at hx
        exact ih seen' hseen' x hx

theorem closeChainFiber_mem_of_seen_step (orients : List TauOrient)
    (fiber : List (List TauState)) (n : Nat) (seen : List (List TauState))
    (current target : List TauState)
    (htarget : target ∈ fiber) (hcurrent : current ∈ seen)
    (hstep : chainSingleKempeStep orients current target = true) :
    target ∈ closeChainFiber orients fiber (n + 1) seen := by
  simp only [closeChainFiber]
  let seen' := chainClosureStep orients fiber seen
  have ht' : target ∈ seen' :=
    chainClosureStep_mem_of_seen_step orients fiber seen current target htarget hcurrent hstep
  by_cases hstop : ((seen'.length == seen.length) = true)
  · simp only [seen', hstop, if_true]
    exact ht'
  · have hfalse : (seen'.length == seen.length) = false :=
      bool_false_of_not_true hstop
    simp only [seen', hfalse, Bool.false_eq_true, if_false]
    exact closeChainFiber_mem_of_seen orients fiber n seen' target ht'

theorem closeChainFiber_mem_of_closureStep (orients : List TauOrient)
    (fiber : List (List TauState)) (n : Nat) (seen : List (List TauState))
    (x : List TauState) (h : x ∈ chainClosureStep orients fiber seen) :
    x ∈ closeChainFiber orients fiber (n + 1) seen := by
  simp only [closeChainFiber]
  let seen' := chainClosureStep orients fiber seen
  have hx' : x ∈ seen' := h
  by_cases hstop : ((seen'.length == seen.length) = true)
  · simp only [seen', hstop, if_true]
    exact hx'
  · have hfalse : (seen'.length == seen.length) = false :=
      bool_false_of_not_true hstop
    simp only [seen', hfalse, Bool.false_eq_true, if_false]
    exact closeChainFiber_mem_of_seen orients fiber n seen' x hx'

theorem closeChainFiber_mem_of_second_closureStep (orients : List TauOrient)
    (fiber : List (List TauState)) (n : Nat) (seen : List (List TauState))
    (x : List TauState)
    (hgrow :
      ((chainClosureStep orients fiber seen).length == seen.length) = false)
    (h : x ∈ chainClosureStep orients fiber
      (chainClosureStep orients fiber seen)) :
    x ∈ closeChainFiber orients fiber (n + 2) seen := by
  simp only [closeChainFiber]
  let seen' := chainClosureStep orients fiber seen
  have hfalse : (seen'.length == seen.length) = false := by
    simpa [seen'] using hgrow
  simp only [seen', hfalse, Bool.false_eq_true, if_false]
  exact closeChainFiber_mem_of_closureStep orients fiber n seen' x h

theorem closeChainFiber_mem_of_third_closureStep (orients : List TauOrient)
    (fiber : List (List TauState)) (n : Nat) (seen : List (List TauState))
    (x : List TauState)
    (hgrow₁ :
      ((chainClosureStep orients fiber seen).length == seen.length) = false)
    (hgrow₂ :
      ((chainClosureStep orients fiber
          (chainClosureStep orients fiber seen)).length ==
        (chainClosureStep orients fiber seen).length) = false)
    (h : x ∈ chainClosureStep orients fiber
      (chainClosureStep orients fiber
        (chainClosureStep orients fiber seen))) :
    x ∈ closeChainFiber orients fiber (n + 3) seen := by
  simp only [closeChainFiber]
  let seen' := chainClosureStep orients fiber seen
  have hfalse : (seen'.length == seen.length) = false := by
    simpa [seen'] using hgrow₁
  simp only [seen', hfalse, Bool.false_eq_true, if_false]
  exact closeChainFiber_mem_of_second_closureStep orients fiber n seen' x (by
    simpa [seen'] using hgrow₂) (by
    simpa [seen'] using h)

theorem closeChainFiber_mem_mono_succ (orients : List TauOrient)
    (fiber : List (List TauState)) (n : Nat) (seen : List (List TauState))
    (x : List TauState)
    (h : x ∈ closeChainFiber orients fiber n seen) :
    x ∈ closeChainFiber orients fiber (n + 1) seen := by
  induction n generalizing seen with
  | zero =>
      exact closeChainFiber_mem_of_seen orients fiber 1 seen x h
  | succ n ih =>
      simp only [closeChainFiber] at h ⊢
      let seen' := chainClosureStep orients fiber seen
      by_cases hstop : ((seen'.length == seen.length) = true)
      · simp only [seen', hstop, if_true] at h ⊢
        exact h
      · have hfalse : (seen'.length == seen.length) = false :=
          bool_false_of_not_true hstop
        simp only [seen', hfalse, Bool.false_eq_true, if_false] at h ⊢
        exact ih seen' h

theorem closeChainFiber_mem_step_of_close (orients : List TauOrient)
    (fiber : List (List TauState)) (n : Nat) (seen : List (List TauState))
    (current target : List TauState)
    (hseen : seen.Nodup)
    (hcurrent : current ∈ closeChainFiber orients fiber n seen)
    (htarget : target ∈ fiber)
    (hstep : chainSingleKempeStep orients current target = true) :
    target ∈ closeChainFiber orients fiber (n + 1) seen := by
  induction n generalizing seen with
  | zero =>
      exact closeChainFiber_mem_of_seen_step orients fiber 0 seen current target
        htarget hcurrent hstep
  | succ n ih =>
      simp only [closeChainFiber] at hcurrent ⊢
      let seen' := chainClosureStep orients fiber seen
      by_cases hstop : ((seen'.length == seen.length) = true)
      · simp only [seen', hstop, if_true] at hcurrent ⊢
        have hcurrentSeen : current ∈ seen := by
          exact chainClosureStep_mem_seen_of_stop orients fiber seen current
            hseen (by simpa [seen'] using hstop) (by simpa [seen'] using hcurrent)
        exact chainClosureStep_mem_of_seen_step orients fiber seen current target
          htarget hcurrentSeen hstep
      · have hfalse : (seen'.length == seen.length) = false := bool_false_of_not_true hstop
        simp only [seen', hfalse, Bool.false_eq_true, if_false] at hcurrent ⊢
        exact ih seen' (chainClosureStep_nodup orients fiber seen hseen) hcurrent

def closeChainFiberBoundedSaturationClosed : Prop :=
  ∀ (orients : List TauOrient) (fiber seen : List (List TauState)),
    seen.Nodup →
      ∀ (target : List TauState),
        target ∈ closeChainFiber orients fiber (fiber.length + 1) seen →
          target ∈ closeChainFiber orients fiber fiber.length seen

theorem closeChainFiber_mem_step_of_close_at_length_of_bounded_saturation
    (hSat : closeChainFiberBoundedSaturationClosed)
    (orients : List TauOrient) (fiber seen : List (List TauState))
    (current target : List TauState)
    (hseen : seen.Nodup)
    (hcurrent : current ∈ closeChainFiber orients fiber fiber.length seen)
    (htarget : target ∈ fiber)
    (hstep : chainSingleKempeStep orients current target = true) :
    target ∈ closeChainFiber orients fiber fiber.length seen := by
  exact hSat orients fiber seen hseen target
    (closeChainFiber_mem_step_of_close orients fiber fiber.length seen
      current target hseen hcurrent htarget hstep)

theorem closeChainFiber_mem_mono_add (orients : List TauOrient)
    (fiber : List (List TauState)) (n m : Nat) (seen : List (List TauState))
    (x : List TauState)
    (h : x ∈ closeChainFiber orients fiber n seen) :
    x ∈ closeChainFiber orients fiber (n + m) seen := by
  induction m with
  | zero =>
      simpa using h
  | succ m ih =>
      change x ∈ closeChainFiber orients fiber ((n + m) + 1) seen
      exact closeChainFiber_mem_mono_succ orients fiber (n + m) seen x ih

theorem chainFiberConnected_of_forall_mem_close (orients : List TauOrient)
    (fiber : List (List TauState))
    (h : ∀ state, state ∈ fiber →
      match fiber with
      | [] => True
      | root :: _ =>
          state ∈ closeChainFiber orients fiber fiber.length [root]) :
    chainFiberConnected orients fiber = true := by
  cases fiber with
  | nil =>
      rfl
  | cons root rest =>
      unfold chainFiberConnected
      rw [List.all_eq_true]
      intro state hmem
      exact List.contains_iff_mem.mpr (h state hmem)

theorem chainSpecifiedKempeStep_implies_single
    (orients : List TauOrient) (s t : List TauState) (move : ChainMove)
    (hpair : colorPairs.contains (move.a, move.c) = true)
    (hseed : (chainEdges orients).contains move.seed = true)
    (hstep : chainSpecifiedKempeStep orients s t move = true) :
    chainSingleKempeStep orients s t = true := by
  unfold chainSingleKempeStep
  rw [List.any_eq_true]
  refine ⟨(move.a, move.c), List.contains_iff_mem.mp hpair, ?_⟩
  rw [List.any_eq_true]
  refine ⟨move.seed, List.contains_iff_mem.mp hseed, ?_⟩
  simpa [chainSpecifiedKempeStep] using hstep

def chainLKRInAudit (orients : List TauOrient) : Bool :=
  let statesList := allChainStates orients
  statesList.all (compatibleChainStates orients) &&
    colorAssignments4.all fun key =>
      chainFiberConnected orients (chainFiberFrom orients statesList key)

def chainParentAt (parents : List Nat) (i : Nat) : Nat :=
  listGetD parents i i

def chainMoveAt (moves : List ChainMove) (i : Nat) : ChainMove :=
  listGetD moves i default

def chainParentIter (parents : List Nat) : Nat → Nat → Nat
  | 0, i => i
  | n + 1, i => chainParentIter parents n (chainParentAt parents i)

def firstChainIndexWithInputAux (orients : List TauOrient) (key : List LColor) :
    List (List TauState) → Nat → Nat
  | [], _ => 0
  | states :: rest, i =>
      if chainInputKey orients states == key then
        i
      else
        firstChainIndexWithInputAux orients key rest (i + 1)

def chainRepresentativeIndex (orients : List TauOrient) (statesList : List (List TauState))
    (states : List TauState) : Nat :=
  firstChainIndexWithInputAux orients (chainInputKey orients states) statesList 0

def chainParentRowValid (orients : List TauOrient) (statesList : List (List TauState))
    (parents : List Nat) (moves : List ChainMove) (i : Nat) : Bool :=
  i < statesList.length &&
    let parent := chainParentAt parents i
    parent < statesList.length &&
      let s := listGetD statesList i []
      let t := listGetD statesList parent []
      chainInputKey orients s == chainInputKey orients t &&
        (i == parent || chainSpecifiedKempeStep orients s t (chainMoveAt moves i))

def chainParentCertificateAudit (orients : List TauOrient) (maxDepth : Nat)
    (parents : List Nat) (moves : List ChainMove) : Bool :=
  let statesList := allChainStates orients
  statesList.all (compatibleChainStates orients) &&
    parents.length == statesList.length &&
    moves.length == statesList.length &&
    (List.range statesList.length).all (chainParentRowValid orients statesList parents moves) &&
    (List.range statesList.length).all fun i =>
      let states := listGetD statesList i []
      chainParentIter parents maxDepth i ==
        chainRepresentativeIndex orients statesList states

/-
Per-fixed-input certificates are the intended replacement for the too-heavy
global `chainParentCertificateAudit`: a generator can emit one tiny parent tree
per input fiber instead of asking Lean to reduce one large closure proof.
-/

structure ChainFiberParentRow where
  source : Nat
  parent : Nat
  move : ChainMove
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr, Inhabited

structure ChainFiberCertificate where
  key : List LColor
  root : Nat
  maxDepth : Nat
  rows : List ChainFiberParentRow
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr, Inhabited

def chainFiberIndicesFrom (orients : List TauOrient)
    (statesList : List (List TauState)) (key : List LColor) : List Nat :=
  (List.range statesList.length).filter fun i =>
    chainInputKey orients (listGetD statesList i []) == key

def chainFiberRootIndex (indices : List Nat) : Nat :=
  listGetD indices 0 0

def chainFiberParentFromRows : List ChainFiberParentRow → Nat → Nat
  | [], i => i
  | row :: rows, i =>
      if row.source == i then row.parent else chainFiberParentFromRows rows i

def chainFiberParentIter (rows : List ChainFiberParentRow) : Nat → Nat → Nat
  | 0, i => i
  | n + 1, i => chainFiberParentIter rows n (chainFiberParentFromRows rows i)

def chainFiberParentRowValidFrom (orients : List TauOrient)
    (statesList : List (List TauState)) (indices : List Nat)
    (row : ChainFiberParentRow) : Bool :=
  indices.contains row.source &&
    indices.contains row.parent &&
      let s := listGetD statesList row.source []
      let t := listGetD statesList row.parent []
      chainInputKey orients s == chainInputKey orients t &&
        (row.source == row.parent || chainSpecifiedKempeStep orients s t row.move)

def chainFiberParentCertificateAuditFrom (orients : List TauOrient)
    (statesList : List (List TauState)) (cert : ChainFiberCertificate) : Bool :=
  let indices := chainFiberIndicesFrom orients statesList cert.key
  cert.key.length == 4 &&
    cert.root == chainFiberRootIndex indices &&
    (cert.rows.map fun row => row.source) == indices &&
    cert.rows.all (chainFiberParentRowValidFrom orients statesList indices) &&
    cert.rows.all fun row =>
      chainFiberParentIter cert.rows cert.maxDepth row.source == cert.root

def chainFiberParentCertificateAudit (orients : List TauOrient)
    (cert : ChainFiberCertificate) : Bool :=
  chainFiberParentCertificateAuditFrom orients (allChainStates orients) cert

def chainAllFiberParentCertificateAudit (orients : List TauOrient)
    (certs : List ChainFiberCertificate) : Bool :=
  let statesList := allChainStates orients
  statesList.all (compatibleChainStates orients) &&
    (certs.map fun cert => cert.key) == colorAssignments4 &&
    certs.all (chainFiberParentCertificateAuditFrom orients statesList)

def chainMove (a c : LColor) (occ : Nat) (seed : TauEdge) : ChainMove :=
  { a := a, c := c, seed := { occ := occ, edge := seed } }

def chainFiberRow (source parent : Nat) (move : ChainMove) : ChainFiberParentRow :=
  { source := source, parent := parent, move := move }

/--
Small semantic smoke certificate for the first fixed-input fiber of a single
normal `τ` chain.  The non-root rows check real input-disjoint Kempe moves in
the chain model, and row `3` intentionally uses a two-step parent path through
row `1`.
-/
def tauSingleNormalFiber0Certificate : ChainFiberCertificate :=
  { key := chainInputKey [TauOrient.normal] [stateAt 0]
    root := 0
    maxDepth := 2
    rows :=
      [ chainFiberRow 0 0 default
      , chainFiberRow 1 0 (chainMove LColor.b LColor.p 0 TauEdge.B5)
      , chainFiberRow 2 0 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
      , chainFiberRow 3 1 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
      , chainFiberRow 48 0 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
      , chainFiberRow 49 1 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
      , chainFiberRow 50 2 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
      , chainFiberRow 51 48 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
      ] }

theorem tauSingleNormalFiber0Certificate_ok :
    chainFiberParentCertificateAudit [TauOrient.normal]
      tauSingleNormalFiber0Certificate = true := by
  decide

def indexedStepToChainMove0 (st : IndexedPathStep) : ChainMove :=
  chainMove st.move.a st.move.c 0 st.move.seed

def tauSingleNormalParentRowFromIndex (i : Nat) : ChainFiberParentRow :=
  let r := rowAt i
  match r.steps with
  | [] => chainFiberRow i i default
  | st :: _ => chainFiberRow i st.target (indexedStepToChainMove0 st)

def tauSingleNormalFiberCertificateForKey (key : List LColor) :
    ChainFiberCertificate :=
  let statesList := allChainStates [TauOrient.normal]
  let indices := chainFiberIndicesFrom [TauOrient.normal] statesList key
  { key := key
    root := chainFiberRootIndex indices
    maxDepth := 2
    rows := indices.map tauSingleNormalParentRowFromIndex }

def tauSingleNormalFiberCertificateAt (i : Nat) : ChainFiberCertificate :=
  tauSingleNormalFiberCertificateForKey (listGetD colorAssignments4 i [])

def tauSingleNormalAllFiberCertificates : List ChainFiberCertificate :=
  colorAssignments4.map tauSingleNormalFiberCertificateForKey

def tauSingleNormalFiberCertificateChunkAudit (start len : Nat) : Bool :=
  (List.range len).all fun k =>
    chainFiberParentCertificateAudit [TauOrient.normal]
      (tauSingleNormalFiberCertificateAt (start + k))

def tauSingleNormalAllFiberCertificateKeysCheck : Bool :=
  (tauSingleNormalAllFiberCertificates.map fun cert => cert.key) == colorAssignments4

def tauSingleNormalChainStatesCompatibleCheck : Bool :=
  (allChainStates [TauOrient.normal]).all (compatibleChainStates [TauOrient.normal])

theorem tauSingleNormalAllFiberCertificateKeysCheck_ok :
    tauSingleNormalAllFiberCertificateKeysCheck = true := by
  decide

theorem tauSingleNormalChainStatesCompatibleCheck_ok :
    tauSingleNormalChainStatesCompatibleCheck = true := by
  decide

theorem tauSingleNormalFiberCertificateChunk_0_9_ok :
    tauSingleNormalFiberCertificateChunkAudit 0 9 = true := by
  decide

theorem tauSingleNormalFiberCertificateChunk_9_9_ok :
    tauSingleNormalFiberCertificateChunkAudit 9 9 = true := by
  decide

theorem tauSingleNormalFiberCertificateChunk_18_9_ok :
    tauSingleNormalFiberCertificateChunkAudit 18 9 = true := by
  decide

theorem tauSingleNormalFiberCertificateChunk_27_9_ok :
    tauSingleNormalFiberCertificateChunkAudit 27 9 = true := by
  decide

theorem tauSingleNormalFiberCertificateChunk_36_9_ok :
    tauSingleNormalFiberCertificateChunkAudit 36 9 = true := by
  decide

theorem tauSingleNormalFiberCertificateChunk_45_9_ok :
    tauSingleNormalFiberCertificateChunkAudit 45 9 = true := by
  decide

theorem tauSingleNormalFiberCertificateChunk_54_9_ok :
    tauSingleNormalFiberCertificateChunkAudit 54 9 = true := by
  decide

theorem tauSingleNormalFiberCertificateChunk_63_9_ok :
    tauSingleNormalFiberCertificateChunkAudit 63 9 = true := by
  decide

theorem tauSingleNormalFiberCertificateChunk_72_9_ok :
    tauSingleNormalFiberCertificateChunkAudit 72 9 = true := by
  decide

def tauSingleNormalAllFiberCertificateAudit : Bool :=
  tauSingleNormalChainStatesCompatibleCheck &&
    tauSingleNormalAllFiberCertificateKeysCheck &&
    tauSingleNormalFiberCertificateChunkAudit 0 9 &&
    tauSingleNormalFiberCertificateChunkAudit 9 9 &&
    tauSingleNormalFiberCertificateChunkAudit 18 9 &&
    tauSingleNormalFiberCertificateChunkAudit 27 9 &&
    tauSingleNormalFiberCertificateChunkAudit 36 9 &&
    tauSingleNormalFiberCertificateChunkAudit 45 9 &&
    tauSingleNormalFiberCertificateChunkAudit 54 9 &&
    tauSingleNormalFiberCertificateChunkAudit 63 9 &&
    tauSingleNormalFiberCertificateChunkAudit 72 9

/--
All 81 fixed-input assignments for a single normal `τ` have checked per-fiber
parent certificates in the chain model.  Empty fibers are included as empty
certificates; the 36 nonempty fibers are generated from the Lemma 8.14 path
rows and checked in nine small chunks.
-/
theorem tauSingleNormalAllFiberCertificateAudit_ok :
    tauSingleNormalAllFiberCertificateAudit = true := by
  simp [tauSingleNormalAllFiberCertificateAudit,
    tauSingleNormalChainStatesCompatibleCheck_ok,
    tauSingleNormalAllFiberCertificateKeysCheck_ok,
    tauSingleNormalFiberCertificateChunk_0_9_ok,
    tauSingleNormalFiberCertificateChunk_9_9_ok,
    tauSingleNormalFiberCertificateChunk_18_9_ok,
    tauSingleNormalFiberCertificateChunk_27_9_ok,
    tauSingleNormalFiberCertificateChunk_36_9_ok,
    tauSingleNormalFiberCertificateChunk_45_9_ok,
    tauSingleNormalFiberCertificateChunk_54_9_ok,
    tauSingleNormalFiberCertificateChunk_63_9_ok,
    tauSingleNormalFiberCertificateChunk_72_9_ok]

def tauSingleFiberCertificateForKey (orient : TauOrient) (key : List LColor) :
    ChainFiberCertificate :=
  let statesList := allChainStates [orient]
  let indices := chainFiberIndicesFrom [orient] statesList key
  { key := key
    root := chainFiberRootIndex indices
    maxDepth := 2
    rows := indices.map tauSingleNormalParentRowFromIndex }

def tauSingleFiberCertificateAt (orient : TauOrient) (i : Nat) :
    ChainFiberCertificate :=
  tauSingleFiberCertificateForKey orient (listGetD colorAssignments4 i [])

def tauSingleAllFiberCertificates (orient : TauOrient) : List ChainFiberCertificate :=
  colorAssignments4.map (tauSingleFiberCertificateForKey orient)

def tauSingleFiberCertificateChunkAudit (orient : TauOrient) (start len : Nat) : Bool :=
  (List.range len).all fun k =>
    chainFiberParentCertificateAudit [orient]
      (tauSingleFiberCertificateAt orient (start + k))

def tauSingleAllFiberCertificateKeysCheck (orient : TauOrient) : Bool :=
  ((tauSingleAllFiberCertificates orient).map fun cert => cert.key) == colorAssignments4

def tauSingleChainStatesCompatibleCheck (orient : TauOrient) : Bool :=
  (allChainStates [orient]).all (compatibleChainStates [orient])

def tauSingleAllFiberCertificateAudit (orient : TauOrient) : Bool :=
  tauSingleChainStatesCompatibleCheck orient &&
    tauSingleAllFiberCertificateKeysCheck orient &&
    tauSingleFiberCertificateChunkAudit orient 0 9 &&
    tauSingleFiberCertificateChunkAudit orient 9 9 &&
    tauSingleFiberCertificateChunkAudit orient 18 9 &&
    tauSingleFiberCertificateChunkAudit orient 27 9 &&
    tauSingleFiberCertificateChunkAudit orient 36 9 &&
    tauSingleFiberCertificateChunkAudit orient 45 9 &&
    tauSingleFiberCertificateChunkAudit orient 54 9 &&
    tauSingleFiberCertificateChunkAudit orient 63 9 &&
    tauSingleFiberCertificateChunkAudit orient 72 9

theorem tauSingleMirrorAllFiberCertificateKeysCheck_ok :
    tauSingleAllFiberCertificateKeysCheck TauOrient.mirror = true := by
  decide

theorem tauSingleMirrorChainStatesCompatibleCheck_ok :
    tauSingleChainStatesCompatibleCheck TauOrient.mirror = true := by
  decide

theorem tauSingleMirrorFiberCertificateChunk_0_9_ok :
    tauSingleFiberCertificateChunkAudit TauOrient.mirror 0 9 = true := by
  decide

theorem tauSingleMirrorFiberCertificateChunk_9_9_ok :
    tauSingleFiberCertificateChunkAudit TauOrient.mirror 9 9 = true := by
  decide

theorem tauSingleMirrorFiberCertificateChunk_18_9_ok :
    tauSingleFiberCertificateChunkAudit TauOrient.mirror 18 9 = true := by
  decide

theorem tauSingleMirrorFiberCertificateChunk_27_9_ok :
    tauSingleFiberCertificateChunkAudit TauOrient.mirror 27 9 = true := by
  decide

theorem tauSingleMirrorFiberCertificateChunk_36_9_ok :
    tauSingleFiberCertificateChunkAudit TauOrient.mirror 36 9 = true := by
  decide

theorem tauSingleMirrorFiberCertificateChunk_45_9_ok :
    tauSingleFiberCertificateChunkAudit TauOrient.mirror 45 9 = true := by
  decide

theorem tauSingleMirrorFiberCertificateChunk_54_9_ok :
    tauSingleFiberCertificateChunkAudit TauOrient.mirror 54 9 = true := by
  decide

theorem tauSingleMirrorFiberCertificateChunk_63_9_ok :
    tauSingleFiberCertificateChunkAudit TauOrient.mirror 63 9 = true := by
  decide

theorem tauSingleMirrorFiberCertificateChunk_72_9_ok :
    tauSingleFiberCertificateChunkAudit TauOrient.mirror 72 9 = true := by
  decide

/--
All 81 fixed-input assignments for a single mirror-`τ` chain have checked
per-fiber parent certificates in the chain model.  The certificate generator
uses the same local Lemma 8.14 parent rows; the mirror case changes only the
ordered outer input key.
-/
theorem tauSingleMirrorAllFiberCertificateAudit_ok :
    tauSingleAllFiberCertificateAudit TauOrient.mirror = true := by
  simp [tauSingleAllFiberCertificateAudit,
    tauSingleMirrorChainStatesCompatibleCheck_ok,
    tauSingleMirrorAllFiberCertificateKeysCheck_ok,
    tauSingleMirrorFiberCertificateChunk_0_9_ok,
    tauSingleMirrorFiberCertificateChunk_9_9_ok,
    tauSingleMirrorFiberCertificateChunk_18_9_ok,
    tauSingleMirrorFiberCertificateChunk_27_9_ok,
    tauSingleMirrorFiberCertificateChunk_36_9_ok,
    tauSingleMirrorFiberCertificateChunk_45_9_ok,
    tauSingleMirrorFiberCertificateChunk_54_9_ok,
    tauSingleMirrorFiberCertificateChunk_63_9_ok,
    tauSingleMirrorFiberCertificateChunk_72_9_ok]

def tauOrientWords2 : List (List TauOrient) :=
  [ [TauOrient.normal, TauOrient.normal]
  , [TauOrient.normal, TauOrient.mirror]
  , [TauOrient.mirror, TauOrient.normal]
  , [TauOrient.mirror, TauOrient.mirror]
  ]

def tauOrientWords3 : List (List TauOrient) :=
  bindList tauOrientWords2 fun word =>
    [word ++ [TauOrient.normal], word ++ [TauOrient.mirror]]

def lemma818_composite_lkr_gate1_finiteCheck : Bool :=
  (tauOrientWords2 ++ tauOrientWords3).all chainLKRInAudit

end GoertzelLemma814

end Mettapedia.GraphTheory.FourColor
