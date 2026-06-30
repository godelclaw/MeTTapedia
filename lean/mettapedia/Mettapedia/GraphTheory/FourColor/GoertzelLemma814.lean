import Mathlib.Data.List.Basic

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
  deriving DecidableEq, BEq, Repr, Inhabited

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
  deriving DecidableEq, BEq, Repr, Inhabited

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
  deriving DecidableEq, BEq, Repr, Inhabited

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
  deriving DecidableEq, BEq, Repr, Inhabited

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
  deriving DecidableEq, BEq, Repr, Inhabited

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
  deriving DecidableEq, BEq, Repr, Inhabited

structure IndexedPathStep where
  move : KempeMove
  target : Nat
  deriving DecidableEq, BEq, Repr, Inhabited

structure IndexedPathRow where
  representative : Nat
  steps : List IndexedPathStep
  deriving DecidableEq, BEq, Repr, Inhabited

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
  deriving DecidableEq, BEq, Repr, Inhabited

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

end GoertzelLemma814

end Mettapedia.GraphTheory.FourColor
