import Mettapedia.GraphTheory.FourColor.GoertzelLemma814

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: explicit component certificates

The generated direct parent/path certificates in the current chain model check
`chainSpecifiedKempeStep`, which computes the two-color component from scratch.
That is fine for the length-two base tables, but it is too large for the
remaining representative words.

This module introduces the smaller certificate shape intended for those
representatives: a row supplies the switched component explicitly.  The checker
then verifies that the supplied component is pair-colored, connected from the
seed, closed under adjacent pair-colored chain edges, disjoint from the fixed
input, and that switching it gives the claimed parent state.
-/

namespace GoertzelLemma818ComponentCertificate

open GoertzelLemma814

structure ChainComponentMoveCertificate where
  move : ChainMove
  component : List ChainEdge
  deriving DecidableEq, BEq, Repr, Inhabited

def chainEdge (occ : Nat) (edge : TauEdge) : ChainEdge :=
  { occ := occ, edge := edge }

def certifiedComponentNextLayer (orients : List TauOrient)
    (component seen : List ChainEdge) : List ChainEdge :=
  component.filter fun e =>
    !seen.contains e && seen.any (chainEdgesShareEndpoint orients e)

def closeCertifiedComponent (orients : List TauOrient)
    (component : List ChainEdge) : Nat → List ChainEdge → List ChainEdge
  | 0, seen => seen
  | n + 1, seen =>
      let layer := certifiedComponentNextLayer orients component seen
      closeCertifiedComponent orients component n (appendFresh seen layer)

def certifiedComponentConnectedFromSeed (orients : List TauOrient)
    (component : List ChainEdge) (seed : ChainEdge) : Bool :=
  let reached := closeCertifiedComponent orients component component.length [seed]
  component.all fun e => reached.contains e

def certifiedComponentPairColored (orients : List TauOrient)
    (states : List TauState) (a c : LColor)
    (component : List ChainEdge) : Bool :=
  component.all fun e =>
    (chainEdges orients).contains e && chainEdgeInPair states a c e

/--
Closure check for an explicit two-color component.

Every pair-colored chain edge adjacent to the supplied component must already
belong to the component.  Together with connectedness from the seed, this is a
finite certificate that the supplied list is exactly the seed component in the
two-color subgraph, without reducing `chainComponent`.
-/
def certifiedComponentClosed (orients : List TauOrient)
    (states : List TauState) (a c : LColor)
    (component : List ChainEdge) : Bool :=
  (chainEdges orients).all fun e =>
    !chainEdgeInPair states a c e ||
      !component.any (chainEdgesShareEndpoint orients e) ||
        component.contains e

def certifiedComponentMoveAudit (orients : List TauOrient)
    (states : List TauState)
    (cert : ChainComponentMoveCertificate) : Bool :=
  let move := cert.move
  !cert.component.isEmpty &&
    (chainEdges orients).contains move.seed &&
    cert.component.contains move.seed &&
    certifiedComponentPairColored orients states move.a move.c cert.component &&
    certifiedComponentConnectedFromSeed orients cert.component move.seed &&
    certifiedComponentClosed orients states move.a move.c cert.component &&
    chainComponentAvoidsInputs orients cert.component

def chainCertifiedKempeStep (orients : List TauOrient)
    (s t : List TauState) (cert : ChainComponentMoveCertificate) : Bool :=
  certifiedComponentMoveAudit orients s cert &&
    chainAgreesWithSwitch orients s t cert.component cert.move.a cert.move.c

structure ChainFiberCertifiedParentRow where
  source : Nat
  parent : Nat
  cert : ChainComponentMoveCertificate
  deriving DecidableEq, BEq, Repr, Inhabited

structure ChainFiberCertifiedCertificate where
  key : List LColor
  root : Nat
  maxDepth : Nat
  rows : List ChainFiberCertifiedParentRow
  deriving DecidableEq, BEq, Repr, Inhabited

def chainFiberCertifiedParentFromRows :
    List ChainFiberCertifiedParentRow → Nat → Nat
  | [], i => i
  | row :: rows, i =>
      if row.source == i then row.parent
      else chainFiberCertifiedParentFromRows rows i

def chainFiberCertifiedParentIter
    (rows : List ChainFiberCertifiedParentRow) : Nat → Nat → Nat
  | 0, i => i
  | n + 1, i =>
      chainFiberCertifiedParentIter rows n
        (chainFiberCertifiedParentFromRows rows i)

def chainFiberCertifiedParentRowValidFrom (orients : List TauOrient)
    (statesList : List (List TauState)) (indices : List Nat)
    (row : ChainFiberCertifiedParentRow) : Bool :=
  indices.contains row.source &&
    indices.contains row.parent &&
      let s := listGetD statesList row.source []
      let t := listGetD statesList row.parent []
      chainInputKey orients s == chainInputKey orients t &&
        (row.source == row.parent || chainCertifiedKempeStep orients s t row.cert)

def chainFiberCertifiedParentCertificateAuditFrom
    (orients : List TauOrient) (statesList : List (List TauState))
    (cert : ChainFiberCertifiedCertificate) : Bool :=
  let indices := chainFiberIndicesFrom orients statesList cert.key
  cert.key.length == 4 &&
    cert.root == chainFiberRootIndex indices &&
    (cert.rows.map fun row => row.source) == indices &&
    cert.rows.all
      (chainFiberCertifiedParentRowValidFrom orients statesList indices) &&
    cert.rows.all fun row =>
      chainFiberCertifiedParentIter cert.rows cert.maxDepth row.source ==
        cert.root

def chainFiberCertifiedParentCertificateAudit
    (orients : List TauOrient)
    (cert : ChainFiberCertifiedCertificate) : Bool :=
  chainFiberCertifiedParentCertificateAuditFrom orients
    (allChainStates orients) cert

def componentCert (move : ChainMove) (component : List ChainEdge) :
    ChainComponentMoveCertificate :=
  { move := move, component := component }

def certifiedFiberRow (source parent : Nat) (move : ChainMove)
    (component : List ChainEdge) : ChainFiberCertifiedParentRow :=
  { source := source
    parent := parent
    cert := componentCert move component }

/--
The first single-`tau` fixed-input fiber checked again through explicit
component certificates.  This is a smoke test for the representative-target
certificate shape: no row asks Lean to compute `chainComponent`.
-/
def tauSingleNormalFiber0ComponentCertificate :
    ChainFiberCertifiedCertificate :=
  { key := chainInputKey [TauOrient.normal] [stateAt 0]
    root := 0
    maxDepth := 2
    rows :=
      [ certifiedFiberRow 0 0 default []
      , certifiedFiberRow 1 0
          (chainMove LColor.b LColor.p 0 TauEdge.B5)
          [ chainEdge 0 TauEdge.B5
          , chainEdge 0 TauEdge.B6
          ]
      , certifiedFiberRow 2 0
          (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
          [ chainEdge 0 TauEdge.F4F5
          , chainEdge 0 TauEdge.B5
          , chainEdge 0 TauEdge.B7
          ]
      , certifiedFiberRow 3 1
          (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
          [ chainEdge 0 TauEdge.F4F5
          , chainEdge 0 TauEdge.B6
          , chainEdge 0 TauEdge.B7
          ]
      , certifiedFiberRow 48 0
          (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
          [ chainEdge 0 TauEdge.F2F3
          , chainEdge 0 TauEdge.F2F4
          , chainEdge 0 TauEdge.B4
          , chainEdge 0 TauEdge.B7
          ]
      , certifiedFiberRow 49 1
          (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
          [ chainEdge 0 TauEdge.F2F3
          , chainEdge 0 TauEdge.F2F4
          , chainEdge 0 TauEdge.B4
          , chainEdge 0 TauEdge.B7
          ]
      , certifiedFiberRow 50 2
          (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
          [ chainEdge 0 TauEdge.F2F3
          , chainEdge 0 TauEdge.F2F4
          , chainEdge 0 TauEdge.B4
          , chainEdge 0 TauEdge.F4F5
          , chainEdge 0 TauEdge.B6
          ]
      , certifiedFiberRow 51 48
          (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
          [ chainEdge 0 TauEdge.F4F5
          , chainEdge 0 TauEdge.B6
          , chainEdge 0 TauEdge.B7
          ]
      ] }

def tauSingleNormalFiber0ComponentStates : List (List TauState) :=
  allChainStates [TauOrient.normal]

def tauSingleNormalFiber0ComponentRows : List ChainFiberCertifiedParentRow :=
  tauSingleNormalFiber0ComponentCertificate.rows

theorem tauSingleNormalFiber0Component_row1_ok :
    chainCertifiedKempeStep [TauOrient.normal]
      (listGetD tauSingleNormalFiber0ComponentStates 1 [])
      (listGetD tauSingleNormalFiber0ComponentStates 0 [])
      (componentCert
        (chainMove LColor.b LColor.p 0 TauEdge.B5)
        [ chainEdge 0 TauEdge.B5
        , chainEdge 0 TauEdge.B6
        ]) = true := by
  decide

theorem tauSingleNormalFiber0Component_row2_ok :
    chainCertifiedKempeStep [TauOrient.normal]
      (listGetD tauSingleNormalFiber0ComponentStates 2 [])
      (listGetD tauSingleNormalFiber0ComponentStates 0 [])
      (componentCert
        (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
        [ chainEdge 0 TauEdge.F4F5
        , chainEdge 0 TauEdge.B5
        , chainEdge 0 TauEdge.B7
        ]) = true := by
  decide

theorem tauSingleNormalFiber0Component_row3_ok :
    chainCertifiedKempeStep [TauOrient.normal]
      (listGetD tauSingleNormalFiber0ComponentStates 3 [])
      (listGetD tauSingleNormalFiber0ComponentStates 1 [])
      (componentCert
        (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
        [ chainEdge 0 TauEdge.F4F5
        , chainEdge 0 TauEdge.B6
        , chainEdge 0 TauEdge.B7
        ]) = true := by
  decide

theorem tauSingleNormalFiber0Component_row48_ok :
    chainCertifiedKempeStep [TauOrient.normal]
      (listGetD tauSingleNormalFiber0ComponentStates 48 [])
      (listGetD tauSingleNormalFiber0ComponentStates 0 [])
      (componentCert
        (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
        [ chainEdge 0 TauEdge.F2F3
        , chainEdge 0 TauEdge.F2F4
        , chainEdge 0 TauEdge.B4
        , chainEdge 0 TauEdge.B7
        ]) = true := by
  decide

theorem tauSingleNormalFiber0Component_row49_ok :
    chainCertifiedKempeStep [TauOrient.normal]
      (listGetD tauSingleNormalFiber0ComponentStates 49 [])
      (listGetD tauSingleNormalFiber0ComponentStates 1 [])
      (componentCert
        (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
        [ chainEdge 0 TauEdge.F2F3
        , chainEdge 0 TauEdge.F2F4
        , chainEdge 0 TauEdge.B4
        , chainEdge 0 TauEdge.B7
        ]) = true := by
  decide

theorem tauSingleNormalFiber0Component_row50_ok :
    chainCertifiedKempeStep [TauOrient.normal]
      (listGetD tauSingleNormalFiber0ComponentStates 50 [])
      (listGetD tauSingleNormalFiber0ComponentStates 2 [])
      (componentCert
        (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
        [ chainEdge 0 TauEdge.F2F3
        , chainEdge 0 TauEdge.F2F4
        , chainEdge 0 TauEdge.B4
        , chainEdge 0 TauEdge.F4F5
        , chainEdge 0 TauEdge.B6
        ]) = true := by
  decide

theorem tauSingleNormalFiber0Component_row51_ok :
    chainCertifiedKempeStep [TauOrient.normal]
      (listGetD tauSingleNormalFiber0ComponentStates 51 [])
      (listGetD tauSingleNormalFiber0ComponentStates 48 [])
      (componentCert
        (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
        [ chainEdge 0 TauEdge.F4F5
        , chainEdge 0 TauEdge.B6
        , chainEdge 0 TauEdge.B7
        ]) = true := by
  decide

def tauSingleNormalFiber0ComponentParentCheck : Bool :=
  [0, 1, 2, 3, 48, 49, 50, 51].all fun i =>
    chainFiberCertifiedParentIter
      tauSingleNormalFiber0ComponentRows 2 i == 0

theorem tauSingleNormalFiber0ComponentParentCheck_ok :
    tauSingleNormalFiber0ComponentParentCheck = true := by
  decide

end GoertzelLemma818ComponentCertificate

end Mettapedia.GraphTheory.FourColor
