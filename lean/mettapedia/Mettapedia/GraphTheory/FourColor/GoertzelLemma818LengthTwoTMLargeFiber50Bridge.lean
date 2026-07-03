import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMLargeFiberBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated multi-pass direct closure bridge for `normal,mirror` size-64 fiber 50

This module proves direct connectedness for a generated size-64 fiber
whose parent order needs two closure scans. It is generated from
row-local reverse certificate chunks and keeps Lean on default limits.
-/

namespace GoertzelLemma818LengthTwoTMLargeFiberBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818TauMirrorCertificate
open GoertzelLemma818TauMirrorReverseAudit

def tmFiber50StateAt (i : Nat) : List TauState :=
  directStates (tmFiber50RowAt i).sourceLeft (tmFiber50RowAt i).sourceRight

def tmFiber50DirectStates : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]

def tmFiber50Prefix0 : List (List TauState) :=
  [tmFiber50StateAt 0]

def tmFiber50Prefix1 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1]

def tmFiber50Prefix2 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2]

def tmFiber50Prefix3 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3]

def tmFiber50Prefix4 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4]

def tmFiber50Prefix5 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5]

def tmFiber50Prefix6 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6]

def tmFiber50Prefix7 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7]

def tmFiber50Prefix8 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8]

def tmFiber50Prefix9 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9]

def tmFiber50Prefix10 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10]

def tmFiber50Prefix11 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11]

def tmFiber50Prefix12 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12]

def tmFiber50Prefix13 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13]

def tmFiber50Prefix14 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14]

def tmFiber50Prefix15 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15]

def tmFiber50Prefix16 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16]

def tmFiber50Prefix17 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17]

def tmFiber50Prefix18 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18]

def tmFiber50Prefix19 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19]

def tmFiber50Prefix20 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20]

def tmFiber50Prefix21 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21]

def tmFiber50Prefix22 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22]

def tmFiber50Prefix23 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23]

def tmFiber50Prefix24 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24]

def tmFiber50Prefix25 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25]

def tmFiber50Prefix26 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26]

def tmFiber50Prefix27 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27]

def tmFiber50Prefix28 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28]

def tmFiber50Prefix29 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29]

def tmFiber50Prefix30 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30]

def tmFiber50Prefix31 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31]

def tmFiber50Prefix32 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32]

def tmFiber50Prefix33 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33]

def tmFiber50Prefix34 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34]

def tmFiber50Prefix35 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35]

def tmFiber50Prefix36 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36]

def tmFiber50Prefix37 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37]

def tmFiber50Prefix38 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38]

def tmFiber50Prefix39 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39]

def tmFiber50Prefix40 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40]

def tmFiber50Prefix41 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41]

def tmFiber50Prefix42 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42]

def tmFiber50Prefix43 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43]

def tmFiber50Prefix44 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44]

def tmFiber50Prefix45 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45]

def tmFiber50Prefix46 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46]

def tmFiber50Prefix47 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47]

def tmFiber50Prefix48 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48]

def tmFiber50Prefix49 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49]

def tmFiber50Prefix50 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50]

def tmFiber50Prefix51 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51]

def tmFiber50Prefix52 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52]

def tmFiber50Prefix53 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53]

def tmFiber50Prefix54 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54]

def tmFiber50Prefix55 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55]

def tmFiber50Prefix56 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56]

def tmFiber50Prefix57 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57]

def tmFiber50Prefix58 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58]

def tmFiber50Prefix59 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59]

def tmFiber50Prefix60 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60]

def tmFiber50Prefix61 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61]

def tmFiber50Prefix62 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62]

def tmFiber50Prefix63 : List (List TauState) :=
  [tmFiber50StateAt 0, tmFiber50StateAt 1, tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]

theorem tmFiber50ReverseRow_1_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 1) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk0_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 0) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber50ReverseSingleStep1 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 0) (tmFiber50StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 0) (tmFiber50StateAt 1)
    (tmFiber50RowAt 1).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 1) (by decide) tmFiber50ReverseRow_1_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_2_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 2) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk1_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 2) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber50ReverseSingleStep2 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 0) (tmFiber50StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 0) (tmFiber50StateAt 2)
    (tmFiber50RowAt 2).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 2) (by decide) tmFiber50ReverseRow_2_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_3_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 3) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk1_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 2) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber50ReverseSingleStep3 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 1) (tmFiber50StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 1) (tmFiber50StateAt 3)
    (tmFiber50RowAt 3).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 3) (by decide) tmFiber50ReverseRow_3_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_4_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 4) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk2_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 4) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber50ReverseSingleStep4 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 2) (tmFiber50StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 2) (tmFiber50StateAt 4)
    (tmFiber50RowAt 4).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 4) (by decide) tmFiber50ReverseRow_4_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_5_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 5) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk2_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 4) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber50ReverseSingleStep5 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 7) (tmFiber50StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 7) (tmFiber50StateAt 5)
    (tmFiber50RowAt 5).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 5) (by decide) tmFiber50ReverseRow_5_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_6_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 6) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk3_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 6) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber50ReverseSingleStep6 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 1) (tmFiber50StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 1) (tmFiber50StateAt 6)
    (tmFiber50RowAt 6).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 6) (by decide) tmFiber50ReverseRow_6_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_7_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 7) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk3_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 6) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber50ReverseSingleStep7 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 0) (tmFiber50StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 0) (tmFiber50StateAt 7)
    (tmFiber50RowAt 7).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 7) (by decide) tmFiber50ReverseRow_7_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_8_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 8) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk4_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 8) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber50ReverseSingleStep8 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 0) (tmFiber50StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 0) (tmFiber50StateAt 8)
    (tmFiber50RowAt 8).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 8) (by decide) tmFiber50ReverseRow_8_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_9_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 9) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk4_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 8) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber50ReverseSingleStep9 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 1) (tmFiber50StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 1) (tmFiber50StateAt 9)
    (tmFiber50RowAt 9).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 9) (by decide) tmFiber50ReverseRow_9_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_10_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 10) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk5_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 10) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber50ReverseSingleStep10 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 2) (tmFiber50StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 2) (tmFiber50StateAt 10)
    (tmFiber50RowAt 10).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 10) (by decide) tmFiber50ReverseRow_10_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_11_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 11) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk5_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 10) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber50ReverseSingleStep11 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 3) (tmFiber50StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 3) (tmFiber50StateAt 11)
    (tmFiber50RowAt 11).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 11) (by decide) tmFiber50ReverseRow_11_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_12_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 12) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk6_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 12) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber50ReverseSingleStep12 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 4) (tmFiber50StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 4) (tmFiber50StateAt 12)
    (tmFiber50RowAt 12).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 12) (by decide) tmFiber50ReverseRow_12_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_13_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 13) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk6_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 12) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber50ReverseSingleStep13 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 5) (tmFiber50StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 5) (tmFiber50StateAt 13)
    (tmFiber50RowAt 13).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 13) (by decide) tmFiber50ReverseRow_13_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_14_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 14) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk7_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 14) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber50ReverseSingleStep14 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 6) (tmFiber50StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 6) (tmFiber50StateAt 14)
    (tmFiber50RowAt 14).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 14) (by decide) tmFiber50ReverseRow_14_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_15_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 15) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk7_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 14) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber50ReverseSingleStep15 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 7) (tmFiber50StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 7) (tmFiber50StateAt 15)
    (tmFiber50RowAt 15).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 15) (by decide) tmFiber50ReverseRow_15_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_16_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 16) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk8_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 16) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber50ReverseSingleStep16 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 8) (tmFiber50StateAt 16) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 8) (tmFiber50StateAt 16)
    (tmFiber50RowAt 16).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 16) (by decide) tmFiber50ReverseRow_16_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_17_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 17) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk8_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 16) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber50ReverseSingleStep17 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 9) (tmFiber50StateAt 17) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 9) (tmFiber50StateAt 17)
    (tmFiber50RowAt 17).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 17) (by decide) tmFiber50ReverseRow_17_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_18_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 18) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk9_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 18) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber50ReverseSingleStep18 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 10) (tmFiber50StateAt 18) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 10) (tmFiber50StateAt 18)
    (tmFiber50RowAt 18).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 18) (by decide) tmFiber50ReverseRow_18_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_19_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 19) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk9_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 18) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber50ReverseSingleStep19 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 11) (tmFiber50StateAt 19) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 11) (tmFiber50StateAt 19)
    (tmFiber50RowAt 19).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 19) (by decide) tmFiber50ReverseRow_19_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_20_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 20) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk10_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 20) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber50ReverseSingleStep20 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 12) (tmFiber50StateAt 20) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 12) (tmFiber50StateAt 20)
    (tmFiber50RowAt 20).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 20) (by decide) tmFiber50ReverseRow_20_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_21_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 21) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk10_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 20) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber50ReverseSingleStep21 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 13) (tmFiber50StateAt 21) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 13) (tmFiber50StateAt 21)
    (tmFiber50RowAt 21).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 21) (by decide) tmFiber50ReverseRow_21_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_22_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 22) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk11_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 22) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber50ReverseSingleStep22 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 14) (tmFiber50StateAt 22) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 14) (tmFiber50StateAt 22)
    (tmFiber50RowAt 22).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 22) (by decide) tmFiber50ReverseRow_22_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_23_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 23) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk11_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 22) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber50ReverseSingleStep23 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 15) (tmFiber50StateAt 23) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 15) (tmFiber50StateAt 23)
    (tmFiber50RowAt 23).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 23) (by decide) tmFiber50ReverseRow_23_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_24_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 24) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk12_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 24) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber50ReverseSingleStep24 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 0) (tmFiber50StateAt 24) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 0) (tmFiber50StateAt 24)
    (tmFiber50RowAt 24).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 24) (by decide) tmFiber50ReverseRow_24_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_25_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 25) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk12_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 24) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber50ReverseSingleStep25 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 1) (tmFiber50StateAt 25) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 1) (tmFiber50StateAt 25)
    (tmFiber50RowAt 25).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 25) (by decide) tmFiber50ReverseRow_25_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_26_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 26) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk13_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 26) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber50ReverseSingleStep26 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 2) (tmFiber50StateAt 26) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 2) (tmFiber50StateAt 26)
    (tmFiber50RowAt 26).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 26) (by decide) tmFiber50ReverseRow_26_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_27_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 27) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk13_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 26) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber50ReverseSingleStep27 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 3) (tmFiber50StateAt 27) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 3) (tmFiber50StateAt 27)
    (tmFiber50RowAt 27).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 27) (by decide) tmFiber50ReverseRow_27_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_28_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 28) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk14_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 28) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber50ReverseSingleStep28 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 4) (tmFiber50StateAt 28) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 4) (tmFiber50StateAt 28)
    (tmFiber50RowAt 28).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 28) (by decide) tmFiber50ReverseRow_28_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_29_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 29) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk14_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 28) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber50ReverseSingleStep29 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 5) (tmFiber50StateAt 29) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 5) (tmFiber50StateAt 29)
    (tmFiber50RowAt 29).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 29) (by decide) tmFiber50ReverseRow_29_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_30_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 30) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk15_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 30) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber50ReverseSingleStep30 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 6) (tmFiber50StateAt 30) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 6) (tmFiber50StateAt 30)
    (tmFiber50RowAt 30).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 30) (by decide) tmFiber50ReverseRow_30_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_31_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 31) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk15_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 30) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber50ReverseSingleStep31 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 7) (tmFiber50StateAt 31) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 7) (tmFiber50StateAt 31)
    (tmFiber50RowAt 31).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 31) (by decide) tmFiber50ReverseRow_31_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_32_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 32) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk16_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 32) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber50ReverseSingleStep32 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 0) (tmFiber50StateAt 32) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 0) (tmFiber50StateAt 32)
    (tmFiber50RowAt 32).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 32) (by decide) tmFiber50ReverseRow_32_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_33_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 33) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk16_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 32) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber50ReverseSingleStep33 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 1) (tmFiber50StateAt 33) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 1) (tmFiber50StateAt 33)
    (tmFiber50RowAt 33).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 33) (by decide) tmFiber50ReverseRow_33_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_34_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 34) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk17_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 34) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber50ReverseSingleStep34 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 2) (tmFiber50StateAt 34) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 2) (tmFiber50StateAt 34)
    (tmFiber50RowAt 34).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 34) (by decide) tmFiber50ReverseRow_34_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_35_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 35) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk17_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 34) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber50ReverseSingleStep35 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 3) (tmFiber50StateAt 35) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 3) (tmFiber50StateAt 35)
    (tmFiber50RowAt 35).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 35) (by decide) tmFiber50ReverseRow_35_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_36_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 36) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk18_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 36) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber50ReverseSingleStep36 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 32) (tmFiber50StateAt 36) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 32) (tmFiber50StateAt 36)
    (tmFiber50RowAt 36).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 36) (by decide) tmFiber50ReverseRow_36_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_37_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 37) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk18_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 36) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber50ReverseSingleStep37 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 33) (tmFiber50StateAt 37) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 33) (tmFiber50StateAt 37)
    (tmFiber50RowAt 37).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 37) (by decide) tmFiber50ReverseRow_37_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_38_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 38) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk19_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 38) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber50ReverseSingleStep38 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 6) (tmFiber50StateAt 38) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 6) (tmFiber50StateAt 38)
    (tmFiber50RowAt 38).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 38) (by decide) tmFiber50ReverseRow_38_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_39_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 39) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk19_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 38) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber50ReverseSingleStep39 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 7) (tmFiber50StateAt 39) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 7) (tmFiber50StateAt 39)
    (tmFiber50RowAt 39).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 39) (by decide) tmFiber50ReverseRow_39_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_40_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 40) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk20_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 40) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber50ReverseSingleStep40 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 8) (tmFiber50StateAt 40) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 8) (tmFiber50StateAt 40)
    (tmFiber50RowAt 40).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 40) (by decide) tmFiber50ReverseRow_40_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_41_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 41) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk20_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 40) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber50ReverseSingleStep41 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 9) (tmFiber50StateAt 41) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 9) (tmFiber50StateAt 41)
    (tmFiber50RowAt 41).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 41) (by decide) tmFiber50ReverseRow_41_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_42_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 42) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk21_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 42) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber50ReverseSingleStep42 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 10) (tmFiber50StateAt 42) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 10) (tmFiber50StateAt 42)
    (tmFiber50RowAt 42).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 42) (by decide) tmFiber50ReverseRow_42_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_43_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 43) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk21_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 42) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber50ReverseSingleStep43 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 11) (tmFiber50StateAt 43) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 11) (tmFiber50StateAt 43)
    (tmFiber50RowAt 43).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 43) (by decide) tmFiber50ReverseRow_43_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_44_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 44) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk22_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 44) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber50ReverseSingleStep44 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 40) (tmFiber50StateAt 44) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 40) (tmFiber50StateAt 44)
    (tmFiber50RowAt 44).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 44) (by decide) tmFiber50ReverseRow_44_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_45_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 45) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk22_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 44) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber50ReverseSingleStep45 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 41) (tmFiber50StateAt 45) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 41) (tmFiber50StateAt 45)
    (tmFiber50RowAt 45).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 45) (by decide) tmFiber50ReverseRow_45_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_46_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 46) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk23_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 46) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber50ReverseSingleStep46 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 14) (tmFiber50StateAt 46) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 14) (tmFiber50StateAt 46)
    (tmFiber50RowAt 46).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 46) (by decide) tmFiber50ReverseRow_46_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_47_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 47) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk23_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 46) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber50ReverseSingleStep47 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 15) (tmFiber50StateAt 47) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 15) (tmFiber50StateAt 47)
    (tmFiber50RowAt 47).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 47) (by decide) tmFiber50ReverseRow_47_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_48_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 48) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk24_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 48) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber50ReverseSingleStep48 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 32) (tmFiber50StateAt 48) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 32) (tmFiber50StateAt 48)
    (tmFiber50RowAt 48).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 48) (by decide) tmFiber50ReverseRow_48_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_49_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 49) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk24_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 48) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber50ReverseSingleStep49 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 33) (tmFiber50StateAt 49) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 33) (tmFiber50StateAt 49)
    (tmFiber50RowAt 49).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 49) (by decide) tmFiber50ReverseRow_49_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_50_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 50) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk25_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 50) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber50ReverseSingleStep50 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 34) (tmFiber50StateAt 50) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 34) (tmFiber50StateAt 50)
    (tmFiber50RowAt 50).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 50) (by decide) tmFiber50ReverseRow_50_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_51_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 51) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk25_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 50) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber50ReverseSingleStep51 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 35) (tmFiber50StateAt 51) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 35) (tmFiber50StateAt 51)
    (tmFiber50RowAt 51).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 51) (by decide) tmFiber50ReverseRow_51_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_52_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 52) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk26_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 52) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber50ReverseSingleStep52 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 36) (tmFiber50StateAt 52) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 36) (tmFiber50StateAt 52)
    (tmFiber50RowAt 52).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 52) (by decide) tmFiber50ReverseRow_52_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_53_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 53) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk26_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 52) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber50ReverseSingleStep53 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 37) (tmFiber50StateAt 53) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 37) (tmFiber50StateAt 53)
    (tmFiber50RowAt 53).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 53) (by decide) tmFiber50ReverseRow_53_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_54_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 54) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk27_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 54) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber50ReverseSingleStep54 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 38) (tmFiber50StateAt 54) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 38) (tmFiber50StateAt 54)
    (tmFiber50RowAt 54).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 54) (by decide) tmFiber50ReverseRow_54_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_55_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 55) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk27_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 54) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber50ReverseSingleStep55 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 39) (tmFiber50StateAt 55) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 39) (tmFiber50StateAt 55)
    (tmFiber50RowAt 55).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 55) (by decide) tmFiber50ReverseRow_55_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_56_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 56) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk28_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 56) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber50ReverseSingleStep56 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 24) (tmFiber50StateAt 56) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 24) (tmFiber50StateAt 56)
    (tmFiber50RowAt 56).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 56) (by decide) tmFiber50ReverseRow_56_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_57_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 57) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk28_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 56) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber50ReverseSingleStep57 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 25) (tmFiber50StateAt 57) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 25) (tmFiber50StateAt 57)
    (tmFiber50RowAt 57).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 57) (by decide) tmFiber50ReverseRow_57_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_58_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 58) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk29_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 58) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber50ReverseSingleStep58 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 26) (tmFiber50StateAt 58) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 26) (tmFiber50StateAt 58)
    (tmFiber50RowAt 58).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 58) (by decide) tmFiber50ReverseRow_58_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_59_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 59) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk29_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 58) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber50ReverseSingleStep59 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 27) (tmFiber50StateAt 59) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 27) (tmFiber50StateAt 59)
    (tmFiber50RowAt 59).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 59) (by decide) tmFiber50ReverseRow_59_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_60_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 60) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk30_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 60) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber50ReverseSingleStep60 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 56) (tmFiber50StateAt 60) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 56) (tmFiber50StateAt 60)
    (tmFiber50RowAt 60).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 60) (by decide) tmFiber50ReverseRow_60_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_61_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 61) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk30_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 60) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber50ReverseSingleStep61 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 57) (tmFiber50StateAt 61) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 57) (tmFiber50StateAt 61)
    (tmFiber50RowAt 61).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 61) (by decide) tmFiber50ReverseRow_61_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_62_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 62) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk31_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 62) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber50ReverseSingleStep62 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 30) (tmFiber50StateAt 62) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 30) (tmFiber50StateAt 62)
    (tmFiber50RowAt 62).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 62) (by decide) tmFiber50ReverseRow_62_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50ReverseRow_63_ok :
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 63) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber50Chunk31_ok
  change (tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 62) &&
    tmRowReverseValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber50ReverseSingleStep63 :
    chainSingleKempeStep tmWord (tmFiber50StateAt 31) (tmFiber50StateAt 63) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber50StateAt 31) (tmFiber50StateAt 63)
    (tmFiber50RowAt 63).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber50Key tmFiber50Expected
        (tmFiber50RowAt 63) (by decide) tmFiber50ReverseRow_63_ok
      simpa [tmFiber50StateAt, tmFiber50RowAt, tmFiber50Rows, listGetD, directRow] using h)

theorem tmFiber50State1_in_pass1_prefix1 :
    tmFiber50StateAt 1 ∈ chainClosureStep tmWord tmFiber50Prefix1 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 0 ∈
      chainClosureStep tmWord tmFiber50Prefix0 ([tmFiber50StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber50Prefix0
      ([tmFiber50StateAt 0]) (tmFiber50StateAt 0) (by simp)
  rw [show tmFiber50Prefix1 = tmFiber50Prefix0 ++ [tmFiber50StateAt 1] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 1) []
    (chainClosureStep tmWord tmFiber50Prefix0 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 0) hparentBefore tmFiber50ReverseSingleStep1
theorem tmFiber50State1_in_pass1_full :
    tmFiber50StateAt 1 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix1 ++ [tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix1 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 1) tmFiber50State1_in_pass1_prefix1
theorem tmFiber50State2_in_pass1_prefix2 :
    tmFiber50StateAt 2 ∈ chainClosureStep tmWord tmFiber50Prefix2 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 0 ∈
      chainClosureStep tmWord tmFiber50Prefix1 ([tmFiber50StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber50Prefix1
      ([tmFiber50StateAt 0]) (tmFiber50StateAt 0) (by simp)
  rw [show tmFiber50Prefix2 = tmFiber50Prefix1 ++ [tmFiber50StateAt 2] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 2) []
    (chainClosureStep tmWord tmFiber50Prefix1 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 0) hparentBefore tmFiber50ReverseSingleStep2
theorem tmFiber50State2_in_pass1_full :
    tmFiber50StateAt 2 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix2 ++ [tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix2 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 2) tmFiber50State2_in_pass1_prefix2
theorem tmFiber50State3_in_pass1_prefix3 :
    tmFiber50StateAt 3 ∈ chainClosureStep tmWord tmFiber50Prefix3 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 1 ∈
      chainClosureStep tmWord tmFiber50Prefix2 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix2 = tmFiber50Prefix1 ++ [tmFiber50StateAt 2] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 2]
      (chainClosureStep tmWord tmFiber50Prefix1 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 1) tmFiber50State1_in_pass1_prefix1
  rw [show tmFiber50Prefix3 = tmFiber50Prefix2 ++ [tmFiber50StateAt 3] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 3) []
    (chainClosureStep tmWord tmFiber50Prefix2 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 1) hparentBefore tmFiber50ReverseSingleStep3
theorem tmFiber50State3_in_pass1_full :
    tmFiber50StateAt 3 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix3 ++ [tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix3 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 3) tmFiber50State3_in_pass1_prefix3
theorem tmFiber50State4_in_pass1_prefix4 :
    tmFiber50StateAt 4 ∈ chainClosureStep tmWord tmFiber50Prefix4 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 2 ∈
      chainClosureStep tmWord tmFiber50Prefix3 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix3 = tmFiber50Prefix2 ++ [tmFiber50StateAt 3] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 3]
      (chainClosureStep tmWord tmFiber50Prefix2 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 2) tmFiber50State2_in_pass1_prefix2
  rw [show tmFiber50Prefix4 = tmFiber50Prefix3 ++ [tmFiber50StateAt 4] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 4) []
    (chainClosureStep tmWord tmFiber50Prefix3 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 2) hparentBefore tmFiber50ReverseSingleStep4
theorem tmFiber50State4_in_pass1_full :
    tmFiber50StateAt 4 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix4 ++ [tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix4 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 4) tmFiber50State4_in_pass1_prefix4
theorem tmFiber50State6_in_pass1_prefix6 :
    tmFiber50StateAt 6 ∈ chainClosureStep tmWord tmFiber50Prefix6 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 1 ∈
      chainClosureStep tmWord tmFiber50Prefix5 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix5 = tmFiber50Prefix1 ++ [tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5]
      (chainClosureStep tmWord tmFiber50Prefix1 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 1) tmFiber50State1_in_pass1_prefix1
  rw [show tmFiber50Prefix6 = tmFiber50Prefix5 ++ [tmFiber50StateAt 6] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 6) []
    (chainClosureStep tmWord tmFiber50Prefix5 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 1) hparentBefore tmFiber50ReverseSingleStep6
theorem tmFiber50State6_in_pass1_full :
    tmFiber50StateAt 6 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix6 ++ [tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix6 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 6) tmFiber50State6_in_pass1_prefix6
theorem tmFiber50State7_in_pass1_prefix7 :
    tmFiber50StateAt 7 ∈ chainClosureStep tmWord tmFiber50Prefix7 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 0 ∈
      chainClosureStep tmWord tmFiber50Prefix6 ([tmFiber50StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber50Prefix6
      ([tmFiber50StateAt 0]) (tmFiber50StateAt 0) (by simp)
  rw [show tmFiber50Prefix7 = tmFiber50Prefix6 ++ [tmFiber50StateAt 7] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 7) []
    (chainClosureStep tmWord tmFiber50Prefix6 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 0) hparentBefore tmFiber50ReverseSingleStep7
theorem tmFiber50State7_in_pass1_full :
    tmFiber50StateAt 7 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix7 ++ [tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix7 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 7) tmFiber50State7_in_pass1_prefix7
theorem tmFiber50State8_in_pass1_prefix8 :
    tmFiber50StateAt 8 ∈ chainClosureStep tmWord tmFiber50Prefix8 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 0 ∈
      chainClosureStep tmWord tmFiber50Prefix7 ([tmFiber50StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber50Prefix7
      ([tmFiber50StateAt 0]) (tmFiber50StateAt 0) (by simp)
  rw [show tmFiber50Prefix8 = tmFiber50Prefix7 ++ [tmFiber50StateAt 8] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 8) []
    (chainClosureStep tmWord tmFiber50Prefix7 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 0) hparentBefore tmFiber50ReverseSingleStep8
theorem tmFiber50State8_in_pass1_full :
    tmFiber50StateAt 8 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix8 ++ [tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix8 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 8) tmFiber50State8_in_pass1_prefix8
theorem tmFiber50State9_in_pass1_prefix9 :
    tmFiber50StateAt 9 ∈ chainClosureStep tmWord tmFiber50Prefix9 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 1 ∈
      chainClosureStep tmWord tmFiber50Prefix8 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix8 = tmFiber50Prefix1 ++ [tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8]
      (chainClosureStep tmWord tmFiber50Prefix1 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 1) tmFiber50State1_in_pass1_prefix1
  rw [show tmFiber50Prefix9 = tmFiber50Prefix8 ++ [tmFiber50StateAt 9] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 9) []
    (chainClosureStep tmWord tmFiber50Prefix8 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 1) hparentBefore tmFiber50ReverseSingleStep9
theorem tmFiber50State9_in_pass1_full :
    tmFiber50StateAt 9 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix9 ++ [tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix9 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 9) tmFiber50State9_in_pass1_prefix9
theorem tmFiber50State10_in_pass1_prefix10 :
    tmFiber50StateAt 10 ∈ chainClosureStep tmWord tmFiber50Prefix10 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 2 ∈
      chainClosureStep tmWord tmFiber50Prefix9 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix9 = tmFiber50Prefix2 ++ [tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9]
      (chainClosureStep tmWord tmFiber50Prefix2 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 2) tmFiber50State2_in_pass1_prefix2
  rw [show tmFiber50Prefix10 = tmFiber50Prefix9 ++ [tmFiber50StateAt 10] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 10) []
    (chainClosureStep tmWord tmFiber50Prefix9 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 2) hparentBefore tmFiber50ReverseSingleStep10
theorem tmFiber50State10_in_pass1_full :
    tmFiber50StateAt 10 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix10 ++ [tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix10 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 10) tmFiber50State10_in_pass1_prefix10
theorem tmFiber50State11_in_pass1_prefix11 :
    tmFiber50StateAt 11 ∈ chainClosureStep tmWord tmFiber50Prefix11 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 3 ∈
      chainClosureStep tmWord tmFiber50Prefix10 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix10 = tmFiber50Prefix3 ++ [tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10]
      (chainClosureStep tmWord tmFiber50Prefix3 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 3) tmFiber50State3_in_pass1_prefix3
  rw [show tmFiber50Prefix11 = tmFiber50Prefix10 ++ [tmFiber50StateAt 11] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 11) []
    (chainClosureStep tmWord tmFiber50Prefix10 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 3) hparentBefore tmFiber50ReverseSingleStep11
theorem tmFiber50State11_in_pass1_full :
    tmFiber50StateAt 11 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix11 ++ [tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix11 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 11) tmFiber50State11_in_pass1_prefix11
theorem tmFiber50State12_in_pass1_prefix12 :
    tmFiber50StateAt 12 ∈ chainClosureStep tmWord tmFiber50Prefix12 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 4 ∈
      chainClosureStep tmWord tmFiber50Prefix11 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix11 = tmFiber50Prefix4 ++ [tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11]
      (chainClosureStep tmWord tmFiber50Prefix4 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 4) tmFiber50State4_in_pass1_prefix4
  rw [show tmFiber50Prefix12 = tmFiber50Prefix11 ++ [tmFiber50StateAt 12] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 12) []
    (chainClosureStep tmWord tmFiber50Prefix11 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 4) hparentBefore tmFiber50ReverseSingleStep12
theorem tmFiber50State12_in_pass1_full :
    tmFiber50StateAt 12 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix12 ++ [tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix12 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 12) tmFiber50State12_in_pass1_prefix12
theorem tmFiber50State14_in_pass1_prefix14 :
    tmFiber50StateAt 14 ∈ chainClosureStep tmWord tmFiber50Prefix14 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 6 ∈
      chainClosureStep tmWord tmFiber50Prefix13 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix13 = tmFiber50Prefix6 ++ [tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13]
      (chainClosureStep tmWord tmFiber50Prefix6 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 6) tmFiber50State6_in_pass1_prefix6
  rw [show tmFiber50Prefix14 = tmFiber50Prefix13 ++ [tmFiber50StateAt 14] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 14) []
    (chainClosureStep tmWord tmFiber50Prefix13 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 6) hparentBefore tmFiber50ReverseSingleStep14
theorem tmFiber50State14_in_pass1_full :
    tmFiber50StateAt 14 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix14 ++ [tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix14 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 14) tmFiber50State14_in_pass1_prefix14
theorem tmFiber50State15_in_pass1_prefix15 :
    tmFiber50StateAt 15 ∈ chainClosureStep tmWord tmFiber50Prefix15 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 7 ∈
      chainClosureStep tmWord tmFiber50Prefix14 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix14 = tmFiber50Prefix7 ++ [tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14]
      (chainClosureStep tmWord tmFiber50Prefix7 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 7) tmFiber50State7_in_pass1_prefix7
  rw [show tmFiber50Prefix15 = tmFiber50Prefix14 ++ [tmFiber50StateAt 15] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 15) []
    (chainClosureStep tmWord tmFiber50Prefix14 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 7) hparentBefore tmFiber50ReverseSingleStep15
theorem tmFiber50State15_in_pass1_full :
    tmFiber50StateAt 15 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix15 ++ [tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix15 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 15) tmFiber50State15_in_pass1_prefix15
theorem tmFiber50State16_in_pass1_prefix16 :
    tmFiber50StateAt 16 ∈ chainClosureStep tmWord tmFiber50Prefix16 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 8 ∈
      chainClosureStep tmWord tmFiber50Prefix15 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix15 = tmFiber50Prefix8 ++ [tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15]
      (chainClosureStep tmWord tmFiber50Prefix8 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 8) tmFiber50State8_in_pass1_prefix8
  rw [show tmFiber50Prefix16 = tmFiber50Prefix15 ++ [tmFiber50StateAt 16] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 16) []
    (chainClosureStep tmWord tmFiber50Prefix15 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 8) hparentBefore tmFiber50ReverseSingleStep16
theorem tmFiber50State16_in_pass1_full :
    tmFiber50StateAt 16 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix16 ++ [tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix16 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 16) tmFiber50State16_in_pass1_prefix16
theorem tmFiber50State17_in_pass1_prefix17 :
    tmFiber50StateAt 17 ∈ chainClosureStep tmWord tmFiber50Prefix17 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 9 ∈
      chainClosureStep tmWord tmFiber50Prefix16 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix16 = tmFiber50Prefix9 ++ [tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16]
      (chainClosureStep tmWord tmFiber50Prefix9 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 9) tmFiber50State9_in_pass1_prefix9
  rw [show tmFiber50Prefix17 = tmFiber50Prefix16 ++ [tmFiber50StateAt 17] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 17) []
    (chainClosureStep tmWord tmFiber50Prefix16 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 9) hparentBefore tmFiber50ReverseSingleStep17
theorem tmFiber50State17_in_pass1_full :
    tmFiber50StateAt 17 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix17 ++ [tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix17 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 17) tmFiber50State17_in_pass1_prefix17
theorem tmFiber50State18_in_pass1_prefix18 :
    tmFiber50StateAt 18 ∈ chainClosureStep tmWord tmFiber50Prefix18 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 10 ∈
      chainClosureStep tmWord tmFiber50Prefix17 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix17 = tmFiber50Prefix10 ++ [tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17]
      (chainClosureStep tmWord tmFiber50Prefix10 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 10) tmFiber50State10_in_pass1_prefix10
  rw [show tmFiber50Prefix18 = tmFiber50Prefix17 ++ [tmFiber50StateAt 18] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 18) []
    (chainClosureStep tmWord tmFiber50Prefix17 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 10) hparentBefore tmFiber50ReverseSingleStep18
theorem tmFiber50State18_in_pass1_full :
    tmFiber50StateAt 18 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix18 ++ [tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix18 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 18) tmFiber50State18_in_pass1_prefix18
theorem tmFiber50State19_in_pass1_prefix19 :
    tmFiber50StateAt 19 ∈ chainClosureStep tmWord tmFiber50Prefix19 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 11 ∈
      chainClosureStep tmWord tmFiber50Prefix18 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix18 = tmFiber50Prefix11 ++ [tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18]
      (chainClosureStep tmWord tmFiber50Prefix11 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 11) tmFiber50State11_in_pass1_prefix11
  rw [show tmFiber50Prefix19 = tmFiber50Prefix18 ++ [tmFiber50StateAt 19] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 19) []
    (chainClosureStep tmWord tmFiber50Prefix18 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 11) hparentBefore tmFiber50ReverseSingleStep19
theorem tmFiber50State19_in_pass1_full :
    tmFiber50StateAt 19 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix19 ++ [tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix19 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 19) tmFiber50State19_in_pass1_prefix19
theorem tmFiber50State20_in_pass1_prefix20 :
    tmFiber50StateAt 20 ∈ chainClosureStep tmWord tmFiber50Prefix20 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 12 ∈
      chainClosureStep tmWord tmFiber50Prefix19 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix19 = tmFiber50Prefix12 ++ [tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19]
      (chainClosureStep tmWord tmFiber50Prefix12 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 12) tmFiber50State12_in_pass1_prefix12
  rw [show tmFiber50Prefix20 = tmFiber50Prefix19 ++ [tmFiber50StateAt 20] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 20) []
    (chainClosureStep tmWord tmFiber50Prefix19 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 12) hparentBefore tmFiber50ReverseSingleStep20
theorem tmFiber50State20_in_pass1_full :
    tmFiber50StateAt 20 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix20 ++ [tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix20 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 20) tmFiber50State20_in_pass1_prefix20
theorem tmFiber50State22_in_pass1_prefix22 :
    tmFiber50StateAt 22 ∈ chainClosureStep tmWord tmFiber50Prefix22 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 14 ∈
      chainClosureStep tmWord tmFiber50Prefix21 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix21 = tmFiber50Prefix14 ++ [tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21]
      (chainClosureStep tmWord tmFiber50Prefix14 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 14) tmFiber50State14_in_pass1_prefix14
  rw [show tmFiber50Prefix22 = tmFiber50Prefix21 ++ [tmFiber50StateAt 22] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 22) []
    (chainClosureStep tmWord tmFiber50Prefix21 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 14) hparentBefore tmFiber50ReverseSingleStep22
theorem tmFiber50State22_in_pass1_full :
    tmFiber50StateAt 22 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix22 ++ [tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix22 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 22) tmFiber50State22_in_pass1_prefix22
theorem tmFiber50State23_in_pass1_prefix23 :
    tmFiber50StateAt 23 ∈ chainClosureStep tmWord tmFiber50Prefix23 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 15 ∈
      chainClosureStep tmWord tmFiber50Prefix22 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix22 = tmFiber50Prefix15 ++ [tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22]
      (chainClosureStep tmWord tmFiber50Prefix15 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 15) tmFiber50State15_in_pass1_prefix15
  rw [show tmFiber50Prefix23 = tmFiber50Prefix22 ++ [tmFiber50StateAt 23] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 23) []
    (chainClosureStep tmWord tmFiber50Prefix22 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 15) hparentBefore tmFiber50ReverseSingleStep23
theorem tmFiber50State23_in_pass1_full :
    tmFiber50StateAt 23 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix23 ++ [tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix23 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 23) tmFiber50State23_in_pass1_prefix23
theorem tmFiber50State24_in_pass1_prefix24 :
    tmFiber50StateAt 24 ∈ chainClosureStep tmWord tmFiber50Prefix24 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 0 ∈
      chainClosureStep tmWord tmFiber50Prefix23 ([tmFiber50StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber50Prefix23
      ([tmFiber50StateAt 0]) (tmFiber50StateAt 0) (by simp)
  rw [show tmFiber50Prefix24 = tmFiber50Prefix23 ++ [tmFiber50StateAt 24] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 24) []
    (chainClosureStep tmWord tmFiber50Prefix23 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 0) hparentBefore tmFiber50ReverseSingleStep24
theorem tmFiber50State24_in_pass1_full :
    tmFiber50StateAt 24 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix24 ++ [tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix24 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 24) tmFiber50State24_in_pass1_prefix24
theorem tmFiber50State25_in_pass1_prefix25 :
    tmFiber50StateAt 25 ∈ chainClosureStep tmWord tmFiber50Prefix25 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 1 ∈
      chainClosureStep tmWord tmFiber50Prefix24 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix24 = tmFiber50Prefix1 ++ [tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24]
      (chainClosureStep tmWord tmFiber50Prefix1 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 1) tmFiber50State1_in_pass1_prefix1
  rw [show tmFiber50Prefix25 = tmFiber50Prefix24 ++ [tmFiber50StateAt 25] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 25) []
    (chainClosureStep tmWord tmFiber50Prefix24 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 1) hparentBefore tmFiber50ReverseSingleStep25
theorem tmFiber50State25_in_pass1_full :
    tmFiber50StateAt 25 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix25 ++ [tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix25 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 25) tmFiber50State25_in_pass1_prefix25
theorem tmFiber50State26_in_pass1_prefix26 :
    tmFiber50StateAt 26 ∈ chainClosureStep tmWord tmFiber50Prefix26 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 2 ∈
      chainClosureStep tmWord tmFiber50Prefix25 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix25 = tmFiber50Prefix2 ++ [tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25]
      (chainClosureStep tmWord tmFiber50Prefix2 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 2) tmFiber50State2_in_pass1_prefix2
  rw [show tmFiber50Prefix26 = tmFiber50Prefix25 ++ [tmFiber50StateAt 26] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 26) []
    (chainClosureStep tmWord tmFiber50Prefix25 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 2) hparentBefore tmFiber50ReverseSingleStep26
theorem tmFiber50State26_in_pass1_full :
    tmFiber50StateAt 26 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix26 ++ [tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix26 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 26) tmFiber50State26_in_pass1_prefix26
theorem tmFiber50State27_in_pass1_prefix27 :
    tmFiber50StateAt 27 ∈ chainClosureStep tmWord tmFiber50Prefix27 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 3 ∈
      chainClosureStep tmWord tmFiber50Prefix26 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix26 = tmFiber50Prefix3 ++ [tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26]
      (chainClosureStep tmWord tmFiber50Prefix3 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 3) tmFiber50State3_in_pass1_prefix3
  rw [show tmFiber50Prefix27 = tmFiber50Prefix26 ++ [tmFiber50StateAt 27] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 27) []
    (chainClosureStep tmWord tmFiber50Prefix26 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 3) hparentBefore tmFiber50ReverseSingleStep27
theorem tmFiber50State27_in_pass1_full :
    tmFiber50StateAt 27 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix27 ++ [tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix27 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 27) tmFiber50State27_in_pass1_prefix27
theorem tmFiber50State28_in_pass1_prefix28 :
    tmFiber50StateAt 28 ∈ chainClosureStep tmWord tmFiber50Prefix28 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 4 ∈
      chainClosureStep tmWord tmFiber50Prefix27 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix27 = tmFiber50Prefix4 ++ [tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27]
      (chainClosureStep tmWord tmFiber50Prefix4 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 4) tmFiber50State4_in_pass1_prefix4
  rw [show tmFiber50Prefix28 = tmFiber50Prefix27 ++ [tmFiber50StateAt 28] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 28) []
    (chainClosureStep tmWord tmFiber50Prefix27 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 4) hparentBefore tmFiber50ReverseSingleStep28
theorem tmFiber50State28_in_pass1_full :
    tmFiber50StateAt 28 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix28 ++ [tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix28 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 28) tmFiber50State28_in_pass1_prefix28
theorem tmFiber50State30_in_pass1_prefix30 :
    tmFiber50StateAt 30 ∈ chainClosureStep tmWord tmFiber50Prefix30 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 6 ∈
      chainClosureStep tmWord tmFiber50Prefix29 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix29 = tmFiber50Prefix6 ++ [tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29]
      (chainClosureStep tmWord tmFiber50Prefix6 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 6) tmFiber50State6_in_pass1_prefix6
  rw [show tmFiber50Prefix30 = tmFiber50Prefix29 ++ [tmFiber50StateAt 30] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 30) []
    (chainClosureStep tmWord tmFiber50Prefix29 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 6) hparentBefore tmFiber50ReverseSingleStep30
theorem tmFiber50State30_in_pass1_full :
    tmFiber50StateAt 30 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix30 ++ [tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix30 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 30) tmFiber50State30_in_pass1_prefix30
theorem tmFiber50State31_in_pass1_prefix31 :
    tmFiber50StateAt 31 ∈ chainClosureStep tmWord tmFiber50Prefix31 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 7 ∈
      chainClosureStep tmWord tmFiber50Prefix30 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix30 = tmFiber50Prefix7 ++ [tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30]
      (chainClosureStep tmWord tmFiber50Prefix7 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 7) tmFiber50State7_in_pass1_prefix7
  rw [show tmFiber50Prefix31 = tmFiber50Prefix30 ++ [tmFiber50StateAt 31] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 31) []
    (chainClosureStep tmWord tmFiber50Prefix30 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 7) hparentBefore tmFiber50ReverseSingleStep31
theorem tmFiber50State31_in_pass1_full :
    tmFiber50StateAt 31 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix31 ++ [tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix31 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 31) tmFiber50State31_in_pass1_prefix31
theorem tmFiber50State32_in_pass1_prefix32 :
    tmFiber50StateAt 32 ∈ chainClosureStep tmWord tmFiber50Prefix32 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 0 ∈
      chainClosureStep tmWord tmFiber50Prefix31 ([tmFiber50StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber50Prefix31
      ([tmFiber50StateAt 0]) (tmFiber50StateAt 0) (by simp)
  rw [show tmFiber50Prefix32 = tmFiber50Prefix31 ++ [tmFiber50StateAt 32] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 32) []
    (chainClosureStep tmWord tmFiber50Prefix31 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 0) hparentBefore tmFiber50ReverseSingleStep32
theorem tmFiber50State32_in_pass1_full :
    tmFiber50StateAt 32 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix32 ++ [tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix32 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 32) tmFiber50State32_in_pass1_prefix32
theorem tmFiber50State33_in_pass1_prefix33 :
    tmFiber50StateAt 33 ∈ chainClosureStep tmWord tmFiber50Prefix33 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 1 ∈
      chainClosureStep tmWord tmFiber50Prefix32 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix32 = tmFiber50Prefix1 ++ [tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 2, tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32]
      (chainClosureStep tmWord tmFiber50Prefix1 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 1) tmFiber50State1_in_pass1_prefix1
  rw [show tmFiber50Prefix33 = tmFiber50Prefix32 ++ [tmFiber50StateAt 33] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 33) []
    (chainClosureStep tmWord tmFiber50Prefix32 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 1) hparentBefore tmFiber50ReverseSingleStep33
theorem tmFiber50State33_in_pass1_full :
    tmFiber50StateAt 33 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix33 ++ [tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix33 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 33) tmFiber50State33_in_pass1_prefix33
theorem tmFiber50State34_in_pass1_prefix34 :
    tmFiber50StateAt 34 ∈ chainClosureStep tmWord tmFiber50Prefix34 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 2 ∈
      chainClosureStep tmWord tmFiber50Prefix33 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix33 = tmFiber50Prefix2 ++ [tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 3, tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33]
      (chainClosureStep tmWord tmFiber50Prefix2 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 2) tmFiber50State2_in_pass1_prefix2
  rw [show tmFiber50Prefix34 = tmFiber50Prefix33 ++ [tmFiber50StateAt 34] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 34) []
    (chainClosureStep tmWord tmFiber50Prefix33 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 2) hparentBefore tmFiber50ReverseSingleStep34
theorem tmFiber50State34_in_pass1_full :
    tmFiber50StateAt 34 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix34 ++ [tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix34 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 34) tmFiber50State34_in_pass1_prefix34
theorem tmFiber50State35_in_pass1_prefix35 :
    tmFiber50StateAt 35 ∈ chainClosureStep tmWord tmFiber50Prefix35 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 3 ∈
      chainClosureStep tmWord tmFiber50Prefix34 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix34 = tmFiber50Prefix3 ++ [tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 4, tmFiber50StateAt 5, tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34]
      (chainClosureStep tmWord tmFiber50Prefix3 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 3) tmFiber50State3_in_pass1_prefix3
  rw [show tmFiber50Prefix35 = tmFiber50Prefix34 ++ [tmFiber50StateAt 35] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 35) []
    (chainClosureStep tmWord tmFiber50Prefix34 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 3) hparentBefore tmFiber50ReverseSingleStep35
theorem tmFiber50State35_in_pass1_full :
    tmFiber50StateAt 35 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix35 ++ [tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix35 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 35) tmFiber50State35_in_pass1_prefix35
theorem tmFiber50State36_in_pass1_prefix36 :
    tmFiber50StateAt 36 ∈ chainClosureStep tmWord tmFiber50Prefix36 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 32 ∈
      chainClosureStep tmWord tmFiber50Prefix35 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix35 = tmFiber50Prefix32 ++ [tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35]
      (chainClosureStep tmWord tmFiber50Prefix32 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 32) tmFiber50State32_in_pass1_prefix32
  rw [show tmFiber50Prefix36 = tmFiber50Prefix35 ++ [tmFiber50StateAt 36] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 36) []
    (chainClosureStep tmWord tmFiber50Prefix35 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 32) hparentBefore tmFiber50ReverseSingleStep36
theorem tmFiber50State36_in_pass1_full :
    tmFiber50StateAt 36 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix36 ++ [tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix36 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 36) tmFiber50State36_in_pass1_prefix36
theorem tmFiber50State37_in_pass1_prefix37 :
    tmFiber50StateAt 37 ∈ chainClosureStep tmWord tmFiber50Prefix37 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 33 ∈
      chainClosureStep tmWord tmFiber50Prefix36 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix36 = tmFiber50Prefix33 ++ [tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36]
      (chainClosureStep tmWord tmFiber50Prefix33 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 33) tmFiber50State33_in_pass1_prefix33
  rw [show tmFiber50Prefix37 = tmFiber50Prefix36 ++ [tmFiber50StateAt 37] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 37) []
    (chainClosureStep tmWord tmFiber50Prefix36 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 33) hparentBefore tmFiber50ReverseSingleStep37
theorem tmFiber50State37_in_pass1_full :
    tmFiber50StateAt 37 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix37 ++ [tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix37 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 37) tmFiber50State37_in_pass1_prefix37
theorem tmFiber50State38_in_pass1_prefix38 :
    tmFiber50StateAt 38 ∈ chainClosureStep tmWord tmFiber50Prefix38 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 6 ∈
      chainClosureStep tmWord tmFiber50Prefix37 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix37 = tmFiber50Prefix6 ++ [tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37]
      (chainClosureStep tmWord tmFiber50Prefix6 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 6) tmFiber50State6_in_pass1_prefix6
  rw [show tmFiber50Prefix38 = tmFiber50Prefix37 ++ [tmFiber50StateAt 38] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 38) []
    (chainClosureStep tmWord tmFiber50Prefix37 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 6) hparentBefore tmFiber50ReverseSingleStep38
theorem tmFiber50State38_in_pass1_full :
    tmFiber50StateAt 38 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix38 ++ [tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix38 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 38) tmFiber50State38_in_pass1_prefix38
theorem tmFiber50State39_in_pass1_prefix39 :
    tmFiber50StateAt 39 ∈ chainClosureStep tmWord tmFiber50Prefix39 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 7 ∈
      chainClosureStep tmWord tmFiber50Prefix38 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix38 = tmFiber50Prefix7 ++ [tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38]
      (chainClosureStep tmWord tmFiber50Prefix7 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 7) tmFiber50State7_in_pass1_prefix7
  rw [show tmFiber50Prefix39 = tmFiber50Prefix38 ++ [tmFiber50StateAt 39] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 39) []
    (chainClosureStep tmWord tmFiber50Prefix38 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 7) hparentBefore tmFiber50ReverseSingleStep39
theorem tmFiber50State39_in_pass1_full :
    tmFiber50StateAt 39 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix39 ++ [tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix39 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 39) tmFiber50State39_in_pass1_prefix39
theorem tmFiber50State40_in_pass1_prefix40 :
    tmFiber50StateAt 40 ∈ chainClosureStep tmWord tmFiber50Prefix40 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 8 ∈
      chainClosureStep tmWord tmFiber50Prefix39 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix39 = tmFiber50Prefix8 ++ [tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39]
      (chainClosureStep tmWord tmFiber50Prefix8 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 8) tmFiber50State8_in_pass1_prefix8
  rw [show tmFiber50Prefix40 = tmFiber50Prefix39 ++ [tmFiber50StateAt 40] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 40) []
    (chainClosureStep tmWord tmFiber50Prefix39 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 8) hparentBefore tmFiber50ReverseSingleStep40
theorem tmFiber50State40_in_pass1_full :
    tmFiber50StateAt 40 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix40 ++ [tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix40 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 40) tmFiber50State40_in_pass1_prefix40
theorem tmFiber50State41_in_pass1_prefix41 :
    tmFiber50StateAt 41 ∈ chainClosureStep tmWord tmFiber50Prefix41 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 9 ∈
      chainClosureStep tmWord tmFiber50Prefix40 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix40 = tmFiber50Prefix9 ++ [tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40]
      (chainClosureStep tmWord tmFiber50Prefix9 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 9) tmFiber50State9_in_pass1_prefix9
  rw [show tmFiber50Prefix41 = tmFiber50Prefix40 ++ [tmFiber50StateAt 41] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 41) []
    (chainClosureStep tmWord tmFiber50Prefix40 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 9) hparentBefore tmFiber50ReverseSingleStep41
theorem tmFiber50State41_in_pass1_full :
    tmFiber50StateAt 41 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix41 ++ [tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix41 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 41) tmFiber50State41_in_pass1_prefix41
theorem tmFiber50State42_in_pass1_prefix42 :
    tmFiber50StateAt 42 ∈ chainClosureStep tmWord tmFiber50Prefix42 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 10 ∈
      chainClosureStep tmWord tmFiber50Prefix41 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix41 = tmFiber50Prefix10 ++ [tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41]
      (chainClosureStep tmWord tmFiber50Prefix10 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 10) tmFiber50State10_in_pass1_prefix10
  rw [show tmFiber50Prefix42 = tmFiber50Prefix41 ++ [tmFiber50StateAt 42] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 42) []
    (chainClosureStep tmWord tmFiber50Prefix41 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 10) hparentBefore tmFiber50ReverseSingleStep42
theorem tmFiber50State42_in_pass1_full :
    tmFiber50StateAt 42 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix42 ++ [tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix42 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 42) tmFiber50State42_in_pass1_prefix42
theorem tmFiber50State43_in_pass1_prefix43 :
    tmFiber50StateAt 43 ∈ chainClosureStep tmWord tmFiber50Prefix43 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 11 ∈
      chainClosureStep tmWord tmFiber50Prefix42 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix42 = tmFiber50Prefix11 ++ [tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42]
      (chainClosureStep tmWord tmFiber50Prefix11 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 11) tmFiber50State11_in_pass1_prefix11
  rw [show tmFiber50Prefix43 = tmFiber50Prefix42 ++ [tmFiber50StateAt 43] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 43) []
    (chainClosureStep tmWord tmFiber50Prefix42 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 11) hparentBefore tmFiber50ReverseSingleStep43
theorem tmFiber50State43_in_pass1_full :
    tmFiber50StateAt 43 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix43 ++ [tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix43 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 43) tmFiber50State43_in_pass1_prefix43
theorem tmFiber50State44_in_pass1_prefix44 :
    tmFiber50StateAt 44 ∈ chainClosureStep tmWord tmFiber50Prefix44 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 40 ∈
      chainClosureStep tmWord tmFiber50Prefix43 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix43 = tmFiber50Prefix40 ++ [tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43]
      (chainClosureStep tmWord tmFiber50Prefix40 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 40) tmFiber50State40_in_pass1_prefix40
  rw [show tmFiber50Prefix44 = tmFiber50Prefix43 ++ [tmFiber50StateAt 44] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 44) []
    (chainClosureStep tmWord tmFiber50Prefix43 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 40) hparentBefore tmFiber50ReverseSingleStep44
theorem tmFiber50State44_in_pass1_full :
    tmFiber50StateAt 44 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix44 ++ [tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix44 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 44) tmFiber50State44_in_pass1_prefix44
theorem tmFiber50State45_in_pass1_prefix45 :
    tmFiber50StateAt 45 ∈ chainClosureStep tmWord tmFiber50Prefix45 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 41 ∈
      chainClosureStep tmWord tmFiber50Prefix44 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix44 = tmFiber50Prefix41 ++ [tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44]
      (chainClosureStep tmWord tmFiber50Prefix41 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 41) tmFiber50State41_in_pass1_prefix41
  rw [show tmFiber50Prefix45 = tmFiber50Prefix44 ++ [tmFiber50StateAt 45] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 45) []
    (chainClosureStep tmWord tmFiber50Prefix44 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 41) hparentBefore tmFiber50ReverseSingleStep45
theorem tmFiber50State45_in_pass1_full :
    tmFiber50StateAt 45 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix45 ++ [tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix45 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 45) tmFiber50State45_in_pass1_prefix45
theorem tmFiber50State46_in_pass1_prefix46 :
    tmFiber50StateAt 46 ∈ chainClosureStep tmWord tmFiber50Prefix46 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 14 ∈
      chainClosureStep tmWord tmFiber50Prefix45 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix45 = tmFiber50Prefix14 ++ [tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45]
      (chainClosureStep tmWord tmFiber50Prefix14 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 14) tmFiber50State14_in_pass1_prefix14
  rw [show tmFiber50Prefix46 = tmFiber50Prefix45 ++ [tmFiber50StateAt 46] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 46) []
    (chainClosureStep tmWord tmFiber50Prefix45 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 14) hparentBefore tmFiber50ReverseSingleStep46
theorem tmFiber50State46_in_pass1_full :
    tmFiber50StateAt 46 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix46 ++ [tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix46 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 46) tmFiber50State46_in_pass1_prefix46
theorem tmFiber50State47_in_pass1_prefix47 :
    tmFiber50StateAt 47 ∈ chainClosureStep tmWord tmFiber50Prefix47 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 15 ∈
      chainClosureStep tmWord tmFiber50Prefix46 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix46 = tmFiber50Prefix15 ++ [tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46]
      (chainClosureStep tmWord tmFiber50Prefix15 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 15) tmFiber50State15_in_pass1_prefix15
  rw [show tmFiber50Prefix47 = tmFiber50Prefix46 ++ [tmFiber50StateAt 47] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 47) []
    (chainClosureStep tmWord tmFiber50Prefix46 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 15) hparentBefore tmFiber50ReverseSingleStep47
theorem tmFiber50State47_in_pass1_full :
    tmFiber50StateAt 47 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix47 ++ [tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix47 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 47) tmFiber50State47_in_pass1_prefix47
theorem tmFiber50State48_in_pass1_prefix48 :
    tmFiber50StateAt 48 ∈ chainClosureStep tmWord tmFiber50Prefix48 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 32 ∈
      chainClosureStep tmWord tmFiber50Prefix47 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix47 = tmFiber50Prefix32 ++ [tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47]
      (chainClosureStep tmWord tmFiber50Prefix32 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 32) tmFiber50State32_in_pass1_prefix32
  rw [show tmFiber50Prefix48 = tmFiber50Prefix47 ++ [tmFiber50StateAt 48] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 48) []
    (chainClosureStep tmWord tmFiber50Prefix47 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 32) hparentBefore tmFiber50ReverseSingleStep48
theorem tmFiber50State48_in_pass1_full :
    tmFiber50StateAt 48 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix48 ++ [tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix48 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 48) tmFiber50State48_in_pass1_prefix48
theorem tmFiber50State49_in_pass1_prefix49 :
    tmFiber50StateAt 49 ∈ chainClosureStep tmWord tmFiber50Prefix49 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 33 ∈
      chainClosureStep tmWord tmFiber50Prefix48 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix48 = tmFiber50Prefix33 ++ [tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48]
      (chainClosureStep tmWord tmFiber50Prefix33 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 33) tmFiber50State33_in_pass1_prefix33
  rw [show tmFiber50Prefix49 = tmFiber50Prefix48 ++ [tmFiber50StateAt 49] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 49) []
    (chainClosureStep tmWord tmFiber50Prefix48 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 33) hparentBefore tmFiber50ReverseSingleStep49
theorem tmFiber50State49_in_pass1_full :
    tmFiber50StateAt 49 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix49 ++ [tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix49 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 49) tmFiber50State49_in_pass1_prefix49
theorem tmFiber50State50_in_pass1_prefix50 :
    tmFiber50StateAt 50 ∈ chainClosureStep tmWord tmFiber50Prefix50 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 34 ∈
      chainClosureStep tmWord tmFiber50Prefix49 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix49 = tmFiber50Prefix34 ++ [tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49]
      (chainClosureStep tmWord tmFiber50Prefix34 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 34) tmFiber50State34_in_pass1_prefix34
  rw [show tmFiber50Prefix50 = tmFiber50Prefix49 ++ [tmFiber50StateAt 50] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 50) []
    (chainClosureStep tmWord tmFiber50Prefix49 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 34) hparentBefore tmFiber50ReverseSingleStep50
theorem tmFiber50State50_in_pass1_full :
    tmFiber50StateAt 50 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix50 ++ [tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix50 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 50) tmFiber50State50_in_pass1_prefix50
theorem tmFiber50State51_in_pass1_prefix51 :
    tmFiber50StateAt 51 ∈ chainClosureStep tmWord tmFiber50Prefix51 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 35 ∈
      chainClosureStep tmWord tmFiber50Prefix50 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix50 = tmFiber50Prefix35 ++ [tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50]
      (chainClosureStep tmWord tmFiber50Prefix35 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 35) tmFiber50State35_in_pass1_prefix35
  rw [show tmFiber50Prefix51 = tmFiber50Prefix50 ++ [tmFiber50StateAt 51] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 51) []
    (chainClosureStep tmWord tmFiber50Prefix50 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 35) hparentBefore tmFiber50ReverseSingleStep51
theorem tmFiber50State51_in_pass1_full :
    tmFiber50StateAt 51 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix51 ++ [tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix51 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 51) tmFiber50State51_in_pass1_prefix51
theorem tmFiber50State52_in_pass1_prefix52 :
    tmFiber50StateAt 52 ∈ chainClosureStep tmWord tmFiber50Prefix52 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 36 ∈
      chainClosureStep tmWord tmFiber50Prefix51 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix51 = tmFiber50Prefix36 ++ [tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51]
      (chainClosureStep tmWord tmFiber50Prefix36 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 36) tmFiber50State36_in_pass1_prefix36
  rw [show tmFiber50Prefix52 = tmFiber50Prefix51 ++ [tmFiber50StateAt 52] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 52) []
    (chainClosureStep tmWord tmFiber50Prefix51 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 36) hparentBefore tmFiber50ReverseSingleStep52
theorem tmFiber50State52_in_pass1_full :
    tmFiber50StateAt 52 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix52 ++ [tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix52 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 52) tmFiber50State52_in_pass1_prefix52
theorem tmFiber50State53_in_pass1_prefix53 :
    tmFiber50StateAt 53 ∈ chainClosureStep tmWord tmFiber50Prefix53 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 37 ∈
      chainClosureStep tmWord tmFiber50Prefix52 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix52 = tmFiber50Prefix37 ++ [tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52]
      (chainClosureStep tmWord tmFiber50Prefix37 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 37) tmFiber50State37_in_pass1_prefix37
  rw [show tmFiber50Prefix53 = tmFiber50Prefix52 ++ [tmFiber50StateAt 53] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 53) []
    (chainClosureStep tmWord tmFiber50Prefix52 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 37) hparentBefore tmFiber50ReverseSingleStep53
theorem tmFiber50State53_in_pass1_full :
    tmFiber50StateAt 53 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix53 ++ [tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix53 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 53) tmFiber50State53_in_pass1_prefix53
theorem tmFiber50State54_in_pass1_prefix54 :
    tmFiber50StateAt 54 ∈ chainClosureStep tmWord tmFiber50Prefix54 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 38 ∈
      chainClosureStep tmWord tmFiber50Prefix53 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix53 = tmFiber50Prefix38 ++ [tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53]
      (chainClosureStep tmWord tmFiber50Prefix38 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 38) tmFiber50State38_in_pass1_prefix38
  rw [show tmFiber50Prefix54 = tmFiber50Prefix53 ++ [tmFiber50StateAt 54] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 54) []
    (chainClosureStep tmWord tmFiber50Prefix53 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 38) hparentBefore tmFiber50ReverseSingleStep54
theorem tmFiber50State54_in_pass1_full :
    tmFiber50StateAt 54 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix54 ++ [tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix54 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 54) tmFiber50State54_in_pass1_prefix54
theorem tmFiber50State55_in_pass1_prefix55 :
    tmFiber50StateAt 55 ∈ chainClosureStep tmWord tmFiber50Prefix55 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 39 ∈
      chainClosureStep tmWord tmFiber50Prefix54 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix54 = tmFiber50Prefix39 ++ [tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54]
      (chainClosureStep tmWord tmFiber50Prefix39 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 39) tmFiber50State39_in_pass1_prefix39
  rw [show tmFiber50Prefix55 = tmFiber50Prefix54 ++ [tmFiber50StateAt 55] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 55) []
    (chainClosureStep tmWord tmFiber50Prefix54 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 39) hparentBefore tmFiber50ReverseSingleStep55
theorem tmFiber50State55_in_pass1_full :
    tmFiber50StateAt 55 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix55 ++ [tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix55 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 55) tmFiber50State55_in_pass1_prefix55
theorem tmFiber50State56_in_pass1_prefix56 :
    tmFiber50StateAt 56 ∈ chainClosureStep tmWord tmFiber50Prefix56 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 24 ∈
      chainClosureStep tmWord tmFiber50Prefix55 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix55 = tmFiber50Prefix24 ++ [tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55]
      (chainClosureStep tmWord tmFiber50Prefix24 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 24) tmFiber50State24_in_pass1_prefix24
  rw [show tmFiber50Prefix56 = tmFiber50Prefix55 ++ [tmFiber50StateAt 56] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 56) []
    (chainClosureStep tmWord tmFiber50Prefix55 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 24) hparentBefore tmFiber50ReverseSingleStep56
theorem tmFiber50State56_in_pass1_full :
    tmFiber50StateAt 56 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix56 ++ [tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix56 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 56) tmFiber50State56_in_pass1_prefix56
theorem tmFiber50State57_in_pass1_prefix57 :
    tmFiber50StateAt 57 ∈ chainClosureStep tmWord tmFiber50Prefix57 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 25 ∈
      chainClosureStep tmWord tmFiber50Prefix56 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix56 = tmFiber50Prefix25 ++ [tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56]
      (chainClosureStep tmWord tmFiber50Prefix25 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 25) tmFiber50State25_in_pass1_prefix25
  rw [show tmFiber50Prefix57 = tmFiber50Prefix56 ++ [tmFiber50StateAt 57] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 57) []
    (chainClosureStep tmWord tmFiber50Prefix56 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 25) hparentBefore tmFiber50ReverseSingleStep57
theorem tmFiber50State57_in_pass1_full :
    tmFiber50StateAt 57 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix57 ++ [tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix57 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 57) tmFiber50State57_in_pass1_prefix57
theorem tmFiber50State58_in_pass1_prefix58 :
    tmFiber50StateAt 58 ∈ chainClosureStep tmWord tmFiber50Prefix58 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 26 ∈
      chainClosureStep tmWord tmFiber50Prefix57 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix57 = tmFiber50Prefix26 ++ [tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57]
      (chainClosureStep tmWord tmFiber50Prefix26 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 26) tmFiber50State26_in_pass1_prefix26
  rw [show tmFiber50Prefix58 = tmFiber50Prefix57 ++ [tmFiber50StateAt 58] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 58) []
    (chainClosureStep tmWord tmFiber50Prefix57 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 26) hparentBefore tmFiber50ReverseSingleStep58
theorem tmFiber50State58_in_pass1_full :
    tmFiber50StateAt 58 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix58 ++ [tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix58 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 58) tmFiber50State58_in_pass1_prefix58
theorem tmFiber50State59_in_pass1_prefix59 :
    tmFiber50StateAt 59 ∈ chainClosureStep tmWord tmFiber50Prefix59 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 27 ∈
      chainClosureStep tmWord tmFiber50Prefix58 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix58 = tmFiber50Prefix27 ++ [tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58]
      (chainClosureStep tmWord tmFiber50Prefix27 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 27) tmFiber50State27_in_pass1_prefix27
  rw [show tmFiber50Prefix59 = tmFiber50Prefix58 ++ [tmFiber50StateAt 59] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 59) []
    (chainClosureStep tmWord tmFiber50Prefix58 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 27) hparentBefore tmFiber50ReverseSingleStep59
theorem tmFiber50State59_in_pass1_full :
    tmFiber50StateAt 59 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix59 ++ [tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix59 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 59) tmFiber50State59_in_pass1_prefix59
theorem tmFiber50State60_in_pass1_prefix60 :
    tmFiber50StateAt 60 ∈ chainClosureStep tmWord tmFiber50Prefix60 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 56 ∈
      chainClosureStep tmWord tmFiber50Prefix59 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix59 = tmFiber50Prefix56 ++ [tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59]
      (chainClosureStep tmWord tmFiber50Prefix56 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 56) tmFiber50State56_in_pass1_prefix56
  rw [show tmFiber50Prefix60 = tmFiber50Prefix59 ++ [tmFiber50StateAt 60] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 60) []
    (chainClosureStep tmWord tmFiber50Prefix59 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 56) hparentBefore tmFiber50ReverseSingleStep60
theorem tmFiber50State60_in_pass1_full :
    tmFiber50StateAt 60 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix60 ++ [tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix60 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 60) tmFiber50State60_in_pass1_prefix60
theorem tmFiber50State61_in_pass1_prefix61 :
    tmFiber50StateAt 61 ∈ chainClosureStep tmWord tmFiber50Prefix61 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 57 ∈
      chainClosureStep tmWord tmFiber50Prefix60 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix60 = tmFiber50Prefix57 ++ [tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60]
      (chainClosureStep tmWord tmFiber50Prefix57 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 57) tmFiber50State57_in_pass1_prefix57
  rw [show tmFiber50Prefix61 = tmFiber50Prefix60 ++ [tmFiber50StateAt 61] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 61) []
    (chainClosureStep tmWord tmFiber50Prefix60 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 57) hparentBefore tmFiber50ReverseSingleStep61
theorem tmFiber50State61_in_pass1_full :
    tmFiber50StateAt 61 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix61 ++ [tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix61 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 61) tmFiber50State61_in_pass1_prefix61
theorem tmFiber50State62_in_pass1_prefix62 :
    tmFiber50StateAt 62 ∈ chainClosureStep tmWord tmFiber50Prefix62 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 30 ∈
      chainClosureStep tmWord tmFiber50Prefix61 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix61 = tmFiber50Prefix30 ++ [tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61]
      (chainClosureStep tmWord tmFiber50Prefix30 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 30) tmFiber50State30_in_pass1_prefix30
  rw [show tmFiber50Prefix62 = tmFiber50Prefix61 ++ [tmFiber50StateAt 62] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 62) []
    (chainClosureStep tmWord tmFiber50Prefix61 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 30) hparentBefore tmFiber50ReverseSingleStep62
theorem tmFiber50State62_in_pass1_full :
    tmFiber50StateAt 62 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix62 ++ [tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix62 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 62) tmFiber50State62_in_pass1_prefix62
theorem tmFiber50State63_in_pass1_prefix63 :
    tmFiber50StateAt 63 ∈ chainClosureStep tmWord tmFiber50Prefix63 ([tmFiber50StateAt 0]) := by
  have hparentBefore : tmFiber50StateAt 31 ∈
      chainClosureStep tmWord tmFiber50Prefix62 ([tmFiber50StateAt 0]) := by
    rw [show tmFiber50Prefix62 = tmFiber50Prefix31 ++ [tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62]
      (chainClosureStep tmWord tmFiber50Prefix31 ([tmFiber50StateAt 0]))
      (tmFiber50StateAt 31) tmFiber50State31_in_pass1_prefix31
  rw [show tmFiber50Prefix63 = tmFiber50Prefix62 ++ [tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 63) []
    (chainClosureStep tmWord tmFiber50Prefix62 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 31) hparentBefore tmFiber50ReverseSingleStep63
theorem tmFiber50State63_in_pass1_full :
    tmFiber50StateAt 63 ∈ chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0]) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix63 ++ [] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord []
    (chainClosureStep tmWord tmFiber50Prefix63 ([tmFiber50StateAt 0]))
    (tmFiber50StateAt 63) tmFiber50State63_in_pass1_prefix63
theorem tmFiber50State5_in_pass2_prefix5 :
    tmFiber50StateAt 5 ∈ chainClosureStep tmWord tmFiber50Prefix5 (chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0])) := by
  have hparentBefore : tmFiber50StateAt 7 ∈
      chainClosureStep tmWord tmFiber50Prefix4 (chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber50Prefix4
      (chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0])) (tmFiber50StateAt 7) tmFiber50State7_in_pass1_full
  rw [show tmFiber50Prefix5 = tmFiber50Prefix4 ++ [tmFiber50StateAt 5] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 5) []
    (chainClosureStep tmWord tmFiber50Prefix4 (chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0])))
    (tmFiber50StateAt 7) hparentBefore tmFiber50ReverseSingleStep5
theorem tmFiber50State5_in_pass2_full :
    tmFiber50StateAt 5 ∈ chainClosureStep tmWord tmFiber50DirectStates (chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0])) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix5 ++ [tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix5 (chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0])))
    (tmFiber50StateAt 5) tmFiber50State5_in_pass2_prefix5
theorem tmFiber50State13_in_pass2_prefix13 :
    tmFiber50StateAt 13 ∈ chainClosureStep tmWord tmFiber50Prefix13 (chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0])) := by
  have hparentBefore : tmFiber50StateAt 5 ∈
      chainClosureStep tmWord tmFiber50Prefix12 (chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0])) := by
    rw [show tmFiber50Prefix12 = tmFiber50Prefix5 ++ [tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12]
      (chainClosureStep tmWord tmFiber50Prefix5 (chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0])))
      (tmFiber50StateAt 5) tmFiber50State5_in_pass2_prefix5
  rw [show tmFiber50Prefix13 = tmFiber50Prefix12 ++ [tmFiber50StateAt 13] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 13) []
    (chainClosureStep tmWord tmFiber50Prefix12 (chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0])))
    (tmFiber50StateAt 5) hparentBefore tmFiber50ReverseSingleStep13
theorem tmFiber50State13_in_pass2_full :
    tmFiber50StateAt 13 ∈ chainClosureStep tmWord tmFiber50DirectStates (chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0])) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix13 ++ [tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix13 (chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0])))
    (tmFiber50StateAt 13) tmFiber50State13_in_pass2_prefix13
theorem tmFiber50State21_in_pass2_prefix21 :
    tmFiber50StateAt 21 ∈ chainClosureStep tmWord tmFiber50Prefix21 (chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0])) := by
  have hparentBefore : tmFiber50StateAt 13 ∈
      chainClosureStep tmWord tmFiber50Prefix20 (chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0])) := by
    rw [show tmFiber50Prefix20 = tmFiber50Prefix13 ++ [tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20]
      (chainClosureStep tmWord tmFiber50Prefix13 (chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0])))
      (tmFiber50StateAt 13) tmFiber50State13_in_pass2_prefix13
  rw [show tmFiber50Prefix21 = tmFiber50Prefix20 ++ [tmFiber50StateAt 21] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 21) []
    (chainClosureStep tmWord tmFiber50Prefix20 (chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0])))
    (tmFiber50StateAt 13) hparentBefore tmFiber50ReverseSingleStep21
theorem tmFiber50State21_in_pass2_full :
    tmFiber50StateAt 21 ∈ chainClosureStep tmWord tmFiber50DirectStates (chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0])) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix21 ++ [tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28, tmFiber50StateAt 29, tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix21 (chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0])))
    (tmFiber50StateAt 21) tmFiber50State21_in_pass2_prefix21
theorem tmFiber50State29_in_pass2_prefix29 :
    tmFiber50StateAt 29 ∈ chainClosureStep tmWord tmFiber50Prefix29 (chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0])) := by
  have hparentBefore : tmFiber50StateAt 5 ∈
      chainClosureStep tmWord tmFiber50Prefix28 (chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0])) := by
    rw [show tmFiber50Prefix28 = tmFiber50Prefix5 ++ [tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 6, tmFiber50StateAt 7, tmFiber50StateAt 8, tmFiber50StateAt 9, tmFiber50StateAt 10, tmFiber50StateAt 11, tmFiber50StateAt 12, tmFiber50StateAt 13, tmFiber50StateAt 14, tmFiber50StateAt 15, tmFiber50StateAt 16, tmFiber50StateAt 17, tmFiber50StateAt 18, tmFiber50StateAt 19, tmFiber50StateAt 20, tmFiber50StateAt 21, tmFiber50StateAt 22, tmFiber50StateAt 23, tmFiber50StateAt 24, tmFiber50StateAt 25, tmFiber50StateAt 26, tmFiber50StateAt 27, tmFiber50StateAt 28]
      (chainClosureStep tmWord tmFiber50Prefix5 (chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0])))
      (tmFiber50StateAt 5) tmFiber50State5_in_pass2_prefix5
  rw [show tmFiber50Prefix29 = tmFiber50Prefix28 ++ [tmFiber50StateAt 29] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber50StateAt 29) []
    (chainClosureStep tmWord tmFiber50Prefix28 (chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0])))
    (tmFiber50StateAt 5) hparentBefore tmFiber50ReverseSingleStep29
theorem tmFiber50State29_in_pass2_full :
    tmFiber50StateAt 29 ∈ chainClosureStep tmWord tmFiber50DirectStates (chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0])) := by
  rw [show tmFiber50DirectStates = tmFiber50Prefix29 ++ [tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber50StateAt 30, tmFiber50StateAt 31, tmFiber50StateAt 32, tmFiber50StateAt 33, tmFiber50StateAt 34, tmFiber50StateAt 35, tmFiber50StateAt 36, tmFiber50StateAt 37, tmFiber50StateAt 38, tmFiber50StateAt 39, tmFiber50StateAt 40, tmFiber50StateAt 41, tmFiber50StateAt 42, tmFiber50StateAt 43, tmFiber50StateAt 44, tmFiber50StateAt 45, tmFiber50StateAt 46, tmFiber50StateAt 47, tmFiber50StateAt 48, tmFiber50StateAt 49, tmFiber50StateAt 50, tmFiber50StateAt 51, tmFiber50StateAt 52, tmFiber50StateAt 53, tmFiber50StateAt 54, tmFiber50StateAt 55, tmFiber50StateAt 56, tmFiber50StateAt 57, tmFiber50StateAt 58, tmFiber50StateAt 59, tmFiber50StateAt 60, tmFiber50StateAt 61, tmFiber50StateAt 62, tmFiber50StateAt 63]
    (chainClosureStep tmWord tmFiber50Prefix29 (chainClosureStep tmWord tmFiber50DirectStates ([tmFiber50StateAt 0])))
    (tmFiber50StateAt 29) tmFiber50State29_in_pass2_prefix29
theorem tmFiber50FirstPassGrows :
    ((chainClosureStep tmWord tmFiber50DirectStates [tmFiber50StateAt 0]).length ==
      [tmFiber50StateAt 0].length) = false := by
  have hroot : tmFiber50StateAt 0 ∈
      chainClosureStep tmWord tmFiber50DirectStates [tmFiber50StateAt 0] :=
    chainClosureStep_mem_of_seen tmWord tmFiber50DirectStates
      [tmFiber50StateAt 0] (tmFiber50StateAt 0) (by simp)
  have hnew : tmFiber50StateAt 1 ∈
      chainClosureStep tmWord tmFiber50DirectStates [tmFiber50StateAt 0] :=
    tmFiber50State1_in_pass1_full
  simpa using list_length_beq_one_false_of_two_mem
    (chainClosureStep tmWord tmFiber50DirectStates [tmFiber50StateAt 0])
    (tmFiber50StateAt 0) (tmFiber50StateAt 1) hroot hnew (by decide)

theorem tmFiber50State0_in_close_short :
    tmFiber50StateAt 0 ∈ closeChainFiber tmWord tmFiber50DirectStates 0 [tmFiber50StateAt 0] := by
  simp [closeChainFiber]

theorem tmFiber50State1_in_close_short :
    tmFiber50StateAt 1 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 1) tmFiber50State1_in_pass1_full

theorem tmFiber50State2_in_close_short :
    tmFiber50StateAt 2 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 2) tmFiber50State2_in_pass1_full

theorem tmFiber50State3_in_close_short :
    tmFiber50StateAt 3 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 3) tmFiber50State3_in_pass1_full

theorem tmFiber50State4_in_close_short :
    tmFiber50StateAt 4 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 4) tmFiber50State4_in_pass1_full

theorem tmFiber50State6_in_close_short :
    tmFiber50StateAt 6 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 6) tmFiber50State6_in_pass1_full

theorem tmFiber50State7_in_close_short :
    tmFiber50StateAt 7 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 7) tmFiber50State7_in_pass1_full

theorem tmFiber50State8_in_close_short :
    tmFiber50StateAt 8 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 8) tmFiber50State8_in_pass1_full

theorem tmFiber50State9_in_close_short :
    tmFiber50StateAt 9 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 9) tmFiber50State9_in_pass1_full

theorem tmFiber50State10_in_close_short :
    tmFiber50StateAt 10 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 10) tmFiber50State10_in_pass1_full

theorem tmFiber50State11_in_close_short :
    tmFiber50StateAt 11 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 11) tmFiber50State11_in_pass1_full

theorem tmFiber50State12_in_close_short :
    tmFiber50StateAt 12 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 12) tmFiber50State12_in_pass1_full

theorem tmFiber50State14_in_close_short :
    tmFiber50StateAt 14 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 14) tmFiber50State14_in_pass1_full

theorem tmFiber50State15_in_close_short :
    tmFiber50StateAt 15 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 15) tmFiber50State15_in_pass1_full

theorem tmFiber50State16_in_close_short :
    tmFiber50StateAt 16 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 16) tmFiber50State16_in_pass1_full

theorem tmFiber50State17_in_close_short :
    tmFiber50StateAt 17 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 17) tmFiber50State17_in_pass1_full

theorem tmFiber50State18_in_close_short :
    tmFiber50StateAt 18 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 18) tmFiber50State18_in_pass1_full

theorem tmFiber50State19_in_close_short :
    tmFiber50StateAt 19 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 19) tmFiber50State19_in_pass1_full

theorem tmFiber50State20_in_close_short :
    tmFiber50StateAt 20 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 20) tmFiber50State20_in_pass1_full

theorem tmFiber50State22_in_close_short :
    tmFiber50StateAt 22 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 22) tmFiber50State22_in_pass1_full

theorem tmFiber50State23_in_close_short :
    tmFiber50StateAt 23 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 23) tmFiber50State23_in_pass1_full

theorem tmFiber50State24_in_close_short :
    tmFiber50StateAt 24 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 24) tmFiber50State24_in_pass1_full

theorem tmFiber50State25_in_close_short :
    tmFiber50StateAt 25 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 25) tmFiber50State25_in_pass1_full

theorem tmFiber50State26_in_close_short :
    tmFiber50StateAt 26 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 26) tmFiber50State26_in_pass1_full

theorem tmFiber50State27_in_close_short :
    tmFiber50StateAt 27 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 27) tmFiber50State27_in_pass1_full

theorem tmFiber50State28_in_close_short :
    tmFiber50StateAt 28 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 28) tmFiber50State28_in_pass1_full

theorem tmFiber50State30_in_close_short :
    tmFiber50StateAt 30 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 30) tmFiber50State30_in_pass1_full

theorem tmFiber50State31_in_close_short :
    tmFiber50StateAt 31 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 31) tmFiber50State31_in_pass1_full

theorem tmFiber50State32_in_close_short :
    tmFiber50StateAt 32 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 32) tmFiber50State32_in_pass1_full

theorem tmFiber50State33_in_close_short :
    tmFiber50StateAt 33 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 33) tmFiber50State33_in_pass1_full

theorem tmFiber50State34_in_close_short :
    tmFiber50StateAt 34 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 34) tmFiber50State34_in_pass1_full

theorem tmFiber50State35_in_close_short :
    tmFiber50StateAt 35 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 35) tmFiber50State35_in_pass1_full

theorem tmFiber50State36_in_close_short :
    tmFiber50StateAt 36 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 36) tmFiber50State36_in_pass1_full

theorem tmFiber50State37_in_close_short :
    tmFiber50StateAt 37 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 37) tmFiber50State37_in_pass1_full

theorem tmFiber50State38_in_close_short :
    tmFiber50StateAt 38 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 38) tmFiber50State38_in_pass1_full

theorem tmFiber50State39_in_close_short :
    tmFiber50StateAt 39 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 39) tmFiber50State39_in_pass1_full

theorem tmFiber50State40_in_close_short :
    tmFiber50StateAt 40 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 40) tmFiber50State40_in_pass1_full

theorem tmFiber50State41_in_close_short :
    tmFiber50StateAt 41 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 41) tmFiber50State41_in_pass1_full

theorem tmFiber50State42_in_close_short :
    tmFiber50StateAt 42 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 42) tmFiber50State42_in_pass1_full

theorem tmFiber50State43_in_close_short :
    tmFiber50StateAt 43 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 43) tmFiber50State43_in_pass1_full

theorem tmFiber50State44_in_close_short :
    tmFiber50StateAt 44 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 44) tmFiber50State44_in_pass1_full

theorem tmFiber50State45_in_close_short :
    tmFiber50StateAt 45 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 45) tmFiber50State45_in_pass1_full

theorem tmFiber50State46_in_close_short :
    tmFiber50StateAt 46 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 46) tmFiber50State46_in_pass1_full

theorem tmFiber50State47_in_close_short :
    tmFiber50StateAt 47 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 47) tmFiber50State47_in_pass1_full

theorem tmFiber50State48_in_close_short :
    tmFiber50StateAt 48 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 48) tmFiber50State48_in_pass1_full

theorem tmFiber50State49_in_close_short :
    tmFiber50StateAt 49 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 49) tmFiber50State49_in_pass1_full

theorem tmFiber50State50_in_close_short :
    tmFiber50StateAt 50 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 50) tmFiber50State50_in_pass1_full

theorem tmFiber50State51_in_close_short :
    tmFiber50StateAt 51 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 51) tmFiber50State51_in_pass1_full

theorem tmFiber50State52_in_close_short :
    tmFiber50StateAt 52 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 52) tmFiber50State52_in_pass1_full

theorem tmFiber50State53_in_close_short :
    tmFiber50StateAt 53 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 53) tmFiber50State53_in_pass1_full

theorem tmFiber50State54_in_close_short :
    tmFiber50StateAt 54 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 54) tmFiber50State54_in_pass1_full

theorem tmFiber50State55_in_close_short :
    tmFiber50StateAt 55 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 55) tmFiber50State55_in_pass1_full

theorem tmFiber50State56_in_close_short :
    tmFiber50StateAt 56 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 56) tmFiber50State56_in_pass1_full

theorem tmFiber50State57_in_close_short :
    tmFiber50StateAt 57 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 57) tmFiber50State57_in_pass1_full

theorem tmFiber50State58_in_close_short :
    tmFiber50StateAt 58 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 58) tmFiber50State58_in_pass1_full

theorem tmFiber50State59_in_close_short :
    tmFiber50StateAt 59 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 59) tmFiber50State59_in_pass1_full

theorem tmFiber50State60_in_close_short :
    tmFiber50StateAt 60 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 60) tmFiber50State60_in_pass1_full

theorem tmFiber50State61_in_close_short :
    tmFiber50StateAt 61 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 61) tmFiber50State61_in_pass1_full

theorem tmFiber50State62_in_close_short :
    tmFiber50StateAt 62 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 62) tmFiber50State62_in_pass1_full

theorem tmFiber50State63_in_close_short :
    tmFiber50StateAt 63 ∈ closeChainFiber tmWord tmFiber50DirectStates 1 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 63) tmFiber50State63_in_pass1_full

theorem tmFiber50State5_in_close_short :
    tmFiber50StateAt 5 ∈ closeChainFiber tmWord tmFiber50DirectStates 2 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 5) tmFiber50FirstPassGrows
    tmFiber50State5_in_pass2_full

theorem tmFiber50State13_in_close_short :
    tmFiber50StateAt 13 ∈ closeChainFiber tmWord tmFiber50DirectStates 2 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 13) tmFiber50FirstPassGrows
    tmFiber50State13_in_pass2_full

theorem tmFiber50State21_in_close_short :
    tmFiber50StateAt 21 ∈ closeChainFiber tmWord tmFiber50DirectStates 2 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 21) tmFiber50FirstPassGrows
    tmFiber50State21_in_pass2_full

theorem tmFiber50State29_in_close_short :
    tmFiber50StateAt 29 ∈ closeChainFiber tmWord tmFiber50DirectStates 2 [tmFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber50DirectStates 0
    [tmFiber50StateAt 0] (tmFiber50StateAt 29) tmFiber50FirstPassGrows
    tmFiber50State29_in_pass2_full

theorem tmFiber50State0_in_close :
    tmFiber50StateAt 0 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 0 ∈ closeChainFiber tmWord tmFiber50DirectStates (0 + 64) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 0 64
    [tmFiber50StateAt 0] (tmFiber50StateAt 0) tmFiber50State0_in_close_short

theorem tmFiber50State1_in_close :
    tmFiber50StateAt 1 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 1 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 1) tmFiber50State1_in_close_short

theorem tmFiber50State2_in_close :
    tmFiber50StateAt 2 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 2 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 2) tmFiber50State2_in_close_short

theorem tmFiber50State3_in_close :
    tmFiber50StateAt 3 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 3 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 3) tmFiber50State3_in_close_short

theorem tmFiber50State4_in_close :
    tmFiber50StateAt 4 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 4 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 4) tmFiber50State4_in_close_short

theorem tmFiber50State5_in_close :
    tmFiber50StateAt 5 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 5 ∈ closeChainFiber tmWord tmFiber50DirectStates (2 + 62) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 2 62
    [tmFiber50StateAt 0] (tmFiber50StateAt 5) tmFiber50State5_in_close_short

theorem tmFiber50State6_in_close :
    tmFiber50StateAt 6 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 6 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 6) tmFiber50State6_in_close_short

theorem tmFiber50State7_in_close :
    tmFiber50StateAt 7 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 7 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 7) tmFiber50State7_in_close_short

theorem tmFiber50State8_in_close :
    tmFiber50StateAt 8 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 8 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 8) tmFiber50State8_in_close_short

theorem tmFiber50State9_in_close :
    tmFiber50StateAt 9 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 9 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 9) tmFiber50State9_in_close_short

theorem tmFiber50State10_in_close :
    tmFiber50StateAt 10 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 10 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 10) tmFiber50State10_in_close_short

theorem tmFiber50State11_in_close :
    tmFiber50StateAt 11 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 11 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 11) tmFiber50State11_in_close_short

theorem tmFiber50State12_in_close :
    tmFiber50StateAt 12 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 12 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 12) tmFiber50State12_in_close_short

theorem tmFiber50State13_in_close :
    tmFiber50StateAt 13 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 13 ∈ closeChainFiber tmWord tmFiber50DirectStates (2 + 62) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 2 62
    [tmFiber50StateAt 0] (tmFiber50StateAt 13) tmFiber50State13_in_close_short

theorem tmFiber50State14_in_close :
    tmFiber50StateAt 14 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 14 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 14) tmFiber50State14_in_close_short

theorem tmFiber50State15_in_close :
    tmFiber50StateAt 15 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 15 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 15) tmFiber50State15_in_close_short

theorem tmFiber50State16_in_close :
    tmFiber50StateAt 16 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 16 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 16) tmFiber50State16_in_close_short

theorem tmFiber50State17_in_close :
    tmFiber50StateAt 17 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 17 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 17) tmFiber50State17_in_close_short

theorem tmFiber50State18_in_close :
    tmFiber50StateAt 18 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 18 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 18) tmFiber50State18_in_close_short

theorem tmFiber50State19_in_close :
    tmFiber50StateAt 19 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 19 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 19) tmFiber50State19_in_close_short

theorem tmFiber50State20_in_close :
    tmFiber50StateAt 20 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 20 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 20) tmFiber50State20_in_close_short

theorem tmFiber50State21_in_close :
    tmFiber50StateAt 21 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 21 ∈ closeChainFiber tmWord tmFiber50DirectStates (2 + 62) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 2 62
    [tmFiber50StateAt 0] (tmFiber50StateAt 21) tmFiber50State21_in_close_short

theorem tmFiber50State22_in_close :
    tmFiber50StateAt 22 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 22 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 22) tmFiber50State22_in_close_short

theorem tmFiber50State23_in_close :
    tmFiber50StateAt 23 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 23 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 23) tmFiber50State23_in_close_short

theorem tmFiber50State24_in_close :
    tmFiber50StateAt 24 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 24 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 24) tmFiber50State24_in_close_short

theorem tmFiber50State25_in_close :
    tmFiber50StateAt 25 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 25 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 25) tmFiber50State25_in_close_short

theorem tmFiber50State26_in_close :
    tmFiber50StateAt 26 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 26 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 26) tmFiber50State26_in_close_short

theorem tmFiber50State27_in_close :
    tmFiber50StateAt 27 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 27 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 27) tmFiber50State27_in_close_short

theorem tmFiber50State28_in_close :
    tmFiber50StateAt 28 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 28 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 28) tmFiber50State28_in_close_short

theorem tmFiber50State29_in_close :
    tmFiber50StateAt 29 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 29 ∈ closeChainFiber tmWord tmFiber50DirectStates (2 + 62) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 2 62
    [tmFiber50StateAt 0] (tmFiber50StateAt 29) tmFiber50State29_in_close_short

theorem tmFiber50State30_in_close :
    tmFiber50StateAt 30 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 30 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 30) tmFiber50State30_in_close_short

theorem tmFiber50State31_in_close :
    tmFiber50StateAt 31 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 31 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 31) tmFiber50State31_in_close_short

theorem tmFiber50State32_in_close :
    tmFiber50StateAt 32 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 32 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 32) tmFiber50State32_in_close_short

theorem tmFiber50State33_in_close :
    tmFiber50StateAt 33 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 33 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 33) tmFiber50State33_in_close_short

theorem tmFiber50State34_in_close :
    tmFiber50StateAt 34 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 34 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 34) tmFiber50State34_in_close_short

theorem tmFiber50State35_in_close :
    tmFiber50StateAt 35 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 35 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 35) tmFiber50State35_in_close_short

theorem tmFiber50State36_in_close :
    tmFiber50StateAt 36 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 36 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 36) tmFiber50State36_in_close_short

theorem tmFiber50State37_in_close :
    tmFiber50StateAt 37 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 37 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 37) tmFiber50State37_in_close_short

theorem tmFiber50State38_in_close :
    tmFiber50StateAt 38 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 38 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 38) tmFiber50State38_in_close_short

theorem tmFiber50State39_in_close :
    tmFiber50StateAt 39 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 39 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 39) tmFiber50State39_in_close_short

theorem tmFiber50State40_in_close :
    tmFiber50StateAt 40 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 40 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 40) tmFiber50State40_in_close_short

theorem tmFiber50State41_in_close :
    tmFiber50StateAt 41 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 41 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 41) tmFiber50State41_in_close_short

theorem tmFiber50State42_in_close :
    tmFiber50StateAt 42 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 42 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 42) tmFiber50State42_in_close_short

theorem tmFiber50State43_in_close :
    tmFiber50StateAt 43 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 43 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 43) tmFiber50State43_in_close_short

theorem tmFiber50State44_in_close :
    tmFiber50StateAt 44 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 44 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 44) tmFiber50State44_in_close_short

theorem tmFiber50State45_in_close :
    tmFiber50StateAt 45 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 45 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 45) tmFiber50State45_in_close_short

theorem tmFiber50State46_in_close :
    tmFiber50StateAt 46 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 46 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 46) tmFiber50State46_in_close_short

theorem tmFiber50State47_in_close :
    tmFiber50StateAt 47 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 47 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 47) tmFiber50State47_in_close_short

theorem tmFiber50State48_in_close :
    tmFiber50StateAt 48 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 48 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 48) tmFiber50State48_in_close_short

theorem tmFiber50State49_in_close :
    tmFiber50StateAt 49 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 49 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 49) tmFiber50State49_in_close_short

theorem tmFiber50State50_in_close :
    tmFiber50StateAt 50 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 50 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 50) tmFiber50State50_in_close_short

theorem tmFiber50State51_in_close :
    tmFiber50StateAt 51 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 51 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 51) tmFiber50State51_in_close_short

theorem tmFiber50State52_in_close :
    tmFiber50StateAt 52 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 52 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 52) tmFiber50State52_in_close_short

theorem tmFiber50State53_in_close :
    tmFiber50StateAt 53 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 53 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 53) tmFiber50State53_in_close_short

theorem tmFiber50State54_in_close :
    tmFiber50StateAt 54 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 54 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 54) tmFiber50State54_in_close_short

theorem tmFiber50State55_in_close :
    tmFiber50StateAt 55 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 55 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 55) tmFiber50State55_in_close_short

theorem tmFiber50State56_in_close :
    tmFiber50StateAt 56 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 56 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 56) tmFiber50State56_in_close_short

theorem tmFiber50State57_in_close :
    tmFiber50StateAt 57 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 57 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 57) tmFiber50State57_in_close_short

theorem tmFiber50State58_in_close :
    tmFiber50StateAt 58 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 58 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 58) tmFiber50State58_in_close_short

theorem tmFiber50State59_in_close :
    tmFiber50StateAt 59 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 59 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 59) tmFiber50State59_in_close_short

theorem tmFiber50State60_in_close :
    tmFiber50StateAt 60 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 60 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 60) tmFiber50State60_in_close_short

theorem tmFiber50State61_in_close :
    tmFiber50StateAt 61 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 61 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 61) tmFiber50State61_in_close_short

theorem tmFiber50State62_in_close :
    tmFiber50StateAt 62 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 62 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 62) tmFiber50State62_in_close_short

theorem tmFiber50State63_in_close :
    tmFiber50StateAt 63 ∈ closeChainFiber tmWord tmFiber50DirectStates tmFiber50DirectStates.length [tmFiber50StateAt 0] := by
  change tmFiber50StateAt 63 ∈ closeChainFiber tmWord tmFiber50DirectStates (1 + 63) [tmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber50DirectStates 1 63
    [tmFiber50StateAt 0] (tmFiber50StateAt 63) tmFiber50State63_in_close_short

theorem tmFiber50DirectConnected :
    chainFiberConnected tmWord tmFiber50DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [tmFiber50DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact tmFiber50State0_in_close
  · subst state
    exact tmFiber50State1_in_close
  · subst state
    exact tmFiber50State2_in_close
  · subst state
    exact tmFiber50State3_in_close
  · subst state
    exact tmFiber50State4_in_close
  · subst state
    exact tmFiber50State5_in_close
  · subst state
    exact tmFiber50State6_in_close
  · subst state
    exact tmFiber50State7_in_close
  · subst state
    exact tmFiber50State8_in_close
  · subst state
    exact tmFiber50State9_in_close
  · subst state
    exact tmFiber50State10_in_close
  · subst state
    exact tmFiber50State11_in_close
  · subst state
    exact tmFiber50State12_in_close
  · subst state
    exact tmFiber50State13_in_close
  · subst state
    exact tmFiber50State14_in_close
  · subst state
    exact tmFiber50State15_in_close
  · subst state
    exact tmFiber50State16_in_close
  · subst state
    exact tmFiber50State17_in_close
  · subst state
    exact tmFiber50State18_in_close
  · subst state
    exact tmFiber50State19_in_close
  · subst state
    exact tmFiber50State20_in_close
  · subst state
    exact tmFiber50State21_in_close
  · subst state
    exact tmFiber50State22_in_close
  · subst state
    exact tmFiber50State23_in_close
  · subst state
    exact tmFiber50State24_in_close
  · subst state
    exact tmFiber50State25_in_close
  · subst state
    exact tmFiber50State26_in_close
  · subst state
    exact tmFiber50State27_in_close
  · subst state
    exact tmFiber50State28_in_close
  · subst state
    exact tmFiber50State29_in_close
  · subst state
    exact tmFiber50State30_in_close
  · subst state
    exact tmFiber50State31_in_close
  · subst state
    exact tmFiber50State32_in_close
  · subst state
    exact tmFiber50State33_in_close
  · subst state
    exact tmFiber50State34_in_close
  · subst state
    exact tmFiber50State35_in_close
  · subst state
    exact tmFiber50State36_in_close
  · subst state
    exact tmFiber50State37_in_close
  · subst state
    exact tmFiber50State38_in_close
  · subst state
    exact tmFiber50State39_in_close
  · subst state
    exact tmFiber50State40_in_close
  · subst state
    exact tmFiber50State41_in_close
  · subst state
    exact tmFiber50State42_in_close
  · subst state
    exact tmFiber50State43_in_close
  · subst state
    exact tmFiber50State44_in_close
  · subst state
    exact tmFiber50State45_in_close
  · subst state
    exact tmFiber50State46_in_close
  · subst state
    exact tmFiber50State47_in_close
  · subst state
    exact tmFiber50State48_in_close
  · subst state
    exact tmFiber50State49_in_close
  · subst state
    exact tmFiber50State50_in_close
  · subst state
    exact tmFiber50State51_in_close
  · subst state
    exact tmFiber50State52_in_close
  · subst state
    exact tmFiber50State53_in_close
  · subst state
    exact tmFiber50State54_in_close
  · subst state
    exact tmFiber50State55_in_close
  · subst state
    exact tmFiber50State56_in_close
  · subst state
    exact tmFiber50State57_in_close
  · subst state
    exact tmFiber50State58_in_close
  · subst state
    exact tmFiber50State59_in_close
  · subst state
    exact tmFiber50State60_in_close
  · subst state
    exact tmFiber50State61_in_close
  · subst state
    exact tmFiber50State62_in_close
  · subst state
    exact tmFiber50State63_in_close
  · cases h

end GoertzelLemma818LengthTwoTMLargeFiberBridge

end Mettapedia.GraphTheory.FourColor
