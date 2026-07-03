import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMLargeFiberBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated multi-pass direct closure bridge for `normal,mirror` size-64 fiber 76

This module proves direct connectedness for one generated size-64 fiber
whose parent order needs multiple closure scans. It is generated from
row-local reverse certificate chunks and keeps Lean on default limits.
-/

namespace GoertzelLemma818LengthTwoTMLargeFiberBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818TauMirrorCertificate
open GoertzelLemma818TauMirrorReverseAudit

def tmFiber76StateAt (i : Nat) : List TauState :=
  directStates (tmFiber76RowAt i).sourceLeft (tmFiber76RowAt i).sourceRight

def tmFiber76DirectStates : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]

def tmFiber76Prefix0 : List (List TauState) :=
  [tmFiber76StateAt 0]

def tmFiber76Prefix1 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1]

def tmFiber76Prefix2 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2]

def tmFiber76Prefix3 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3]

def tmFiber76Prefix4 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4]

def tmFiber76Prefix5 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5]

def tmFiber76Prefix6 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6]

def tmFiber76Prefix7 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7]

def tmFiber76Prefix8 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8]

def tmFiber76Prefix9 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9]

def tmFiber76Prefix10 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10]

def tmFiber76Prefix11 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11]

def tmFiber76Prefix12 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12]

def tmFiber76Prefix13 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13]

def tmFiber76Prefix14 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14]

def tmFiber76Prefix15 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15]

def tmFiber76Prefix16 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16]

def tmFiber76Prefix17 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17]

def tmFiber76Prefix18 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18]

def tmFiber76Prefix19 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19]

def tmFiber76Prefix20 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20]

def tmFiber76Prefix21 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21]

def tmFiber76Prefix22 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22]

def tmFiber76Prefix23 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23]

def tmFiber76Prefix24 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24]

def tmFiber76Prefix25 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25]

def tmFiber76Prefix26 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26]

def tmFiber76Prefix27 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27]

def tmFiber76Prefix28 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28]

def tmFiber76Prefix29 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29]

def tmFiber76Prefix30 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30]

def tmFiber76Prefix31 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31]

def tmFiber76Prefix32 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32]

def tmFiber76Prefix33 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33]

def tmFiber76Prefix34 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34]

def tmFiber76Prefix35 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35]

def tmFiber76Prefix36 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36]

def tmFiber76Prefix37 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37]

def tmFiber76Prefix38 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38]

def tmFiber76Prefix39 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39]

def tmFiber76Prefix40 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40]

def tmFiber76Prefix41 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41]

def tmFiber76Prefix42 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42]

def tmFiber76Prefix43 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43]

def tmFiber76Prefix44 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44]

def tmFiber76Prefix45 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45]

def tmFiber76Prefix46 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46]

def tmFiber76Prefix47 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47]

def tmFiber76Prefix48 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48]

def tmFiber76Prefix49 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49]

def tmFiber76Prefix50 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50]

def tmFiber76Prefix51 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51]

def tmFiber76Prefix52 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52]

def tmFiber76Prefix53 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53]

def tmFiber76Prefix54 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54]

def tmFiber76Prefix55 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55]

def tmFiber76Prefix56 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56]

def tmFiber76Prefix57 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57]

def tmFiber76Prefix58 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58]

def tmFiber76Prefix59 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59]

def tmFiber76Prefix60 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60]

def tmFiber76Prefix61 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61]

def tmFiber76Prefix62 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62]

def tmFiber76Prefix63 : List (List TauState) :=
  [tmFiber76StateAt 0, tmFiber76StateAt 1, tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]

theorem tmFiber76ReverseRow_1_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 1) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk0_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 0) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber76ReverseSingleStep1 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 0) (tmFiber76StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 0) (tmFiber76StateAt 1)
    (tmFiber76RowAt 1).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 1) (by decide) tmFiber76ReverseRow_1_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_2_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 2) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk1_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 2) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber76ReverseSingleStep2 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 1) (tmFiber76StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 1) (tmFiber76StateAt 2)
    (tmFiber76RowAt 2).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 2) (by decide) tmFiber76ReverseRow_2_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_3_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 3) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk1_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 2) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber76ReverseSingleStep3 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 0) (tmFiber76StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 0) (tmFiber76StateAt 3)
    (tmFiber76RowAt 3).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 3) (by decide) tmFiber76ReverseRow_3_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_4_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 4) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk2_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 4) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber76ReverseSingleStep4 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 0) (tmFiber76StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 0) (tmFiber76StateAt 4)
    (tmFiber76RowAt 4).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 4) (by decide) tmFiber76ReverseRow_4_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_5_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 5) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk2_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 4) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber76ReverseSingleStep5 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 1) (tmFiber76StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 1) (tmFiber76StateAt 5)
    (tmFiber76RowAt 5).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 5) (by decide) tmFiber76ReverseRow_5_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_6_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 6) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk3_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 6) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber76ReverseSingleStep6 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 4) (tmFiber76StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 4) (tmFiber76StateAt 6)
    (tmFiber76RowAt 6).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 6) (by decide) tmFiber76ReverseRow_6_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_7_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 7) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk3_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 6) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber76ReverseSingleStep7 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 3) (tmFiber76StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 3) (tmFiber76StateAt 7)
    (tmFiber76RowAt 7).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 7) (by decide) tmFiber76ReverseRow_7_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_8_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 8) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk4_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 8) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber76ReverseSingleStep8 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 0) (tmFiber76StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 0) (tmFiber76StateAt 8)
    (tmFiber76RowAt 8).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 8) (by decide) tmFiber76ReverseRow_8_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_9_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 9) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk4_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 8) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber76ReverseSingleStep9 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 1) (tmFiber76StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 1) (tmFiber76StateAt 9)
    (tmFiber76RowAt 9).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 9) (by decide) tmFiber76ReverseRow_9_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_10_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 10) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk5_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 10) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber76ReverseSingleStep10 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 2) (tmFiber76StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 2) (tmFiber76StateAt 10)
    (tmFiber76RowAt 10).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 10) (by decide) tmFiber76ReverseRow_10_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_11_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 11) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk5_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 10) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber76ReverseSingleStep11 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 3) (tmFiber76StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 3) (tmFiber76StateAt 11)
    (tmFiber76RowAt 11).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 11) (by decide) tmFiber76ReverseRow_11_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_12_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 12) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk6_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 12) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber76ReverseSingleStep12 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 4) (tmFiber76StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 4) (tmFiber76StateAt 12)
    (tmFiber76RowAt 12).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 12) (by decide) tmFiber76ReverseRow_12_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_13_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 13) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk6_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 12) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber76ReverseSingleStep13 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 5) (tmFiber76StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 5) (tmFiber76StateAt 13)
    (tmFiber76RowAt 13).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 13) (by decide) tmFiber76ReverseRow_13_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_14_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 14) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk7_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 14) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber76ReverseSingleStep14 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 6) (tmFiber76StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 6) (tmFiber76StateAt 14)
    (tmFiber76RowAt 14).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 14) (by decide) tmFiber76ReverseRow_14_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_15_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 15) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk7_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 14) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber76ReverseSingleStep15 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 7) (tmFiber76StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 7) (tmFiber76StateAt 15)
    (tmFiber76RowAt 15).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 15) (by decide) tmFiber76ReverseRow_15_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_16_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 16) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk8_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 16) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber76ReverseSingleStep16 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 0) (tmFiber76StateAt 16) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 0) (tmFiber76StateAt 16)
    (tmFiber76RowAt 16).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 16) (by decide) tmFiber76ReverseRow_16_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_17_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 17) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk8_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 16) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber76ReverseSingleStep17 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 1) (tmFiber76StateAt 17) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 1) (tmFiber76StateAt 17)
    (tmFiber76RowAt 17).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 17) (by decide) tmFiber76ReverseRow_17_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_18_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 18) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk9_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 18) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber76ReverseSingleStep18 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 2) (tmFiber76StateAt 18) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 2) (tmFiber76StateAt 18)
    (tmFiber76RowAt 18).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 18) (by decide) tmFiber76ReverseRow_18_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_19_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 19) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk9_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 18) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber76ReverseSingleStep19 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 3) (tmFiber76StateAt 19) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 3) (tmFiber76StateAt 19)
    (tmFiber76RowAt 19).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 19) (by decide) tmFiber76ReverseRow_19_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_20_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 20) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk10_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 20) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber76ReverseSingleStep20 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 4) (tmFiber76StateAt 20) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 4) (tmFiber76StateAt 20)
    (tmFiber76RowAt 20).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 20) (by decide) tmFiber76ReverseRow_20_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_21_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 21) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk10_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 20) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber76ReverseSingleStep21 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 5) (tmFiber76StateAt 21) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 5) (tmFiber76StateAt 21)
    (tmFiber76RowAt 21).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 21) (by decide) tmFiber76ReverseRow_21_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_22_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 22) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk11_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 22) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber76ReverseSingleStep22 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 6) (tmFiber76StateAt 22) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 6) (tmFiber76StateAt 22)
    (tmFiber76RowAt 22).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 22) (by decide) tmFiber76ReverseRow_22_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_23_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 23) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk11_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 22) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber76ReverseSingleStep23 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 7) (tmFiber76StateAt 23) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 7) (tmFiber76StateAt 23)
    (tmFiber76RowAt 23).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 23) (by decide) tmFiber76ReverseRow_23_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_24_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 24) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk12_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 24) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber76ReverseSingleStep24 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 8) (tmFiber76StateAt 24) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 8) (tmFiber76StateAt 24)
    (tmFiber76RowAt 24).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 24) (by decide) tmFiber76ReverseRow_24_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_25_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 25) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk12_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 24) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber76ReverseSingleStep25 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 9) (tmFiber76StateAt 25) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 9) (tmFiber76StateAt 25)
    (tmFiber76RowAt 25).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 25) (by decide) tmFiber76ReverseRow_25_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_26_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 26) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk13_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 26) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber76ReverseSingleStep26 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 10) (tmFiber76StateAt 26) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 10) (tmFiber76StateAt 26)
    (tmFiber76RowAt 26).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 26) (by decide) tmFiber76ReverseRow_26_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_27_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 27) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk13_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 26) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber76ReverseSingleStep27 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 11) (tmFiber76StateAt 27) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 11) (tmFiber76StateAt 27)
    (tmFiber76RowAt 27).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 27) (by decide) tmFiber76ReverseRow_27_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_28_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 28) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk14_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 28) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber76ReverseSingleStep28 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 12) (tmFiber76StateAt 28) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 12) (tmFiber76StateAt 28)
    (tmFiber76RowAt 28).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 28) (by decide) tmFiber76ReverseRow_28_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_29_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 29) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk14_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 28) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber76ReverseSingleStep29 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 13) (tmFiber76StateAt 29) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 13) (tmFiber76StateAt 29)
    (tmFiber76RowAt 29).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 29) (by decide) tmFiber76ReverseRow_29_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_30_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 30) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk15_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 30) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber76ReverseSingleStep30 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 14) (tmFiber76StateAt 30) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 14) (tmFiber76StateAt 30)
    (tmFiber76RowAt 30).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 30) (by decide) tmFiber76ReverseRow_30_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_31_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 31) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk15_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 30) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber76ReverseSingleStep31 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 15) (tmFiber76StateAt 31) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 15) (tmFiber76StateAt 31)
    (tmFiber76RowAt 31).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 31) (by decide) tmFiber76ReverseRow_31_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_32_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 32) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk16_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 32) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber76ReverseSingleStep32 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 36) (tmFiber76StateAt 32) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 36) (tmFiber76StateAt 32)
    (tmFiber76RowAt 32).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 32) (by decide) tmFiber76ReverseRow_32_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_33_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 33) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk16_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 32) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber76ReverseSingleStep33 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 37) (tmFiber76StateAt 33) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 37) (tmFiber76StateAt 33)
    (tmFiber76RowAt 33).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 33) (by decide) tmFiber76ReverseRow_33_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_34_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 34) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk17_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 34) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber76ReverseSingleStep34 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 20) (tmFiber76StateAt 34) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 20) (tmFiber76StateAt 34)
    (tmFiber76RowAt 34).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 34) (by decide) tmFiber76ReverseRow_34_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_35_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 35) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk17_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 34) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber76ReverseSingleStep35 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 21) (tmFiber76StateAt 35) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 21) (tmFiber76StateAt 35)
    (tmFiber76RowAt 35).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 35) (by decide) tmFiber76ReverseRow_35_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_36_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 36) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk18_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 36) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber76ReverseSingleStep36 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 16) (tmFiber76StateAt 36) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 16) (tmFiber76StateAt 36)
    (tmFiber76RowAt 36).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 36) (by decide) tmFiber76ReverseRow_36_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_37_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 37) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk18_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 36) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber76ReverseSingleStep37 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 17) (tmFiber76StateAt 37) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 17) (tmFiber76StateAt 37)
    (tmFiber76RowAt 37).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 37) (by decide) tmFiber76ReverseRow_37_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_38_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 38) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk19_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 38) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber76ReverseSingleStep38 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 18) (tmFiber76StateAt 38) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 18) (tmFiber76StateAt 38)
    (tmFiber76RowAt 38).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 38) (by decide) tmFiber76ReverseRow_38_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_39_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 39) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk19_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 38) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber76ReverseSingleStep39 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 19) (tmFiber76StateAt 39) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 19) (tmFiber76StateAt 39)
    (tmFiber76RowAt 39).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 39) (by decide) tmFiber76ReverseRow_39_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_40_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 40) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk20_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 40) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber76ReverseSingleStep40 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 44) (tmFiber76StateAt 40) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 44) (tmFiber76StateAt 40)
    (tmFiber76RowAt 40).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 40) (by decide) tmFiber76ReverseRow_40_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_41_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 41) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk20_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 40) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber76ReverseSingleStep41 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 45) (tmFiber76StateAt 41) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 45) (tmFiber76StateAt 41)
    (tmFiber76RowAt 41).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 41) (by decide) tmFiber76ReverseRow_41_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_42_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 42) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk21_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 42) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber76ReverseSingleStep42 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 58) (tmFiber76StateAt 42) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 58) (tmFiber76StateAt 42)
    (tmFiber76RowAt 42).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 42) (by decide) tmFiber76ReverseRow_42_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_43_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 43) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk21_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 42) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber76ReverseSingleStep43 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 59) (tmFiber76StateAt 43) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 59) (tmFiber76StateAt 43)
    (tmFiber76RowAt 43).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 43) (by decide) tmFiber76ReverseRow_43_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_44_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 44) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk22_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 44) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber76ReverseSingleStep44 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 60) (tmFiber76StateAt 44) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 60) (tmFiber76StateAt 44)
    (tmFiber76RowAt 44).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 44) (by decide) tmFiber76ReverseRow_44_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_45_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 45) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk22_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 44) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber76ReverseSingleStep45 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 61) (tmFiber76StateAt 45) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 61) (tmFiber76StateAt 45)
    (tmFiber76RowAt 45).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 45) (by decide) tmFiber76ReverseRow_45_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_46_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 46) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk23_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 46) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber76ReverseSingleStep46 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 62) (tmFiber76StateAt 46) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 62) (tmFiber76StateAt 46)
    (tmFiber76RowAt 46).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 46) (by decide) tmFiber76ReverseRow_46_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_47_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 47) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk23_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 46) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber76ReverseSingleStep47 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 63) (tmFiber76StateAt 47) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 63) (tmFiber76StateAt 47)
    (tmFiber76RowAt 47).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 47) (by decide) tmFiber76ReverseRow_47_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_48_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 48) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk24_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 48) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber76ReverseSingleStep48 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 52) (tmFiber76StateAt 48) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 52) (tmFiber76StateAt 48)
    (tmFiber76RowAt 48).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 48) (by decide) tmFiber76ReverseRow_48_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_49_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 49) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk24_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 48) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber76ReverseSingleStep49 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 53) (tmFiber76StateAt 49) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 53) (tmFiber76StateAt 49)
    (tmFiber76RowAt 49).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 49) (by decide) tmFiber76ReverseRow_49_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_50_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 50) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk25_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 50) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber76ReverseSingleStep50 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 12) (tmFiber76StateAt 50) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 12) (tmFiber76StateAt 50)
    (tmFiber76RowAt 50).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 50) (by decide) tmFiber76ReverseRow_50_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_51_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 51) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk25_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 50) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber76ReverseSingleStep51 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 13) (tmFiber76StateAt 51) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 13) (tmFiber76StateAt 51)
    (tmFiber76RowAt 51).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 51) (by decide) tmFiber76ReverseRow_51_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_52_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 52) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk26_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 52) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber76ReverseSingleStep52 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 8) (tmFiber76StateAt 52) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 8) (tmFiber76StateAt 52)
    (tmFiber76RowAt 52).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 52) (by decide) tmFiber76ReverseRow_52_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_53_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 53) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk26_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 52) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber76ReverseSingleStep53 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 9) (tmFiber76StateAt 53) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 9) (tmFiber76StateAt 53)
    (tmFiber76RowAt 53).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 53) (by decide) tmFiber76ReverseRow_53_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_54_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 54) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk27_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 54) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber76ReverseSingleStep54 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 10) (tmFiber76StateAt 54) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 10) (tmFiber76StateAt 54)
    (tmFiber76RowAt 54).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 54) (by decide) tmFiber76ReverseRow_54_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_55_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 55) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk27_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 54) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber76ReverseSingleStep55 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 11) (tmFiber76StateAt 55) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 11) (tmFiber76StateAt 55)
    (tmFiber76RowAt 55).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 55) (by decide) tmFiber76ReverseRow_55_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_56_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 56) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk28_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 56) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber76ReverseSingleStep56 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 60) (tmFiber76StateAt 56) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 60) (tmFiber76StateAt 56)
    (tmFiber76RowAt 56).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 56) (by decide) tmFiber76ReverseRow_56_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_57_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 57) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk28_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 56) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber76ReverseSingleStep57 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 61) (tmFiber76StateAt 57) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 61) (tmFiber76StateAt 57)
    (tmFiber76RowAt 57).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 57) (by decide) tmFiber76ReverseRow_57_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_58_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 58) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk29_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 58) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber76ReverseSingleStep58 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 4) (tmFiber76StateAt 58) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 4) (tmFiber76StateAt 58)
    (tmFiber76RowAt 58).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 58) (by decide) tmFiber76ReverseRow_58_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_59_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 59) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk29_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 58) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber76ReverseSingleStep59 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 5) (tmFiber76StateAt 59) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 5) (tmFiber76StateAt 59)
    (tmFiber76RowAt 59).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 59) (by decide) tmFiber76ReverseRow_59_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_60_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 60) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk30_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 60) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber76ReverseSingleStep60 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 0) (tmFiber76StateAt 60) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 0) (tmFiber76StateAt 60)
    (tmFiber76RowAt 60).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 60) (by decide) tmFiber76ReverseRow_60_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_61_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 61) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk30_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 60) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber76ReverseSingleStep61 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 1) (tmFiber76StateAt 61) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 1) (tmFiber76StateAt 61)
    (tmFiber76RowAt 61).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 61) (by decide) tmFiber76ReverseRow_61_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_62_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 62) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk31_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 62) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber76ReverseSingleStep62 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 2) (tmFiber76StateAt 62) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 2) (tmFiber76StateAt 62)
    (tmFiber76RowAt 62).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 62) (by decide) tmFiber76ReverseRow_62_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76ReverseRow_63_ok :
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 63) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber76Chunk31_ok
  change (tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 62) &&
    tmRowReverseValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber76ReverseSingleStep63 :
    chainSingleKempeStep tmWord (tmFiber76StateAt 3) (tmFiber76StateAt 63) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber76StateAt 3) (tmFiber76StateAt 63)
    (tmFiber76RowAt 63).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber76Key tmFiber76Expected
        (tmFiber76RowAt 63) (by decide) tmFiber76ReverseRow_63_ok
      simpa [tmFiber76StateAt, tmFiber76RowAt, tmFiber76Rows, listGetD, directRow] using h)

theorem tmFiber76State1_in_pass1_prefix1 :
    tmFiber76StateAt 1 ∈ chainClosureStep tmWord tmFiber76Prefix1 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 0 ∈
      chainClosureStep tmWord tmFiber76Prefix0 ([tmFiber76StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber76Prefix0
      ([tmFiber76StateAt 0]) (tmFiber76StateAt 0) (by simp)
  rw [show tmFiber76Prefix1 = tmFiber76Prefix0 ++ [tmFiber76StateAt 1] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 1) []
    (chainClosureStep tmWord tmFiber76Prefix0 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 0) hparentBefore tmFiber76ReverseSingleStep1

theorem tmFiber76State1_in_pass1_full :
    tmFiber76StateAt 1 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix1 ++ [tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix1 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 1) tmFiber76State1_in_pass1_prefix1

theorem tmFiber76State2_in_pass1_prefix2 :
    tmFiber76StateAt 2 ∈ chainClosureStep tmWord tmFiber76Prefix2 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 1 ∈
      chainClosureStep tmWord tmFiber76Prefix1 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix1 = tmFiber76Prefix1 ++ [] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord []
      (chainClosureStep tmWord tmFiber76Prefix1 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 1) tmFiber76State1_in_pass1_prefix1
  rw [show tmFiber76Prefix2 = tmFiber76Prefix1 ++ [tmFiber76StateAt 2] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 2) []
    (chainClosureStep tmWord tmFiber76Prefix1 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 1) hparentBefore tmFiber76ReverseSingleStep2

theorem tmFiber76State2_in_pass1_full :
    tmFiber76StateAt 2 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix2 ++ [tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix2 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 2) tmFiber76State2_in_pass1_prefix2

theorem tmFiber76State3_in_pass1_prefix3 :
    tmFiber76StateAt 3 ∈ chainClosureStep tmWord tmFiber76Prefix3 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 0 ∈
      chainClosureStep tmWord tmFiber76Prefix2 ([tmFiber76StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber76Prefix2
      ([tmFiber76StateAt 0]) (tmFiber76StateAt 0) (by simp)
  rw [show tmFiber76Prefix3 = tmFiber76Prefix2 ++ [tmFiber76StateAt 3] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 3) []
    (chainClosureStep tmWord tmFiber76Prefix2 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 0) hparentBefore tmFiber76ReverseSingleStep3

theorem tmFiber76State3_in_pass1_full :
    tmFiber76StateAt 3 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix3 ++ [tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix3 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 3) tmFiber76State3_in_pass1_prefix3

theorem tmFiber76State4_in_pass1_prefix4 :
    tmFiber76StateAt 4 ∈ chainClosureStep tmWord tmFiber76Prefix4 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 0 ∈
      chainClosureStep tmWord tmFiber76Prefix3 ([tmFiber76StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber76Prefix3
      ([tmFiber76StateAt 0]) (tmFiber76StateAt 0) (by simp)
  rw [show tmFiber76Prefix4 = tmFiber76Prefix3 ++ [tmFiber76StateAt 4] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 4) []
    (chainClosureStep tmWord tmFiber76Prefix3 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 0) hparentBefore tmFiber76ReverseSingleStep4

theorem tmFiber76State4_in_pass1_full :
    tmFiber76StateAt 4 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix4 ++ [tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix4 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 4) tmFiber76State4_in_pass1_prefix4

theorem tmFiber76State5_in_pass1_prefix5 :
    tmFiber76StateAt 5 ∈ chainClosureStep tmWord tmFiber76Prefix5 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 1 ∈
      chainClosureStep tmWord tmFiber76Prefix4 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix4 = tmFiber76Prefix1 ++ [tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4]
      (chainClosureStep tmWord tmFiber76Prefix1 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 1) tmFiber76State1_in_pass1_prefix1
  rw [show tmFiber76Prefix5 = tmFiber76Prefix4 ++ [tmFiber76StateAt 5] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 5) []
    (chainClosureStep tmWord tmFiber76Prefix4 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 1) hparentBefore tmFiber76ReverseSingleStep5

theorem tmFiber76State5_in_pass1_full :
    tmFiber76StateAt 5 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix5 ++ [tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix5 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 5) tmFiber76State5_in_pass1_prefix5

theorem tmFiber76State6_in_pass1_prefix6 :
    tmFiber76StateAt 6 ∈ chainClosureStep tmWord tmFiber76Prefix6 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 4 ∈
      chainClosureStep tmWord tmFiber76Prefix5 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix5 = tmFiber76Prefix4 ++ [tmFiber76StateAt 5] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 5]
      (chainClosureStep tmWord tmFiber76Prefix4 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 4) tmFiber76State4_in_pass1_prefix4
  rw [show tmFiber76Prefix6 = tmFiber76Prefix5 ++ [tmFiber76StateAt 6] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 6) []
    (chainClosureStep tmWord tmFiber76Prefix5 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 4) hparentBefore tmFiber76ReverseSingleStep6

theorem tmFiber76State6_in_pass1_full :
    tmFiber76StateAt 6 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix6 ++ [tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix6 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 6) tmFiber76State6_in_pass1_prefix6

theorem tmFiber76State7_in_pass1_prefix7 :
    tmFiber76StateAt 7 ∈ chainClosureStep tmWord tmFiber76Prefix7 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 3 ∈
      chainClosureStep tmWord tmFiber76Prefix6 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix6 = tmFiber76Prefix3 ++ [tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6]
      (chainClosureStep tmWord tmFiber76Prefix3 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 3) tmFiber76State3_in_pass1_prefix3
  rw [show tmFiber76Prefix7 = tmFiber76Prefix6 ++ [tmFiber76StateAt 7] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 7) []
    (chainClosureStep tmWord tmFiber76Prefix6 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 3) hparentBefore tmFiber76ReverseSingleStep7

theorem tmFiber76State7_in_pass1_full :
    tmFiber76StateAt 7 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix7 ++ [tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix7 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 7) tmFiber76State7_in_pass1_prefix7

theorem tmFiber76State8_in_pass1_prefix8 :
    tmFiber76StateAt 8 ∈ chainClosureStep tmWord tmFiber76Prefix8 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 0 ∈
      chainClosureStep tmWord tmFiber76Prefix7 ([tmFiber76StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber76Prefix7
      ([tmFiber76StateAt 0]) (tmFiber76StateAt 0) (by simp)
  rw [show tmFiber76Prefix8 = tmFiber76Prefix7 ++ [tmFiber76StateAt 8] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 8) []
    (chainClosureStep tmWord tmFiber76Prefix7 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 0) hparentBefore tmFiber76ReverseSingleStep8

theorem tmFiber76State8_in_pass1_full :
    tmFiber76StateAt 8 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix8 ++ [tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix8 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 8) tmFiber76State8_in_pass1_prefix8

theorem tmFiber76State9_in_pass1_prefix9 :
    tmFiber76StateAt 9 ∈ chainClosureStep tmWord tmFiber76Prefix9 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 1 ∈
      chainClosureStep tmWord tmFiber76Prefix8 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix8 = tmFiber76Prefix1 ++ [tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8]
      (chainClosureStep tmWord tmFiber76Prefix1 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 1) tmFiber76State1_in_pass1_prefix1
  rw [show tmFiber76Prefix9 = tmFiber76Prefix8 ++ [tmFiber76StateAt 9] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 9) []
    (chainClosureStep tmWord tmFiber76Prefix8 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 1) hparentBefore tmFiber76ReverseSingleStep9

theorem tmFiber76State9_in_pass1_full :
    tmFiber76StateAt 9 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix9 ++ [tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix9 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 9) tmFiber76State9_in_pass1_prefix9

theorem tmFiber76State10_in_pass1_prefix10 :
    tmFiber76StateAt 10 ∈ chainClosureStep tmWord tmFiber76Prefix10 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 2 ∈
      chainClosureStep tmWord tmFiber76Prefix9 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix9 = tmFiber76Prefix2 ++ [tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9]
      (chainClosureStep tmWord tmFiber76Prefix2 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 2) tmFiber76State2_in_pass1_prefix2
  rw [show tmFiber76Prefix10 = tmFiber76Prefix9 ++ [tmFiber76StateAt 10] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 10) []
    (chainClosureStep tmWord tmFiber76Prefix9 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 2) hparentBefore tmFiber76ReverseSingleStep10

theorem tmFiber76State10_in_pass1_full :
    tmFiber76StateAt 10 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix10 ++ [tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix10 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 10) tmFiber76State10_in_pass1_prefix10

theorem tmFiber76State11_in_pass1_prefix11 :
    tmFiber76StateAt 11 ∈ chainClosureStep tmWord tmFiber76Prefix11 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 3 ∈
      chainClosureStep tmWord tmFiber76Prefix10 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix10 = tmFiber76Prefix3 ++ [tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10]
      (chainClosureStep tmWord tmFiber76Prefix3 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 3) tmFiber76State3_in_pass1_prefix3
  rw [show tmFiber76Prefix11 = tmFiber76Prefix10 ++ [tmFiber76StateAt 11] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 11) []
    (chainClosureStep tmWord tmFiber76Prefix10 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 3) hparentBefore tmFiber76ReverseSingleStep11

theorem tmFiber76State11_in_pass1_full :
    tmFiber76StateAt 11 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix11 ++ [tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix11 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 11) tmFiber76State11_in_pass1_prefix11

theorem tmFiber76State12_in_pass1_prefix12 :
    tmFiber76StateAt 12 ∈ chainClosureStep tmWord tmFiber76Prefix12 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 4 ∈
      chainClosureStep tmWord tmFiber76Prefix11 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix11 = tmFiber76Prefix4 ++ [tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11]
      (chainClosureStep tmWord tmFiber76Prefix4 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 4) tmFiber76State4_in_pass1_prefix4
  rw [show tmFiber76Prefix12 = tmFiber76Prefix11 ++ [tmFiber76StateAt 12] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 12) []
    (chainClosureStep tmWord tmFiber76Prefix11 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 4) hparentBefore tmFiber76ReverseSingleStep12

theorem tmFiber76State12_in_pass1_full :
    tmFiber76StateAt 12 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix12 ++ [tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix12 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 12) tmFiber76State12_in_pass1_prefix12

theorem tmFiber76State13_in_pass1_prefix13 :
    tmFiber76StateAt 13 ∈ chainClosureStep tmWord tmFiber76Prefix13 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 5 ∈
      chainClosureStep tmWord tmFiber76Prefix12 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix12 = tmFiber76Prefix5 ++ [tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12]
      (chainClosureStep tmWord tmFiber76Prefix5 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 5) tmFiber76State5_in_pass1_prefix5
  rw [show tmFiber76Prefix13 = tmFiber76Prefix12 ++ [tmFiber76StateAt 13] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 13) []
    (chainClosureStep tmWord tmFiber76Prefix12 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 5) hparentBefore tmFiber76ReverseSingleStep13

theorem tmFiber76State13_in_pass1_full :
    tmFiber76StateAt 13 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix13 ++ [tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix13 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 13) tmFiber76State13_in_pass1_prefix13

theorem tmFiber76State14_in_pass1_prefix14 :
    tmFiber76StateAt 14 ∈ chainClosureStep tmWord tmFiber76Prefix14 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 6 ∈
      chainClosureStep tmWord tmFiber76Prefix13 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix13 = tmFiber76Prefix6 ++ [tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13]
      (chainClosureStep tmWord tmFiber76Prefix6 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 6) tmFiber76State6_in_pass1_prefix6
  rw [show tmFiber76Prefix14 = tmFiber76Prefix13 ++ [tmFiber76StateAt 14] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 14) []
    (chainClosureStep tmWord tmFiber76Prefix13 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 6) hparentBefore tmFiber76ReverseSingleStep14

theorem tmFiber76State14_in_pass1_full :
    tmFiber76StateAt 14 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix14 ++ [tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix14 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 14) tmFiber76State14_in_pass1_prefix14

theorem tmFiber76State15_in_pass1_prefix15 :
    tmFiber76StateAt 15 ∈ chainClosureStep tmWord tmFiber76Prefix15 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 7 ∈
      chainClosureStep tmWord tmFiber76Prefix14 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix14 = tmFiber76Prefix7 ++ [tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14]
      (chainClosureStep tmWord tmFiber76Prefix7 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 7) tmFiber76State7_in_pass1_prefix7
  rw [show tmFiber76Prefix15 = tmFiber76Prefix14 ++ [tmFiber76StateAt 15] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 15) []
    (chainClosureStep tmWord tmFiber76Prefix14 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 7) hparentBefore tmFiber76ReverseSingleStep15

theorem tmFiber76State15_in_pass1_full :
    tmFiber76StateAt 15 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix15 ++ [tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix15 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 15) tmFiber76State15_in_pass1_prefix15

theorem tmFiber76State16_in_pass1_prefix16 :
    tmFiber76StateAt 16 ∈ chainClosureStep tmWord tmFiber76Prefix16 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 0 ∈
      chainClosureStep tmWord tmFiber76Prefix15 ([tmFiber76StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber76Prefix15
      ([tmFiber76StateAt 0]) (tmFiber76StateAt 0) (by simp)
  rw [show tmFiber76Prefix16 = tmFiber76Prefix15 ++ [tmFiber76StateAt 16] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 16) []
    (chainClosureStep tmWord tmFiber76Prefix15 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 0) hparentBefore tmFiber76ReverseSingleStep16

theorem tmFiber76State16_in_pass1_full :
    tmFiber76StateAt 16 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix16 ++ [tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix16 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 16) tmFiber76State16_in_pass1_prefix16

theorem tmFiber76State17_in_pass1_prefix17 :
    tmFiber76StateAt 17 ∈ chainClosureStep tmWord tmFiber76Prefix17 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 1 ∈
      chainClosureStep tmWord tmFiber76Prefix16 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix16 = tmFiber76Prefix1 ++ [tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16]
      (chainClosureStep tmWord tmFiber76Prefix1 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 1) tmFiber76State1_in_pass1_prefix1
  rw [show tmFiber76Prefix17 = tmFiber76Prefix16 ++ [tmFiber76StateAt 17] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 17) []
    (chainClosureStep tmWord tmFiber76Prefix16 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 1) hparentBefore tmFiber76ReverseSingleStep17

theorem tmFiber76State17_in_pass1_full :
    tmFiber76StateAt 17 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix17 ++ [tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix17 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 17) tmFiber76State17_in_pass1_prefix17

theorem tmFiber76State18_in_pass1_prefix18 :
    tmFiber76StateAt 18 ∈ chainClosureStep tmWord tmFiber76Prefix18 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 2 ∈
      chainClosureStep tmWord tmFiber76Prefix17 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix17 = tmFiber76Prefix2 ++ [tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17]
      (chainClosureStep tmWord tmFiber76Prefix2 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 2) tmFiber76State2_in_pass1_prefix2
  rw [show tmFiber76Prefix18 = tmFiber76Prefix17 ++ [tmFiber76StateAt 18] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 18) []
    (chainClosureStep tmWord tmFiber76Prefix17 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 2) hparentBefore tmFiber76ReverseSingleStep18

theorem tmFiber76State18_in_pass1_full :
    tmFiber76StateAt 18 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix18 ++ [tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix18 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 18) tmFiber76State18_in_pass1_prefix18

theorem tmFiber76State19_in_pass1_prefix19 :
    tmFiber76StateAt 19 ∈ chainClosureStep tmWord tmFiber76Prefix19 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 3 ∈
      chainClosureStep tmWord tmFiber76Prefix18 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix18 = tmFiber76Prefix3 ++ [tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18]
      (chainClosureStep tmWord tmFiber76Prefix3 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 3) tmFiber76State3_in_pass1_prefix3
  rw [show tmFiber76Prefix19 = tmFiber76Prefix18 ++ [tmFiber76StateAt 19] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 19) []
    (chainClosureStep tmWord tmFiber76Prefix18 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 3) hparentBefore tmFiber76ReverseSingleStep19

theorem tmFiber76State19_in_pass1_full :
    tmFiber76StateAt 19 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix19 ++ [tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix19 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 19) tmFiber76State19_in_pass1_prefix19

theorem tmFiber76State20_in_pass1_prefix20 :
    tmFiber76StateAt 20 ∈ chainClosureStep tmWord tmFiber76Prefix20 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 4 ∈
      chainClosureStep tmWord tmFiber76Prefix19 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix19 = tmFiber76Prefix4 ++ [tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19]
      (chainClosureStep tmWord tmFiber76Prefix4 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 4) tmFiber76State4_in_pass1_prefix4
  rw [show tmFiber76Prefix20 = tmFiber76Prefix19 ++ [tmFiber76StateAt 20] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 20) []
    (chainClosureStep tmWord tmFiber76Prefix19 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 4) hparentBefore tmFiber76ReverseSingleStep20

theorem tmFiber76State20_in_pass1_full :
    tmFiber76StateAt 20 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix20 ++ [tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix20 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 20) tmFiber76State20_in_pass1_prefix20

theorem tmFiber76State21_in_pass1_prefix21 :
    tmFiber76StateAt 21 ∈ chainClosureStep tmWord tmFiber76Prefix21 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 5 ∈
      chainClosureStep tmWord tmFiber76Prefix20 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix20 = tmFiber76Prefix5 ++ [tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20]
      (chainClosureStep tmWord tmFiber76Prefix5 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 5) tmFiber76State5_in_pass1_prefix5
  rw [show tmFiber76Prefix21 = tmFiber76Prefix20 ++ [tmFiber76StateAt 21] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 21) []
    (chainClosureStep tmWord tmFiber76Prefix20 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 5) hparentBefore tmFiber76ReverseSingleStep21

theorem tmFiber76State21_in_pass1_full :
    tmFiber76StateAt 21 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix21 ++ [tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix21 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 21) tmFiber76State21_in_pass1_prefix21

theorem tmFiber76State22_in_pass1_prefix22 :
    tmFiber76StateAt 22 ∈ chainClosureStep tmWord tmFiber76Prefix22 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 6 ∈
      chainClosureStep tmWord tmFiber76Prefix21 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix21 = tmFiber76Prefix6 ++ [tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21]
      (chainClosureStep tmWord tmFiber76Prefix6 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 6) tmFiber76State6_in_pass1_prefix6
  rw [show tmFiber76Prefix22 = tmFiber76Prefix21 ++ [tmFiber76StateAt 22] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 22) []
    (chainClosureStep tmWord tmFiber76Prefix21 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 6) hparentBefore tmFiber76ReverseSingleStep22

theorem tmFiber76State22_in_pass1_full :
    tmFiber76StateAt 22 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix22 ++ [tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix22 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 22) tmFiber76State22_in_pass1_prefix22

theorem tmFiber76State23_in_pass1_prefix23 :
    tmFiber76StateAt 23 ∈ chainClosureStep tmWord tmFiber76Prefix23 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 7 ∈
      chainClosureStep tmWord tmFiber76Prefix22 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix22 = tmFiber76Prefix7 ++ [tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22]
      (chainClosureStep tmWord tmFiber76Prefix7 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 7) tmFiber76State7_in_pass1_prefix7
  rw [show tmFiber76Prefix23 = tmFiber76Prefix22 ++ [tmFiber76StateAt 23] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 23) []
    (chainClosureStep tmWord tmFiber76Prefix22 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 7) hparentBefore tmFiber76ReverseSingleStep23

theorem tmFiber76State23_in_pass1_full :
    tmFiber76StateAt 23 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix23 ++ [tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix23 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 23) tmFiber76State23_in_pass1_prefix23

theorem tmFiber76State24_in_pass1_prefix24 :
    tmFiber76StateAt 24 ∈ chainClosureStep tmWord tmFiber76Prefix24 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 8 ∈
      chainClosureStep tmWord tmFiber76Prefix23 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix23 = tmFiber76Prefix8 ++ [tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23]
      (chainClosureStep tmWord tmFiber76Prefix8 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 8) tmFiber76State8_in_pass1_prefix8
  rw [show tmFiber76Prefix24 = tmFiber76Prefix23 ++ [tmFiber76StateAt 24] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 24) []
    (chainClosureStep tmWord tmFiber76Prefix23 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 8) hparentBefore tmFiber76ReverseSingleStep24

theorem tmFiber76State24_in_pass1_full :
    tmFiber76StateAt 24 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix24 ++ [tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix24 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 24) tmFiber76State24_in_pass1_prefix24

theorem tmFiber76State25_in_pass1_prefix25 :
    tmFiber76StateAt 25 ∈ chainClosureStep tmWord tmFiber76Prefix25 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 9 ∈
      chainClosureStep tmWord tmFiber76Prefix24 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix24 = tmFiber76Prefix9 ++ [tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24]
      (chainClosureStep tmWord tmFiber76Prefix9 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 9) tmFiber76State9_in_pass1_prefix9
  rw [show tmFiber76Prefix25 = tmFiber76Prefix24 ++ [tmFiber76StateAt 25] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 25) []
    (chainClosureStep tmWord tmFiber76Prefix24 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 9) hparentBefore tmFiber76ReverseSingleStep25

theorem tmFiber76State25_in_pass1_full :
    tmFiber76StateAt 25 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix25 ++ [tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix25 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 25) tmFiber76State25_in_pass1_prefix25

theorem tmFiber76State26_in_pass1_prefix26 :
    tmFiber76StateAt 26 ∈ chainClosureStep tmWord tmFiber76Prefix26 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 10 ∈
      chainClosureStep tmWord tmFiber76Prefix25 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix25 = tmFiber76Prefix10 ++ [tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25]
      (chainClosureStep tmWord tmFiber76Prefix10 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 10) tmFiber76State10_in_pass1_prefix10
  rw [show tmFiber76Prefix26 = tmFiber76Prefix25 ++ [tmFiber76StateAt 26] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 26) []
    (chainClosureStep tmWord tmFiber76Prefix25 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 10) hparentBefore tmFiber76ReverseSingleStep26

theorem tmFiber76State26_in_pass1_full :
    tmFiber76StateAt 26 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix26 ++ [tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix26 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 26) tmFiber76State26_in_pass1_prefix26

theorem tmFiber76State27_in_pass1_prefix27 :
    tmFiber76StateAt 27 ∈ chainClosureStep tmWord tmFiber76Prefix27 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 11 ∈
      chainClosureStep tmWord tmFiber76Prefix26 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix26 = tmFiber76Prefix11 ++ [tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26]
      (chainClosureStep tmWord tmFiber76Prefix11 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 11) tmFiber76State11_in_pass1_prefix11
  rw [show tmFiber76Prefix27 = tmFiber76Prefix26 ++ [tmFiber76StateAt 27] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 27) []
    (chainClosureStep tmWord tmFiber76Prefix26 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 11) hparentBefore tmFiber76ReverseSingleStep27

theorem tmFiber76State27_in_pass1_full :
    tmFiber76StateAt 27 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix27 ++ [tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix27 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 27) tmFiber76State27_in_pass1_prefix27

theorem tmFiber76State28_in_pass1_prefix28 :
    tmFiber76StateAt 28 ∈ chainClosureStep tmWord tmFiber76Prefix28 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 12 ∈
      chainClosureStep tmWord tmFiber76Prefix27 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix27 = tmFiber76Prefix12 ++ [tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27]
      (chainClosureStep tmWord tmFiber76Prefix12 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 12) tmFiber76State12_in_pass1_prefix12
  rw [show tmFiber76Prefix28 = tmFiber76Prefix27 ++ [tmFiber76StateAt 28] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 28) []
    (chainClosureStep tmWord tmFiber76Prefix27 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 12) hparentBefore tmFiber76ReverseSingleStep28

theorem tmFiber76State28_in_pass1_full :
    tmFiber76StateAt 28 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix28 ++ [tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix28 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 28) tmFiber76State28_in_pass1_prefix28

theorem tmFiber76State29_in_pass1_prefix29 :
    tmFiber76StateAt 29 ∈ chainClosureStep tmWord tmFiber76Prefix29 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 13 ∈
      chainClosureStep tmWord tmFiber76Prefix28 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix28 = tmFiber76Prefix13 ++ [tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28]
      (chainClosureStep tmWord tmFiber76Prefix13 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 13) tmFiber76State13_in_pass1_prefix13
  rw [show tmFiber76Prefix29 = tmFiber76Prefix28 ++ [tmFiber76StateAt 29] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 29) []
    (chainClosureStep tmWord tmFiber76Prefix28 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 13) hparentBefore tmFiber76ReverseSingleStep29

theorem tmFiber76State29_in_pass1_full :
    tmFiber76StateAt 29 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix29 ++ [tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix29 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 29) tmFiber76State29_in_pass1_prefix29

theorem tmFiber76State30_in_pass1_prefix30 :
    tmFiber76StateAt 30 ∈ chainClosureStep tmWord tmFiber76Prefix30 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 14 ∈
      chainClosureStep tmWord tmFiber76Prefix29 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix29 = tmFiber76Prefix14 ++ [tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29]
      (chainClosureStep tmWord tmFiber76Prefix14 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 14) tmFiber76State14_in_pass1_prefix14
  rw [show tmFiber76Prefix30 = tmFiber76Prefix29 ++ [tmFiber76StateAt 30] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 30) []
    (chainClosureStep tmWord tmFiber76Prefix29 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 14) hparentBefore tmFiber76ReverseSingleStep30

theorem tmFiber76State30_in_pass1_full :
    tmFiber76StateAt 30 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix30 ++ [tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix30 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 30) tmFiber76State30_in_pass1_prefix30

theorem tmFiber76State31_in_pass1_prefix31 :
    tmFiber76StateAt 31 ∈ chainClosureStep tmWord tmFiber76Prefix31 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 15 ∈
      chainClosureStep tmWord tmFiber76Prefix30 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix30 = tmFiber76Prefix15 ++ [tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30]
      (chainClosureStep tmWord tmFiber76Prefix15 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 15) tmFiber76State15_in_pass1_prefix15
  rw [show tmFiber76Prefix31 = tmFiber76Prefix30 ++ [tmFiber76StateAt 31] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 31) []
    (chainClosureStep tmWord tmFiber76Prefix30 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 15) hparentBefore tmFiber76ReverseSingleStep31

theorem tmFiber76State31_in_pass1_full :
    tmFiber76StateAt 31 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix31 ++ [tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix31 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 31) tmFiber76State31_in_pass1_prefix31

theorem tmFiber76State34_in_pass1_prefix34 :
    tmFiber76StateAt 34 ∈ chainClosureStep tmWord tmFiber76Prefix34 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 20 ∈
      chainClosureStep tmWord tmFiber76Prefix33 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix33 = tmFiber76Prefix20 ++ [tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33]
      (chainClosureStep tmWord tmFiber76Prefix20 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 20) tmFiber76State20_in_pass1_prefix20
  rw [show tmFiber76Prefix34 = tmFiber76Prefix33 ++ [tmFiber76StateAt 34] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 34) []
    (chainClosureStep tmWord tmFiber76Prefix33 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 20) hparentBefore tmFiber76ReverseSingleStep34

theorem tmFiber76State34_in_pass1_full :
    tmFiber76StateAt 34 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix34 ++ [tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix34 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 34) tmFiber76State34_in_pass1_prefix34

theorem tmFiber76State35_in_pass1_prefix35 :
    tmFiber76StateAt 35 ∈ chainClosureStep tmWord tmFiber76Prefix35 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 21 ∈
      chainClosureStep tmWord tmFiber76Prefix34 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix34 = tmFiber76Prefix21 ++ [tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34]
      (chainClosureStep tmWord tmFiber76Prefix21 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 21) tmFiber76State21_in_pass1_prefix21
  rw [show tmFiber76Prefix35 = tmFiber76Prefix34 ++ [tmFiber76StateAt 35] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 35) []
    (chainClosureStep tmWord tmFiber76Prefix34 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 21) hparentBefore tmFiber76ReverseSingleStep35

theorem tmFiber76State35_in_pass1_full :
    tmFiber76StateAt 35 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix35 ++ [tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix35 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 35) tmFiber76State35_in_pass1_prefix35

theorem tmFiber76State36_in_pass1_prefix36 :
    tmFiber76StateAt 36 ∈ chainClosureStep tmWord tmFiber76Prefix36 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 16 ∈
      chainClosureStep tmWord tmFiber76Prefix35 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix35 = tmFiber76Prefix16 ++ [tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35]
      (chainClosureStep tmWord tmFiber76Prefix16 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 16) tmFiber76State16_in_pass1_prefix16
  rw [show tmFiber76Prefix36 = tmFiber76Prefix35 ++ [tmFiber76StateAt 36] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 36) []
    (chainClosureStep tmWord tmFiber76Prefix35 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 16) hparentBefore tmFiber76ReverseSingleStep36

theorem tmFiber76State36_in_pass1_full :
    tmFiber76StateAt 36 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix36 ++ [tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix36 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 36) tmFiber76State36_in_pass1_prefix36

theorem tmFiber76State37_in_pass1_prefix37 :
    tmFiber76StateAt 37 ∈ chainClosureStep tmWord tmFiber76Prefix37 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 17 ∈
      chainClosureStep tmWord tmFiber76Prefix36 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix36 = tmFiber76Prefix17 ++ [tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36]
      (chainClosureStep tmWord tmFiber76Prefix17 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 17) tmFiber76State17_in_pass1_prefix17
  rw [show tmFiber76Prefix37 = tmFiber76Prefix36 ++ [tmFiber76StateAt 37] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 37) []
    (chainClosureStep tmWord tmFiber76Prefix36 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 17) hparentBefore tmFiber76ReverseSingleStep37

theorem tmFiber76State37_in_pass1_full :
    tmFiber76StateAt 37 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix37 ++ [tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix37 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 37) tmFiber76State37_in_pass1_prefix37

theorem tmFiber76State38_in_pass1_prefix38 :
    tmFiber76StateAt 38 ∈ chainClosureStep tmWord tmFiber76Prefix38 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 18 ∈
      chainClosureStep tmWord tmFiber76Prefix37 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix37 = tmFiber76Prefix18 ++ [tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37]
      (chainClosureStep tmWord tmFiber76Prefix18 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 18) tmFiber76State18_in_pass1_prefix18
  rw [show tmFiber76Prefix38 = tmFiber76Prefix37 ++ [tmFiber76StateAt 38] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 38) []
    (chainClosureStep tmWord tmFiber76Prefix37 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 18) hparentBefore tmFiber76ReverseSingleStep38

theorem tmFiber76State38_in_pass1_full :
    tmFiber76StateAt 38 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix38 ++ [tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix38 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 38) tmFiber76State38_in_pass1_prefix38

theorem tmFiber76State39_in_pass1_prefix39 :
    tmFiber76StateAt 39 ∈ chainClosureStep tmWord tmFiber76Prefix39 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 19 ∈
      chainClosureStep tmWord tmFiber76Prefix38 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix38 = tmFiber76Prefix19 ++ [tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38]
      (chainClosureStep tmWord tmFiber76Prefix19 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 19) tmFiber76State19_in_pass1_prefix19
  rw [show tmFiber76Prefix39 = tmFiber76Prefix38 ++ [tmFiber76StateAt 39] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 39) []
    (chainClosureStep tmWord tmFiber76Prefix38 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 19) hparentBefore tmFiber76ReverseSingleStep39

theorem tmFiber76State39_in_pass1_full :
    tmFiber76StateAt 39 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix39 ++ [tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix39 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 39) tmFiber76State39_in_pass1_prefix39

theorem tmFiber76State50_in_pass1_prefix50 :
    tmFiber76StateAt 50 ∈ chainClosureStep tmWord tmFiber76Prefix50 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 12 ∈
      chainClosureStep tmWord tmFiber76Prefix49 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix49 = tmFiber76Prefix12 ++ [tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49]
      (chainClosureStep tmWord tmFiber76Prefix12 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 12) tmFiber76State12_in_pass1_prefix12
  rw [show tmFiber76Prefix50 = tmFiber76Prefix49 ++ [tmFiber76StateAt 50] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 50) []
    (chainClosureStep tmWord tmFiber76Prefix49 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 12) hparentBefore tmFiber76ReverseSingleStep50

theorem tmFiber76State50_in_pass1_full :
    tmFiber76StateAt 50 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix50 ++ [tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix50 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 50) tmFiber76State50_in_pass1_prefix50

theorem tmFiber76State51_in_pass1_prefix51 :
    tmFiber76StateAt 51 ∈ chainClosureStep tmWord tmFiber76Prefix51 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 13 ∈
      chainClosureStep tmWord tmFiber76Prefix50 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix50 = tmFiber76Prefix13 ++ [tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50]
      (chainClosureStep tmWord tmFiber76Prefix13 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 13) tmFiber76State13_in_pass1_prefix13
  rw [show tmFiber76Prefix51 = tmFiber76Prefix50 ++ [tmFiber76StateAt 51] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 51) []
    (chainClosureStep tmWord tmFiber76Prefix50 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 13) hparentBefore tmFiber76ReverseSingleStep51

theorem tmFiber76State51_in_pass1_full :
    tmFiber76StateAt 51 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix51 ++ [tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix51 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 51) tmFiber76State51_in_pass1_prefix51

theorem tmFiber76State52_in_pass1_prefix52 :
    tmFiber76StateAt 52 ∈ chainClosureStep tmWord tmFiber76Prefix52 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 8 ∈
      chainClosureStep tmWord tmFiber76Prefix51 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix51 = tmFiber76Prefix8 ++ [tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51]
      (chainClosureStep tmWord tmFiber76Prefix8 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 8) tmFiber76State8_in_pass1_prefix8
  rw [show tmFiber76Prefix52 = tmFiber76Prefix51 ++ [tmFiber76StateAt 52] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 52) []
    (chainClosureStep tmWord tmFiber76Prefix51 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 8) hparentBefore tmFiber76ReverseSingleStep52

theorem tmFiber76State52_in_pass1_full :
    tmFiber76StateAt 52 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix52 ++ [tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix52 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 52) tmFiber76State52_in_pass1_prefix52

theorem tmFiber76State53_in_pass1_prefix53 :
    tmFiber76StateAt 53 ∈ chainClosureStep tmWord tmFiber76Prefix53 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 9 ∈
      chainClosureStep tmWord tmFiber76Prefix52 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix52 = tmFiber76Prefix9 ++ [tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52]
      (chainClosureStep tmWord tmFiber76Prefix9 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 9) tmFiber76State9_in_pass1_prefix9
  rw [show tmFiber76Prefix53 = tmFiber76Prefix52 ++ [tmFiber76StateAt 53] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 53) []
    (chainClosureStep tmWord tmFiber76Prefix52 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 9) hparentBefore tmFiber76ReverseSingleStep53

theorem tmFiber76State53_in_pass1_full :
    tmFiber76StateAt 53 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix53 ++ [tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix53 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 53) tmFiber76State53_in_pass1_prefix53

theorem tmFiber76State54_in_pass1_prefix54 :
    tmFiber76StateAt 54 ∈ chainClosureStep tmWord tmFiber76Prefix54 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 10 ∈
      chainClosureStep tmWord tmFiber76Prefix53 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix53 = tmFiber76Prefix10 ++ [tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53]
      (chainClosureStep tmWord tmFiber76Prefix10 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 10) tmFiber76State10_in_pass1_prefix10
  rw [show tmFiber76Prefix54 = tmFiber76Prefix53 ++ [tmFiber76StateAt 54] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 54) []
    (chainClosureStep tmWord tmFiber76Prefix53 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 10) hparentBefore tmFiber76ReverseSingleStep54

theorem tmFiber76State54_in_pass1_full :
    tmFiber76StateAt 54 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix54 ++ [tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix54 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 54) tmFiber76State54_in_pass1_prefix54

theorem tmFiber76State55_in_pass1_prefix55 :
    tmFiber76StateAt 55 ∈ chainClosureStep tmWord tmFiber76Prefix55 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 11 ∈
      chainClosureStep tmWord tmFiber76Prefix54 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix54 = tmFiber76Prefix11 ++ [tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54]
      (chainClosureStep tmWord tmFiber76Prefix11 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 11) tmFiber76State11_in_pass1_prefix11
  rw [show tmFiber76Prefix55 = tmFiber76Prefix54 ++ [tmFiber76StateAt 55] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 55) []
    (chainClosureStep tmWord tmFiber76Prefix54 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 11) hparentBefore tmFiber76ReverseSingleStep55

theorem tmFiber76State55_in_pass1_full :
    tmFiber76StateAt 55 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix55 ++ [tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix55 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 55) tmFiber76State55_in_pass1_prefix55

theorem tmFiber76State58_in_pass1_prefix58 :
    tmFiber76StateAt 58 ∈ chainClosureStep tmWord tmFiber76Prefix58 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 4 ∈
      chainClosureStep tmWord tmFiber76Prefix57 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix57 = tmFiber76Prefix4 ++ [tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57]
      (chainClosureStep tmWord tmFiber76Prefix4 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 4) tmFiber76State4_in_pass1_prefix4
  rw [show tmFiber76Prefix58 = tmFiber76Prefix57 ++ [tmFiber76StateAt 58] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 58) []
    (chainClosureStep tmWord tmFiber76Prefix57 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 4) hparentBefore tmFiber76ReverseSingleStep58

theorem tmFiber76State58_in_pass1_full :
    tmFiber76StateAt 58 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix58 ++ [tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix58 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 58) tmFiber76State58_in_pass1_prefix58

theorem tmFiber76State59_in_pass1_prefix59 :
    tmFiber76StateAt 59 ∈ chainClosureStep tmWord tmFiber76Prefix59 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 5 ∈
      chainClosureStep tmWord tmFiber76Prefix58 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix58 = tmFiber76Prefix5 ++ [tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58]
      (chainClosureStep tmWord tmFiber76Prefix5 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 5) tmFiber76State5_in_pass1_prefix5
  rw [show tmFiber76Prefix59 = tmFiber76Prefix58 ++ [tmFiber76StateAt 59] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 59) []
    (chainClosureStep tmWord tmFiber76Prefix58 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 5) hparentBefore tmFiber76ReverseSingleStep59

theorem tmFiber76State59_in_pass1_full :
    tmFiber76StateAt 59 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix59 ++ [tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix59 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 59) tmFiber76State59_in_pass1_prefix59

theorem tmFiber76State60_in_pass1_prefix60 :
    tmFiber76StateAt 60 ∈ chainClosureStep tmWord tmFiber76Prefix60 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 0 ∈
      chainClosureStep tmWord tmFiber76Prefix59 ([tmFiber76StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber76Prefix59
      ([tmFiber76StateAt 0]) (tmFiber76StateAt 0) (by simp)
  rw [show tmFiber76Prefix60 = tmFiber76Prefix59 ++ [tmFiber76StateAt 60] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 60) []
    (chainClosureStep tmWord tmFiber76Prefix59 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 0) hparentBefore tmFiber76ReverseSingleStep60

theorem tmFiber76State60_in_pass1_full :
    tmFiber76StateAt 60 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix60 ++ [tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix60 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 60) tmFiber76State60_in_pass1_prefix60

theorem tmFiber76State61_in_pass1_prefix61 :
    tmFiber76StateAt 61 ∈ chainClosureStep tmWord tmFiber76Prefix61 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 1 ∈
      chainClosureStep tmWord tmFiber76Prefix60 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix60 = tmFiber76Prefix1 ++ [tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 2, tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60]
      (chainClosureStep tmWord tmFiber76Prefix1 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 1) tmFiber76State1_in_pass1_prefix1
  rw [show tmFiber76Prefix61 = tmFiber76Prefix60 ++ [tmFiber76StateAt 61] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 61) []
    (chainClosureStep tmWord tmFiber76Prefix60 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 1) hparentBefore tmFiber76ReverseSingleStep61

theorem tmFiber76State61_in_pass1_full :
    tmFiber76StateAt 61 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix61 ++ [tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix61 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 61) tmFiber76State61_in_pass1_prefix61

theorem tmFiber76State62_in_pass1_prefix62 :
    tmFiber76StateAt 62 ∈ chainClosureStep tmWord tmFiber76Prefix62 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 2 ∈
      chainClosureStep tmWord tmFiber76Prefix61 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix61 = tmFiber76Prefix2 ++ [tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 3, tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61]
      (chainClosureStep tmWord tmFiber76Prefix2 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 2) tmFiber76State2_in_pass1_prefix2
  rw [show tmFiber76Prefix62 = tmFiber76Prefix61 ++ [tmFiber76StateAt 62] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 62) []
    (chainClosureStep tmWord tmFiber76Prefix61 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 2) hparentBefore tmFiber76ReverseSingleStep62

theorem tmFiber76State62_in_pass1_full :
    tmFiber76StateAt 62 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix62 ++ [tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix62 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 62) tmFiber76State62_in_pass1_prefix62

theorem tmFiber76State63_in_pass1_prefix63 :
    tmFiber76StateAt 63 ∈ chainClosureStep tmWord tmFiber76Prefix63 ([tmFiber76StateAt 0]) := by
  have hparentBefore : tmFiber76StateAt 3 ∈
      chainClosureStep tmWord tmFiber76Prefix62 ([tmFiber76StateAt 0]) := by
    rw [show tmFiber76Prefix62 = tmFiber76Prefix3 ++ [tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 4, tmFiber76StateAt 5, tmFiber76StateAt 6, tmFiber76StateAt 7, tmFiber76StateAt 8, tmFiber76StateAt 9, tmFiber76StateAt 10, tmFiber76StateAt 11, tmFiber76StateAt 12, tmFiber76StateAt 13, tmFiber76StateAt 14, tmFiber76StateAt 15, tmFiber76StateAt 16, tmFiber76StateAt 17, tmFiber76StateAt 18, tmFiber76StateAt 19, tmFiber76StateAt 20, tmFiber76StateAt 21, tmFiber76StateAt 22, tmFiber76StateAt 23, tmFiber76StateAt 24, tmFiber76StateAt 25, tmFiber76StateAt 26, tmFiber76StateAt 27, tmFiber76StateAt 28, tmFiber76StateAt 29, tmFiber76StateAt 30, tmFiber76StateAt 31, tmFiber76StateAt 32, tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62]
      (chainClosureStep tmWord tmFiber76Prefix3 ([tmFiber76StateAt 0]))
      (tmFiber76StateAt 3) tmFiber76State3_in_pass1_prefix3
  rw [show tmFiber76Prefix63 = tmFiber76Prefix62 ++ [tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 63) []
    (chainClosureStep tmWord tmFiber76Prefix62 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 3) hparentBefore tmFiber76ReverseSingleStep63

theorem tmFiber76State63_in_pass1_full :
    tmFiber76StateAt 63 ∈ chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix63 ++ [] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord []
    (chainClosureStep tmWord tmFiber76Prefix63 ([tmFiber76StateAt 0]))
    (tmFiber76StateAt 63) tmFiber76State63_in_pass1_prefix63

theorem tmFiber76State32_in_pass2_prefix32 :
    tmFiber76StateAt 32 ∈ chainClosureStep tmWord tmFiber76Prefix32 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) := by
  have hparentBefore : tmFiber76StateAt 36 ∈
      chainClosureStep tmWord tmFiber76Prefix31 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber76Prefix31
      (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) (tmFiber76StateAt 36) tmFiber76State36_in_pass1_full
  rw [show tmFiber76Prefix32 = tmFiber76Prefix31 ++ [tmFiber76StateAt 32] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 32) []
    (chainClosureStep tmWord tmFiber76Prefix31 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])))
    (tmFiber76StateAt 36) hparentBefore tmFiber76ReverseSingleStep32

theorem tmFiber76State32_in_pass2_full :
    tmFiber76StateAt 32 ∈ chainClosureStep tmWord tmFiber76DirectStates (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix32 ++ [tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 33, tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix32 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])))
    (tmFiber76StateAt 32) tmFiber76State32_in_pass2_prefix32

theorem tmFiber76State33_in_pass2_prefix33 :
    tmFiber76StateAt 33 ∈ chainClosureStep tmWord tmFiber76Prefix33 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) := by
  have hparentBefore : tmFiber76StateAt 37 ∈
      chainClosureStep tmWord tmFiber76Prefix32 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber76Prefix32
      (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) (tmFiber76StateAt 37) tmFiber76State37_in_pass1_full
  rw [show tmFiber76Prefix33 = tmFiber76Prefix32 ++ [tmFiber76StateAt 33] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 33) []
    (chainClosureStep tmWord tmFiber76Prefix32 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])))
    (tmFiber76StateAt 37) hparentBefore tmFiber76ReverseSingleStep33

theorem tmFiber76State33_in_pass2_full :
    tmFiber76StateAt 33 ∈ chainClosureStep tmWord tmFiber76DirectStates (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix33 ++ [tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 34, tmFiber76StateAt 35, tmFiber76StateAt 36, tmFiber76StateAt 37, tmFiber76StateAt 38, tmFiber76StateAt 39, tmFiber76StateAt 40, tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix33 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])))
    (tmFiber76StateAt 33) tmFiber76State33_in_pass2_prefix33

theorem tmFiber76State42_in_pass2_prefix42 :
    tmFiber76StateAt 42 ∈ chainClosureStep tmWord tmFiber76Prefix42 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) := by
  have hparentBefore : tmFiber76StateAt 58 ∈
      chainClosureStep tmWord tmFiber76Prefix41 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber76Prefix41
      (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) (tmFiber76StateAt 58) tmFiber76State58_in_pass1_full
  rw [show tmFiber76Prefix42 = tmFiber76Prefix41 ++ [tmFiber76StateAt 42] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 42) []
    (chainClosureStep tmWord tmFiber76Prefix41 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])))
    (tmFiber76StateAt 58) hparentBefore tmFiber76ReverseSingleStep42

theorem tmFiber76State42_in_pass2_full :
    tmFiber76StateAt 42 ∈ chainClosureStep tmWord tmFiber76DirectStates (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix42 ++ [tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix42 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])))
    (tmFiber76StateAt 42) tmFiber76State42_in_pass2_prefix42

theorem tmFiber76State43_in_pass2_prefix43 :
    tmFiber76StateAt 43 ∈ chainClosureStep tmWord tmFiber76Prefix43 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) := by
  have hparentBefore : tmFiber76StateAt 59 ∈
      chainClosureStep tmWord tmFiber76Prefix42 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber76Prefix42
      (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) (tmFiber76StateAt 59) tmFiber76State59_in_pass1_full
  rw [show tmFiber76Prefix43 = tmFiber76Prefix42 ++ [tmFiber76StateAt 43] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 43) []
    (chainClosureStep tmWord tmFiber76Prefix42 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])))
    (tmFiber76StateAt 59) hparentBefore tmFiber76ReverseSingleStep43

theorem tmFiber76State43_in_pass2_full :
    tmFiber76StateAt 43 ∈ chainClosureStep tmWord tmFiber76DirectStates (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix43 ++ [tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix43 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])))
    (tmFiber76StateAt 43) tmFiber76State43_in_pass2_prefix43

theorem tmFiber76State44_in_pass2_prefix44 :
    tmFiber76StateAt 44 ∈ chainClosureStep tmWord tmFiber76Prefix44 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) := by
  have hparentBefore : tmFiber76StateAt 60 ∈
      chainClosureStep tmWord tmFiber76Prefix43 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber76Prefix43
      (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) (tmFiber76StateAt 60) tmFiber76State60_in_pass1_full
  rw [show tmFiber76Prefix44 = tmFiber76Prefix43 ++ [tmFiber76StateAt 44] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 44) []
    (chainClosureStep tmWord tmFiber76Prefix43 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])))
    (tmFiber76StateAt 60) hparentBefore tmFiber76ReverseSingleStep44

theorem tmFiber76State44_in_pass2_full :
    tmFiber76StateAt 44 ∈ chainClosureStep tmWord tmFiber76DirectStates (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix44 ++ [tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix44 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])))
    (tmFiber76StateAt 44) tmFiber76State44_in_pass2_prefix44

theorem tmFiber76State45_in_pass2_prefix45 :
    tmFiber76StateAt 45 ∈ chainClosureStep tmWord tmFiber76Prefix45 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) := by
  have hparentBefore : tmFiber76StateAt 61 ∈
      chainClosureStep tmWord tmFiber76Prefix44 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber76Prefix44
      (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) (tmFiber76StateAt 61) tmFiber76State61_in_pass1_full
  rw [show tmFiber76Prefix45 = tmFiber76Prefix44 ++ [tmFiber76StateAt 45] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 45) []
    (chainClosureStep tmWord tmFiber76Prefix44 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])))
    (tmFiber76StateAt 61) hparentBefore tmFiber76ReverseSingleStep45

theorem tmFiber76State45_in_pass2_full :
    tmFiber76StateAt 45 ∈ chainClosureStep tmWord tmFiber76DirectStates (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix45 ++ [tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix45 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])))
    (tmFiber76StateAt 45) tmFiber76State45_in_pass2_prefix45

theorem tmFiber76State46_in_pass2_prefix46 :
    tmFiber76StateAt 46 ∈ chainClosureStep tmWord tmFiber76Prefix46 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) := by
  have hparentBefore : tmFiber76StateAt 62 ∈
      chainClosureStep tmWord tmFiber76Prefix45 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber76Prefix45
      (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) (tmFiber76StateAt 62) tmFiber76State62_in_pass1_full
  rw [show tmFiber76Prefix46 = tmFiber76Prefix45 ++ [tmFiber76StateAt 46] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 46) []
    (chainClosureStep tmWord tmFiber76Prefix45 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])))
    (tmFiber76StateAt 62) hparentBefore tmFiber76ReverseSingleStep46

theorem tmFiber76State46_in_pass2_full :
    tmFiber76StateAt 46 ∈ chainClosureStep tmWord tmFiber76DirectStates (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix46 ++ [tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix46 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])))
    (tmFiber76StateAt 46) tmFiber76State46_in_pass2_prefix46

theorem tmFiber76State47_in_pass2_prefix47 :
    tmFiber76StateAt 47 ∈ chainClosureStep tmWord tmFiber76Prefix47 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) := by
  have hparentBefore : tmFiber76StateAt 63 ∈
      chainClosureStep tmWord tmFiber76Prefix46 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber76Prefix46
      (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) (tmFiber76StateAt 63) tmFiber76State63_in_pass1_full
  rw [show tmFiber76Prefix47 = tmFiber76Prefix46 ++ [tmFiber76StateAt 47] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 47) []
    (chainClosureStep tmWord tmFiber76Prefix46 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])))
    (tmFiber76StateAt 63) hparentBefore tmFiber76ReverseSingleStep47

theorem tmFiber76State47_in_pass2_full :
    tmFiber76StateAt 47 ∈ chainClosureStep tmWord tmFiber76DirectStates (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix47 ++ [tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix47 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])))
    (tmFiber76StateAt 47) tmFiber76State47_in_pass2_prefix47

theorem tmFiber76State48_in_pass2_prefix48 :
    tmFiber76StateAt 48 ∈ chainClosureStep tmWord tmFiber76Prefix48 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) := by
  have hparentBefore : tmFiber76StateAt 52 ∈
      chainClosureStep tmWord tmFiber76Prefix47 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber76Prefix47
      (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) (tmFiber76StateAt 52) tmFiber76State52_in_pass1_full
  rw [show tmFiber76Prefix48 = tmFiber76Prefix47 ++ [tmFiber76StateAt 48] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 48) []
    (chainClosureStep tmWord tmFiber76Prefix47 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])))
    (tmFiber76StateAt 52) hparentBefore tmFiber76ReverseSingleStep48

theorem tmFiber76State48_in_pass2_full :
    tmFiber76StateAt 48 ∈ chainClosureStep tmWord tmFiber76DirectStates (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix48 ++ [tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix48 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])))
    (tmFiber76StateAt 48) tmFiber76State48_in_pass2_prefix48

theorem tmFiber76State49_in_pass2_prefix49 :
    tmFiber76StateAt 49 ∈ chainClosureStep tmWord tmFiber76Prefix49 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) := by
  have hparentBefore : tmFiber76StateAt 53 ∈
      chainClosureStep tmWord tmFiber76Prefix48 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber76Prefix48
      (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) (tmFiber76StateAt 53) tmFiber76State53_in_pass1_full
  rw [show tmFiber76Prefix49 = tmFiber76Prefix48 ++ [tmFiber76StateAt 49] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 49) []
    (chainClosureStep tmWord tmFiber76Prefix48 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])))
    (tmFiber76StateAt 53) hparentBefore tmFiber76ReverseSingleStep49

theorem tmFiber76State49_in_pass2_full :
    tmFiber76StateAt 49 ∈ chainClosureStep tmWord tmFiber76DirectStates (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix49 ++ [tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix49 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])))
    (tmFiber76StateAt 49) tmFiber76State49_in_pass2_prefix49

theorem tmFiber76State56_in_pass2_prefix56 :
    tmFiber76StateAt 56 ∈ chainClosureStep tmWord tmFiber76Prefix56 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) := by
  have hparentBefore : tmFiber76StateAt 60 ∈
      chainClosureStep tmWord tmFiber76Prefix55 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber76Prefix55
      (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) (tmFiber76StateAt 60) tmFiber76State60_in_pass1_full
  rw [show tmFiber76Prefix56 = tmFiber76Prefix55 ++ [tmFiber76StateAt 56] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 56) []
    (chainClosureStep tmWord tmFiber76Prefix55 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])))
    (tmFiber76StateAt 60) hparentBefore tmFiber76ReverseSingleStep56

theorem tmFiber76State56_in_pass2_full :
    tmFiber76StateAt 56 ∈ chainClosureStep tmWord tmFiber76DirectStates (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix56 ++ [tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix56 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])))
    (tmFiber76StateAt 56) tmFiber76State56_in_pass2_prefix56

theorem tmFiber76State57_in_pass2_prefix57 :
    tmFiber76StateAt 57 ∈ chainClosureStep tmWord tmFiber76Prefix57 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) := by
  have hparentBefore : tmFiber76StateAt 61 ∈
      chainClosureStep tmWord tmFiber76Prefix56 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber76Prefix56
      (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) (tmFiber76StateAt 61) tmFiber76State61_in_pass1_full
  rw [show tmFiber76Prefix57 = tmFiber76Prefix56 ++ [tmFiber76StateAt 57] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 57) []
    (chainClosureStep tmWord tmFiber76Prefix56 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])))
    (tmFiber76StateAt 61) hparentBefore tmFiber76ReverseSingleStep57

theorem tmFiber76State57_in_pass2_full :
    tmFiber76StateAt 57 ∈ chainClosureStep tmWord tmFiber76DirectStates (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix57 ++ [tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix57 (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0])))
    (tmFiber76StateAt 57) tmFiber76State57_in_pass2_prefix57

theorem tmFiber76State40_in_pass3_prefix40 :
    tmFiber76StateAt 40 ∈ chainClosureStep tmWord tmFiber76Prefix40 (chainClosureStep tmWord tmFiber76DirectStates (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]))) := by
  have hparentBefore : tmFiber76StateAt 44 ∈
      chainClosureStep tmWord tmFiber76Prefix39 (chainClosureStep tmWord tmFiber76DirectStates (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]))) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber76Prefix39
      (chainClosureStep tmWord tmFiber76DirectStates (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]))) (tmFiber76StateAt 44) tmFiber76State44_in_pass2_full
  rw [show tmFiber76Prefix40 = tmFiber76Prefix39 ++ [tmFiber76StateAt 40] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 40) []
    (chainClosureStep tmWord tmFiber76Prefix39 (chainClosureStep tmWord tmFiber76DirectStates (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]))))
    (tmFiber76StateAt 44) hparentBefore tmFiber76ReverseSingleStep40

theorem tmFiber76State40_in_pass3_full :
    tmFiber76StateAt 40 ∈ chainClosureStep tmWord tmFiber76DirectStates (chainClosureStep tmWord tmFiber76DirectStates (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]))) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix40 ++ [tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 41, tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix40 (chainClosureStep tmWord tmFiber76DirectStates (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]))))
    (tmFiber76StateAt 40) tmFiber76State40_in_pass3_prefix40

theorem tmFiber76State41_in_pass3_prefix41 :
    tmFiber76StateAt 41 ∈ chainClosureStep tmWord tmFiber76Prefix41 (chainClosureStep tmWord tmFiber76DirectStates (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]))) := by
  have hparentBefore : tmFiber76StateAt 45 ∈
      chainClosureStep tmWord tmFiber76Prefix40 (chainClosureStep tmWord tmFiber76DirectStates (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]))) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber76Prefix40
      (chainClosureStep tmWord tmFiber76DirectStates (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]))) (tmFiber76StateAt 45) tmFiber76State45_in_pass2_full
  rw [show tmFiber76Prefix41 = tmFiber76Prefix40 ++ [tmFiber76StateAt 41] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber76StateAt 41) []
    (chainClosureStep tmWord tmFiber76Prefix40 (chainClosureStep tmWord tmFiber76DirectStates (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]))))
    (tmFiber76StateAt 45) hparentBefore tmFiber76ReverseSingleStep41

theorem tmFiber76State41_in_pass3_full :
    tmFiber76StateAt 41 ∈ chainClosureStep tmWord tmFiber76DirectStates (chainClosureStep tmWord tmFiber76DirectStates (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]))) := by
  rw [show tmFiber76DirectStates = tmFiber76Prefix41 ++ [tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber76StateAt 42, tmFiber76StateAt 43, tmFiber76StateAt 44, tmFiber76StateAt 45, tmFiber76StateAt 46, tmFiber76StateAt 47, tmFiber76StateAt 48, tmFiber76StateAt 49, tmFiber76StateAt 50, tmFiber76StateAt 51, tmFiber76StateAt 52, tmFiber76StateAt 53, tmFiber76StateAt 54, tmFiber76StateAt 55, tmFiber76StateAt 56, tmFiber76StateAt 57, tmFiber76StateAt 58, tmFiber76StateAt 59, tmFiber76StateAt 60, tmFiber76StateAt 61, tmFiber76StateAt 62, tmFiber76StateAt 63]
    (chainClosureStep tmWord tmFiber76Prefix41 (chainClosureStep tmWord tmFiber76DirectStates (chainClosureStep tmWord tmFiber76DirectStates ([tmFiber76StateAt 0]))))
    (tmFiber76StateAt 41) tmFiber76State41_in_pass3_prefix41

theorem tmFiber76FirstPassGrows :
    ((chainClosureStep tmWord tmFiber76DirectStates [tmFiber76StateAt 0]).length ==
      [tmFiber76StateAt 0].length) = false := by
  have hroot : tmFiber76StateAt 0 ∈
      chainClosureStep tmWord tmFiber76DirectStates [tmFiber76StateAt 0] :=
    chainClosureStep_mem_of_seen tmWord tmFiber76DirectStates
      [tmFiber76StateAt 0] (tmFiber76StateAt 0) (by simp)
  have hnew : tmFiber76StateAt 1 ∈
      chainClosureStep tmWord tmFiber76DirectStates [tmFiber76StateAt 0] :=
    tmFiber76State1_in_pass1_full
  simpa using list_length_beq_one_false_of_two_mem
    (chainClosureStep tmWord tmFiber76DirectStates [tmFiber76StateAt 0])
    (tmFiber76StateAt 0) (tmFiber76StateAt 1) hroot hnew (by decide)

theorem tmFiber76State0_in_close_short :
    tmFiber76StateAt 0 ∈ closeChainFiber tmWord tmFiber76DirectStates 0 [tmFiber76StateAt 0] := by
  simp [closeChainFiber]

theorem tmFiber76State1_in_close_short :
    tmFiber76StateAt 1 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 1) tmFiber76State1_in_pass1_full

theorem tmFiber76State2_in_close_short :
    tmFiber76StateAt 2 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 2) tmFiber76State2_in_pass1_full

theorem tmFiber76State3_in_close_short :
    tmFiber76StateAt 3 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 3) tmFiber76State3_in_pass1_full

theorem tmFiber76State4_in_close_short :
    tmFiber76StateAt 4 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 4) tmFiber76State4_in_pass1_full

theorem tmFiber76State5_in_close_short :
    tmFiber76StateAt 5 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 5) tmFiber76State5_in_pass1_full

theorem tmFiber76State6_in_close_short :
    tmFiber76StateAt 6 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 6) tmFiber76State6_in_pass1_full

theorem tmFiber76State7_in_close_short :
    tmFiber76StateAt 7 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 7) tmFiber76State7_in_pass1_full

theorem tmFiber76State8_in_close_short :
    tmFiber76StateAt 8 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 8) tmFiber76State8_in_pass1_full

theorem tmFiber76State9_in_close_short :
    tmFiber76StateAt 9 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 9) tmFiber76State9_in_pass1_full

theorem tmFiber76State10_in_close_short :
    tmFiber76StateAt 10 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 10) tmFiber76State10_in_pass1_full

theorem tmFiber76State11_in_close_short :
    tmFiber76StateAt 11 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 11) tmFiber76State11_in_pass1_full

theorem tmFiber76State12_in_close_short :
    tmFiber76StateAt 12 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 12) tmFiber76State12_in_pass1_full

theorem tmFiber76State13_in_close_short :
    tmFiber76StateAt 13 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 13) tmFiber76State13_in_pass1_full

theorem tmFiber76State14_in_close_short :
    tmFiber76StateAt 14 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 14) tmFiber76State14_in_pass1_full

theorem tmFiber76State15_in_close_short :
    tmFiber76StateAt 15 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 15) tmFiber76State15_in_pass1_full

theorem tmFiber76State16_in_close_short :
    tmFiber76StateAt 16 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 16) tmFiber76State16_in_pass1_full

theorem tmFiber76State17_in_close_short :
    tmFiber76StateAt 17 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 17) tmFiber76State17_in_pass1_full

theorem tmFiber76State18_in_close_short :
    tmFiber76StateAt 18 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 18) tmFiber76State18_in_pass1_full

theorem tmFiber76State19_in_close_short :
    tmFiber76StateAt 19 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 19) tmFiber76State19_in_pass1_full

theorem tmFiber76State20_in_close_short :
    tmFiber76StateAt 20 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 20) tmFiber76State20_in_pass1_full

theorem tmFiber76State21_in_close_short :
    tmFiber76StateAt 21 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 21) tmFiber76State21_in_pass1_full

theorem tmFiber76State22_in_close_short :
    tmFiber76StateAt 22 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 22) tmFiber76State22_in_pass1_full

theorem tmFiber76State23_in_close_short :
    tmFiber76StateAt 23 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 23) tmFiber76State23_in_pass1_full

theorem tmFiber76State24_in_close_short :
    tmFiber76StateAt 24 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 24) tmFiber76State24_in_pass1_full

theorem tmFiber76State25_in_close_short :
    tmFiber76StateAt 25 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 25) tmFiber76State25_in_pass1_full

theorem tmFiber76State26_in_close_short :
    tmFiber76StateAt 26 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 26) tmFiber76State26_in_pass1_full

theorem tmFiber76State27_in_close_short :
    tmFiber76StateAt 27 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 27) tmFiber76State27_in_pass1_full

theorem tmFiber76State28_in_close_short :
    tmFiber76StateAt 28 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 28) tmFiber76State28_in_pass1_full

theorem tmFiber76State29_in_close_short :
    tmFiber76StateAt 29 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 29) tmFiber76State29_in_pass1_full

theorem tmFiber76State30_in_close_short :
    tmFiber76StateAt 30 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 30) tmFiber76State30_in_pass1_full

theorem tmFiber76State31_in_close_short :
    tmFiber76StateAt 31 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 31) tmFiber76State31_in_pass1_full

theorem tmFiber76State34_in_close_short :
    tmFiber76StateAt 34 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 34) tmFiber76State34_in_pass1_full

theorem tmFiber76State35_in_close_short :
    tmFiber76StateAt 35 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 35) tmFiber76State35_in_pass1_full

theorem tmFiber76State36_in_close_short :
    tmFiber76StateAt 36 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 36) tmFiber76State36_in_pass1_full

theorem tmFiber76State37_in_close_short :
    tmFiber76StateAt 37 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 37) tmFiber76State37_in_pass1_full

theorem tmFiber76State38_in_close_short :
    tmFiber76StateAt 38 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 38) tmFiber76State38_in_pass1_full

theorem tmFiber76State39_in_close_short :
    tmFiber76StateAt 39 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 39) tmFiber76State39_in_pass1_full

theorem tmFiber76State50_in_close_short :
    tmFiber76StateAt 50 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 50) tmFiber76State50_in_pass1_full

theorem tmFiber76State51_in_close_short :
    tmFiber76StateAt 51 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 51) tmFiber76State51_in_pass1_full

theorem tmFiber76State52_in_close_short :
    tmFiber76StateAt 52 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 52) tmFiber76State52_in_pass1_full

theorem tmFiber76State53_in_close_short :
    tmFiber76StateAt 53 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 53) tmFiber76State53_in_pass1_full

theorem tmFiber76State54_in_close_short :
    tmFiber76StateAt 54 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 54) tmFiber76State54_in_pass1_full

theorem tmFiber76State55_in_close_short :
    tmFiber76StateAt 55 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 55) tmFiber76State55_in_pass1_full

theorem tmFiber76State58_in_close_short :
    tmFiber76StateAt 58 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 58) tmFiber76State58_in_pass1_full

theorem tmFiber76State59_in_close_short :
    tmFiber76StateAt 59 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 59) tmFiber76State59_in_pass1_full

theorem tmFiber76State60_in_close_short :
    tmFiber76StateAt 60 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 60) tmFiber76State60_in_pass1_full

theorem tmFiber76State61_in_close_short :
    tmFiber76StateAt 61 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 61) tmFiber76State61_in_pass1_full

theorem tmFiber76State62_in_close_short :
    tmFiber76StateAt 62 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 62) tmFiber76State62_in_pass1_full

theorem tmFiber76State63_in_close_short :
    tmFiber76StateAt 63 ∈ closeChainFiber tmWord tmFiber76DirectStates 1 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 63) tmFiber76State63_in_pass1_full

theorem tmFiber76State32_in_close_short :
    tmFiber76StateAt 32 ∈ closeChainFiber tmWord tmFiber76DirectStates 2 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 32) tmFiber76FirstPassGrows
    tmFiber76State32_in_pass2_full

theorem tmFiber76State33_in_close_short :
    tmFiber76StateAt 33 ∈ closeChainFiber tmWord tmFiber76DirectStates 2 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 33) tmFiber76FirstPassGrows
    tmFiber76State33_in_pass2_full

theorem tmFiber76State42_in_close_short :
    tmFiber76StateAt 42 ∈ closeChainFiber tmWord tmFiber76DirectStates 2 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 42) tmFiber76FirstPassGrows
    tmFiber76State42_in_pass2_full

theorem tmFiber76State43_in_close_short :
    tmFiber76StateAt 43 ∈ closeChainFiber tmWord tmFiber76DirectStates 2 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 43) tmFiber76FirstPassGrows
    tmFiber76State43_in_pass2_full

theorem tmFiber76State44_in_close_short :
    tmFiber76StateAt 44 ∈ closeChainFiber tmWord tmFiber76DirectStates 2 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 44) tmFiber76FirstPassGrows
    tmFiber76State44_in_pass2_full

theorem tmFiber76State45_in_close_short :
    tmFiber76StateAt 45 ∈ closeChainFiber tmWord tmFiber76DirectStates 2 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 45) tmFiber76FirstPassGrows
    tmFiber76State45_in_pass2_full

theorem tmFiber76State46_in_close_short :
    tmFiber76StateAt 46 ∈ closeChainFiber tmWord tmFiber76DirectStates 2 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 46) tmFiber76FirstPassGrows
    tmFiber76State46_in_pass2_full

theorem tmFiber76State47_in_close_short :
    tmFiber76StateAt 47 ∈ closeChainFiber tmWord tmFiber76DirectStates 2 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 47) tmFiber76FirstPassGrows
    tmFiber76State47_in_pass2_full

theorem tmFiber76State48_in_close_short :
    tmFiber76StateAt 48 ∈ closeChainFiber tmWord tmFiber76DirectStates 2 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 48) tmFiber76FirstPassGrows
    tmFiber76State48_in_pass2_full

theorem tmFiber76State49_in_close_short :
    tmFiber76StateAt 49 ∈ closeChainFiber tmWord tmFiber76DirectStates 2 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 49) tmFiber76FirstPassGrows
    tmFiber76State49_in_pass2_full

theorem tmFiber76State56_in_close_short :
    tmFiber76StateAt 56 ∈ closeChainFiber tmWord tmFiber76DirectStates 2 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 56) tmFiber76FirstPassGrows
    tmFiber76State56_in_pass2_full

theorem tmFiber76State57_in_close_short :
    tmFiber76StateAt 57 ∈ closeChainFiber tmWord tmFiber76DirectStates 2 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber76DirectStates 0
    [tmFiber76StateAt 0] (tmFiber76StateAt 57) tmFiber76FirstPassGrows
    tmFiber76State57_in_pass2_full

theorem tmFiber76State40_in_close_short :
    tmFiber76StateAt 40 ∈ closeChainFiber tmWord tmFiber76DirectStates 3 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_step_of_close tmWord tmFiber76DirectStates 2
    [tmFiber76StateAt 0] (tmFiber76StateAt 44) (tmFiber76StateAt 40)
    (by simp) tmFiber76State44_in_close_short (by decide) tmFiber76ReverseSingleStep40

theorem tmFiber76State41_in_close_short :
    tmFiber76StateAt 41 ∈ closeChainFiber tmWord tmFiber76DirectStates 3 [tmFiber76StateAt 0] := by
  exact closeChainFiber_mem_step_of_close tmWord tmFiber76DirectStates 2
    [tmFiber76StateAt 0] (tmFiber76StateAt 45) (tmFiber76StateAt 41)
    (by simp) tmFiber76State45_in_close_short (by decide) tmFiber76ReverseSingleStep41

theorem tmFiber76State0_in_close :
    tmFiber76StateAt 0 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 0 ∈ closeChainFiber tmWord tmFiber76DirectStates (0 + 64) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 0 64
    [tmFiber76StateAt 0] (tmFiber76StateAt 0) tmFiber76State0_in_close_short

theorem tmFiber76State1_in_close :
    tmFiber76StateAt 1 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 1 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 1) tmFiber76State1_in_close_short

theorem tmFiber76State2_in_close :
    tmFiber76StateAt 2 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 2 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 2) tmFiber76State2_in_close_short

theorem tmFiber76State3_in_close :
    tmFiber76StateAt 3 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 3 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 3) tmFiber76State3_in_close_short

theorem tmFiber76State4_in_close :
    tmFiber76StateAt 4 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 4 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 4) tmFiber76State4_in_close_short

theorem tmFiber76State5_in_close :
    tmFiber76StateAt 5 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 5 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 5) tmFiber76State5_in_close_short

theorem tmFiber76State6_in_close :
    tmFiber76StateAt 6 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 6 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 6) tmFiber76State6_in_close_short

theorem tmFiber76State7_in_close :
    tmFiber76StateAt 7 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 7 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 7) tmFiber76State7_in_close_short

theorem tmFiber76State8_in_close :
    tmFiber76StateAt 8 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 8 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 8) tmFiber76State8_in_close_short

theorem tmFiber76State9_in_close :
    tmFiber76StateAt 9 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 9 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 9) tmFiber76State9_in_close_short

theorem tmFiber76State10_in_close :
    tmFiber76StateAt 10 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 10 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 10) tmFiber76State10_in_close_short

theorem tmFiber76State11_in_close :
    tmFiber76StateAt 11 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 11 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 11) tmFiber76State11_in_close_short

theorem tmFiber76State12_in_close :
    tmFiber76StateAt 12 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 12 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 12) tmFiber76State12_in_close_short

theorem tmFiber76State13_in_close :
    tmFiber76StateAt 13 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 13 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 13) tmFiber76State13_in_close_short

theorem tmFiber76State14_in_close :
    tmFiber76StateAt 14 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 14 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 14) tmFiber76State14_in_close_short

theorem tmFiber76State15_in_close :
    tmFiber76StateAt 15 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 15 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 15) tmFiber76State15_in_close_short

theorem tmFiber76State16_in_close :
    tmFiber76StateAt 16 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 16 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 16) tmFiber76State16_in_close_short

theorem tmFiber76State17_in_close :
    tmFiber76StateAt 17 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 17 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 17) tmFiber76State17_in_close_short

theorem tmFiber76State18_in_close :
    tmFiber76StateAt 18 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 18 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 18) tmFiber76State18_in_close_short

theorem tmFiber76State19_in_close :
    tmFiber76StateAt 19 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 19 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 19) tmFiber76State19_in_close_short

theorem tmFiber76State20_in_close :
    tmFiber76StateAt 20 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 20 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 20) tmFiber76State20_in_close_short

theorem tmFiber76State21_in_close :
    tmFiber76StateAt 21 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 21 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 21) tmFiber76State21_in_close_short

theorem tmFiber76State22_in_close :
    tmFiber76StateAt 22 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 22 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 22) tmFiber76State22_in_close_short

theorem tmFiber76State23_in_close :
    tmFiber76StateAt 23 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 23 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 23) tmFiber76State23_in_close_short

theorem tmFiber76State24_in_close :
    tmFiber76StateAt 24 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 24 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 24) tmFiber76State24_in_close_short

theorem tmFiber76State25_in_close :
    tmFiber76StateAt 25 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 25 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 25) tmFiber76State25_in_close_short

theorem tmFiber76State26_in_close :
    tmFiber76StateAt 26 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 26 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 26) tmFiber76State26_in_close_short

theorem tmFiber76State27_in_close :
    tmFiber76StateAt 27 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 27 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 27) tmFiber76State27_in_close_short

theorem tmFiber76State28_in_close :
    tmFiber76StateAt 28 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 28 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 28) tmFiber76State28_in_close_short

theorem tmFiber76State29_in_close :
    tmFiber76StateAt 29 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 29 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 29) tmFiber76State29_in_close_short

theorem tmFiber76State30_in_close :
    tmFiber76StateAt 30 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 30 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 30) tmFiber76State30_in_close_short

theorem tmFiber76State31_in_close :
    tmFiber76StateAt 31 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 31 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 31) tmFiber76State31_in_close_short

theorem tmFiber76State32_in_close :
    tmFiber76StateAt 32 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 32 ∈ closeChainFiber tmWord tmFiber76DirectStates (2 + 62) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 2 62
    [tmFiber76StateAt 0] (tmFiber76StateAt 32) tmFiber76State32_in_close_short

theorem tmFiber76State33_in_close :
    tmFiber76StateAt 33 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 33 ∈ closeChainFiber tmWord tmFiber76DirectStates (2 + 62) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 2 62
    [tmFiber76StateAt 0] (tmFiber76StateAt 33) tmFiber76State33_in_close_short

theorem tmFiber76State34_in_close :
    tmFiber76StateAt 34 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 34 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 34) tmFiber76State34_in_close_short

theorem tmFiber76State35_in_close :
    tmFiber76StateAt 35 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 35 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 35) tmFiber76State35_in_close_short

theorem tmFiber76State36_in_close :
    tmFiber76StateAt 36 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 36 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 36) tmFiber76State36_in_close_short

theorem tmFiber76State37_in_close :
    tmFiber76StateAt 37 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 37 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 37) tmFiber76State37_in_close_short

theorem tmFiber76State38_in_close :
    tmFiber76StateAt 38 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 38 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 38) tmFiber76State38_in_close_short

theorem tmFiber76State39_in_close :
    tmFiber76StateAt 39 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 39 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 39) tmFiber76State39_in_close_short

theorem tmFiber76State40_in_close :
    tmFiber76StateAt 40 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 40 ∈ closeChainFiber tmWord tmFiber76DirectStates (3 + 61) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 3 61
    [tmFiber76StateAt 0] (tmFiber76StateAt 40) tmFiber76State40_in_close_short

theorem tmFiber76State41_in_close :
    tmFiber76StateAt 41 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 41 ∈ closeChainFiber tmWord tmFiber76DirectStates (3 + 61) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 3 61
    [tmFiber76StateAt 0] (tmFiber76StateAt 41) tmFiber76State41_in_close_short

theorem tmFiber76State42_in_close :
    tmFiber76StateAt 42 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 42 ∈ closeChainFiber tmWord tmFiber76DirectStates (2 + 62) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 2 62
    [tmFiber76StateAt 0] (tmFiber76StateAt 42) tmFiber76State42_in_close_short

theorem tmFiber76State43_in_close :
    tmFiber76StateAt 43 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 43 ∈ closeChainFiber tmWord tmFiber76DirectStates (2 + 62) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 2 62
    [tmFiber76StateAt 0] (tmFiber76StateAt 43) tmFiber76State43_in_close_short

theorem tmFiber76State44_in_close :
    tmFiber76StateAt 44 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 44 ∈ closeChainFiber tmWord tmFiber76DirectStates (2 + 62) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 2 62
    [tmFiber76StateAt 0] (tmFiber76StateAt 44) tmFiber76State44_in_close_short

theorem tmFiber76State45_in_close :
    tmFiber76StateAt 45 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 45 ∈ closeChainFiber tmWord tmFiber76DirectStates (2 + 62) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 2 62
    [tmFiber76StateAt 0] (tmFiber76StateAt 45) tmFiber76State45_in_close_short

theorem tmFiber76State46_in_close :
    tmFiber76StateAt 46 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 46 ∈ closeChainFiber tmWord tmFiber76DirectStates (2 + 62) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 2 62
    [tmFiber76StateAt 0] (tmFiber76StateAt 46) tmFiber76State46_in_close_short

theorem tmFiber76State47_in_close :
    tmFiber76StateAt 47 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 47 ∈ closeChainFiber tmWord tmFiber76DirectStates (2 + 62) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 2 62
    [tmFiber76StateAt 0] (tmFiber76StateAt 47) tmFiber76State47_in_close_short

theorem tmFiber76State48_in_close :
    tmFiber76StateAt 48 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 48 ∈ closeChainFiber tmWord tmFiber76DirectStates (2 + 62) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 2 62
    [tmFiber76StateAt 0] (tmFiber76StateAt 48) tmFiber76State48_in_close_short

theorem tmFiber76State49_in_close :
    tmFiber76StateAt 49 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 49 ∈ closeChainFiber tmWord tmFiber76DirectStates (2 + 62) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 2 62
    [tmFiber76StateAt 0] (tmFiber76StateAt 49) tmFiber76State49_in_close_short

theorem tmFiber76State50_in_close :
    tmFiber76StateAt 50 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 50 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 50) tmFiber76State50_in_close_short

theorem tmFiber76State51_in_close :
    tmFiber76StateAt 51 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 51 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 51) tmFiber76State51_in_close_short

theorem tmFiber76State52_in_close :
    tmFiber76StateAt 52 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 52 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 52) tmFiber76State52_in_close_short

theorem tmFiber76State53_in_close :
    tmFiber76StateAt 53 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 53 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 53) tmFiber76State53_in_close_short

theorem tmFiber76State54_in_close :
    tmFiber76StateAt 54 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 54 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 54) tmFiber76State54_in_close_short

theorem tmFiber76State55_in_close :
    tmFiber76StateAt 55 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 55 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 55) tmFiber76State55_in_close_short

theorem tmFiber76State56_in_close :
    tmFiber76StateAt 56 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 56 ∈ closeChainFiber tmWord tmFiber76DirectStates (2 + 62) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 2 62
    [tmFiber76StateAt 0] (tmFiber76StateAt 56) tmFiber76State56_in_close_short

theorem tmFiber76State57_in_close :
    tmFiber76StateAt 57 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 57 ∈ closeChainFiber tmWord tmFiber76DirectStates (2 + 62) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 2 62
    [tmFiber76StateAt 0] (tmFiber76StateAt 57) tmFiber76State57_in_close_short

theorem tmFiber76State58_in_close :
    tmFiber76StateAt 58 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 58 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 58) tmFiber76State58_in_close_short

theorem tmFiber76State59_in_close :
    tmFiber76StateAt 59 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 59 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 59) tmFiber76State59_in_close_short

theorem tmFiber76State60_in_close :
    tmFiber76StateAt 60 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 60 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 60) tmFiber76State60_in_close_short

theorem tmFiber76State61_in_close :
    tmFiber76StateAt 61 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 61 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 61) tmFiber76State61_in_close_short

theorem tmFiber76State62_in_close :
    tmFiber76StateAt 62 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 62 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 62) tmFiber76State62_in_close_short

theorem tmFiber76State63_in_close :
    tmFiber76StateAt 63 ∈ closeChainFiber tmWord tmFiber76DirectStates tmFiber76DirectStates.length [tmFiber76StateAt 0] := by
  change tmFiber76StateAt 63 ∈ closeChainFiber tmWord tmFiber76DirectStates (1 + 63) [tmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber76DirectStates 1 63
    [tmFiber76StateAt 0] (tmFiber76StateAt 63) tmFiber76State63_in_close_short

theorem tmFiber76DirectConnected :
    chainFiberConnected tmWord tmFiber76DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [tmFiber76DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact tmFiber76State0_in_close
  · subst state
    exact tmFiber76State1_in_close
  · subst state
    exact tmFiber76State2_in_close
  · subst state
    exact tmFiber76State3_in_close
  · subst state
    exact tmFiber76State4_in_close
  · subst state
    exact tmFiber76State5_in_close
  · subst state
    exact tmFiber76State6_in_close
  · subst state
    exact tmFiber76State7_in_close
  · subst state
    exact tmFiber76State8_in_close
  · subst state
    exact tmFiber76State9_in_close
  · subst state
    exact tmFiber76State10_in_close
  · subst state
    exact tmFiber76State11_in_close
  · subst state
    exact tmFiber76State12_in_close
  · subst state
    exact tmFiber76State13_in_close
  · subst state
    exact tmFiber76State14_in_close
  · subst state
    exact tmFiber76State15_in_close
  · subst state
    exact tmFiber76State16_in_close
  · subst state
    exact tmFiber76State17_in_close
  · subst state
    exact tmFiber76State18_in_close
  · subst state
    exact tmFiber76State19_in_close
  · subst state
    exact tmFiber76State20_in_close
  · subst state
    exact tmFiber76State21_in_close
  · subst state
    exact tmFiber76State22_in_close
  · subst state
    exact tmFiber76State23_in_close
  · subst state
    exact tmFiber76State24_in_close
  · subst state
    exact tmFiber76State25_in_close
  · subst state
    exact tmFiber76State26_in_close
  · subst state
    exact tmFiber76State27_in_close
  · subst state
    exact tmFiber76State28_in_close
  · subst state
    exact tmFiber76State29_in_close
  · subst state
    exact tmFiber76State30_in_close
  · subst state
    exact tmFiber76State31_in_close
  · subst state
    exact tmFiber76State32_in_close
  · subst state
    exact tmFiber76State33_in_close
  · subst state
    exact tmFiber76State34_in_close
  · subst state
    exact tmFiber76State35_in_close
  · subst state
    exact tmFiber76State36_in_close
  · subst state
    exact tmFiber76State37_in_close
  · subst state
    exact tmFiber76State38_in_close
  · subst state
    exact tmFiber76State39_in_close
  · subst state
    exact tmFiber76State40_in_close
  · subst state
    exact tmFiber76State41_in_close
  · subst state
    exact tmFiber76State42_in_close
  · subst state
    exact tmFiber76State43_in_close
  · subst state
    exact tmFiber76State44_in_close
  · subst state
    exact tmFiber76State45_in_close
  · subst state
    exact tmFiber76State46_in_close
  · subst state
    exact tmFiber76State47_in_close
  · subst state
    exact tmFiber76State48_in_close
  · subst state
    exact tmFiber76State49_in_close
  · subst state
    exact tmFiber76State50_in_close
  · subst state
    exact tmFiber76State51_in_close
  · subst state
    exact tmFiber76State52_in_close
  · subst state
    exact tmFiber76State53_in_close
  · subst state
    exact tmFiber76State54_in_close
  · subst state
    exact tmFiber76State55_in_close
  · subst state
    exact tmFiber76State56_in_close
  · subst state
    exact tmFiber76State57_in_close
  · subst state
    exact tmFiber76State58_in_close
  · subst state
    exact tmFiber76State59_in_close
  · subst state
    exact tmFiber76State60_in_close
  · subst state
    exact tmFiber76State61_in_close
  · subst state
    exact tmFiber76State62_in_close
  · subst state
    exact tmFiber76State63_in_close
  · cases h

end GoertzelLemma818LengthTwoTMLargeFiberBridge

end Mettapedia.GraphTheory.FourColor
