import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMLargeFiberBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated multi-pass direct closure bridge for `normal,mirror` size-64 fiber 44

This module proves direct connectedness for a generated size-64 fiber
whose parent order needs two closure scans. It is generated from
row-local reverse certificate chunks and keeps Lean on default limits.
-/

namespace GoertzelLemma818LengthTwoTMLargeFiberBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818TauMirrorCertificate
open GoertzelLemma818TauMirrorReverseAudit

def tmFiber44StateAt (i : Nat) : List TauState :=
  directStates (tmFiber44RowAt i).sourceLeft (tmFiber44RowAt i).sourceRight

def tmFiber44DirectStates : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]

def tmFiber44Prefix0 : List (List TauState) :=
  [tmFiber44StateAt 0]

def tmFiber44Prefix1 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1]

def tmFiber44Prefix2 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2]

def tmFiber44Prefix3 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3]

def tmFiber44Prefix4 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4]

def tmFiber44Prefix5 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5]

def tmFiber44Prefix6 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6]

def tmFiber44Prefix7 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7]

def tmFiber44Prefix8 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8]

def tmFiber44Prefix9 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9]

def tmFiber44Prefix10 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10]

def tmFiber44Prefix11 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11]

def tmFiber44Prefix12 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12]

def tmFiber44Prefix13 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13]

def tmFiber44Prefix14 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14]

def tmFiber44Prefix15 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15]

def tmFiber44Prefix16 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16]

def tmFiber44Prefix17 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17]

def tmFiber44Prefix18 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18]

def tmFiber44Prefix19 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19]

def tmFiber44Prefix20 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20]

def tmFiber44Prefix21 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21]

def tmFiber44Prefix22 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22]

def tmFiber44Prefix23 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23]

def tmFiber44Prefix24 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24]

def tmFiber44Prefix25 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25]

def tmFiber44Prefix26 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26]

def tmFiber44Prefix27 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27]

def tmFiber44Prefix28 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28]

def tmFiber44Prefix29 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29]

def tmFiber44Prefix30 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30]

def tmFiber44Prefix31 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31]

def tmFiber44Prefix32 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32]

def tmFiber44Prefix33 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33]

def tmFiber44Prefix34 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34]

def tmFiber44Prefix35 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35]

def tmFiber44Prefix36 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36]

def tmFiber44Prefix37 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37]

def tmFiber44Prefix38 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38]

def tmFiber44Prefix39 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39]

def tmFiber44Prefix40 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40]

def tmFiber44Prefix41 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41]

def tmFiber44Prefix42 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42]

def tmFiber44Prefix43 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43]

def tmFiber44Prefix44 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44]

def tmFiber44Prefix45 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45]

def tmFiber44Prefix46 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46]

def tmFiber44Prefix47 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47]

def tmFiber44Prefix48 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48]

def tmFiber44Prefix49 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49]

def tmFiber44Prefix50 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50]

def tmFiber44Prefix51 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51]

def tmFiber44Prefix52 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52]

def tmFiber44Prefix53 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53]

def tmFiber44Prefix54 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54]

def tmFiber44Prefix55 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55]

def tmFiber44Prefix56 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56]

def tmFiber44Prefix57 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57]

def tmFiber44Prefix58 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58]

def tmFiber44Prefix59 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59]

def tmFiber44Prefix60 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60]

def tmFiber44Prefix61 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61]

def tmFiber44Prefix62 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62]

def tmFiber44Prefix63 : List (List TauState) :=
  [tmFiber44StateAt 0, tmFiber44StateAt 1, tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]

theorem tmFiber44ReverseRow_1_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 1) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk0_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 0) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber44ReverseSingleStep1 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 0) (tmFiber44StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 0) (tmFiber44StateAt 1)
    (tmFiber44RowAt 1).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 1) (by decide) tmFiber44ReverseRow_1_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_2_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 2) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk1_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 2) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber44ReverseSingleStep2 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 0) (tmFiber44StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 0) (tmFiber44StateAt 2)
    (tmFiber44RowAt 2).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 2) (by decide) tmFiber44ReverseRow_2_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_3_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 3) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk1_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 2) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber44ReverseSingleStep3 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 1) (tmFiber44StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 1) (tmFiber44StateAt 3)
    (tmFiber44RowAt 3).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 3) (by decide) tmFiber44ReverseRow_3_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_4_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 4) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk2_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 4) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber44ReverseSingleStep4 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 2) (tmFiber44StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 2) (tmFiber44StateAt 4)
    (tmFiber44RowAt 4).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 4) (by decide) tmFiber44ReverseRow_4_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_5_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 5) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk2_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 4) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber44ReverseSingleStep5 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 7) (tmFiber44StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 7) (tmFiber44StateAt 5)
    (tmFiber44RowAt 5).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 5) (by decide) tmFiber44ReverseRow_5_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_6_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 6) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk3_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 6) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber44ReverseSingleStep6 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 1) (tmFiber44StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 1) (tmFiber44StateAt 6)
    (tmFiber44RowAt 6).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 6) (by decide) tmFiber44ReverseRow_6_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_7_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 7) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk3_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 6) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber44ReverseSingleStep7 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 0) (tmFiber44StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 0) (tmFiber44StateAt 7)
    (tmFiber44RowAt 7).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 7) (by decide) tmFiber44ReverseRow_7_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_8_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 8) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk4_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 8) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber44ReverseSingleStep8 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 0) (tmFiber44StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 0) (tmFiber44StateAt 8)
    (tmFiber44RowAt 8).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 8) (by decide) tmFiber44ReverseRow_8_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_9_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 9) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk4_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 8) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber44ReverseSingleStep9 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 1) (tmFiber44StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 1) (tmFiber44StateAt 9)
    (tmFiber44RowAt 9).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 9) (by decide) tmFiber44ReverseRow_9_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_10_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 10) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk5_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 10) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber44ReverseSingleStep10 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 2) (tmFiber44StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 2) (tmFiber44StateAt 10)
    (tmFiber44RowAt 10).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 10) (by decide) tmFiber44ReverseRow_10_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_11_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 11) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk5_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 10) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber44ReverseSingleStep11 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 3) (tmFiber44StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 3) (tmFiber44StateAt 11)
    (tmFiber44RowAt 11).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 11) (by decide) tmFiber44ReverseRow_11_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_12_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 12) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk6_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 12) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber44ReverseSingleStep12 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 4) (tmFiber44StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 4) (tmFiber44StateAt 12)
    (tmFiber44RowAt 12).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 12) (by decide) tmFiber44ReverseRow_12_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_13_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 13) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk6_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 12) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber44ReverseSingleStep13 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 5) (tmFiber44StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 5) (tmFiber44StateAt 13)
    (tmFiber44RowAt 13).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 13) (by decide) tmFiber44ReverseRow_13_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_14_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 14) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk7_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 14) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber44ReverseSingleStep14 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 6) (tmFiber44StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 6) (tmFiber44StateAt 14)
    (tmFiber44RowAt 14).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 14) (by decide) tmFiber44ReverseRow_14_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_15_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 15) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk7_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 14) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber44ReverseSingleStep15 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 7) (tmFiber44StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 7) (tmFiber44StateAt 15)
    (tmFiber44RowAt 15).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 15) (by decide) tmFiber44ReverseRow_15_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_16_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 16) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk8_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 16) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber44ReverseSingleStep16 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 8) (tmFiber44StateAt 16) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 8) (tmFiber44StateAt 16)
    (tmFiber44RowAt 16).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 16) (by decide) tmFiber44ReverseRow_16_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_17_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 17) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk8_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 16) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber44ReverseSingleStep17 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 9) (tmFiber44StateAt 17) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 9) (tmFiber44StateAt 17)
    (tmFiber44RowAt 17).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 17) (by decide) tmFiber44ReverseRow_17_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_18_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 18) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk9_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 18) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber44ReverseSingleStep18 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 10) (tmFiber44StateAt 18) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 10) (tmFiber44StateAt 18)
    (tmFiber44RowAt 18).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 18) (by decide) tmFiber44ReverseRow_18_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_19_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 19) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk9_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 18) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber44ReverseSingleStep19 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 11) (tmFiber44StateAt 19) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 11) (tmFiber44StateAt 19)
    (tmFiber44RowAt 19).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 19) (by decide) tmFiber44ReverseRow_19_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_20_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 20) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk10_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 20) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber44ReverseSingleStep20 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 12) (tmFiber44StateAt 20) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 12) (tmFiber44StateAt 20)
    (tmFiber44RowAt 20).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 20) (by decide) tmFiber44ReverseRow_20_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_21_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 21) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk10_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 20) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber44ReverseSingleStep21 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 13) (tmFiber44StateAt 21) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 13) (tmFiber44StateAt 21)
    (tmFiber44RowAt 21).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 21) (by decide) tmFiber44ReverseRow_21_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_22_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 22) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk11_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 22) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber44ReverseSingleStep22 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 14) (tmFiber44StateAt 22) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 14) (tmFiber44StateAt 22)
    (tmFiber44RowAt 22).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 22) (by decide) tmFiber44ReverseRow_22_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_23_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 23) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk11_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 22) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber44ReverseSingleStep23 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 15) (tmFiber44StateAt 23) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 15) (tmFiber44StateAt 23)
    (tmFiber44RowAt 23).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 23) (by decide) tmFiber44ReverseRow_23_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_24_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 24) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk12_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 24) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber44ReverseSingleStep24 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 0) (tmFiber44StateAt 24) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 0) (tmFiber44StateAt 24)
    (tmFiber44RowAt 24).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 24) (by decide) tmFiber44ReverseRow_24_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_25_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 25) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk12_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 24) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber44ReverseSingleStep25 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 1) (tmFiber44StateAt 25) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 1) (tmFiber44StateAt 25)
    (tmFiber44RowAt 25).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 25) (by decide) tmFiber44ReverseRow_25_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_26_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 26) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk13_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 26) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber44ReverseSingleStep26 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 2) (tmFiber44StateAt 26) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 2) (tmFiber44StateAt 26)
    (tmFiber44RowAt 26).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 26) (by decide) tmFiber44ReverseRow_26_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_27_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 27) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk13_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 26) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber44ReverseSingleStep27 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 3) (tmFiber44StateAt 27) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 3) (tmFiber44StateAt 27)
    (tmFiber44RowAt 27).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 27) (by decide) tmFiber44ReverseRow_27_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_28_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 28) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk14_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 28) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber44ReverseSingleStep28 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 4) (tmFiber44StateAt 28) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 4) (tmFiber44StateAt 28)
    (tmFiber44RowAt 28).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 28) (by decide) tmFiber44ReverseRow_28_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_29_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 29) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk14_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 28) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber44ReverseSingleStep29 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 5) (tmFiber44StateAt 29) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 5) (tmFiber44StateAt 29)
    (tmFiber44RowAt 29).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 29) (by decide) tmFiber44ReverseRow_29_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_30_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 30) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk15_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 30) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber44ReverseSingleStep30 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 6) (tmFiber44StateAt 30) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 6) (tmFiber44StateAt 30)
    (tmFiber44RowAt 30).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 30) (by decide) tmFiber44ReverseRow_30_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_31_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 31) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk15_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 30) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber44ReverseSingleStep31 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 7) (tmFiber44StateAt 31) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 7) (tmFiber44StateAt 31)
    (tmFiber44RowAt 31).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 31) (by decide) tmFiber44ReverseRow_31_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_32_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 32) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk16_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 32) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber44ReverseSingleStep32 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 0) (tmFiber44StateAt 32) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 0) (tmFiber44StateAt 32)
    (tmFiber44RowAt 32).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 32) (by decide) tmFiber44ReverseRow_32_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_33_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 33) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk16_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 32) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber44ReverseSingleStep33 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 1) (tmFiber44StateAt 33) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 1) (tmFiber44StateAt 33)
    (tmFiber44RowAt 33).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 33) (by decide) tmFiber44ReverseRow_33_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_34_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 34) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk17_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 34) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber44ReverseSingleStep34 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 2) (tmFiber44StateAt 34) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 2) (tmFiber44StateAt 34)
    (tmFiber44RowAt 34).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 34) (by decide) tmFiber44ReverseRow_34_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_35_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 35) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk17_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 34) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber44ReverseSingleStep35 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 3) (tmFiber44StateAt 35) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 3) (tmFiber44StateAt 35)
    (tmFiber44RowAt 35).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 35) (by decide) tmFiber44ReverseRow_35_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_36_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 36) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk18_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 36) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber44ReverseSingleStep36 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 32) (tmFiber44StateAt 36) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 32) (tmFiber44StateAt 36)
    (tmFiber44RowAt 36).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 36) (by decide) tmFiber44ReverseRow_36_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_37_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 37) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk18_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 36) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber44ReverseSingleStep37 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 33) (tmFiber44StateAt 37) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 33) (tmFiber44StateAt 37)
    (tmFiber44RowAt 37).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 37) (by decide) tmFiber44ReverseRow_37_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_38_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 38) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk19_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 38) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber44ReverseSingleStep38 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 6) (tmFiber44StateAt 38) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 6) (tmFiber44StateAt 38)
    (tmFiber44RowAt 38).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 38) (by decide) tmFiber44ReverseRow_38_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_39_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 39) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk19_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 38) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber44ReverseSingleStep39 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 7) (tmFiber44StateAt 39) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 7) (tmFiber44StateAt 39)
    (tmFiber44RowAt 39).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 39) (by decide) tmFiber44ReverseRow_39_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_40_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 40) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk20_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 40) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber44ReverseSingleStep40 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 8) (tmFiber44StateAt 40) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 8) (tmFiber44StateAt 40)
    (tmFiber44RowAt 40).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 40) (by decide) tmFiber44ReverseRow_40_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_41_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 41) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk20_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 40) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber44ReverseSingleStep41 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 9) (tmFiber44StateAt 41) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 9) (tmFiber44StateAt 41)
    (tmFiber44RowAt 41).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 41) (by decide) tmFiber44ReverseRow_41_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_42_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 42) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk21_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 42) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber44ReverseSingleStep42 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 10) (tmFiber44StateAt 42) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 10) (tmFiber44StateAt 42)
    (tmFiber44RowAt 42).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 42) (by decide) tmFiber44ReverseRow_42_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_43_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 43) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk21_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 42) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber44ReverseSingleStep43 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 11) (tmFiber44StateAt 43) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 11) (tmFiber44StateAt 43)
    (tmFiber44RowAt 43).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 43) (by decide) tmFiber44ReverseRow_43_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_44_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 44) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk22_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 44) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber44ReverseSingleStep44 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 40) (tmFiber44StateAt 44) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 40) (tmFiber44StateAt 44)
    (tmFiber44RowAt 44).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 44) (by decide) tmFiber44ReverseRow_44_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_45_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 45) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk22_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 44) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber44ReverseSingleStep45 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 41) (tmFiber44StateAt 45) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 41) (tmFiber44StateAt 45)
    (tmFiber44RowAt 45).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 45) (by decide) tmFiber44ReverseRow_45_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_46_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 46) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk23_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 46) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber44ReverseSingleStep46 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 14) (tmFiber44StateAt 46) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 14) (tmFiber44StateAt 46)
    (tmFiber44RowAt 46).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 46) (by decide) tmFiber44ReverseRow_46_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_47_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 47) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk23_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 46) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber44ReverseSingleStep47 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 15) (tmFiber44StateAt 47) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 15) (tmFiber44StateAt 47)
    (tmFiber44RowAt 47).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 47) (by decide) tmFiber44ReverseRow_47_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_48_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 48) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk24_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 48) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber44ReverseSingleStep48 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 32) (tmFiber44StateAt 48) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 32) (tmFiber44StateAt 48)
    (tmFiber44RowAt 48).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 48) (by decide) tmFiber44ReverseRow_48_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_49_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 49) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk24_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 48) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber44ReverseSingleStep49 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 33) (tmFiber44StateAt 49) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 33) (tmFiber44StateAt 49)
    (tmFiber44RowAt 49).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 49) (by decide) tmFiber44ReverseRow_49_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_50_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 50) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk25_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 50) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber44ReverseSingleStep50 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 34) (tmFiber44StateAt 50) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 34) (tmFiber44StateAt 50)
    (tmFiber44RowAt 50).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 50) (by decide) tmFiber44ReverseRow_50_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_51_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 51) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk25_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 50) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber44ReverseSingleStep51 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 35) (tmFiber44StateAt 51) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 35) (tmFiber44StateAt 51)
    (tmFiber44RowAt 51).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 51) (by decide) tmFiber44ReverseRow_51_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_52_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 52) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk26_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 52) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber44ReverseSingleStep52 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 36) (tmFiber44StateAt 52) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 36) (tmFiber44StateAt 52)
    (tmFiber44RowAt 52).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 52) (by decide) tmFiber44ReverseRow_52_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_53_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 53) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk26_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 52) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber44ReverseSingleStep53 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 37) (tmFiber44StateAt 53) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 37) (tmFiber44StateAt 53)
    (tmFiber44RowAt 53).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 53) (by decide) tmFiber44ReverseRow_53_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_54_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 54) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk27_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 54) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber44ReverseSingleStep54 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 38) (tmFiber44StateAt 54) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 38) (tmFiber44StateAt 54)
    (tmFiber44RowAt 54).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 54) (by decide) tmFiber44ReverseRow_54_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_55_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 55) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk27_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 54) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber44ReverseSingleStep55 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 39) (tmFiber44StateAt 55) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 39) (tmFiber44StateAt 55)
    (tmFiber44RowAt 55).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 55) (by decide) tmFiber44ReverseRow_55_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_56_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 56) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk28_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 56) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber44ReverseSingleStep56 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 24) (tmFiber44StateAt 56) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 24) (tmFiber44StateAt 56)
    (tmFiber44RowAt 56).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 56) (by decide) tmFiber44ReverseRow_56_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_57_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 57) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk28_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 56) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber44ReverseSingleStep57 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 25) (tmFiber44StateAt 57) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 25) (tmFiber44StateAt 57)
    (tmFiber44RowAt 57).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 57) (by decide) tmFiber44ReverseRow_57_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_58_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 58) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk29_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 58) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber44ReverseSingleStep58 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 26) (tmFiber44StateAt 58) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 26) (tmFiber44StateAt 58)
    (tmFiber44RowAt 58).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 58) (by decide) tmFiber44ReverseRow_58_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_59_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 59) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk29_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 58) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber44ReverseSingleStep59 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 27) (tmFiber44StateAt 59) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 27) (tmFiber44StateAt 59)
    (tmFiber44RowAt 59).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 59) (by decide) tmFiber44ReverseRow_59_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_60_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 60) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk30_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 60) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber44ReverseSingleStep60 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 56) (tmFiber44StateAt 60) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 56) (tmFiber44StateAt 60)
    (tmFiber44RowAt 60).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 60) (by decide) tmFiber44ReverseRow_60_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_61_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 61) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk30_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 60) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber44ReverseSingleStep61 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 57) (tmFiber44StateAt 61) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 57) (tmFiber44StateAt 61)
    (tmFiber44RowAt 61).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 61) (by decide) tmFiber44ReverseRow_61_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_62_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 62) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk31_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 62) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber44ReverseSingleStep62 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 30) (tmFiber44StateAt 62) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 30) (tmFiber44StateAt 62)
    (tmFiber44RowAt 62).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 62) (by decide) tmFiber44ReverseRow_62_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44ReverseRow_63_ok :
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 63) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber44Chunk31_ok
  change (tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 62) &&
    tmRowReverseValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber44ReverseSingleStep63 :
    chainSingleKempeStep tmWord (tmFiber44StateAt 31) (tmFiber44StateAt 63) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber44StateAt 31) (tmFiber44StateAt 63)
    (tmFiber44RowAt 63).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber44Key tmFiber44Expected
        (tmFiber44RowAt 63) (by decide) tmFiber44ReverseRow_63_ok
      simpa [tmFiber44StateAt, tmFiber44RowAt, tmFiber44Rows, listGetD, directRow] using h)

theorem tmFiber44State1_in_pass1_prefix1 :
    tmFiber44StateAt 1 ∈ chainClosureStep tmWord tmFiber44Prefix1 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 0 ∈
      chainClosureStep tmWord tmFiber44Prefix0 ([tmFiber44StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber44Prefix0
      ([tmFiber44StateAt 0]) (tmFiber44StateAt 0) (by simp)
  rw [show tmFiber44Prefix1 = tmFiber44Prefix0 ++ [tmFiber44StateAt 1] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 1) []
    (chainClosureStep tmWord tmFiber44Prefix0 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 0) hparentBefore tmFiber44ReverseSingleStep1
theorem tmFiber44State1_in_pass1_full :
    tmFiber44StateAt 1 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix1 ++ [tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix1 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 1) tmFiber44State1_in_pass1_prefix1
theorem tmFiber44State2_in_pass1_prefix2 :
    tmFiber44StateAt 2 ∈ chainClosureStep tmWord tmFiber44Prefix2 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 0 ∈
      chainClosureStep tmWord tmFiber44Prefix1 ([tmFiber44StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber44Prefix1
      ([tmFiber44StateAt 0]) (tmFiber44StateAt 0) (by simp)
  rw [show tmFiber44Prefix2 = tmFiber44Prefix1 ++ [tmFiber44StateAt 2] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 2) []
    (chainClosureStep tmWord tmFiber44Prefix1 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 0) hparentBefore tmFiber44ReverseSingleStep2
theorem tmFiber44State2_in_pass1_full :
    tmFiber44StateAt 2 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix2 ++ [tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix2 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 2) tmFiber44State2_in_pass1_prefix2
theorem tmFiber44State3_in_pass1_prefix3 :
    tmFiber44StateAt 3 ∈ chainClosureStep tmWord tmFiber44Prefix3 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 1 ∈
      chainClosureStep tmWord tmFiber44Prefix2 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix2 = tmFiber44Prefix1 ++ [tmFiber44StateAt 2] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 2]
      (chainClosureStep tmWord tmFiber44Prefix1 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 1) tmFiber44State1_in_pass1_prefix1
  rw [show tmFiber44Prefix3 = tmFiber44Prefix2 ++ [tmFiber44StateAt 3] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 3) []
    (chainClosureStep tmWord tmFiber44Prefix2 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 1) hparentBefore tmFiber44ReverseSingleStep3
theorem tmFiber44State3_in_pass1_full :
    tmFiber44StateAt 3 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix3 ++ [tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix3 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 3) tmFiber44State3_in_pass1_prefix3
theorem tmFiber44State4_in_pass1_prefix4 :
    tmFiber44StateAt 4 ∈ chainClosureStep tmWord tmFiber44Prefix4 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 2 ∈
      chainClosureStep tmWord tmFiber44Prefix3 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix3 = tmFiber44Prefix2 ++ [tmFiber44StateAt 3] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 3]
      (chainClosureStep tmWord tmFiber44Prefix2 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 2) tmFiber44State2_in_pass1_prefix2
  rw [show tmFiber44Prefix4 = tmFiber44Prefix3 ++ [tmFiber44StateAt 4] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 4) []
    (chainClosureStep tmWord tmFiber44Prefix3 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 2) hparentBefore tmFiber44ReverseSingleStep4
theorem tmFiber44State4_in_pass1_full :
    tmFiber44StateAt 4 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix4 ++ [tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix4 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 4) tmFiber44State4_in_pass1_prefix4
theorem tmFiber44State6_in_pass1_prefix6 :
    tmFiber44StateAt 6 ∈ chainClosureStep tmWord tmFiber44Prefix6 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 1 ∈
      chainClosureStep tmWord tmFiber44Prefix5 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix5 = tmFiber44Prefix1 ++ [tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5]
      (chainClosureStep tmWord tmFiber44Prefix1 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 1) tmFiber44State1_in_pass1_prefix1
  rw [show tmFiber44Prefix6 = tmFiber44Prefix5 ++ [tmFiber44StateAt 6] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 6) []
    (chainClosureStep tmWord tmFiber44Prefix5 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 1) hparentBefore tmFiber44ReverseSingleStep6
theorem tmFiber44State6_in_pass1_full :
    tmFiber44StateAt 6 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix6 ++ [tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix6 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 6) tmFiber44State6_in_pass1_prefix6
theorem tmFiber44State7_in_pass1_prefix7 :
    tmFiber44StateAt 7 ∈ chainClosureStep tmWord tmFiber44Prefix7 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 0 ∈
      chainClosureStep tmWord tmFiber44Prefix6 ([tmFiber44StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber44Prefix6
      ([tmFiber44StateAt 0]) (tmFiber44StateAt 0) (by simp)
  rw [show tmFiber44Prefix7 = tmFiber44Prefix6 ++ [tmFiber44StateAt 7] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 7) []
    (chainClosureStep tmWord tmFiber44Prefix6 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 0) hparentBefore tmFiber44ReverseSingleStep7
theorem tmFiber44State7_in_pass1_full :
    tmFiber44StateAt 7 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix7 ++ [tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix7 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 7) tmFiber44State7_in_pass1_prefix7
theorem tmFiber44State8_in_pass1_prefix8 :
    tmFiber44StateAt 8 ∈ chainClosureStep tmWord tmFiber44Prefix8 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 0 ∈
      chainClosureStep tmWord tmFiber44Prefix7 ([tmFiber44StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber44Prefix7
      ([tmFiber44StateAt 0]) (tmFiber44StateAt 0) (by simp)
  rw [show tmFiber44Prefix8 = tmFiber44Prefix7 ++ [tmFiber44StateAt 8] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 8) []
    (chainClosureStep tmWord tmFiber44Prefix7 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 0) hparentBefore tmFiber44ReverseSingleStep8
theorem tmFiber44State8_in_pass1_full :
    tmFiber44StateAt 8 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix8 ++ [tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix8 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 8) tmFiber44State8_in_pass1_prefix8
theorem tmFiber44State9_in_pass1_prefix9 :
    tmFiber44StateAt 9 ∈ chainClosureStep tmWord tmFiber44Prefix9 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 1 ∈
      chainClosureStep tmWord tmFiber44Prefix8 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix8 = tmFiber44Prefix1 ++ [tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8]
      (chainClosureStep tmWord tmFiber44Prefix1 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 1) tmFiber44State1_in_pass1_prefix1
  rw [show tmFiber44Prefix9 = tmFiber44Prefix8 ++ [tmFiber44StateAt 9] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 9) []
    (chainClosureStep tmWord tmFiber44Prefix8 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 1) hparentBefore tmFiber44ReverseSingleStep9
theorem tmFiber44State9_in_pass1_full :
    tmFiber44StateAt 9 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix9 ++ [tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix9 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 9) tmFiber44State9_in_pass1_prefix9
theorem tmFiber44State10_in_pass1_prefix10 :
    tmFiber44StateAt 10 ∈ chainClosureStep tmWord tmFiber44Prefix10 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 2 ∈
      chainClosureStep tmWord tmFiber44Prefix9 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix9 = tmFiber44Prefix2 ++ [tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9]
      (chainClosureStep tmWord tmFiber44Prefix2 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 2) tmFiber44State2_in_pass1_prefix2
  rw [show tmFiber44Prefix10 = tmFiber44Prefix9 ++ [tmFiber44StateAt 10] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 10) []
    (chainClosureStep tmWord tmFiber44Prefix9 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 2) hparentBefore tmFiber44ReverseSingleStep10
theorem tmFiber44State10_in_pass1_full :
    tmFiber44StateAt 10 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix10 ++ [tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix10 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 10) tmFiber44State10_in_pass1_prefix10
theorem tmFiber44State11_in_pass1_prefix11 :
    tmFiber44StateAt 11 ∈ chainClosureStep tmWord tmFiber44Prefix11 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 3 ∈
      chainClosureStep tmWord tmFiber44Prefix10 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix10 = tmFiber44Prefix3 ++ [tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10]
      (chainClosureStep tmWord tmFiber44Prefix3 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 3) tmFiber44State3_in_pass1_prefix3
  rw [show tmFiber44Prefix11 = tmFiber44Prefix10 ++ [tmFiber44StateAt 11] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 11) []
    (chainClosureStep tmWord tmFiber44Prefix10 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 3) hparentBefore tmFiber44ReverseSingleStep11
theorem tmFiber44State11_in_pass1_full :
    tmFiber44StateAt 11 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix11 ++ [tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix11 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 11) tmFiber44State11_in_pass1_prefix11
theorem tmFiber44State12_in_pass1_prefix12 :
    tmFiber44StateAt 12 ∈ chainClosureStep tmWord tmFiber44Prefix12 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 4 ∈
      chainClosureStep tmWord tmFiber44Prefix11 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix11 = tmFiber44Prefix4 ++ [tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11]
      (chainClosureStep tmWord tmFiber44Prefix4 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 4) tmFiber44State4_in_pass1_prefix4
  rw [show tmFiber44Prefix12 = tmFiber44Prefix11 ++ [tmFiber44StateAt 12] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 12) []
    (chainClosureStep tmWord tmFiber44Prefix11 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 4) hparentBefore tmFiber44ReverseSingleStep12
theorem tmFiber44State12_in_pass1_full :
    tmFiber44StateAt 12 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix12 ++ [tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix12 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 12) tmFiber44State12_in_pass1_prefix12
theorem tmFiber44State14_in_pass1_prefix14 :
    tmFiber44StateAt 14 ∈ chainClosureStep tmWord tmFiber44Prefix14 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 6 ∈
      chainClosureStep tmWord tmFiber44Prefix13 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix13 = tmFiber44Prefix6 ++ [tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13]
      (chainClosureStep tmWord tmFiber44Prefix6 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 6) tmFiber44State6_in_pass1_prefix6
  rw [show tmFiber44Prefix14 = tmFiber44Prefix13 ++ [tmFiber44StateAt 14] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 14) []
    (chainClosureStep tmWord tmFiber44Prefix13 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 6) hparentBefore tmFiber44ReverseSingleStep14
theorem tmFiber44State14_in_pass1_full :
    tmFiber44StateAt 14 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix14 ++ [tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix14 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 14) tmFiber44State14_in_pass1_prefix14
theorem tmFiber44State15_in_pass1_prefix15 :
    tmFiber44StateAt 15 ∈ chainClosureStep tmWord tmFiber44Prefix15 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 7 ∈
      chainClosureStep tmWord tmFiber44Prefix14 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix14 = tmFiber44Prefix7 ++ [tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14]
      (chainClosureStep tmWord tmFiber44Prefix7 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 7) tmFiber44State7_in_pass1_prefix7
  rw [show tmFiber44Prefix15 = tmFiber44Prefix14 ++ [tmFiber44StateAt 15] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 15) []
    (chainClosureStep tmWord tmFiber44Prefix14 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 7) hparentBefore tmFiber44ReverseSingleStep15
theorem tmFiber44State15_in_pass1_full :
    tmFiber44StateAt 15 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix15 ++ [tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix15 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 15) tmFiber44State15_in_pass1_prefix15
theorem tmFiber44State16_in_pass1_prefix16 :
    tmFiber44StateAt 16 ∈ chainClosureStep tmWord tmFiber44Prefix16 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 8 ∈
      chainClosureStep tmWord tmFiber44Prefix15 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix15 = tmFiber44Prefix8 ++ [tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15]
      (chainClosureStep tmWord tmFiber44Prefix8 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 8) tmFiber44State8_in_pass1_prefix8
  rw [show tmFiber44Prefix16 = tmFiber44Prefix15 ++ [tmFiber44StateAt 16] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 16) []
    (chainClosureStep tmWord tmFiber44Prefix15 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 8) hparentBefore tmFiber44ReverseSingleStep16
theorem tmFiber44State16_in_pass1_full :
    tmFiber44StateAt 16 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix16 ++ [tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix16 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 16) tmFiber44State16_in_pass1_prefix16
theorem tmFiber44State17_in_pass1_prefix17 :
    tmFiber44StateAt 17 ∈ chainClosureStep tmWord tmFiber44Prefix17 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 9 ∈
      chainClosureStep tmWord tmFiber44Prefix16 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix16 = tmFiber44Prefix9 ++ [tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16]
      (chainClosureStep tmWord tmFiber44Prefix9 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 9) tmFiber44State9_in_pass1_prefix9
  rw [show tmFiber44Prefix17 = tmFiber44Prefix16 ++ [tmFiber44StateAt 17] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 17) []
    (chainClosureStep tmWord tmFiber44Prefix16 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 9) hparentBefore tmFiber44ReverseSingleStep17
theorem tmFiber44State17_in_pass1_full :
    tmFiber44StateAt 17 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix17 ++ [tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix17 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 17) tmFiber44State17_in_pass1_prefix17
theorem tmFiber44State18_in_pass1_prefix18 :
    tmFiber44StateAt 18 ∈ chainClosureStep tmWord tmFiber44Prefix18 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 10 ∈
      chainClosureStep tmWord tmFiber44Prefix17 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix17 = tmFiber44Prefix10 ++ [tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17]
      (chainClosureStep tmWord tmFiber44Prefix10 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 10) tmFiber44State10_in_pass1_prefix10
  rw [show tmFiber44Prefix18 = tmFiber44Prefix17 ++ [tmFiber44StateAt 18] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 18) []
    (chainClosureStep tmWord tmFiber44Prefix17 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 10) hparentBefore tmFiber44ReverseSingleStep18
theorem tmFiber44State18_in_pass1_full :
    tmFiber44StateAt 18 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix18 ++ [tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix18 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 18) tmFiber44State18_in_pass1_prefix18
theorem tmFiber44State19_in_pass1_prefix19 :
    tmFiber44StateAt 19 ∈ chainClosureStep tmWord tmFiber44Prefix19 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 11 ∈
      chainClosureStep tmWord tmFiber44Prefix18 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix18 = tmFiber44Prefix11 ++ [tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18]
      (chainClosureStep tmWord tmFiber44Prefix11 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 11) tmFiber44State11_in_pass1_prefix11
  rw [show tmFiber44Prefix19 = tmFiber44Prefix18 ++ [tmFiber44StateAt 19] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 19) []
    (chainClosureStep tmWord tmFiber44Prefix18 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 11) hparentBefore tmFiber44ReverseSingleStep19
theorem tmFiber44State19_in_pass1_full :
    tmFiber44StateAt 19 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix19 ++ [tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix19 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 19) tmFiber44State19_in_pass1_prefix19
theorem tmFiber44State20_in_pass1_prefix20 :
    tmFiber44StateAt 20 ∈ chainClosureStep tmWord tmFiber44Prefix20 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 12 ∈
      chainClosureStep tmWord tmFiber44Prefix19 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix19 = tmFiber44Prefix12 ++ [tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19]
      (chainClosureStep tmWord tmFiber44Prefix12 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 12) tmFiber44State12_in_pass1_prefix12
  rw [show tmFiber44Prefix20 = tmFiber44Prefix19 ++ [tmFiber44StateAt 20] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 20) []
    (chainClosureStep tmWord tmFiber44Prefix19 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 12) hparentBefore tmFiber44ReverseSingleStep20
theorem tmFiber44State20_in_pass1_full :
    tmFiber44StateAt 20 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix20 ++ [tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix20 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 20) tmFiber44State20_in_pass1_prefix20
theorem tmFiber44State22_in_pass1_prefix22 :
    tmFiber44StateAt 22 ∈ chainClosureStep tmWord tmFiber44Prefix22 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 14 ∈
      chainClosureStep tmWord tmFiber44Prefix21 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix21 = tmFiber44Prefix14 ++ [tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21]
      (chainClosureStep tmWord tmFiber44Prefix14 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 14) tmFiber44State14_in_pass1_prefix14
  rw [show tmFiber44Prefix22 = tmFiber44Prefix21 ++ [tmFiber44StateAt 22] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 22) []
    (chainClosureStep tmWord tmFiber44Prefix21 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 14) hparentBefore tmFiber44ReverseSingleStep22
theorem tmFiber44State22_in_pass1_full :
    tmFiber44StateAt 22 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix22 ++ [tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix22 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 22) tmFiber44State22_in_pass1_prefix22
theorem tmFiber44State23_in_pass1_prefix23 :
    tmFiber44StateAt 23 ∈ chainClosureStep tmWord tmFiber44Prefix23 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 15 ∈
      chainClosureStep tmWord tmFiber44Prefix22 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix22 = tmFiber44Prefix15 ++ [tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22]
      (chainClosureStep tmWord tmFiber44Prefix15 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 15) tmFiber44State15_in_pass1_prefix15
  rw [show tmFiber44Prefix23 = tmFiber44Prefix22 ++ [tmFiber44StateAt 23] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 23) []
    (chainClosureStep tmWord tmFiber44Prefix22 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 15) hparentBefore tmFiber44ReverseSingleStep23
theorem tmFiber44State23_in_pass1_full :
    tmFiber44StateAt 23 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix23 ++ [tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix23 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 23) tmFiber44State23_in_pass1_prefix23
theorem tmFiber44State24_in_pass1_prefix24 :
    tmFiber44StateAt 24 ∈ chainClosureStep tmWord tmFiber44Prefix24 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 0 ∈
      chainClosureStep tmWord tmFiber44Prefix23 ([tmFiber44StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber44Prefix23
      ([tmFiber44StateAt 0]) (tmFiber44StateAt 0) (by simp)
  rw [show tmFiber44Prefix24 = tmFiber44Prefix23 ++ [tmFiber44StateAt 24] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 24) []
    (chainClosureStep tmWord tmFiber44Prefix23 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 0) hparentBefore tmFiber44ReverseSingleStep24
theorem tmFiber44State24_in_pass1_full :
    tmFiber44StateAt 24 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix24 ++ [tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix24 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 24) tmFiber44State24_in_pass1_prefix24
theorem tmFiber44State25_in_pass1_prefix25 :
    tmFiber44StateAt 25 ∈ chainClosureStep tmWord tmFiber44Prefix25 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 1 ∈
      chainClosureStep tmWord tmFiber44Prefix24 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix24 = tmFiber44Prefix1 ++ [tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24]
      (chainClosureStep tmWord tmFiber44Prefix1 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 1) tmFiber44State1_in_pass1_prefix1
  rw [show tmFiber44Prefix25 = tmFiber44Prefix24 ++ [tmFiber44StateAt 25] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 25) []
    (chainClosureStep tmWord tmFiber44Prefix24 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 1) hparentBefore tmFiber44ReverseSingleStep25
theorem tmFiber44State25_in_pass1_full :
    tmFiber44StateAt 25 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix25 ++ [tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix25 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 25) tmFiber44State25_in_pass1_prefix25
theorem tmFiber44State26_in_pass1_prefix26 :
    tmFiber44StateAt 26 ∈ chainClosureStep tmWord tmFiber44Prefix26 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 2 ∈
      chainClosureStep tmWord tmFiber44Prefix25 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix25 = tmFiber44Prefix2 ++ [tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25]
      (chainClosureStep tmWord tmFiber44Prefix2 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 2) tmFiber44State2_in_pass1_prefix2
  rw [show tmFiber44Prefix26 = tmFiber44Prefix25 ++ [tmFiber44StateAt 26] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 26) []
    (chainClosureStep tmWord tmFiber44Prefix25 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 2) hparentBefore tmFiber44ReverseSingleStep26
theorem tmFiber44State26_in_pass1_full :
    tmFiber44StateAt 26 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix26 ++ [tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix26 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 26) tmFiber44State26_in_pass1_prefix26
theorem tmFiber44State27_in_pass1_prefix27 :
    tmFiber44StateAt 27 ∈ chainClosureStep tmWord tmFiber44Prefix27 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 3 ∈
      chainClosureStep tmWord tmFiber44Prefix26 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix26 = tmFiber44Prefix3 ++ [tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26]
      (chainClosureStep tmWord tmFiber44Prefix3 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 3) tmFiber44State3_in_pass1_prefix3
  rw [show tmFiber44Prefix27 = tmFiber44Prefix26 ++ [tmFiber44StateAt 27] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 27) []
    (chainClosureStep tmWord tmFiber44Prefix26 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 3) hparentBefore tmFiber44ReverseSingleStep27
theorem tmFiber44State27_in_pass1_full :
    tmFiber44StateAt 27 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix27 ++ [tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix27 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 27) tmFiber44State27_in_pass1_prefix27
theorem tmFiber44State28_in_pass1_prefix28 :
    tmFiber44StateAt 28 ∈ chainClosureStep tmWord tmFiber44Prefix28 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 4 ∈
      chainClosureStep tmWord tmFiber44Prefix27 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix27 = tmFiber44Prefix4 ++ [tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27]
      (chainClosureStep tmWord tmFiber44Prefix4 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 4) tmFiber44State4_in_pass1_prefix4
  rw [show tmFiber44Prefix28 = tmFiber44Prefix27 ++ [tmFiber44StateAt 28] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 28) []
    (chainClosureStep tmWord tmFiber44Prefix27 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 4) hparentBefore tmFiber44ReverseSingleStep28
theorem tmFiber44State28_in_pass1_full :
    tmFiber44StateAt 28 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix28 ++ [tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix28 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 28) tmFiber44State28_in_pass1_prefix28
theorem tmFiber44State30_in_pass1_prefix30 :
    tmFiber44StateAt 30 ∈ chainClosureStep tmWord tmFiber44Prefix30 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 6 ∈
      chainClosureStep tmWord tmFiber44Prefix29 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix29 = tmFiber44Prefix6 ++ [tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29]
      (chainClosureStep tmWord tmFiber44Prefix6 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 6) tmFiber44State6_in_pass1_prefix6
  rw [show tmFiber44Prefix30 = tmFiber44Prefix29 ++ [tmFiber44StateAt 30] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 30) []
    (chainClosureStep tmWord tmFiber44Prefix29 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 6) hparentBefore tmFiber44ReverseSingleStep30
theorem tmFiber44State30_in_pass1_full :
    tmFiber44StateAt 30 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix30 ++ [tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix30 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 30) tmFiber44State30_in_pass1_prefix30
theorem tmFiber44State31_in_pass1_prefix31 :
    tmFiber44StateAt 31 ∈ chainClosureStep tmWord tmFiber44Prefix31 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 7 ∈
      chainClosureStep tmWord tmFiber44Prefix30 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix30 = tmFiber44Prefix7 ++ [tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30]
      (chainClosureStep tmWord tmFiber44Prefix7 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 7) tmFiber44State7_in_pass1_prefix7
  rw [show tmFiber44Prefix31 = tmFiber44Prefix30 ++ [tmFiber44StateAt 31] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 31) []
    (chainClosureStep tmWord tmFiber44Prefix30 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 7) hparentBefore tmFiber44ReverseSingleStep31
theorem tmFiber44State31_in_pass1_full :
    tmFiber44StateAt 31 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix31 ++ [tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix31 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 31) tmFiber44State31_in_pass1_prefix31
theorem tmFiber44State32_in_pass1_prefix32 :
    tmFiber44StateAt 32 ∈ chainClosureStep tmWord tmFiber44Prefix32 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 0 ∈
      chainClosureStep tmWord tmFiber44Prefix31 ([tmFiber44StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber44Prefix31
      ([tmFiber44StateAt 0]) (tmFiber44StateAt 0) (by simp)
  rw [show tmFiber44Prefix32 = tmFiber44Prefix31 ++ [tmFiber44StateAt 32] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 32) []
    (chainClosureStep tmWord tmFiber44Prefix31 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 0) hparentBefore tmFiber44ReverseSingleStep32
theorem tmFiber44State32_in_pass1_full :
    tmFiber44StateAt 32 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix32 ++ [tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix32 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 32) tmFiber44State32_in_pass1_prefix32
theorem tmFiber44State33_in_pass1_prefix33 :
    tmFiber44StateAt 33 ∈ chainClosureStep tmWord tmFiber44Prefix33 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 1 ∈
      chainClosureStep tmWord tmFiber44Prefix32 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix32 = tmFiber44Prefix1 ++ [tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 2, tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32]
      (chainClosureStep tmWord tmFiber44Prefix1 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 1) tmFiber44State1_in_pass1_prefix1
  rw [show tmFiber44Prefix33 = tmFiber44Prefix32 ++ [tmFiber44StateAt 33] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 33) []
    (chainClosureStep tmWord tmFiber44Prefix32 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 1) hparentBefore tmFiber44ReverseSingleStep33
theorem tmFiber44State33_in_pass1_full :
    tmFiber44StateAt 33 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix33 ++ [tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix33 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 33) tmFiber44State33_in_pass1_prefix33
theorem tmFiber44State34_in_pass1_prefix34 :
    tmFiber44StateAt 34 ∈ chainClosureStep tmWord tmFiber44Prefix34 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 2 ∈
      chainClosureStep tmWord tmFiber44Prefix33 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix33 = tmFiber44Prefix2 ++ [tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 3, tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33]
      (chainClosureStep tmWord tmFiber44Prefix2 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 2) tmFiber44State2_in_pass1_prefix2
  rw [show tmFiber44Prefix34 = tmFiber44Prefix33 ++ [tmFiber44StateAt 34] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 34) []
    (chainClosureStep tmWord tmFiber44Prefix33 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 2) hparentBefore tmFiber44ReverseSingleStep34
theorem tmFiber44State34_in_pass1_full :
    tmFiber44StateAt 34 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix34 ++ [tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix34 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 34) tmFiber44State34_in_pass1_prefix34
theorem tmFiber44State35_in_pass1_prefix35 :
    tmFiber44StateAt 35 ∈ chainClosureStep tmWord tmFiber44Prefix35 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 3 ∈
      chainClosureStep tmWord tmFiber44Prefix34 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix34 = tmFiber44Prefix3 ++ [tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 4, tmFiber44StateAt 5, tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34]
      (chainClosureStep tmWord tmFiber44Prefix3 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 3) tmFiber44State3_in_pass1_prefix3
  rw [show tmFiber44Prefix35 = tmFiber44Prefix34 ++ [tmFiber44StateAt 35] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 35) []
    (chainClosureStep tmWord tmFiber44Prefix34 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 3) hparentBefore tmFiber44ReverseSingleStep35
theorem tmFiber44State35_in_pass1_full :
    tmFiber44StateAt 35 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix35 ++ [tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix35 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 35) tmFiber44State35_in_pass1_prefix35
theorem tmFiber44State36_in_pass1_prefix36 :
    tmFiber44StateAt 36 ∈ chainClosureStep tmWord tmFiber44Prefix36 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 32 ∈
      chainClosureStep tmWord tmFiber44Prefix35 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix35 = tmFiber44Prefix32 ++ [tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35]
      (chainClosureStep tmWord tmFiber44Prefix32 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 32) tmFiber44State32_in_pass1_prefix32
  rw [show tmFiber44Prefix36 = tmFiber44Prefix35 ++ [tmFiber44StateAt 36] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 36) []
    (chainClosureStep tmWord tmFiber44Prefix35 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 32) hparentBefore tmFiber44ReverseSingleStep36
theorem tmFiber44State36_in_pass1_full :
    tmFiber44StateAt 36 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix36 ++ [tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix36 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 36) tmFiber44State36_in_pass1_prefix36
theorem tmFiber44State37_in_pass1_prefix37 :
    tmFiber44StateAt 37 ∈ chainClosureStep tmWord tmFiber44Prefix37 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 33 ∈
      chainClosureStep tmWord tmFiber44Prefix36 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix36 = tmFiber44Prefix33 ++ [tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36]
      (chainClosureStep tmWord tmFiber44Prefix33 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 33) tmFiber44State33_in_pass1_prefix33
  rw [show tmFiber44Prefix37 = tmFiber44Prefix36 ++ [tmFiber44StateAt 37] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 37) []
    (chainClosureStep tmWord tmFiber44Prefix36 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 33) hparentBefore tmFiber44ReverseSingleStep37
theorem tmFiber44State37_in_pass1_full :
    tmFiber44StateAt 37 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix37 ++ [tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix37 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 37) tmFiber44State37_in_pass1_prefix37
theorem tmFiber44State38_in_pass1_prefix38 :
    tmFiber44StateAt 38 ∈ chainClosureStep tmWord tmFiber44Prefix38 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 6 ∈
      chainClosureStep tmWord tmFiber44Prefix37 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix37 = tmFiber44Prefix6 ++ [tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37]
      (chainClosureStep tmWord tmFiber44Prefix6 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 6) tmFiber44State6_in_pass1_prefix6
  rw [show tmFiber44Prefix38 = tmFiber44Prefix37 ++ [tmFiber44StateAt 38] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 38) []
    (chainClosureStep tmWord tmFiber44Prefix37 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 6) hparentBefore tmFiber44ReverseSingleStep38
theorem tmFiber44State38_in_pass1_full :
    tmFiber44StateAt 38 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix38 ++ [tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix38 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 38) tmFiber44State38_in_pass1_prefix38
theorem tmFiber44State39_in_pass1_prefix39 :
    tmFiber44StateAt 39 ∈ chainClosureStep tmWord tmFiber44Prefix39 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 7 ∈
      chainClosureStep tmWord tmFiber44Prefix38 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix38 = tmFiber44Prefix7 ++ [tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38]
      (chainClosureStep tmWord tmFiber44Prefix7 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 7) tmFiber44State7_in_pass1_prefix7
  rw [show tmFiber44Prefix39 = tmFiber44Prefix38 ++ [tmFiber44StateAt 39] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 39) []
    (chainClosureStep tmWord tmFiber44Prefix38 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 7) hparentBefore tmFiber44ReverseSingleStep39
theorem tmFiber44State39_in_pass1_full :
    tmFiber44StateAt 39 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix39 ++ [tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix39 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 39) tmFiber44State39_in_pass1_prefix39
theorem tmFiber44State40_in_pass1_prefix40 :
    tmFiber44StateAt 40 ∈ chainClosureStep tmWord tmFiber44Prefix40 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 8 ∈
      chainClosureStep tmWord tmFiber44Prefix39 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix39 = tmFiber44Prefix8 ++ [tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39]
      (chainClosureStep tmWord tmFiber44Prefix8 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 8) tmFiber44State8_in_pass1_prefix8
  rw [show tmFiber44Prefix40 = tmFiber44Prefix39 ++ [tmFiber44StateAt 40] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 40) []
    (chainClosureStep tmWord tmFiber44Prefix39 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 8) hparentBefore tmFiber44ReverseSingleStep40
theorem tmFiber44State40_in_pass1_full :
    tmFiber44StateAt 40 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix40 ++ [tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix40 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 40) tmFiber44State40_in_pass1_prefix40
theorem tmFiber44State41_in_pass1_prefix41 :
    tmFiber44StateAt 41 ∈ chainClosureStep tmWord tmFiber44Prefix41 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 9 ∈
      chainClosureStep tmWord tmFiber44Prefix40 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix40 = tmFiber44Prefix9 ++ [tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40]
      (chainClosureStep tmWord tmFiber44Prefix9 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 9) tmFiber44State9_in_pass1_prefix9
  rw [show tmFiber44Prefix41 = tmFiber44Prefix40 ++ [tmFiber44StateAt 41] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 41) []
    (chainClosureStep tmWord tmFiber44Prefix40 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 9) hparentBefore tmFiber44ReverseSingleStep41
theorem tmFiber44State41_in_pass1_full :
    tmFiber44StateAt 41 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix41 ++ [tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix41 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 41) tmFiber44State41_in_pass1_prefix41
theorem tmFiber44State42_in_pass1_prefix42 :
    tmFiber44StateAt 42 ∈ chainClosureStep tmWord tmFiber44Prefix42 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 10 ∈
      chainClosureStep tmWord tmFiber44Prefix41 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix41 = tmFiber44Prefix10 ++ [tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41]
      (chainClosureStep tmWord tmFiber44Prefix10 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 10) tmFiber44State10_in_pass1_prefix10
  rw [show tmFiber44Prefix42 = tmFiber44Prefix41 ++ [tmFiber44StateAt 42] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 42) []
    (chainClosureStep tmWord tmFiber44Prefix41 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 10) hparentBefore tmFiber44ReverseSingleStep42
theorem tmFiber44State42_in_pass1_full :
    tmFiber44StateAt 42 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix42 ++ [tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix42 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 42) tmFiber44State42_in_pass1_prefix42
theorem tmFiber44State43_in_pass1_prefix43 :
    tmFiber44StateAt 43 ∈ chainClosureStep tmWord tmFiber44Prefix43 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 11 ∈
      chainClosureStep tmWord tmFiber44Prefix42 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix42 = tmFiber44Prefix11 ++ [tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42]
      (chainClosureStep tmWord tmFiber44Prefix11 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 11) tmFiber44State11_in_pass1_prefix11
  rw [show tmFiber44Prefix43 = tmFiber44Prefix42 ++ [tmFiber44StateAt 43] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 43) []
    (chainClosureStep tmWord tmFiber44Prefix42 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 11) hparentBefore tmFiber44ReverseSingleStep43
theorem tmFiber44State43_in_pass1_full :
    tmFiber44StateAt 43 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix43 ++ [tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix43 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 43) tmFiber44State43_in_pass1_prefix43
theorem tmFiber44State44_in_pass1_prefix44 :
    tmFiber44StateAt 44 ∈ chainClosureStep tmWord tmFiber44Prefix44 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 40 ∈
      chainClosureStep tmWord tmFiber44Prefix43 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix43 = tmFiber44Prefix40 ++ [tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43]
      (chainClosureStep tmWord tmFiber44Prefix40 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 40) tmFiber44State40_in_pass1_prefix40
  rw [show tmFiber44Prefix44 = tmFiber44Prefix43 ++ [tmFiber44StateAt 44] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 44) []
    (chainClosureStep tmWord tmFiber44Prefix43 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 40) hparentBefore tmFiber44ReverseSingleStep44
theorem tmFiber44State44_in_pass1_full :
    tmFiber44StateAt 44 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix44 ++ [tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix44 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 44) tmFiber44State44_in_pass1_prefix44
theorem tmFiber44State45_in_pass1_prefix45 :
    tmFiber44StateAt 45 ∈ chainClosureStep tmWord tmFiber44Prefix45 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 41 ∈
      chainClosureStep tmWord tmFiber44Prefix44 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix44 = tmFiber44Prefix41 ++ [tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44]
      (chainClosureStep tmWord tmFiber44Prefix41 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 41) tmFiber44State41_in_pass1_prefix41
  rw [show tmFiber44Prefix45 = tmFiber44Prefix44 ++ [tmFiber44StateAt 45] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 45) []
    (chainClosureStep tmWord tmFiber44Prefix44 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 41) hparentBefore tmFiber44ReverseSingleStep45
theorem tmFiber44State45_in_pass1_full :
    tmFiber44StateAt 45 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix45 ++ [tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix45 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 45) tmFiber44State45_in_pass1_prefix45
theorem tmFiber44State46_in_pass1_prefix46 :
    tmFiber44StateAt 46 ∈ chainClosureStep tmWord tmFiber44Prefix46 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 14 ∈
      chainClosureStep tmWord tmFiber44Prefix45 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix45 = tmFiber44Prefix14 ++ [tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45]
      (chainClosureStep tmWord tmFiber44Prefix14 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 14) tmFiber44State14_in_pass1_prefix14
  rw [show tmFiber44Prefix46 = tmFiber44Prefix45 ++ [tmFiber44StateAt 46] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 46) []
    (chainClosureStep tmWord tmFiber44Prefix45 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 14) hparentBefore tmFiber44ReverseSingleStep46
theorem tmFiber44State46_in_pass1_full :
    tmFiber44StateAt 46 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix46 ++ [tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix46 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 46) tmFiber44State46_in_pass1_prefix46
theorem tmFiber44State47_in_pass1_prefix47 :
    tmFiber44StateAt 47 ∈ chainClosureStep tmWord tmFiber44Prefix47 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 15 ∈
      chainClosureStep tmWord tmFiber44Prefix46 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix46 = tmFiber44Prefix15 ++ [tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46]
      (chainClosureStep tmWord tmFiber44Prefix15 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 15) tmFiber44State15_in_pass1_prefix15
  rw [show tmFiber44Prefix47 = tmFiber44Prefix46 ++ [tmFiber44StateAt 47] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 47) []
    (chainClosureStep tmWord tmFiber44Prefix46 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 15) hparentBefore tmFiber44ReverseSingleStep47
theorem tmFiber44State47_in_pass1_full :
    tmFiber44StateAt 47 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix47 ++ [tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix47 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 47) tmFiber44State47_in_pass1_prefix47
theorem tmFiber44State48_in_pass1_prefix48 :
    tmFiber44StateAt 48 ∈ chainClosureStep tmWord tmFiber44Prefix48 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 32 ∈
      chainClosureStep tmWord tmFiber44Prefix47 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix47 = tmFiber44Prefix32 ++ [tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47]
      (chainClosureStep tmWord tmFiber44Prefix32 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 32) tmFiber44State32_in_pass1_prefix32
  rw [show tmFiber44Prefix48 = tmFiber44Prefix47 ++ [tmFiber44StateAt 48] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 48) []
    (chainClosureStep tmWord tmFiber44Prefix47 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 32) hparentBefore tmFiber44ReverseSingleStep48
theorem tmFiber44State48_in_pass1_full :
    tmFiber44StateAt 48 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix48 ++ [tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix48 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 48) tmFiber44State48_in_pass1_prefix48
theorem tmFiber44State49_in_pass1_prefix49 :
    tmFiber44StateAt 49 ∈ chainClosureStep tmWord tmFiber44Prefix49 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 33 ∈
      chainClosureStep tmWord tmFiber44Prefix48 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix48 = tmFiber44Prefix33 ++ [tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48]
      (chainClosureStep tmWord tmFiber44Prefix33 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 33) tmFiber44State33_in_pass1_prefix33
  rw [show tmFiber44Prefix49 = tmFiber44Prefix48 ++ [tmFiber44StateAt 49] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 49) []
    (chainClosureStep tmWord tmFiber44Prefix48 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 33) hparentBefore tmFiber44ReverseSingleStep49
theorem tmFiber44State49_in_pass1_full :
    tmFiber44StateAt 49 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix49 ++ [tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix49 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 49) tmFiber44State49_in_pass1_prefix49
theorem tmFiber44State50_in_pass1_prefix50 :
    tmFiber44StateAt 50 ∈ chainClosureStep tmWord tmFiber44Prefix50 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 34 ∈
      chainClosureStep tmWord tmFiber44Prefix49 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix49 = tmFiber44Prefix34 ++ [tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49]
      (chainClosureStep tmWord tmFiber44Prefix34 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 34) tmFiber44State34_in_pass1_prefix34
  rw [show tmFiber44Prefix50 = tmFiber44Prefix49 ++ [tmFiber44StateAt 50] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 50) []
    (chainClosureStep tmWord tmFiber44Prefix49 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 34) hparentBefore tmFiber44ReverseSingleStep50
theorem tmFiber44State50_in_pass1_full :
    tmFiber44StateAt 50 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix50 ++ [tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix50 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 50) tmFiber44State50_in_pass1_prefix50
theorem tmFiber44State51_in_pass1_prefix51 :
    tmFiber44StateAt 51 ∈ chainClosureStep tmWord tmFiber44Prefix51 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 35 ∈
      chainClosureStep tmWord tmFiber44Prefix50 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix50 = tmFiber44Prefix35 ++ [tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50]
      (chainClosureStep tmWord tmFiber44Prefix35 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 35) tmFiber44State35_in_pass1_prefix35
  rw [show tmFiber44Prefix51 = tmFiber44Prefix50 ++ [tmFiber44StateAt 51] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 51) []
    (chainClosureStep tmWord tmFiber44Prefix50 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 35) hparentBefore tmFiber44ReverseSingleStep51
theorem tmFiber44State51_in_pass1_full :
    tmFiber44StateAt 51 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix51 ++ [tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix51 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 51) tmFiber44State51_in_pass1_prefix51
theorem tmFiber44State52_in_pass1_prefix52 :
    tmFiber44StateAt 52 ∈ chainClosureStep tmWord tmFiber44Prefix52 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 36 ∈
      chainClosureStep tmWord tmFiber44Prefix51 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix51 = tmFiber44Prefix36 ++ [tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51]
      (chainClosureStep tmWord tmFiber44Prefix36 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 36) tmFiber44State36_in_pass1_prefix36
  rw [show tmFiber44Prefix52 = tmFiber44Prefix51 ++ [tmFiber44StateAt 52] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 52) []
    (chainClosureStep tmWord tmFiber44Prefix51 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 36) hparentBefore tmFiber44ReverseSingleStep52
theorem tmFiber44State52_in_pass1_full :
    tmFiber44StateAt 52 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix52 ++ [tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix52 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 52) tmFiber44State52_in_pass1_prefix52
theorem tmFiber44State53_in_pass1_prefix53 :
    tmFiber44StateAt 53 ∈ chainClosureStep tmWord tmFiber44Prefix53 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 37 ∈
      chainClosureStep tmWord tmFiber44Prefix52 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix52 = tmFiber44Prefix37 ++ [tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52]
      (chainClosureStep tmWord tmFiber44Prefix37 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 37) tmFiber44State37_in_pass1_prefix37
  rw [show tmFiber44Prefix53 = tmFiber44Prefix52 ++ [tmFiber44StateAt 53] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 53) []
    (chainClosureStep tmWord tmFiber44Prefix52 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 37) hparentBefore tmFiber44ReverseSingleStep53
theorem tmFiber44State53_in_pass1_full :
    tmFiber44StateAt 53 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix53 ++ [tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix53 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 53) tmFiber44State53_in_pass1_prefix53
theorem tmFiber44State54_in_pass1_prefix54 :
    tmFiber44StateAt 54 ∈ chainClosureStep tmWord tmFiber44Prefix54 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 38 ∈
      chainClosureStep tmWord tmFiber44Prefix53 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix53 = tmFiber44Prefix38 ++ [tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53]
      (chainClosureStep tmWord tmFiber44Prefix38 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 38) tmFiber44State38_in_pass1_prefix38
  rw [show tmFiber44Prefix54 = tmFiber44Prefix53 ++ [tmFiber44StateAt 54] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 54) []
    (chainClosureStep tmWord tmFiber44Prefix53 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 38) hparentBefore tmFiber44ReverseSingleStep54
theorem tmFiber44State54_in_pass1_full :
    tmFiber44StateAt 54 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix54 ++ [tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix54 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 54) tmFiber44State54_in_pass1_prefix54
theorem tmFiber44State55_in_pass1_prefix55 :
    tmFiber44StateAt 55 ∈ chainClosureStep tmWord tmFiber44Prefix55 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 39 ∈
      chainClosureStep tmWord tmFiber44Prefix54 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix54 = tmFiber44Prefix39 ++ [tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54]
      (chainClosureStep tmWord tmFiber44Prefix39 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 39) tmFiber44State39_in_pass1_prefix39
  rw [show tmFiber44Prefix55 = tmFiber44Prefix54 ++ [tmFiber44StateAt 55] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 55) []
    (chainClosureStep tmWord tmFiber44Prefix54 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 39) hparentBefore tmFiber44ReverseSingleStep55
theorem tmFiber44State55_in_pass1_full :
    tmFiber44StateAt 55 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix55 ++ [tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix55 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 55) tmFiber44State55_in_pass1_prefix55
theorem tmFiber44State56_in_pass1_prefix56 :
    tmFiber44StateAt 56 ∈ chainClosureStep tmWord tmFiber44Prefix56 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 24 ∈
      chainClosureStep tmWord tmFiber44Prefix55 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix55 = tmFiber44Prefix24 ++ [tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55]
      (chainClosureStep tmWord tmFiber44Prefix24 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 24) tmFiber44State24_in_pass1_prefix24
  rw [show tmFiber44Prefix56 = tmFiber44Prefix55 ++ [tmFiber44StateAt 56] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 56) []
    (chainClosureStep tmWord tmFiber44Prefix55 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 24) hparentBefore tmFiber44ReverseSingleStep56
theorem tmFiber44State56_in_pass1_full :
    tmFiber44StateAt 56 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix56 ++ [tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix56 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 56) tmFiber44State56_in_pass1_prefix56
theorem tmFiber44State57_in_pass1_prefix57 :
    tmFiber44StateAt 57 ∈ chainClosureStep tmWord tmFiber44Prefix57 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 25 ∈
      chainClosureStep tmWord tmFiber44Prefix56 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix56 = tmFiber44Prefix25 ++ [tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56]
      (chainClosureStep tmWord tmFiber44Prefix25 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 25) tmFiber44State25_in_pass1_prefix25
  rw [show tmFiber44Prefix57 = tmFiber44Prefix56 ++ [tmFiber44StateAt 57] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 57) []
    (chainClosureStep tmWord tmFiber44Prefix56 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 25) hparentBefore tmFiber44ReverseSingleStep57
theorem tmFiber44State57_in_pass1_full :
    tmFiber44StateAt 57 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix57 ++ [tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix57 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 57) tmFiber44State57_in_pass1_prefix57
theorem tmFiber44State58_in_pass1_prefix58 :
    tmFiber44StateAt 58 ∈ chainClosureStep tmWord tmFiber44Prefix58 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 26 ∈
      chainClosureStep tmWord tmFiber44Prefix57 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix57 = tmFiber44Prefix26 ++ [tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57]
      (chainClosureStep tmWord tmFiber44Prefix26 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 26) tmFiber44State26_in_pass1_prefix26
  rw [show tmFiber44Prefix58 = tmFiber44Prefix57 ++ [tmFiber44StateAt 58] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 58) []
    (chainClosureStep tmWord tmFiber44Prefix57 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 26) hparentBefore tmFiber44ReverseSingleStep58
theorem tmFiber44State58_in_pass1_full :
    tmFiber44StateAt 58 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix58 ++ [tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix58 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 58) tmFiber44State58_in_pass1_prefix58
theorem tmFiber44State59_in_pass1_prefix59 :
    tmFiber44StateAt 59 ∈ chainClosureStep tmWord tmFiber44Prefix59 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 27 ∈
      chainClosureStep tmWord tmFiber44Prefix58 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix58 = tmFiber44Prefix27 ++ [tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58]
      (chainClosureStep tmWord tmFiber44Prefix27 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 27) tmFiber44State27_in_pass1_prefix27
  rw [show tmFiber44Prefix59 = tmFiber44Prefix58 ++ [tmFiber44StateAt 59] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 59) []
    (chainClosureStep tmWord tmFiber44Prefix58 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 27) hparentBefore tmFiber44ReverseSingleStep59
theorem tmFiber44State59_in_pass1_full :
    tmFiber44StateAt 59 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix59 ++ [tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix59 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 59) tmFiber44State59_in_pass1_prefix59
theorem tmFiber44State60_in_pass1_prefix60 :
    tmFiber44StateAt 60 ∈ chainClosureStep tmWord tmFiber44Prefix60 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 56 ∈
      chainClosureStep tmWord tmFiber44Prefix59 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix59 = tmFiber44Prefix56 ++ [tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59]
      (chainClosureStep tmWord tmFiber44Prefix56 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 56) tmFiber44State56_in_pass1_prefix56
  rw [show tmFiber44Prefix60 = tmFiber44Prefix59 ++ [tmFiber44StateAt 60] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 60) []
    (chainClosureStep tmWord tmFiber44Prefix59 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 56) hparentBefore tmFiber44ReverseSingleStep60
theorem tmFiber44State60_in_pass1_full :
    tmFiber44StateAt 60 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix60 ++ [tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix60 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 60) tmFiber44State60_in_pass1_prefix60
theorem tmFiber44State61_in_pass1_prefix61 :
    tmFiber44StateAt 61 ∈ chainClosureStep tmWord tmFiber44Prefix61 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 57 ∈
      chainClosureStep tmWord tmFiber44Prefix60 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix60 = tmFiber44Prefix57 ++ [tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60]
      (chainClosureStep tmWord tmFiber44Prefix57 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 57) tmFiber44State57_in_pass1_prefix57
  rw [show tmFiber44Prefix61 = tmFiber44Prefix60 ++ [tmFiber44StateAt 61] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 61) []
    (chainClosureStep tmWord tmFiber44Prefix60 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 57) hparentBefore tmFiber44ReverseSingleStep61
theorem tmFiber44State61_in_pass1_full :
    tmFiber44StateAt 61 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix61 ++ [tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix61 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 61) tmFiber44State61_in_pass1_prefix61
theorem tmFiber44State62_in_pass1_prefix62 :
    tmFiber44StateAt 62 ∈ chainClosureStep tmWord tmFiber44Prefix62 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 30 ∈
      chainClosureStep tmWord tmFiber44Prefix61 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix61 = tmFiber44Prefix30 ++ [tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61]
      (chainClosureStep tmWord tmFiber44Prefix30 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 30) tmFiber44State30_in_pass1_prefix30
  rw [show tmFiber44Prefix62 = tmFiber44Prefix61 ++ [tmFiber44StateAt 62] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 62) []
    (chainClosureStep tmWord tmFiber44Prefix61 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 30) hparentBefore tmFiber44ReverseSingleStep62
theorem tmFiber44State62_in_pass1_full :
    tmFiber44StateAt 62 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix62 ++ [tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix62 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 62) tmFiber44State62_in_pass1_prefix62
theorem tmFiber44State63_in_pass1_prefix63 :
    tmFiber44StateAt 63 ∈ chainClosureStep tmWord tmFiber44Prefix63 ([tmFiber44StateAt 0]) := by
  have hparentBefore : tmFiber44StateAt 31 ∈
      chainClosureStep tmWord tmFiber44Prefix62 ([tmFiber44StateAt 0]) := by
    rw [show tmFiber44Prefix62 = tmFiber44Prefix31 ++ [tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62]
      (chainClosureStep tmWord tmFiber44Prefix31 ([tmFiber44StateAt 0]))
      (tmFiber44StateAt 31) tmFiber44State31_in_pass1_prefix31
  rw [show tmFiber44Prefix63 = tmFiber44Prefix62 ++ [tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 63) []
    (chainClosureStep tmWord tmFiber44Prefix62 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 31) hparentBefore tmFiber44ReverseSingleStep63
theorem tmFiber44State63_in_pass1_full :
    tmFiber44StateAt 63 ∈ chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0]) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix63 ++ [] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord []
    (chainClosureStep tmWord tmFiber44Prefix63 ([tmFiber44StateAt 0]))
    (tmFiber44StateAt 63) tmFiber44State63_in_pass1_prefix63
theorem tmFiber44State5_in_pass2_prefix5 :
    tmFiber44StateAt 5 ∈ chainClosureStep tmWord tmFiber44Prefix5 (chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0])) := by
  have hparentBefore : tmFiber44StateAt 7 ∈
      chainClosureStep tmWord tmFiber44Prefix4 (chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber44Prefix4
      (chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0])) (tmFiber44StateAt 7) tmFiber44State7_in_pass1_full
  rw [show tmFiber44Prefix5 = tmFiber44Prefix4 ++ [tmFiber44StateAt 5] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 5) []
    (chainClosureStep tmWord tmFiber44Prefix4 (chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0])))
    (tmFiber44StateAt 7) hparentBefore tmFiber44ReverseSingleStep5
theorem tmFiber44State5_in_pass2_full :
    tmFiber44StateAt 5 ∈ chainClosureStep tmWord tmFiber44DirectStates (chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0])) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix5 ++ [tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix5 (chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0])))
    (tmFiber44StateAt 5) tmFiber44State5_in_pass2_prefix5
theorem tmFiber44State13_in_pass2_prefix13 :
    tmFiber44StateAt 13 ∈ chainClosureStep tmWord tmFiber44Prefix13 (chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0])) := by
  have hparentBefore : tmFiber44StateAt 5 ∈
      chainClosureStep tmWord tmFiber44Prefix12 (chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0])) := by
    rw [show tmFiber44Prefix12 = tmFiber44Prefix5 ++ [tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12]
      (chainClosureStep tmWord tmFiber44Prefix5 (chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0])))
      (tmFiber44StateAt 5) tmFiber44State5_in_pass2_prefix5
  rw [show tmFiber44Prefix13 = tmFiber44Prefix12 ++ [tmFiber44StateAt 13] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 13) []
    (chainClosureStep tmWord tmFiber44Prefix12 (chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0])))
    (tmFiber44StateAt 5) hparentBefore tmFiber44ReverseSingleStep13
theorem tmFiber44State13_in_pass2_full :
    tmFiber44StateAt 13 ∈ chainClosureStep tmWord tmFiber44DirectStates (chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0])) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix13 ++ [tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix13 (chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0])))
    (tmFiber44StateAt 13) tmFiber44State13_in_pass2_prefix13
theorem tmFiber44State21_in_pass2_prefix21 :
    tmFiber44StateAt 21 ∈ chainClosureStep tmWord tmFiber44Prefix21 (chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0])) := by
  have hparentBefore : tmFiber44StateAt 13 ∈
      chainClosureStep tmWord tmFiber44Prefix20 (chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0])) := by
    rw [show tmFiber44Prefix20 = tmFiber44Prefix13 ++ [tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20]
      (chainClosureStep tmWord tmFiber44Prefix13 (chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0])))
      (tmFiber44StateAt 13) tmFiber44State13_in_pass2_prefix13
  rw [show tmFiber44Prefix21 = tmFiber44Prefix20 ++ [tmFiber44StateAt 21] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 21) []
    (chainClosureStep tmWord tmFiber44Prefix20 (chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0])))
    (tmFiber44StateAt 13) hparentBefore tmFiber44ReverseSingleStep21
theorem tmFiber44State21_in_pass2_full :
    tmFiber44StateAt 21 ∈ chainClosureStep tmWord tmFiber44DirectStates (chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0])) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix21 ++ [tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28, tmFiber44StateAt 29, tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix21 (chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0])))
    (tmFiber44StateAt 21) tmFiber44State21_in_pass2_prefix21
theorem tmFiber44State29_in_pass2_prefix29 :
    tmFiber44StateAt 29 ∈ chainClosureStep tmWord tmFiber44Prefix29 (chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0])) := by
  have hparentBefore : tmFiber44StateAt 5 ∈
      chainClosureStep tmWord tmFiber44Prefix28 (chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0])) := by
    rw [show tmFiber44Prefix28 = tmFiber44Prefix5 ++ [tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 6, tmFiber44StateAt 7, tmFiber44StateAt 8, tmFiber44StateAt 9, tmFiber44StateAt 10, tmFiber44StateAt 11, tmFiber44StateAt 12, tmFiber44StateAt 13, tmFiber44StateAt 14, tmFiber44StateAt 15, tmFiber44StateAt 16, tmFiber44StateAt 17, tmFiber44StateAt 18, tmFiber44StateAt 19, tmFiber44StateAt 20, tmFiber44StateAt 21, tmFiber44StateAt 22, tmFiber44StateAt 23, tmFiber44StateAt 24, tmFiber44StateAt 25, tmFiber44StateAt 26, tmFiber44StateAt 27, tmFiber44StateAt 28]
      (chainClosureStep tmWord tmFiber44Prefix5 (chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0])))
      (tmFiber44StateAt 5) tmFiber44State5_in_pass2_prefix5
  rw [show tmFiber44Prefix29 = tmFiber44Prefix28 ++ [tmFiber44StateAt 29] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber44StateAt 29) []
    (chainClosureStep tmWord tmFiber44Prefix28 (chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0])))
    (tmFiber44StateAt 5) hparentBefore tmFiber44ReverseSingleStep29
theorem tmFiber44State29_in_pass2_full :
    tmFiber44StateAt 29 ∈ chainClosureStep tmWord tmFiber44DirectStates (chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0])) := by
  rw [show tmFiber44DirectStates = tmFiber44Prefix29 ++ [tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber44StateAt 30, tmFiber44StateAt 31, tmFiber44StateAt 32, tmFiber44StateAt 33, tmFiber44StateAt 34, tmFiber44StateAt 35, tmFiber44StateAt 36, tmFiber44StateAt 37, tmFiber44StateAt 38, tmFiber44StateAt 39, tmFiber44StateAt 40, tmFiber44StateAt 41, tmFiber44StateAt 42, tmFiber44StateAt 43, tmFiber44StateAt 44, tmFiber44StateAt 45, tmFiber44StateAt 46, tmFiber44StateAt 47, tmFiber44StateAt 48, tmFiber44StateAt 49, tmFiber44StateAt 50, tmFiber44StateAt 51, tmFiber44StateAt 52, tmFiber44StateAt 53, tmFiber44StateAt 54, tmFiber44StateAt 55, tmFiber44StateAt 56, tmFiber44StateAt 57, tmFiber44StateAt 58, tmFiber44StateAt 59, tmFiber44StateAt 60, tmFiber44StateAt 61, tmFiber44StateAt 62, tmFiber44StateAt 63]
    (chainClosureStep tmWord tmFiber44Prefix29 (chainClosureStep tmWord tmFiber44DirectStates ([tmFiber44StateAt 0])))
    (tmFiber44StateAt 29) tmFiber44State29_in_pass2_prefix29
theorem tmFiber44FirstPassGrows :
    ((chainClosureStep tmWord tmFiber44DirectStates [tmFiber44StateAt 0]).length ==
      [tmFiber44StateAt 0].length) = false := by
  have hroot : tmFiber44StateAt 0 ∈
      chainClosureStep tmWord tmFiber44DirectStates [tmFiber44StateAt 0] :=
    chainClosureStep_mem_of_seen tmWord tmFiber44DirectStates
      [tmFiber44StateAt 0] (tmFiber44StateAt 0) (by simp)
  have hnew : tmFiber44StateAt 1 ∈
      chainClosureStep tmWord tmFiber44DirectStates [tmFiber44StateAt 0] :=
    tmFiber44State1_in_pass1_full
  simpa using list_length_beq_one_false_of_two_mem
    (chainClosureStep tmWord tmFiber44DirectStates [tmFiber44StateAt 0])
    (tmFiber44StateAt 0) (tmFiber44StateAt 1) hroot hnew (by decide)

theorem tmFiber44State0_in_close_short :
    tmFiber44StateAt 0 ∈ closeChainFiber tmWord tmFiber44DirectStates 0 [tmFiber44StateAt 0] := by
  simp [closeChainFiber]

theorem tmFiber44State1_in_close_short :
    tmFiber44StateAt 1 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 1) tmFiber44State1_in_pass1_full

theorem tmFiber44State2_in_close_short :
    tmFiber44StateAt 2 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 2) tmFiber44State2_in_pass1_full

theorem tmFiber44State3_in_close_short :
    tmFiber44StateAt 3 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 3) tmFiber44State3_in_pass1_full

theorem tmFiber44State4_in_close_short :
    tmFiber44StateAt 4 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 4) tmFiber44State4_in_pass1_full

theorem tmFiber44State6_in_close_short :
    tmFiber44StateAt 6 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 6) tmFiber44State6_in_pass1_full

theorem tmFiber44State7_in_close_short :
    tmFiber44StateAt 7 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 7) tmFiber44State7_in_pass1_full

theorem tmFiber44State8_in_close_short :
    tmFiber44StateAt 8 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 8) tmFiber44State8_in_pass1_full

theorem tmFiber44State9_in_close_short :
    tmFiber44StateAt 9 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 9) tmFiber44State9_in_pass1_full

theorem tmFiber44State10_in_close_short :
    tmFiber44StateAt 10 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 10) tmFiber44State10_in_pass1_full

theorem tmFiber44State11_in_close_short :
    tmFiber44StateAt 11 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 11) tmFiber44State11_in_pass1_full

theorem tmFiber44State12_in_close_short :
    tmFiber44StateAt 12 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 12) tmFiber44State12_in_pass1_full

theorem tmFiber44State14_in_close_short :
    tmFiber44StateAt 14 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 14) tmFiber44State14_in_pass1_full

theorem tmFiber44State15_in_close_short :
    tmFiber44StateAt 15 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 15) tmFiber44State15_in_pass1_full

theorem tmFiber44State16_in_close_short :
    tmFiber44StateAt 16 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 16) tmFiber44State16_in_pass1_full

theorem tmFiber44State17_in_close_short :
    tmFiber44StateAt 17 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 17) tmFiber44State17_in_pass1_full

theorem tmFiber44State18_in_close_short :
    tmFiber44StateAt 18 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 18) tmFiber44State18_in_pass1_full

theorem tmFiber44State19_in_close_short :
    tmFiber44StateAt 19 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 19) tmFiber44State19_in_pass1_full

theorem tmFiber44State20_in_close_short :
    tmFiber44StateAt 20 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 20) tmFiber44State20_in_pass1_full

theorem tmFiber44State22_in_close_short :
    tmFiber44StateAt 22 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 22) tmFiber44State22_in_pass1_full

theorem tmFiber44State23_in_close_short :
    tmFiber44StateAt 23 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 23) tmFiber44State23_in_pass1_full

theorem tmFiber44State24_in_close_short :
    tmFiber44StateAt 24 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 24) tmFiber44State24_in_pass1_full

theorem tmFiber44State25_in_close_short :
    tmFiber44StateAt 25 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 25) tmFiber44State25_in_pass1_full

theorem tmFiber44State26_in_close_short :
    tmFiber44StateAt 26 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 26) tmFiber44State26_in_pass1_full

theorem tmFiber44State27_in_close_short :
    tmFiber44StateAt 27 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 27) tmFiber44State27_in_pass1_full

theorem tmFiber44State28_in_close_short :
    tmFiber44StateAt 28 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 28) tmFiber44State28_in_pass1_full

theorem tmFiber44State30_in_close_short :
    tmFiber44StateAt 30 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 30) tmFiber44State30_in_pass1_full

theorem tmFiber44State31_in_close_short :
    tmFiber44StateAt 31 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 31) tmFiber44State31_in_pass1_full

theorem tmFiber44State32_in_close_short :
    tmFiber44StateAt 32 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 32) tmFiber44State32_in_pass1_full

theorem tmFiber44State33_in_close_short :
    tmFiber44StateAt 33 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 33) tmFiber44State33_in_pass1_full

theorem tmFiber44State34_in_close_short :
    tmFiber44StateAt 34 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 34) tmFiber44State34_in_pass1_full

theorem tmFiber44State35_in_close_short :
    tmFiber44StateAt 35 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 35) tmFiber44State35_in_pass1_full

theorem tmFiber44State36_in_close_short :
    tmFiber44StateAt 36 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 36) tmFiber44State36_in_pass1_full

theorem tmFiber44State37_in_close_short :
    tmFiber44StateAt 37 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 37) tmFiber44State37_in_pass1_full

theorem tmFiber44State38_in_close_short :
    tmFiber44StateAt 38 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 38) tmFiber44State38_in_pass1_full

theorem tmFiber44State39_in_close_short :
    tmFiber44StateAt 39 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 39) tmFiber44State39_in_pass1_full

theorem tmFiber44State40_in_close_short :
    tmFiber44StateAt 40 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 40) tmFiber44State40_in_pass1_full

theorem tmFiber44State41_in_close_short :
    tmFiber44StateAt 41 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 41) tmFiber44State41_in_pass1_full

theorem tmFiber44State42_in_close_short :
    tmFiber44StateAt 42 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 42) tmFiber44State42_in_pass1_full

theorem tmFiber44State43_in_close_short :
    tmFiber44StateAt 43 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 43) tmFiber44State43_in_pass1_full

theorem tmFiber44State44_in_close_short :
    tmFiber44StateAt 44 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 44) tmFiber44State44_in_pass1_full

theorem tmFiber44State45_in_close_short :
    tmFiber44StateAt 45 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 45) tmFiber44State45_in_pass1_full

theorem tmFiber44State46_in_close_short :
    tmFiber44StateAt 46 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 46) tmFiber44State46_in_pass1_full

theorem tmFiber44State47_in_close_short :
    tmFiber44StateAt 47 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 47) tmFiber44State47_in_pass1_full

theorem tmFiber44State48_in_close_short :
    tmFiber44StateAt 48 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 48) tmFiber44State48_in_pass1_full

theorem tmFiber44State49_in_close_short :
    tmFiber44StateAt 49 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 49) tmFiber44State49_in_pass1_full

theorem tmFiber44State50_in_close_short :
    tmFiber44StateAt 50 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 50) tmFiber44State50_in_pass1_full

theorem tmFiber44State51_in_close_short :
    tmFiber44StateAt 51 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 51) tmFiber44State51_in_pass1_full

theorem tmFiber44State52_in_close_short :
    tmFiber44StateAt 52 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 52) tmFiber44State52_in_pass1_full

theorem tmFiber44State53_in_close_short :
    tmFiber44StateAt 53 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 53) tmFiber44State53_in_pass1_full

theorem tmFiber44State54_in_close_short :
    tmFiber44StateAt 54 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 54) tmFiber44State54_in_pass1_full

theorem tmFiber44State55_in_close_short :
    tmFiber44StateAt 55 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 55) tmFiber44State55_in_pass1_full

theorem tmFiber44State56_in_close_short :
    tmFiber44StateAt 56 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 56) tmFiber44State56_in_pass1_full

theorem tmFiber44State57_in_close_short :
    tmFiber44StateAt 57 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 57) tmFiber44State57_in_pass1_full

theorem tmFiber44State58_in_close_short :
    tmFiber44StateAt 58 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 58) tmFiber44State58_in_pass1_full

theorem tmFiber44State59_in_close_short :
    tmFiber44StateAt 59 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 59) tmFiber44State59_in_pass1_full

theorem tmFiber44State60_in_close_short :
    tmFiber44StateAt 60 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 60) tmFiber44State60_in_pass1_full

theorem tmFiber44State61_in_close_short :
    tmFiber44StateAt 61 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 61) tmFiber44State61_in_pass1_full

theorem tmFiber44State62_in_close_short :
    tmFiber44StateAt 62 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 62) tmFiber44State62_in_pass1_full

theorem tmFiber44State63_in_close_short :
    tmFiber44StateAt 63 ∈ closeChainFiber tmWord tmFiber44DirectStates 1 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 63) tmFiber44State63_in_pass1_full

theorem tmFiber44State5_in_close_short :
    tmFiber44StateAt 5 ∈ closeChainFiber tmWord tmFiber44DirectStates 2 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 5) tmFiber44FirstPassGrows
    tmFiber44State5_in_pass2_full

theorem tmFiber44State13_in_close_short :
    tmFiber44StateAt 13 ∈ closeChainFiber tmWord tmFiber44DirectStates 2 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 13) tmFiber44FirstPassGrows
    tmFiber44State13_in_pass2_full

theorem tmFiber44State21_in_close_short :
    tmFiber44StateAt 21 ∈ closeChainFiber tmWord tmFiber44DirectStates 2 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 21) tmFiber44FirstPassGrows
    tmFiber44State21_in_pass2_full

theorem tmFiber44State29_in_close_short :
    tmFiber44StateAt 29 ∈ closeChainFiber tmWord tmFiber44DirectStates 2 [tmFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber44DirectStates 0
    [tmFiber44StateAt 0] (tmFiber44StateAt 29) tmFiber44FirstPassGrows
    tmFiber44State29_in_pass2_full

theorem tmFiber44State0_in_close :
    tmFiber44StateAt 0 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 0 ∈ closeChainFiber tmWord tmFiber44DirectStates (0 + 64) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 0 64
    [tmFiber44StateAt 0] (tmFiber44StateAt 0) tmFiber44State0_in_close_short

theorem tmFiber44State1_in_close :
    tmFiber44StateAt 1 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 1 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 1) tmFiber44State1_in_close_short

theorem tmFiber44State2_in_close :
    tmFiber44StateAt 2 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 2 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 2) tmFiber44State2_in_close_short

theorem tmFiber44State3_in_close :
    tmFiber44StateAt 3 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 3 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 3) tmFiber44State3_in_close_short

theorem tmFiber44State4_in_close :
    tmFiber44StateAt 4 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 4 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 4) tmFiber44State4_in_close_short

theorem tmFiber44State5_in_close :
    tmFiber44StateAt 5 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 5 ∈ closeChainFiber tmWord tmFiber44DirectStates (2 + 62) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 2 62
    [tmFiber44StateAt 0] (tmFiber44StateAt 5) tmFiber44State5_in_close_short

theorem tmFiber44State6_in_close :
    tmFiber44StateAt 6 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 6 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 6) tmFiber44State6_in_close_short

theorem tmFiber44State7_in_close :
    tmFiber44StateAt 7 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 7 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 7) tmFiber44State7_in_close_short

theorem tmFiber44State8_in_close :
    tmFiber44StateAt 8 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 8 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 8) tmFiber44State8_in_close_short

theorem tmFiber44State9_in_close :
    tmFiber44StateAt 9 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 9 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 9) tmFiber44State9_in_close_short

theorem tmFiber44State10_in_close :
    tmFiber44StateAt 10 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 10 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 10) tmFiber44State10_in_close_short

theorem tmFiber44State11_in_close :
    tmFiber44StateAt 11 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 11 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 11) tmFiber44State11_in_close_short

theorem tmFiber44State12_in_close :
    tmFiber44StateAt 12 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 12 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 12) tmFiber44State12_in_close_short

theorem tmFiber44State13_in_close :
    tmFiber44StateAt 13 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 13 ∈ closeChainFiber tmWord tmFiber44DirectStates (2 + 62) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 2 62
    [tmFiber44StateAt 0] (tmFiber44StateAt 13) tmFiber44State13_in_close_short

theorem tmFiber44State14_in_close :
    tmFiber44StateAt 14 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 14 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 14) tmFiber44State14_in_close_short

theorem tmFiber44State15_in_close :
    tmFiber44StateAt 15 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 15 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 15) tmFiber44State15_in_close_short

theorem tmFiber44State16_in_close :
    tmFiber44StateAt 16 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 16 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 16) tmFiber44State16_in_close_short

theorem tmFiber44State17_in_close :
    tmFiber44StateAt 17 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 17 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 17) tmFiber44State17_in_close_short

theorem tmFiber44State18_in_close :
    tmFiber44StateAt 18 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 18 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 18) tmFiber44State18_in_close_short

theorem tmFiber44State19_in_close :
    tmFiber44StateAt 19 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 19 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 19) tmFiber44State19_in_close_short

theorem tmFiber44State20_in_close :
    tmFiber44StateAt 20 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 20 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 20) tmFiber44State20_in_close_short

theorem tmFiber44State21_in_close :
    tmFiber44StateAt 21 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 21 ∈ closeChainFiber tmWord tmFiber44DirectStates (2 + 62) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 2 62
    [tmFiber44StateAt 0] (tmFiber44StateAt 21) tmFiber44State21_in_close_short

theorem tmFiber44State22_in_close :
    tmFiber44StateAt 22 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 22 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 22) tmFiber44State22_in_close_short

theorem tmFiber44State23_in_close :
    tmFiber44StateAt 23 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 23 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 23) tmFiber44State23_in_close_short

theorem tmFiber44State24_in_close :
    tmFiber44StateAt 24 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 24 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 24) tmFiber44State24_in_close_short

theorem tmFiber44State25_in_close :
    tmFiber44StateAt 25 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 25 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 25) tmFiber44State25_in_close_short

theorem tmFiber44State26_in_close :
    tmFiber44StateAt 26 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 26 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 26) tmFiber44State26_in_close_short

theorem tmFiber44State27_in_close :
    tmFiber44StateAt 27 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 27 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 27) tmFiber44State27_in_close_short

theorem tmFiber44State28_in_close :
    tmFiber44StateAt 28 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 28 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 28) tmFiber44State28_in_close_short

theorem tmFiber44State29_in_close :
    tmFiber44StateAt 29 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 29 ∈ closeChainFiber tmWord tmFiber44DirectStates (2 + 62) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 2 62
    [tmFiber44StateAt 0] (tmFiber44StateAt 29) tmFiber44State29_in_close_short

theorem tmFiber44State30_in_close :
    tmFiber44StateAt 30 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 30 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 30) tmFiber44State30_in_close_short

theorem tmFiber44State31_in_close :
    tmFiber44StateAt 31 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 31 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 31) tmFiber44State31_in_close_short

theorem tmFiber44State32_in_close :
    tmFiber44StateAt 32 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 32 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 32) tmFiber44State32_in_close_short

theorem tmFiber44State33_in_close :
    tmFiber44StateAt 33 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 33 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 33) tmFiber44State33_in_close_short

theorem tmFiber44State34_in_close :
    tmFiber44StateAt 34 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 34 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 34) tmFiber44State34_in_close_short

theorem tmFiber44State35_in_close :
    tmFiber44StateAt 35 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 35 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 35) tmFiber44State35_in_close_short

theorem tmFiber44State36_in_close :
    tmFiber44StateAt 36 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 36 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 36) tmFiber44State36_in_close_short

theorem tmFiber44State37_in_close :
    tmFiber44StateAt 37 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 37 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 37) tmFiber44State37_in_close_short

theorem tmFiber44State38_in_close :
    tmFiber44StateAt 38 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 38 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 38) tmFiber44State38_in_close_short

theorem tmFiber44State39_in_close :
    tmFiber44StateAt 39 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 39 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 39) tmFiber44State39_in_close_short

theorem tmFiber44State40_in_close :
    tmFiber44StateAt 40 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 40 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 40) tmFiber44State40_in_close_short

theorem tmFiber44State41_in_close :
    tmFiber44StateAt 41 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 41 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 41) tmFiber44State41_in_close_short

theorem tmFiber44State42_in_close :
    tmFiber44StateAt 42 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 42 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 42) tmFiber44State42_in_close_short

theorem tmFiber44State43_in_close :
    tmFiber44StateAt 43 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 43 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 43) tmFiber44State43_in_close_short

theorem tmFiber44State44_in_close :
    tmFiber44StateAt 44 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 44 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 44) tmFiber44State44_in_close_short

theorem tmFiber44State45_in_close :
    tmFiber44StateAt 45 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 45 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 45) tmFiber44State45_in_close_short

theorem tmFiber44State46_in_close :
    tmFiber44StateAt 46 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 46 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 46) tmFiber44State46_in_close_short

theorem tmFiber44State47_in_close :
    tmFiber44StateAt 47 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 47 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 47) tmFiber44State47_in_close_short

theorem tmFiber44State48_in_close :
    tmFiber44StateAt 48 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 48 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 48) tmFiber44State48_in_close_short

theorem tmFiber44State49_in_close :
    tmFiber44StateAt 49 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 49 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 49) tmFiber44State49_in_close_short

theorem tmFiber44State50_in_close :
    tmFiber44StateAt 50 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 50 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 50) tmFiber44State50_in_close_short

theorem tmFiber44State51_in_close :
    tmFiber44StateAt 51 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 51 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 51) tmFiber44State51_in_close_short

theorem tmFiber44State52_in_close :
    tmFiber44StateAt 52 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 52 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 52) tmFiber44State52_in_close_short

theorem tmFiber44State53_in_close :
    tmFiber44StateAt 53 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 53 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 53) tmFiber44State53_in_close_short

theorem tmFiber44State54_in_close :
    tmFiber44StateAt 54 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 54 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 54) tmFiber44State54_in_close_short

theorem tmFiber44State55_in_close :
    tmFiber44StateAt 55 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 55 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 55) tmFiber44State55_in_close_short

theorem tmFiber44State56_in_close :
    tmFiber44StateAt 56 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 56 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 56) tmFiber44State56_in_close_short

theorem tmFiber44State57_in_close :
    tmFiber44StateAt 57 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 57 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 57) tmFiber44State57_in_close_short

theorem tmFiber44State58_in_close :
    tmFiber44StateAt 58 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 58 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 58) tmFiber44State58_in_close_short

theorem tmFiber44State59_in_close :
    tmFiber44StateAt 59 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 59 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 59) tmFiber44State59_in_close_short

theorem tmFiber44State60_in_close :
    tmFiber44StateAt 60 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 60 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 60) tmFiber44State60_in_close_short

theorem tmFiber44State61_in_close :
    tmFiber44StateAt 61 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 61 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 61) tmFiber44State61_in_close_short

theorem tmFiber44State62_in_close :
    tmFiber44StateAt 62 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 62 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 62) tmFiber44State62_in_close_short

theorem tmFiber44State63_in_close :
    tmFiber44StateAt 63 ∈ closeChainFiber tmWord tmFiber44DirectStates tmFiber44DirectStates.length [tmFiber44StateAt 0] := by
  change tmFiber44StateAt 63 ∈ closeChainFiber tmWord tmFiber44DirectStates (1 + 63) [tmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber44DirectStates 1 63
    [tmFiber44StateAt 0] (tmFiber44StateAt 63) tmFiber44State63_in_close_short

theorem tmFiber44DirectConnected :
    chainFiberConnected tmWord tmFiber44DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [tmFiber44DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact tmFiber44State0_in_close
  · subst state
    exact tmFiber44State1_in_close
  · subst state
    exact tmFiber44State2_in_close
  · subst state
    exact tmFiber44State3_in_close
  · subst state
    exact tmFiber44State4_in_close
  · subst state
    exact tmFiber44State5_in_close
  · subst state
    exact tmFiber44State6_in_close
  · subst state
    exact tmFiber44State7_in_close
  · subst state
    exact tmFiber44State8_in_close
  · subst state
    exact tmFiber44State9_in_close
  · subst state
    exact tmFiber44State10_in_close
  · subst state
    exact tmFiber44State11_in_close
  · subst state
    exact tmFiber44State12_in_close
  · subst state
    exact tmFiber44State13_in_close
  · subst state
    exact tmFiber44State14_in_close
  · subst state
    exact tmFiber44State15_in_close
  · subst state
    exact tmFiber44State16_in_close
  · subst state
    exact tmFiber44State17_in_close
  · subst state
    exact tmFiber44State18_in_close
  · subst state
    exact tmFiber44State19_in_close
  · subst state
    exact tmFiber44State20_in_close
  · subst state
    exact tmFiber44State21_in_close
  · subst state
    exact tmFiber44State22_in_close
  · subst state
    exact tmFiber44State23_in_close
  · subst state
    exact tmFiber44State24_in_close
  · subst state
    exact tmFiber44State25_in_close
  · subst state
    exact tmFiber44State26_in_close
  · subst state
    exact tmFiber44State27_in_close
  · subst state
    exact tmFiber44State28_in_close
  · subst state
    exact tmFiber44State29_in_close
  · subst state
    exact tmFiber44State30_in_close
  · subst state
    exact tmFiber44State31_in_close
  · subst state
    exact tmFiber44State32_in_close
  · subst state
    exact tmFiber44State33_in_close
  · subst state
    exact tmFiber44State34_in_close
  · subst state
    exact tmFiber44State35_in_close
  · subst state
    exact tmFiber44State36_in_close
  · subst state
    exact tmFiber44State37_in_close
  · subst state
    exact tmFiber44State38_in_close
  · subst state
    exact tmFiber44State39_in_close
  · subst state
    exact tmFiber44State40_in_close
  · subst state
    exact tmFiber44State41_in_close
  · subst state
    exact tmFiber44State42_in_close
  · subst state
    exact tmFiber44State43_in_close
  · subst state
    exact tmFiber44State44_in_close
  · subst state
    exact tmFiber44State45_in_close
  · subst state
    exact tmFiber44State46_in_close
  · subst state
    exact tmFiber44State47_in_close
  · subst state
    exact tmFiber44State48_in_close
  · subst state
    exact tmFiber44State49_in_close
  · subst state
    exact tmFiber44State50_in_close
  · subst state
    exact tmFiber44State51_in_close
  · subst state
    exact tmFiber44State52_in_close
  · subst state
    exact tmFiber44State53_in_close
  · subst state
    exact tmFiber44State54_in_close
  · subst state
    exact tmFiber44State55_in_close
  · subst state
    exact tmFiber44State56_in_close
  · subst state
    exact tmFiber44State57_in_close
  · subst state
    exact tmFiber44State58_in_close
  · subst state
    exact tmFiber44State59_in_close
  · subst state
    exact tmFiber44State60_in_close
  · subst state
    exact tmFiber44State61_in_close
  · subst state
    exact tmFiber44State62_in_close
  · subst state
    exact tmFiber44State63_in_close
  · cases h

end GoertzelLemma818LengthTwoTMLargeFiberBridge

end Mettapedia.GraphTheory.FourColor
