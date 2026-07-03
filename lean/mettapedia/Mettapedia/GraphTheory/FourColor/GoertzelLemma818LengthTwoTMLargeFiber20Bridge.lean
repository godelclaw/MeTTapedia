import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMLargeFiberBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated multi-pass direct closure bridge for `normal,mirror` size-64 fiber 20

This module proves direct connectedness for a generated size-64 fiber
whose parent order needs two closure scans. It is generated from
row-local reverse certificate chunks and keeps Lean on default limits.
-/

namespace GoertzelLemma818LengthTwoTMLargeFiberBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818TauMirrorCertificate
open GoertzelLemma818TauMirrorReverseAudit

def tmFiber20StateAt (i : Nat) : List TauState :=
  directStates (tmFiber20RowAt i).sourceLeft (tmFiber20RowAt i).sourceRight

def tmFiber20DirectStates : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]

def tmFiber20Prefix0 : List (List TauState) :=
  [tmFiber20StateAt 0]

def tmFiber20Prefix1 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1]

def tmFiber20Prefix2 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2]

def tmFiber20Prefix3 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3]

def tmFiber20Prefix4 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4]

def tmFiber20Prefix5 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5]

def tmFiber20Prefix6 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6]

def tmFiber20Prefix7 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7]

def tmFiber20Prefix8 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8]

def tmFiber20Prefix9 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9]

def tmFiber20Prefix10 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10]

def tmFiber20Prefix11 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11]

def tmFiber20Prefix12 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12]

def tmFiber20Prefix13 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13]

def tmFiber20Prefix14 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14]

def tmFiber20Prefix15 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15]

def tmFiber20Prefix16 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16]

def tmFiber20Prefix17 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17]

def tmFiber20Prefix18 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18]

def tmFiber20Prefix19 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19]

def tmFiber20Prefix20 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20]

def tmFiber20Prefix21 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21]

def tmFiber20Prefix22 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22]

def tmFiber20Prefix23 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23]

def tmFiber20Prefix24 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24]

def tmFiber20Prefix25 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25]

def tmFiber20Prefix26 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26]

def tmFiber20Prefix27 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27]

def tmFiber20Prefix28 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28]

def tmFiber20Prefix29 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29]

def tmFiber20Prefix30 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30]

def tmFiber20Prefix31 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31]

def tmFiber20Prefix32 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32]

def tmFiber20Prefix33 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33]

def tmFiber20Prefix34 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34]

def tmFiber20Prefix35 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35]

def tmFiber20Prefix36 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36]

def tmFiber20Prefix37 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37]

def tmFiber20Prefix38 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38]

def tmFiber20Prefix39 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39]

def tmFiber20Prefix40 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40]

def tmFiber20Prefix41 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41]

def tmFiber20Prefix42 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42]

def tmFiber20Prefix43 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43]

def tmFiber20Prefix44 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44]

def tmFiber20Prefix45 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45]

def tmFiber20Prefix46 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46]

def tmFiber20Prefix47 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47]

def tmFiber20Prefix48 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48]

def tmFiber20Prefix49 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49]

def tmFiber20Prefix50 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50]

def tmFiber20Prefix51 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51]

def tmFiber20Prefix52 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52]

def tmFiber20Prefix53 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53]

def tmFiber20Prefix54 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54]

def tmFiber20Prefix55 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55]

def tmFiber20Prefix56 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56]

def tmFiber20Prefix57 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57]

def tmFiber20Prefix58 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58]

def tmFiber20Prefix59 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59]

def tmFiber20Prefix60 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60]

def tmFiber20Prefix61 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61]

def tmFiber20Prefix62 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62]

def tmFiber20Prefix63 : List (List TauState) :=
  [tmFiber20StateAt 0, tmFiber20StateAt 1, tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]

theorem tmFiber20ReverseRow_1_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 1) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk0_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 0) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber20ReverseSingleStep1 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 0) (tmFiber20StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 0) (tmFiber20StateAt 1)
    (tmFiber20RowAt 1).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 1) (by decide) tmFiber20ReverseRow_1_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_2_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 2) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk1_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 2) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber20ReverseSingleStep2 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 0) (tmFiber20StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 0) (tmFiber20StateAt 2)
    (tmFiber20RowAt 2).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 2) (by decide) tmFiber20ReverseRow_2_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_3_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 3) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk1_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 2) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber20ReverseSingleStep3 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 1) (tmFiber20StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 1) (tmFiber20StateAt 3)
    (tmFiber20RowAt 3).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 3) (by decide) tmFiber20ReverseRow_3_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_4_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 4) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk2_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 4) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber20ReverseSingleStep4 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 2) (tmFiber20StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 2) (tmFiber20StateAt 4)
    (tmFiber20RowAt 4).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 4) (by decide) tmFiber20ReverseRow_4_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_5_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 5) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk2_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 4) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber20ReverseSingleStep5 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 7) (tmFiber20StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 7) (tmFiber20StateAt 5)
    (tmFiber20RowAt 5).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 5) (by decide) tmFiber20ReverseRow_5_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_6_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 6) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk3_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 6) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber20ReverseSingleStep6 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 1) (tmFiber20StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 1) (tmFiber20StateAt 6)
    (tmFiber20RowAt 6).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 6) (by decide) tmFiber20ReverseRow_6_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_7_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 7) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk3_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 6) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber20ReverseSingleStep7 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 0) (tmFiber20StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 0) (tmFiber20StateAt 7)
    (tmFiber20RowAt 7).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 7) (by decide) tmFiber20ReverseRow_7_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_8_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 8) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk4_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 8) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber20ReverseSingleStep8 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 0) (tmFiber20StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 0) (tmFiber20StateAt 8)
    (tmFiber20RowAt 8).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 8) (by decide) tmFiber20ReverseRow_8_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_9_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 9) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk4_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 8) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber20ReverseSingleStep9 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 1) (tmFiber20StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 1) (tmFiber20StateAt 9)
    (tmFiber20RowAt 9).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 9) (by decide) tmFiber20ReverseRow_9_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_10_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 10) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk5_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 10) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber20ReverseSingleStep10 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 2) (tmFiber20StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 2) (tmFiber20StateAt 10)
    (tmFiber20RowAt 10).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 10) (by decide) tmFiber20ReverseRow_10_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_11_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 11) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk5_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 10) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber20ReverseSingleStep11 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 3) (tmFiber20StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 3) (tmFiber20StateAt 11)
    (tmFiber20RowAt 11).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 11) (by decide) tmFiber20ReverseRow_11_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_12_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 12) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk6_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 12) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber20ReverseSingleStep12 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 4) (tmFiber20StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 4) (tmFiber20StateAt 12)
    (tmFiber20RowAt 12).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 12) (by decide) tmFiber20ReverseRow_12_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_13_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 13) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk6_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 12) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber20ReverseSingleStep13 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 5) (tmFiber20StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 5) (tmFiber20StateAt 13)
    (tmFiber20RowAt 13).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 13) (by decide) tmFiber20ReverseRow_13_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_14_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 14) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk7_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 14) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber20ReverseSingleStep14 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 6) (tmFiber20StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 6) (tmFiber20StateAt 14)
    (tmFiber20RowAt 14).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 14) (by decide) tmFiber20ReverseRow_14_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_15_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 15) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk7_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 14) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber20ReverseSingleStep15 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 7) (tmFiber20StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 7) (tmFiber20StateAt 15)
    (tmFiber20RowAt 15).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 15) (by decide) tmFiber20ReverseRow_15_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_16_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 16) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk8_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 16) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber20ReverseSingleStep16 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 8) (tmFiber20StateAt 16) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 8) (tmFiber20StateAt 16)
    (tmFiber20RowAt 16).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 16) (by decide) tmFiber20ReverseRow_16_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_17_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 17) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk8_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 16) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber20ReverseSingleStep17 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 9) (tmFiber20StateAt 17) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 9) (tmFiber20StateAt 17)
    (tmFiber20RowAt 17).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 17) (by decide) tmFiber20ReverseRow_17_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_18_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 18) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk9_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 18) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber20ReverseSingleStep18 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 10) (tmFiber20StateAt 18) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 10) (tmFiber20StateAt 18)
    (tmFiber20RowAt 18).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 18) (by decide) tmFiber20ReverseRow_18_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_19_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 19) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk9_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 18) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber20ReverseSingleStep19 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 11) (tmFiber20StateAt 19) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 11) (tmFiber20StateAt 19)
    (tmFiber20RowAt 19).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 19) (by decide) tmFiber20ReverseRow_19_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_20_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 20) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk10_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 20) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber20ReverseSingleStep20 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 12) (tmFiber20StateAt 20) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 12) (tmFiber20StateAt 20)
    (tmFiber20RowAt 20).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 20) (by decide) tmFiber20ReverseRow_20_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_21_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 21) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk10_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 20) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber20ReverseSingleStep21 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 13) (tmFiber20StateAt 21) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 13) (tmFiber20StateAt 21)
    (tmFiber20RowAt 21).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 21) (by decide) tmFiber20ReverseRow_21_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_22_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 22) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk11_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 22) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber20ReverseSingleStep22 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 14) (tmFiber20StateAt 22) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 14) (tmFiber20StateAt 22)
    (tmFiber20RowAt 22).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 22) (by decide) tmFiber20ReverseRow_22_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_23_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 23) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk11_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 22) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber20ReverseSingleStep23 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 15) (tmFiber20StateAt 23) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 15) (tmFiber20StateAt 23)
    (tmFiber20RowAt 23).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 23) (by decide) tmFiber20ReverseRow_23_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_24_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 24) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk12_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 24) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber20ReverseSingleStep24 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 0) (tmFiber20StateAt 24) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 0) (tmFiber20StateAt 24)
    (tmFiber20RowAt 24).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 24) (by decide) tmFiber20ReverseRow_24_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_25_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 25) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk12_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 24) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber20ReverseSingleStep25 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 1) (tmFiber20StateAt 25) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 1) (tmFiber20StateAt 25)
    (tmFiber20RowAt 25).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 25) (by decide) tmFiber20ReverseRow_25_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_26_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 26) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk13_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 26) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber20ReverseSingleStep26 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 2) (tmFiber20StateAt 26) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 2) (tmFiber20StateAt 26)
    (tmFiber20RowAt 26).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 26) (by decide) tmFiber20ReverseRow_26_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_27_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 27) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk13_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 26) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber20ReverseSingleStep27 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 3) (tmFiber20StateAt 27) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 3) (tmFiber20StateAt 27)
    (tmFiber20RowAt 27).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 27) (by decide) tmFiber20ReverseRow_27_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_28_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 28) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk14_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 28) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber20ReverseSingleStep28 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 4) (tmFiber20StateAt 28) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 4) (tmFiber20StateAt 28)
    (tmFiber20RowAt 28).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 28) (by decide) tmFiber20ReverseRow_28_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_29_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 29) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk14_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 28) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber20ReverseSingleStep29 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 5) (tmFiber20StateAt 29) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 5) (tmFiber20StateAt 29)
    (tmFiber20RowAt 29).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 29) (by decide) tmFiber20ReverseRow_29_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_30_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 30) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk15_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 30) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber20ReverseSingleStep30 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 6) (tmFiber20StateAt 30) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 6) (tmFiber20StateAt 30)
    (tmFiber20RowAt 30).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 30) (by decide) tmFiber20ReverseRow_30_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_31_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 31) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk15_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 30) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber20ReverseSingleStep31 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 7) (tmFiber20StateAt 31) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 7) (tmFiber20StateAt 31)
    (tmFiber20RowAt 31).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 31) (by decide) tmFiber20ReverseRow_31_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_32_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 32) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk16_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 32) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber20ReverseSingleStep32 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 0) (tmFiber20StateAt 32) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 0) (tmFiber20StateAt 32)
    (tmFiber20RowAt 32).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 32) (by decide) tmFiber20ReverseRow_32_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_33_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 33) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk16_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 32) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber20ReverseSingleStep33 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 1) (tmFiber20StateAt 33) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 1) (tmFiber20StateAt 33)
    (tmFiber20RowAt 33).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 33) (by decide) tmFiber20ReverseRow_33_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_34_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 34) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk17_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 34) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber20ReverseSingleStep34 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 2) (tmFiber20StateAt 34) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 2) (tmFiber20StateAt 34)
    (tmFiber20RowAt 34).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 34) (by decide) tmFiber20ReverseRow_34_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_35_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 35) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk17_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 34) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber20ReverseSingleStep35 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 3) (tmFiber20StateAt 35) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 3) (tmFiber20StateAt 35)
    (tmFiber20RowAt 35).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 35) (by decide) tmFiber20ReverseRow_35_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_36_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 36) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk18_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 36) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber20ReverseSingleStep36 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 32) (tmFiber20StateAt 36) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 32) (tmFiber20StateAt 36)
    (tmFiber20RowAt 36).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 36) (by decide) tmFiber20ReverseRow_36_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_37_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 37) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk18_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 36) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber20ReverseSingleStep37 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 33) (tmFiber20StateAt 37) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 33) (tmFiber20StateAt 37)
    (tmFiber20RowAt 37).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 37) (by decide) tmFiber20ReverseRow_37_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_38_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 38) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk19_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 38) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber20ReverseSingleStep38 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 6) (tmFiber20StateAt 38) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 6) (tmFiber20StateAt 38)
    (tmFiber20RowAt 38).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 38) (by decide) tmFiber20ReverseRow_38_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_39_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 39) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk19_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 38) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber20ReverseSingleStep39 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 7) (tmFiber20StateAt 39) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 7) (tmFiber20StateAt 39)
    (tmFiber20RowAt 39).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 39) (by decide) tmFiber20ReverseRow_39_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_40_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 40) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk20_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 40) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber20ReverseSingleStep40 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 8) (tmFiber20StateAt 40) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 8) (tmFiber20StateAt 40)
    (tmFiber20RowAt 40).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 40) (by decide) tmFiber20ReverseRow_40_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_41_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 41) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk20_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 40) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber20ReverseSingleStep41 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 9) (tmFiber20StateAt 41) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 9) (tmFiber20StateAt 41)
    (tmFiber20RowAt 41).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 41) (by decide) tmFiber20ReverseRow_41_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_42_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 42) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk21_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 42) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber20ReverseSingleStep42 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 10) (tmFiber20StateAt 42) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 10) (tmFiber20StateAt 42)
    (tmFiber20RowAt 42).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 42) (by decide) tmFiber20ReverseRow_42_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_43_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 43) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk21_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 42) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber20ReverseSingleStep43 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 11) (tmFiber20StateAt 43) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 11) (tmFiber20StateAt 43)
    (tmFiber20RowAt 43).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 43) (by decide) tmFiber20ReverseRow_43_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_44_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 44) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk22_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 44) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber20ReverseSingleStep44 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 40) (tmFiber20StateAt 44) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 40) (tmFiber20StateAt 44)
    (tmFiber20RowAt 44).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 44) (by decide) tmFiber20ReverseRow_44_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_45_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 45) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk22_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 44) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber20ReverseSingleStep45 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 41) (tmFiber20StateAt 45) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 41) (tmFiber20StateAt 45)
    (tmFiber20RowAt 45).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 45) (by decide) tmFiber20ReverseRow_45_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_46_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 46) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk23_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 46) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber20ReverseSingleStep46 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 14) (tmFiber20StateAt 46) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 14) (tmFiber20StateAt 46)
    (tmFiber20RowAt 46).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 46) (by decide) tmFiber20ReverseRow_46_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_47_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 47) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk23_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 46) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber20ReverseSingleStep47 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 15) (tmFiber20StateAt 47) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 15) (tmFiber20StateAt 47)
    (tmFiber20RowAt 47).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 47) (by decide) tmFiber20ReverseRow_47_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_48_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 48) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk24_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 48) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber20ReverseSingleStep48 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 32) (tmFiber20StateAt 48) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 32) (tmFiber20StateAt 48)
    (tmFiber20RowAt 48).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 48) (by decide) tmFiber20ReverseRow_48_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_49_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 49) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk24_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 48) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber20ReverseSingleStep49 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 33) (tmFiber20StateAt 49) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 33) (tmFiber20StateAt 49)
    (tmFiber20RowAt 49).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 49) (by decide) tmFiber20ReverseRow_49_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_50_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 50) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk25_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 50) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber20ReverseSingleStep50 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 34) (tmFiber20StateAt 50) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 34) (tmFiber20StateAt 50)
    (tmFiber20RowAt 50).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 50) (by decide) tmFiber20ReverseRow_50_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_51_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 51) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk25_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 50) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber20ReverseSingleStep51 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 35) (tmFiber20StateAt 51) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 35) (tmFiber20StateAt 51)
    (tmFiber20RowAt 51).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 51) (by decide) tmFiber20ReverseRow_51_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_52_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 52) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk26_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 52) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber20ReverseSingleStep52 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 36) (tmFiber20StateAt 52) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 36) (tmFiber20StateAt 52)
    (tmFiber20RowAt 52).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 52) (by decide) tmFiber20ReverseRow_52_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_53_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 53) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk26_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 52) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber20ReverseSingleStep53 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 37) (tmFiber20StateAt 53) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 37) (tmFiber20StateAt 53)
    (tmFiber20RowAt 53).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 53) (by decide) tmFiber20ReverseRow_53_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_54_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 54) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk27_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 54) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber20ReverseSingleStep54 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 38) (tmFiber20StateAt 54) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 38) (tmFiber20StateAt 54)
    (tmFiber20RowAt 54).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 54) (by decide) tmFiber20ReverseRow_54_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_55_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 55) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk27_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 54) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber20ReverseSingleStep55 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 39) (tmFiber20StateAt 55) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 39) (tmFiber20StateAt 55)
    (tmFiber20RowAt 55).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 55) (by decide) tmFiber20ReverseRow_55_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_56_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 56) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk28_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 56) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber20ReverseSingleStep56 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 24) (tmFiber20StateAt 56) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 24) (tmFiber20StateAt 56)
    (tmFiber20RowAt 56).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 56) (by decide) tmFiber20ReverseRow_56_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_57_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 57) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk28_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 56) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber20ReverseSingleStep57 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 25) (tmFiber20StateAt 57) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 25) (tmFiber20StateAt 57)
    (tmFiber20RowAt 57).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 57) (by decide) tmFiber20ReverseRow_57_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_58_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 58) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk29_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 58) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber20ReverseSingleStep58 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 26) (tmFiber20StateAt 58) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 26) (tmFiber20StateAt 58)
    (tmFiber20RowAt 58).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 58) (by decide) tmFiber20ReverseRow_58_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_59_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 59) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk29_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 58) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber20ReverseSingleStep59 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 27) (tmFiber20StateAt 59) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 27) (tmFiber20StateAt 59)
    (tmFiber20RowAt 59).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 59) (by decide) tmFiber20ReverseRow_59_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_60_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 60) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk30_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 60) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber20ReverseSingleStep60 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 56) (tmFiber20StateAt 60) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 56) (tmFiber20StateAt 60)
    (tmFiber20RowAt 60).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 60) (by decide) tmFiber20ReverseRow_60_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_61_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 61) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk30_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 60) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber20ReverseSingleStep61 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 57) (tmFiber20StateAt 61) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 57) (tmFiber20StateAt 61)
    (tmFiber20RowAt 61).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 61) (by decide) tmFiber20ReverseRow_61_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_62_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 62) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk31_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 62) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber20ReverseSingleStep62 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 30) (tmFiber20StateAt 62) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 30) (tmFiber20StateAt 62)
    (tmFiber20RowAt 62).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 62) (by decide) tmFiber20ReverseRow_62_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20ReverseRow_63_ok :
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 63) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber20Chunk31_ok
  change (tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 62) &&
    tmRowReverseValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber20ReverseSingleStep63 :
    chainSingleKempeStep tmWord (tmFiber20StateAt 31) (tmFiber20StateAt 63) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber20StateAt 31) (tmFiber20StateAt 63)
    (tmFiber20RowAt 63).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber20Key tmFiber20Expected
        (tmFiber20RowAt 63) (by decide) tmFiber20ReverseRow_63_ok
      simpa [tmFiber20StateAt, tmFiber20RowAt, tmFiber20Rows, listGetD, directRow] using h)

theorem tmFiber20State1_in_pass1_prefix1 :
    tmFiber20StateAt 1 ∈ chainClosureStep tmWord tmFiber20Prefix1 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 0 ∈
      chainClosureStep tmWord tmFiber20Prefix0 ([tmFiber20StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber20Prefix0
      ([tmFiber20StateAt 0]) (tmFiber20StateAt 0) (by simp)
  rw [show tmFiber20Prefix1 = tmFiber20Prefix0 ++ [tmFiber20StateAt 1] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 1) []
    (chainClosureStep tmWord tmFiber20Prefix0 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 0) hparentBefore tmFiber20ReverseSingleStep1
theorem tmFiber20State1_in_pass1_full :
    tmFiber20StateAt 1 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix1 ++ [tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix1 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 1) tmFiber20State1_in_pass1_prefix1
theorem tmFiber20State2_in_pass1_prefix2 :
    tmFiber20StateAt 2 ∈ chainClosureStep tmWord tmFiber20Prefix2 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 0 ∈
      chainClosureStep tmWord tmFiber20Prefix1 ([tmFiber20StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber20Prefix1
      ([tmFiber20StateAt 0]) (tmFiber20StateAt 0) (by simp)
  rw [show tmFiber20Prefix2 = tmFiber20Prefix1 ++ [tmFiber20StateAt 2] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 2) []
    (chainClosureStep tmWord tmFiber20Prefix1 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 0) hparentBefore tmFiber20ReverseSingleStep2
theorem tmFiber20State2_in_pass1_full :
    tmFiber20StateAt 2 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix2 ++ [tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix2 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 2) tmFiber20State2_in_pass1_prefix2
theorem tmFiber20State3_in_pass1_prefix3 :
    tmFiber20StateAt 3 ∈ chainClosureStep tmWord tmFiber20Prefix3 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 1 ∈
      chainClosureStep tmWord tmFiber20Prefix2 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix2 = tmFiber20Prefix1 ++ [tmFiber20StateAt 2] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 2]
      (chainClosureStep tmWord tmFiber20Prefix1 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 1) tmFiber20State1_in_pass1_prefix1
  rw [show tmFiber20Prefix3 = tmFiber20Prefix2 ++ [tmFiber20StateAt 3] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 3) []
    (chainClosureStep tmWord tmFiber20Prefix2 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 1) hparentBefore tmFiber20ReverseSingleStep3
theorem tmFiber20State3_in_pass1_full :
    tmFiber20StateAt 3 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix3 ++ [tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix3 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 3) tmFiber20State3_in_pass1_prefix3
theorem tmFiber20State4_in_pass1_prefix4 :
    tmFiber20StateAt 4 ∈ chainClosureStep tmWord tmFiber20Prefix4 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 2 ∈
      chainClosureStep tmWord tmFiber20Prefix3 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix3 = tmFiber20Prefix2 ++ [tmFiber20StateAt 3] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 3]
      (chainClosureStep tmWord tmFiber20Prefix2 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 2) tmFiber20State2_in_pass1_prefix2
  rw [show tmFiber20Prefix4 = tmFiber20Prefix3 ++ [tmFiber20StateAt 4] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 4) []
    (chainClosureStep tmWord tmFiber20Prefix3 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 2) hparentBefore tmFiber20ReverseSingleStep4
theorem tmFiber20State4_in_pass1_full :
    tmFiber20StateAt 4 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix4 ++ [tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix4 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 4) tmFiber20State4_in_pass1_prefix4
theorem tmFiber20State6_in_pass1_prefix6 :
    tmFiber20StateAt 6 ∈ chainClosureStep tmWord tmFiber20Prefix6 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 1 ∈
      chainClosureStep tmWord tmFiber20Prefix5 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix5 = tmFiber20Prefix1 ++ [tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5]
      (chainClosureStep tmWord tmFiber20Prefix1 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 1) tmFiber20State1_in_pass1_prefix1
  rw [show tmFiber20Prefix6 = tmFiber20Prefix5 ++ [tmFiber20StateAt 6] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 6) []
    (chainClosureStep tmWord tmFiber20Prefix5 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 1) hparentBefore tmFiber20ReverseSingleStep6
theorem tmFiber20State6_in_pass1_full :
    tmFiber20StateAt 6 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix6 ++ [tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix6 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 6) tmFiber20State6_in_pass1_prefix6
theorem tmFiber20State7_in_pass1_prefix7 :
    tmFiber20StateAt 7 ∈ chainClosureStep tmWord tmFiber20Prefix7 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 0 ∈
      chainClosureStep tmWord tmFiber20Prefix6 ([tmFiber20StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber20Prefix6
      ([tmFiber20StateAt 0]) (tmFiber20StateAt 0) (by simp)
  rw [show tmFiber20Prefix7 = tmFiber20Prefix6 ++ [tmFiber20StateAt 7] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 7) []
    (chainClosureStep tmWord tmFiber20Prefix6 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 0) hparentBefore tmFiber20ReverseSingleStep7
theorem tmFiber20State7_in_pass1_full :
    tmFiber20StateAt 7 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix7 ++ [tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix7 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 7) tmFiber20State7_in_pass1_prefix7
theorem tmFiber20State8_in_pass1_prefix8 :
    tmFiber20StateAt 8 ∈ chainClosureStep tmWord tmFiber20Prefix8 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 0 ∈
      chainClosureStep tmWord tmFiber20Prefix7 ([tmFiber20StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber20Prefix7
      ([tmFiber20StateAt 0]) (tmFiber20StateAt 0) (by simp)
  rw [show tmFiber20Prefix8 = tmFiber20Prefix7 ++ [tmFiber20StateAt 8] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 8) []
    (chainClosureStep tmWord tmFiber20Prefix7 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 0) hparentBefore tmFiber20ReverseSingleStep8
theorem tmFiber20State8_in_pass1_full :
    tmFiber20StateAt 8 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix8 ++ [tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix8 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 8) tmFiber20State8_in_pass1_prefix8
theorem tmFiber20State9_in_pass1_prefix9 :
    tmFiber20StateAt 9 ∈ chainClosureStep tmWord tmFiber20Prefix9 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 1 ∈
      chainClosureStep tmWord tmFiber20Prefix8 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix8 = tmFiber20Prefix1 ++ [tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8]
      (chainClosureStep tmWord tmFiber20Prefix1 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 1) tmFiber20State1_in_pass1_prefix1
  rw [show tmFiber20Prefix9 = tmFiber20Prefix8 ++ [tmFiber20StateAt 9] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 9) []
    (chainClosureStep tmWord tmFiber20Prefix8 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 1) hparentBefore tmFiber20ReverseSingleStep9
theorem tmFiber20State9_in_pass1_full :
    tmFiber20StateAt 9 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix9 ++ [tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix9 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 9) tmFiber20State9_in_pass1_prefix9
theorem tmFiber20State10_in_pass1_prefix10 :
    tmFiber20StateAt 10 ∈ chainClosureStep tmWord tmFiber20Prefix10 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 2 ∈
      chainClosureStep tmWord tmFiber20Prefix9 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix9 = tmFiber20Prefix2 ++ [tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9]
      (chainClosureStep tmWord tmFiber20Prefix2 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 2) tmFiber20State2_in_pass1_prefix2
  rw [show tmFiber20Prefix10 = tmFiber20Prefix9 ++ [tmFiber20StateAt 10] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 10) []
    (chainClosureStep tmWord tmFiber20Prefix9 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 2) hparentBefore tmFiber20ReverseSingleStep10
theorem tmFiber20State10_in_pass1_full :
    tmFiber20StateAt 10 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix10 ++ [tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix10 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 10) tmFiber20State10_in_pass1_prefix10
theorem tmFiber20State11_in_pass1_prefix11 :
    tmFiber20StateAt 11 ∈ chainClosureStep tmWord tmFiber20Prefix11 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 3 ∈
      chainClosureStep tmWord tmFiber20Prefix10 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix10 = tmFiber20Prefix3 ++ [tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10]
      (chainClosureStep tmWord tmFiber20Prefix3 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 3) tmFiber20State3_in_pass1_prefix3
  rw [show tmFiber20Prefix11 = tmFiber20Prefix10 ++ [tmFiber20StateAt 11] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 11) []
    (chainClosureStep tmWord tmFiber20Prefix10 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 3) hparentBefore tmFiber20ReverseSingleStep11
theorem tmFiber20State11_in_pass1_full :
    tmFiber20StateAt 11 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix11 ++ [tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix11 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 11) tmFiber20State11_in_pass1_prefix11
theorem tmFiber20State12_in_pass1_prefix12 :
    tmFiber20StateAt 12 ∈ chainClosureStep tmWord tmFiber20Prefix12 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 4 ∈
      chainClosureStep tmWord tmFiber20Prefix11 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix11 = tmFiber20Prefix4 ++ [tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11]
      (chainClosureStep tmWord tmFiber20Prefix4 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 4) tmFiber20State4_in_pass1_prefix4
  rw [show tmFiber20Prefix12 = tmFiber20Prefix11 ++ [tmFiber20StateAt 12] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 12) []
    (chainClosureStep tmWord tmFiber20Prefix11 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 4) hparentBefore tmFiber20ReverseSingleStep12
theorem tmFiber20State12_in_pass1_full :
    tmFiber20StateAt 12 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix12 ++ [tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix12 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 12) tmFiber20State12_in_pass1_prefix12
theorem tmFiber20State14_in_pass1_prefix14 :
    tmFiber20StateAt 14 ∈ chainClosureStep tmWord tmFiber20Prefix14 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 6 ∈
      chainClosureStep tmWord tmFiber20Prefix13 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix13 = tmFiber20Prefix6 ++ [tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13]
      (chainClosureStep tmWord tmFiber20Prefix6 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 6) tmFiber20State6_in_pass1_prefix6
  rw [show tmFiber20Prefix14 = tmFiber20Prefix13 ++ [tmFiber20StateAt 14] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 14) []
    (chainClosureStep tmWord tmFiber20Prefix13 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 6) hparentBefore tmFiber20ReverseSingleStep14
theorem tmFiber20State14_in_pass1_full :
    tmFiber20StateAt 14 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix14 ++ [tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix14 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 14) tmFiber20State14_in_pass1_prefix14
theorem tmFiber20State15_in_pass1_prefix15 :
    tmFiber20StateAt 15 ∈ chainClosureStep tmWord tmFiber20Prefix15 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 7 ∈
      chainClosureStep tmWord tmFiber20Prefix14 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix14 = tmFiber20Prefix7 ++ [tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14]
      (chainClosureStep tmWord tmFiber20Prefix7 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 7) tmFiber20State7_in_pass1_prefix7
  rw [show tmFiber20Prefix15 = tmFiber20Prefix14 ++ [tmFiber20StateAt 15] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 15) []
    (chainClosureStep tmWord tmFiber20Prefix14 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 7) hparentBefore tmFiber20ReverseSingleStep15
theorem tmFiber20State15_in_pass1_full :
    tmFiber20StateAt 15 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix15 ++ [tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix15 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 15) tmFiber20State15_in_pass1_prefix15
theorem tmFiber20State16_in_pass1_prefix16 :
    tmFiber20StateAt 16 ∈ chainClosureStep tmWord tmFiber20Prefix16 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 8 ∈
      chainClosureStep tmWord tmFiber20Prefix15 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix15 = tmFiber20Prefix8 ++ [tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15]
      (chainClosureStep tmWord tmFiber20Prefix8 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 8) tmFiber20State8_in_pass1_prefix8
  rw [show tmFiber20Prefix16 = tmFiber20Prefix15 ++ [tmFiber20StateAt 16] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 16) []
    (chainClosureStep tmWord tmFiber20Prefix15 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 8) hparentBefore tmFiber20ReverseSingleStep16
theorem tmFiber20State16_in_pass1_full :
    tmFiber20StateAt 16 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix16 ++ [tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix16 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 16) tmFiber20State16_in_pass1_prefix16
theorem tmFiber20State17_in_pass1_prefix17 :
    tmFiber20StateAt 17 ∈ chainClosureStep tmWord tmFiber20Prefix17 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 9 ∈
      chainClosureStep tmWord tmFiber20Prefix16 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix16 = tmFiber20Prefix9 ++ [tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16]
      (chainClosureStep tmWord tmFiber20Prefix9 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 9) tmFiber20State9_in_pass1_prefix9
  rw [show tmFiber20Prefix17 = tmFiber20Prefix16 ++ [tmFiber20StateAt 17] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 17) []
    (chainClosureStep tmWord tmFiber20Prefix16 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 9) hparentBefore tmFiber20ReverseSingleStep17
theorem tmFiber20State17_in_pass1_full :
    tmFiber20StateAt 17 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix17 ++ [tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix17 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 17) tmFiber20State17_in_pass1_prefix17
theorem tmFiber20State18_in_pass1_prefix18 :
    tmFiber20StateAt 18 ∈ chainClosureStep tmWord tmFiber20Prefix18 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 10 ∈
      chainClosureStep tmWord tmFiber20Prefix17 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix17 = tmFiber20Prefix10 ++ [tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17]
      (chainClosureStep tmWord tmFiber20Prefix10 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 10) tmFiber20State10_in_pass1_prefix10
  rw [show tmFiber20Prefix18 = tmFiber20Prefix17 ++ [tmFiber20StateAt 18] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 18) []
    (chainClosureStep tmWord tmFiber20Prefix17 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 10) hparentBefore tmFiber20ReverseSingleStep18
theorem tmFiber20State18_in_pass1_full :
    tmFiber20StateAt 18 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix18 ++ [tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix18 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 18) tmFiber20State18_in_pass1_prefix18
theorem tmFiber20State19_in_pass1_prefix19 :
    tmFiber20StateAt 19 ∈ chainClosureStep tmWord tmFiber20Prefix19 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 11 ∈
      chainClosureStep tmWord tmFiber20Prefix18 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix18 = tmFiber20Prefix11 ++ [tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18]
      (chainClosureStep tmWord tmFiber20Prefix11 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 11) tmFiber20State11_in_pass1_prefix11
  rw [show tmFiber20Prefix19 = tmFiber20Prefix18 ++ [tmFiber20StateAt 19] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 19) []
    (chainClosureStep tmWord tmFiber20Prefix18 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 11) hparentBefore tmFiber20ReverseSingleStep19
theorem tmFiber20State19_in_pass1_full :
    tmFiber20StateAt 19 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix19 ++ [tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix19 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 19) tmFiber20State19_in_pass1_prefix19
theorem tmFiber20State20_in_pass1_prefix20 :
    tmFiber20StateAt 20 ∈ chainClosureStep tmWord tmFiber20Prefix20 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 12 ∈
      chainClosureStep tmWord tmFiber20Prefix19 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix19 = tmFiber20Prefix12 ++ [tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19]
      (chainClosureStep tmWord tmFiber20Prefix12 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 12) tmFiber20State12_in_pass1_prefix12
  rw [show tmFiber20Prefix20 = tmFiber20Prefix19 ++ [tmFiber20StateAt 20] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 20) []
    (chainClosureStep tmWord tmFiber20Prefix19 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 12) hparentBefore tmFiber20ReverseSingleStep20
theorem tmFiber20State20_in_pass1_full :
    tmFiber20StateAt 20 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix20 ++ [tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix20 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 20) tmFiber20State20_in_pass1_prefix20
theorem tmFiber20State22_in_pass1_prefix22 :
    tmFiber20StateAt 22 ∈ chainClosureStep tmWord tmFiber20Prefix22 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 14 ∈
      chainClosureStep tmWord tmFiber20Prefix21 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix21 = tmFiber20Prefix14 ++ [tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21]
      (chainClosureStep tmWord tmFiber20Prefix14 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 14) tmFiber20State14_in_pass1_prefix14
  rw [show tmFiber20Prefix22 = tmFiber20Prefix21 ++ [tmFiber20StateAt 22] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 22) []
    (chainClosureStep tmWord tmFiber20Prefix21 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 14) hparentBefore tmFiber20ReverseSingleStep22
theorem tmFiber20State22_in_pass1_full :
    tmFiber20StateAt 22 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix22 ++ [tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix22 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 22) tmFiber20State22_in_pass1_prefix22
theorem tmFiber20State23_in_pass1_prefix23 :
    tmFiber20StateAt 23 ∈ chainClosureStep tmWord tmFiber20Prefix23 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 15 ∈
      chainClosureStep tmWord tmFiber20Prefix22 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix22 = tmFiber20Prefix15 ++ [tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22]
      (chainClosureStep tmWord tmFiber20Prefix15 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 15) tmFiber20State15_in_pass1_prefix15
  rw [show tmFiber20Prefix23 = tmFiber20Prefix22 ++ [tmFiber20StateAt 23] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 23) []
    (chainClosureStep tmWord tmFiber20Prefix22 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 15) hparentBefore tmFiber20ReverseSingleStep23
theorem tmFiber20State23_in_pass1_full :
    tmFiber20StateAt 23 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix23 ++ [tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix23 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 23) tmFiber20State23_in_pass1_prefix23
theorem tmFiber20State24_in_pass1_prefix24 :
    tmFiber20StateAt 24 ∈ chainClosureStep tmWord tmFiber20Prefix24 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 0 ∈
      chainClosureStep tmWord tmFiber20Prefix23 ([tmFiber20StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber20Prefix23
      ([tmFiber20StateAt 0]) (tmFiber20StateAt 0) (by simp)
  rw [show tmFiber20Prefix24 = tmFiber20Prefix23 ++ [tmFiber20StateAt 24] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 24) []
    (chainClosureStep tmWord tmFiber20Prefix23 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 0) hparentBefore tmFiber20ReverseSingleStep24
theorem tmFiber20State24_in_pass1_full :
    tmFiber20StateAt 24 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix24 ++ [tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix24 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 24) tmFiber20State24_in_pass1_prefix24
theorem tmFiber20State25_in_pass1_prefix25 :
    tmFiber20StateAt 25 ∈ chainClosureStep tmWord tmFiber20Prefix25 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 1 ∈
      chainClosureStep tmWord tmFiber20Prefix24 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix24 = tmFiber20Prefix1 ++ [tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24]
      (chainClosureStep tmWord tmFiber20Prefix1 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 1) tmFiber20State1_in_pass1_prefix1
  rw [show tmFiber20Prefix25 = tmFiber20Prefix24 ++ [tmFiber20StateAt 25] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 25) []
    (chainClosureStep tmWord tmFiber20Prefix24 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 1) hparentBefore tmFiber20ReverseSingleStep25
theorem tmFiber20State25_in_pass1_full :
    tmFiber20StateAt 25 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix25 ++ [tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix25 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 25) tmFiber20State25_in_pass1_prefix25
theorem tmFiber20State26_in_pass1_prefix26 :
    tmFiber20StateAt 26 ∈ chainClosureStep tmWord tmFiber20Prefix26 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 2 ∈
      chainClosureStep tmWord tmFiber20Prefix25 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix25 = tmFiber20Prefix2 ++ [tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25]
      (chainClosureStep tmWord tmFiber20Prefix2 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 2) tmFiber20State2_in_pass1_prefix2
  rw [show tmFiber20Prefix26 = tmFiber20Prefix25 ++ [tmFiber20StateAt 26] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 26) []
    (chainClosureStep tmWord tmFiber20Prefix25 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 2) hparentBefore tmFiber20ReverseSingleStep26
theorem tmFiber20State26_in_pass1_full :
    tmFiber20StateAt 26 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix26 ++ [tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix26 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 26) tmFiber20State26_in_pass1_prefix26
theorem tmFiber20State27_in_pass1_prefix27 :
    tmFiber20StateAt 27 ∈ chainClosureStep tmWord tmFiber20Prefix27 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 3 ∈
      chainClosureStep tmWord tmFiber20Prefix26 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix26 = tmFiber20Prefix3 ++ [tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26]
      (chainClosureStep tmWord tmFiber20Prefix3 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 3) tmFiber20State3_in_pass1_prefix3
  rw [show tmFiber20Prefix27 = tmFiber20Prefix26 ++ [tmFiber20StateAt 27] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 27) []
    (chainClosureStep tmWord tmFiber20Prefix26 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 3) hparentBefore tmFiber20ReverseSingleStep27
theorem tmFiber20State27_in_pass1_full :
    tmFiber20StateAt 27 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix27 ++ [tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix27 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 27) tmFiber20State27_in_pass1_prefix27
theorem tmFiber20State28_in_pass1_prefix28 :
    tmFiber20StateAt 28 ∈ chainClosureStep tmWord tmFiber20Prefix28 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 4 ∈
      chainClosureStep tmWord tmFiber20Prefix27 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix27 = tmFiber20Prefix4 ++ [tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27]
      (chainClosureStep tmWord tmFiber20Prefix4 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 4) tmFiber20State4_in_pass1_prefix4
  rw [show tmFiber20Prefix28 = tmFiber20Prefix27 ++ [tmFiber20StateAt 28] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 28) []
    (chainClosureStep tmWord tmFiber20Prefix27 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 4) hparentBefore tmFiber20ReverseSingleStep28
theorem tmFiber20State28_in_pass1_full :
    tmFiber20StateAt 28 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix28 ++ [tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix28 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 28) tmFiber20State28_in_pass1_prefix28
theorem tmFiber20State30_in_pass1_prefix30 :
    tmFiber20StateAt 30 ∈ chainClosureStep tmWord tmFiber20Prefix30 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 6 ∈
      chainClosureStep tmWord tmFiber20Prefix29 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix29 = tmFiber20Prefix6 ++ [tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29]
      (chainClosureStep tmWord tmFiber20Prefix6 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 6) tmFiber20State6_in_pass1_prefix6
  rw [show tmFiber20Prefix30 = tmFiber20Prefix29 ++ [tmFiber20StateAt 30] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 30) []
    (chainClosureStep tmWord tmFiber20Prefix29 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 6) hparentBefore tmFiber20ReverseSingleStep30
theorem tmFiber20State30_in_pass1_full :
    tmFiber20StateAt 30 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix30 ++ [tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix30 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 30) tmFiber20State30_in_pass1_prefix30
theorem tmFiber20State31_in_pass1_prefix31 :
    tmFiber20StateAt 31 ∈ chainClosureStep tmWord tmFiber20Prefix31 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 7 ∈
      chainClosureStep tmWord tmFiber20Prefix30 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix30 = tmFiber20Prefix7 ++ [tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30]
      (chainClosureStep tmWord tmFiber20Prefix7 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 7) tmFiber20State7_in_pass1_prefix7
  rw [show tmFiber20Prefix31 = tmFiber20Prefix30 ++ [tmFiber20StateAt 31] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 31) []
    (chainClosureStep tmWord tmFiber20Prefix30 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 7) hparentBefore tmFiber20ReverseSingleStep31
theorem tmFiber20State31_in_pass1_full :
    tmFiber20StateAt 31 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix31 ++ [tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix31 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 31) tmFiber20State31_in_pass1_prefix31
theorem tmFiber20State32_in_pass1_prefix32 :
    tmFiber20StateAt 32 ∈ chainClosureStep tmWord tmFiber20Prefix32 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 0 ∈
      chainClosureStep tmWord tmFiber20Prefix31 ([tmFiber20StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber20Prefix31
      ([tmFiber20StateAt 0]) (tmFiber20StateAt 0) (by simp)
  rw [show tmFiber20Prefix32 = tmFiber20Prefix31 ++ [tmFiber20StateAt 32] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 32) []
    (chainClosureStep tmWord tmFiber20Prefix31 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 0) hparentBefore tmFiber20ReverseSingleStep32
theorem tmFiber20State32_in_pass1_full :
    tmFiber20StateAt 32 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix32 ++ [tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix32 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 32) tmFiber20State32_in_pass1_prefix32
theorem tmFiber20State33_in_pass1_prefix33 :
    tmFiber20StateAt 33 ∈ chainClosureStep tmWord tmFiber20Prefix33 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 1 ∈
      chainClosureStep tmWord tmFiber20Prefix32 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix32 = tmFiber20Prefix1 ++ [tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 2, tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32]
      (chainClosureStep tmWord tmFiber20Prefix1 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 1) tmFiber20State1_in_pass1_prefix1
  rw [show tmFiber20Prefix33 = tmFiber20Prefix32 ++ [tmFiber20StateAt 33] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 33) []
    (chainClosureStep tmWord tmFiber20Prefix32 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 1) hparentBefore tmFiber20ReverseSingleStep33
theorem tmFiber20State33_in_pass1_full :
    tmFiber20StateAt 33 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix33 ++ [tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix33 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 33) tmFiber20State33_in_pass1_prefix33
theorem tmFiber20State34_in_pass1_prefix34 :
    tmFiber20StateAt 34 ∈ chainClosureStep tmWord tmFiber20Prefix34 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 2 ∈
      chainClosureStep tmWord tmFiber20Prefix33 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix33 = tmFiber20Prefix2 ++ [tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 3, tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33]
      (chainClosureStep tmWord tmFiber20Prefix2 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 2) tmFiber20State2_in_pass1_prefix2
  rw [show tmFiber20Prefix34 = tmFiber20Prefix33 ++ [tmFiber20StateAt 34] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 34) []
    (chainClosureStep tmWord tmFiber20Prefix33 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 2) hparentBefore tmFiber20ReverseSingleStep34
theorem tmFiber20State34_in_pass1_full :
    tmFiber20StateAt 34 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix34 ++ [tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix34 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 34) tmFiber20State34_in_pass1_prefix34
theorem tmFiber20State35_in_pass1_prefix35 :
    tmFiber20StateAt 35 ∈ chainClosureStep tmWord tmFiber20Prefix35 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 3 ∈
      chainClosureStep tmWord tmFiber20Prefix34 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix34 = tmFiber20Prefix3 ++ [tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 4, tmFiber20StateAt 5, tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34]
      (chainClosureStep tmWord tmFiber20Prefix3 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 3) tmFiber20State3_in_pass1_prefix3
  rw [show tmFiber20Prefix35 = tmFiber20Prefix34 ++ [tmFiber20StateAt 35] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 35) []
    (chainClosureStep tmWord tmFiber20Prefix34 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 3) hparentBefore tmFiber20ReverseSingleStep35
theorem tmFiber20State35_in_pass1_full :
    tmFiber20StateAt 35 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix35 ++ [tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix35 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 35) tmFiber20State35_in_pass1_prefix35
theorem tmFiber20State36_in_pass1_prefix36 :
    tmFiber20StateAt 36 ∈ chainClosureStep tmWord tmFiber20Prefix36 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 32 ∈
      chainClosureStep tmWord tmFiber20Prefix35 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix35 = tmFiber20Prefix32 ++ [tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35]
      (chainClosureStep tmWord tmFiber20Prefix32 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 32) tmFiber20State32_in_pass1_prefix32
  rw [show tmFiber20Prefix36 = tmFiber20Prefix35 ++ [tmFiber20StateAt 36] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 36) []
    (chainClosureStep tmWord tmFiber20Prefix35 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 32) hparentBefore tmFiber20ReverseSingleStep36
theorem tmFiber20State36_in_pass1_full :
    tmFiber20StateAt 36 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix36 ++ [tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix36 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 36) tmFiber20State36_in_pass1_prefix36
theorem tmFiber20State37_in_pass1_prefix37 :
    tmFiber20StateAt 37 ∈ chainClosureStep tmWord tmFiber20Prefix37 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 33 ∈
      chainClosureStep tmWord tmFiber20Prefix36 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix36 = tmFiber20Prefix33 ++ [tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36]
      (chainClosureStep tmWord tmFiber20Prefix33 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 33) tmFiber20State33_in_pass1_prefix33
  rw [show tmFiber20Prefix37 = tmFiber20Prefix36 ++ [tmFiber20StateAt 37] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 37) []
    (chainClosureStep tmWord tmFiber20Prefix36 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 33) hparentBefore tmFiber20ReverseSingleStep37
theorem tmFiber20State37_in_pass1_full :
    tmFiber20StateAt 37 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix37 ++ [tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix37 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 37) tmFiber20State37_in_pass1_prefix37
theorem tmFiber20State38_in_pass1_prefix38 :
    tmFiber20StateAt 38 ∈ chainClosureStep tmWord tmFiber20Prefix38 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 6 ∈
      chainClosureStep tmWord tmFiber20Prefix37 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix37 = tmFiber20Prefix6 ++ [tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37]
      (chainClosureStep tmWord tmFiber20Prefix6 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 6) tmFiber20State6_in_pass1_prefix6
  rw [show tmFiber20Prefix38 = tmFiber20Prefix37 ++ [tmFiber20StateAt 38] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 38) []
    (chainClosureStep tmWord tmFiber20Prefix37 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 6) hparentBefore tmFiber20ReverseSingleStep38
theorem tmFiber20State38_in_pass1_full :
    tmFiber20StateAt 38 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix38 ++ [tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix38 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 38) tmFiber20State38_in_pass1_prefix38
theorem tmFiber20State39_in_pass1_prefix39 :
    tmFiber20StateAt 39 ∈ chainClosureStep tmWord tmFiber20Prefix39 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 7 ∈
      chainClosureStep tmWord tmFiber20Prefix38 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix38 = tmFiber20Prefix7 ++ [tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38]
      (chainClosureStep tmWord tmFiber20Prefix7 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 7) tmFiber20State7_in_pass1_prefix7
  rw [show tmFiber20Prefix39 = tmFiber20Prefix38 ++ [tmFiber20StateAt 39] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 39) []
    (chainClosureStep tmWord tmFiber20Prefix38 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 7) hparentBefore tmFiber20ReverseSingleStep39
theorem tmFiber20State39_in_pass1_full :
    tmFiber20StateAt 39 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix39 ++ [tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix39 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 39) tmFiber20State39_in_pass1_prefix39
theorem tmFiber20State40_in_pass1_prefix40 :
    tmFiber20StateAt 40 ∈ chainClosureStep tmWord tmFiber20Prefix40 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 8 ∈
      chainClosureStep tmWord tmFiber20Prefix39 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix39 = tmFiber20Prefix8 ++ [tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39]
      (chainClosureStep tmWord tmFiber20Prefix8 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 8) tmFiber20State8_in_pass1_prefix8
  rw [show tmFiber20Prefix40 = tmFiber20Prefix39 ++ [tmFiber20StateAt 40] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 40) []
    (chainClosureStep tmWord tmFiber20Prefix39 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 8) hparentBefore tmFiber20ReverseSingleStep40
theorem tmFiber20State40_in_pass1_full :
    tmFiber20StateAt 40 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix40 ++ [tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix40 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 40) tmFiber20State40_in_pass1_prefix40
theorem tmFiber20State41_in_pass1_prefix41 :
    tmFiber20StateAt 41 ∈ chainClosureStep tmWord tmFiber20Prefix41 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 9 ∈
      chainClosureStep tmWord tmFiber20Prefix40 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix40 = tmFiber20Prefix9 ++ [tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40]
      (chainClosureStep tmWord tmFiber20Prefix9 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 9) tmFiber20State9_in_pass1_prefix9
  rw [show tmFiber20Prefix41 = tmFiber20Prefix40 ++ [tmFiber20StateAt 41] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 41) []
    (chainClosureStep tmWord tmFiber20Prefix40 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 9) hparentBefore tmFiber20ReverseSingleStep41
theorem tmFiber20State41_in_pass1_full :
    tmFiber20StateAt 41 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix41 ++ [tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix41 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 41) tmFiber20State41_in_pass1_prefix41
theorem tmFiber20State42_in_pass1_prefix42 :
    tmFiber20StateAt 42 ∈ chainClosureStep tmWord tmFiber20Prefix42 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 10 ∈
      chainClosureStep tmWord tmFiber20Prefix41 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix41 = tmFiber20Prefix10 ++ [tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41]
      (chainClosureStep tmWord tmFiber20Prefix10 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 10) tmFiber20State10_in_pass1_prefix10
  rw [show tmFiber20Prefix42 = tmFiber20Prefix41 ++ [tmFiber20StateAt 42] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 42) []
    (chainClosureStep tmWord tmFiber20Prefix41 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 10) hparentBefore tmFiber20ReverseSingleStep42
theorem tmFiber20State42_in_pass1_full :
    tmFiber20StateAt 42 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix42 ++ [tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix42 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 42) tmFiber20State42_in_pass1_prefix42
theorem tmFiber20State43_in_pass1_prefix43 :
    tmFiber20StateAt 43 ∈ chainClosureStep tmWord tmFiber20Prefix43 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 11 ∈
      chainClosureStep tmWord tmFiber20Prefix42 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix42 = tmFiber20Prefix11 ++ [tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42]
      (chainClosureStep tmWord tmFiber20Prefix11 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 11) tmFiber20State11_in_pass1_prefix11
  rw [show tmFiber20Prefix43 = tmFiber20Prefix42 ++ [tmFiber20StateAt 43] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 43) []
    (chainClosureStep tmWord tmFiber20Prefix42 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 11) hparentBefore tmFiber20ReverseSingleStep43
theorem tmFiber20State43_in_pass1_full :
    tmFiber20StateAt 43 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix43 ++ [tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix43 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 43) tmFiber20State43_in_pass1_prefix43
theorem tmFiber20State44_in_pass1_prefix44 :
    tmFiber20StateAt 44 ∈ chainClosureStep tmWord tmFiber20Prefix44 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 40 ∈
      chainClosureStep tmWord tmFiber20Prefix43 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix43 = tmFiber20Prefix40 ++ [tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43]
      (chainClosureStep tmWord tmFiber20Prefix40 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 40) tmFiber20State40_in_pass1_prefix40
  rw [show tmFiber20Prefix44 = tmFiber20Prefix43 ++ [tmFiber20StateAt 44] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 44) []
    (chainClosureStep tmWord tmFiber20Prefix43 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 40) hparentBefore tmFiber20ReverseSingleStep44
theorem tmFiber20State44_in_pass1_full :
    tmFiber20StateAt 44 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix44 ++ [tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix44 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 44) tmFiber20State44_in_pass1_prefix44
theorem tmFiber20State45_in_pass1_prefix45 :
    tmFiber20StateAt 45 ∈ chainClosureStep tmWord tmFiber20Prefix45 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 41 ∈
      chainClosureStep tmWord tmFiber20Prefix44 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix44 = tmFiber20Prefix41 ++ [tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44]
      (chainClosureStep tmWord tmFiber20Prefix41 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 41) tmFiber20State41_in_pass1_prefix41
  rw [show tmFiber20Prefix45 = tmFiber20Prefix44 ++ [tmFiber20StateAt 45] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 45) []
    (chainClosureStep tmWord tmFiber20Prefix44 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 41) hparentBefore tmFiber20ReverseSingleStep45
theorem tmFiber20State45_in_pass1_full :
    tmFiber20StateAt 45 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix45 ++ [tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix45 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 45) tmFiber20State45_in_pass1_prefix45
theorem tmFiber20State46_in_pass1_prefix46 :
    tmFiber20StateAt 46 ∈ chainClosureStep tmWord tmFiber20Prefix46 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 14 ∈
      chainClosureStep tmWord tmFiber20Prefix45 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix45 = tmFiber20Prefix14 ++ [tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45]
      (chainClosureStep tmWord tmFiber20Prefix14 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 14) tmFiber20State14_in_pass1_prefix14
  rw [show tmFiber20Prefix46 = tmFiber20Prefix45 ++ [tmFiber20StateAt 46] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 46) []
    (chainClosureStep tmWord tmFiber20Prefix45 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 14) hparentBefore tmFiber20ReverseSingleStep46
theorem tmFiber20State46_in_pass1_full :
    tmFiber20StateAt 46 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix46 ++ [tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix46 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 46) tmFiber20State46_in_pass1_prefix46
theorem tmFiber20State47_in_pass1_prefix47 :
    tmFiber20StateAt 47 ∈ chainClosureStep tmWord tmFiber20Prefix47 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 15 ∈
      chainClosureStep tmWord tmFiber20Prefix46 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix46 = tmFiber20Prefix15 ++ [tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46]
      (chainClosureStep tmWord tmFiber20Prefix15 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 15) tmFiber20State15_in_pass1_prefix15
  rw [show tmFiber20Prefix47 = tmFiber20Prefix46 ++ [tmFiber20StateAt 47] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 47) []
    (chainClosureStep tmWord tmFiber20Prefix46 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 15) hparentBefore tmFiber20ReverseSingleStep47
theorem tmFiber20State47_in_pass1_full :
    tmFiber20StateAt 47 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix47 ++ [tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix47 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 47) tmFiber20State47_in_pass1_prefix47
theorem tmFiber20State48_in_pass1_prefix48 :
    tmFiber20StateAt 48 ∈ chainClosureStep tmWord tmFiber20Prefix48 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 32 ∈
      chainClosureStep tmWord tmFiber20Prefix47 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix47 = tmFiber20Prefix32 ++ [tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47]
      (chainClosureStep tmWord tmFiber20Prefix32 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 32) tmFiber20State32_in_pass1_prefix32
  rw [show tmFiber20Prefix48 = tmFiber20Prefix47 ++ [tmFiber20StateAt 48] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 48) []
    (chainClosureStep tmWord tmFiber20Prefix47 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 32) hparentBefore tmFiber20ReverseSingleStep48
theorem tmFiber20State48_in_pass1_full :
    tmFiber20StateAt 48 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix48 ++ [tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix48 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 48) tmFiber20State48_in_pass1_prefix48
theorem tmFiber20State49_in_pass1_prefix49 :
    tmFiber20StateAt 49 ∈ chainClosureStep tmWord tmFiber20Prefix49 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 33 ∈
      chainClosureStep tmWord tmFiber20Prefix48 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix48 = tmFiber20Prefix33 ++ [tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48]
      (chainClosureStep tmWord tmFiber20Prefix33 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 33) tmFiber20State33_in_pass1_prefix33
  rw [show tmFiber20Prefix49 = tmFiber20Prefix48 ++ [tmFiber20StateAt 49] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 49) []
    (chainClosureStep tmWord tmFiber20Prefix48 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 33) hparentBefore tmFiber20ReverseSingleStep49
theorem tmFiber20State49_in_pass1_full :
    tmFiber20StateAt 49 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix49 ++ [tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix49 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 49) tmFiber20State49_in_pass1_prefix49
theorem tmFiber20State50_in_pass1_prefix50 :
    tmFiber20StateAt 50 ∈ chainClosureStep tmWord tmFiber20Prefix50 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 34 ∈
      chainClosureStep tmWord tmFiber20Prefix49 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix49 = tmFiber20Prefix34 ++ [tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49]
      (chainClosureStep tmWord tmFiber20Prefix34 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 34) tmFiber20State34_in_pass1_prefix34
  rw [show tmFiber20Prefix50 = tmFiber20Prefix49 ++ [tmFiber20StateAt 50] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 50) []
    (chainClosureStep tmWord tmFiber20Prefix49 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 34) hparentBefore tmFiber20ReverseSingleStep50
theorem tmFiber20State50_in_pass1_full :
    tmFiber20StateAt 50 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix50 ++ [tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix50 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 50) tmFiber20State50_in_pass1_prefix50
theorem tmFiber20State51_in_pass1_prefix51 :
    tmFiber20StateAt 51 ∈ chainClosureStep tmWord tmFiber20Prefix51 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 35 ∈
      chainClosureStep tmWord tmFiber20Prefix50 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix50 = tmFiber20Prefix35 ++ [tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50]
      (chainClosureStep tmWord tmFiber20Prefix35 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 35) tmFiber20State35_in_pass1_prefix35
  rw [show tmFiber20Prefix51 = tmFiber20Prefix50 ++ [tmFiber20StateAt 51] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 51) []
    (chainClosureStep tmWord tmFiber20Prefix50 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 35) hparentBefore tmFiber20ReverseSingleStep51
theorem tmFiber20State51_in_pass1_full :
    tmFiber20StateAt 51 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix51 ++ [tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix51 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 51) tmFiber20State51_in_pass1_prefix51
theorem tmFiber20State52_in_pass1_prefix52 :
    tmFiber20StateAt 52 ∈ chainClosureStep tmWord tmFiber20Prefix52 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 36 ∈
      chainClosureStep tmWord tmFiber20Prefix51 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix51 = tmFiber20Prefix36 ++ [tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51]
      (chainClosureStep tmWord tmFiber20Prefix36 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 36) tmFiber20State36_in_pass1_prefix36
  rw [show tmFiber20Prefix52 = tmFiber20Prefix51 ++ [tmFiber20StateAt 52] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 52) []
    (chainClosureStep tmWord tmFiber20Prefix51 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 36) hparentBefore tmFiber20ReverseSingleStep52
theorem tmFiber20State52_in_pass1_full :
    tmFiber20StateAt 52 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix52 ++ [tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix52 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 52) tmFiber20State52_in_pass1_prefix52
theorem tmFiber20State53_in_pass1_prefix53 :
    tmFiber20StateAt 53 ∈ chainClosureStep tmWord tmFiber20Prefix53 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 37 ∈
      chainClosureStep tmWord tmFiber20Prefix52 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix52 = tmFiber20Prefix37 ++ [tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52]
      (chainClosureStep tmWord tmFiber20Prefix37 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 37) tmFiber20State37_in_pass1_prefix37
  rw [show tmFiber20Prefix53 = tmFiber20Prefix52 ++ [tmFiber20StateAt 53] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 53) []
    (chainClosureStep tmWord tmFiber20Prefix52 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 37) hparentBefore tmFiber20ReverseSingleStep53
theorem tmFiber20State53_in_pass1_full :
    tmFiber20StateAt 53 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix53 ++ [tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix53 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 53) tmFiber20State53_in_pass1_prefix53
theorem tmFiber20State54_in_pass1_prefix54 :
    tmFiber20StateAt 54 ∈ chainClosureStep tmWord tmFiber20Prefix54 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 38 ∈
      chainClosureStep tmWord tmFiber20Prefix53 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix53 = tmFiber20Prefix38 ++ [tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53]
      (chainClosureStep tmWord tmFiber20Prefix38 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 38) tmFiber20State38_in_pass1_prefix38
  rw [show tmFiber20Prefix54 = tmFiber20Prefix53 ++ [tmFiber20StateAt 54] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 54) []
    (chainClosureStep tmWord tmFiber20Prefix53 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 38) hparentBefore tmFiber20ReverseSingleStep54
theorem tmFiber20State54_in_pass1_full :
    tmFiber20StateAt 54 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix54 ++ [tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix54 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 54) tmFiber20State54_in_pass1_prefix54
theorem tmFiber20State55_in_pass1_prefix55 :
    tmFiber20StateAt 55 ∈ chainClosureStep tmWord tmFiber20Prefix55 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 39 ∈
      chainClosureStep tmWord tmFiber20Prefix54 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix54 = tmFiber20Prefix39 ++ [tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54]
      (chainClosureStep tmWord tmFiber20Prefix39 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 39) tmFiber20State39_in_pass1_prefix39
  rw [show tmFiber20Prefix55 = tmFiber20Prefix54 ++ [tmFiber20StateAt 55] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 55) []
    (chainClosureStep tmWord tmFiber20Prefix54 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 39) hparentBefore tmFiber20ReverseSingleStep55
theorem tmFiber20State55_in_pass1_full :
    tmFiber20StateAt 55 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix55 ++ [tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix55 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 55) tmFiber20State55_in_pass1_prefix55
theorem tmFiber20State56_in_pass1_prefix56 :
    tmFiber20StateAt 56 ∈ chainClosureStep tmWord tmFiber20Prefix56 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 24 ∈
      chainClosureStep tmWord tmFiber20Prefix55 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix55 = tmFiber20Prefix24 ++ [tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55]
      (chainClosureStep tmWord tmFiber20Prefix24 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 24) tmFiber20State24_in_pass1_prefix24
  rw [show tmFiber20Prefix56 = tmFiber20Prefix55 ++ [tmFiber20StateAt 56] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 56) []
    (chainClosureStep tmWord tmFiber20Prefix55 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 24) hparentBefore tmFiber20ReverseSingleStep56
theorem tmFiber20State56_in_pass1_full :
    tmFiber20StateAt 56 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix56 ++ [tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix56 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 56) tmFiber20State56_in_pass1_prefix56
theorem tmFiber20State57_in_pass1_prefix57 :
    tmFiber20StateAt 57 ∈ chainClosureStep tmWord tmFiber20Prefix57 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 25 ∈
      chainClosureStep tmWord tmFiber20Prefix56 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix56 = tmFiber20Prefix25 ++ [tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56]
      (chainClosureStep tmWord tmFiber20Prefix25 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 25) tmFiber20State25_in_pass1_prefix25
  rw [show tmFiber20Prefix57 = tmFiber20Prefix56 ++ [tmFiber20StateAt 57] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 57) []
    (chainClosureStep tmWord tmFiber20Prefix56 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 25) hparentBefore tmFiber20ReverseSingleStep57
theorem tmFiber20State57_in_pass1_full :
    tmFiber20StateAt 57 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix57 ++ [tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix57 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 57) tmFiber20State57_in_pass1_prefix57
theorem tmFiber20State58_in_pass1_prefix58 :
    tmFiber20StateAt 58 ∈ chainClosureStep tmWord tmFiber20Prefix58 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 26 ∈
      chainClosureStep tmWord tmFiber20Prefix57 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix57 = tmFiber20Prefix26 ++ [tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57]
      (chainClosureStep tmWord tmFiber20Prefix26 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 26) tmFiber20State26_in_pass1_prefix26
  rw [show tmFiber20Prefix58 = tmFiber20Prefix57 ++ [tmFiber20StateAt 58] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 58) []
    (chainClosureStep tmWord tmFiber20Prefix57 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 26) hparentBefore tmFiber20ReverseSingleStep58
theorem tmFiber20State58_in_pass1_full :
    tmFiber20StateAt 58 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix58 ++ [tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix58 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 58) tmFiber20State58_in_pass1_prefix58
theorem tmFiber20State59_in_pass1_prefix59 :
    tmFiber20StateAt 59 ∈ chainClosureStep tmWord tmFiber20Prefix59 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 27 ∈
      chainClosureStep tmWord tmFiber20Prefix58 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix58 = tmFiber20Prefix27 ++ [tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58]
      (chainClosureStep tmWord tmFiber20Prefix27 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 27) tmFiber20State27_in_pass1_prefix27
  rw [show tmFiber20Prefix59 = tmFiber20Prefix58 ++ [tmFiber20StateAt 59] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 59) []
    (chainClosureStep tmWord tmFiber20Prefix58 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 27) hparentBefore tmFiber20ReverseSingleStep59
theorem tmFiber20State59_in_pass1_full :
    tmFiber20StateAt 59 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix59 ++ [tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix59 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 59) tmFiber20State59_in_pass1_prefix59
theorem tmFiber20State60_in_pass1_prefix60 :
    tmFiber20StateAt 60 ∈ chainClosureStep tmWord tmFiber20Prefix60 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 56 ∈
      chainClosureStep tmWord tmFiber20Prefix59 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix59 = tmFiber20Prefix56 ++ [tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59]
      (chainClosureStep tmWord tmFiber20Prefix56 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 56) tmFiber20State56_in_pass1_prefix56
  rw [show tmFiber20Prefix60 = tmFiber20Prefix59 ++ [tmFiber20StateAt 60] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 60) []
    (chainClosureStep tmWord tmFiber20Prefix59 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 56) hparentBefore tmFiber20ReverseSingleStep60
theorem tmFiber20State60_in_pass1_full :
    tmFiber20StateAt 60 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix60 ++ [tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix60 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 60) tmFiber20State60_in_pass1_prefix60
theorem tmFiber20State61_in_pass1_prefix61 :
    tmFiber20StateAt 61 ∈ chainClosureStep tmWord tmFiber20Prefix61 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 57 ∈
      chainClosureStep tmWord tmFiber20Prefix60 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix60 = tmFiber20Prefix57 ++ [tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60]
      (chainClosureStep tmWord tmFiber20Prefix57 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 57) tmFiber20State57_in_pass1_prefix57
  rw [show tmFiber20Prefix61 = tmFiber20Prefix60 ++ [tmFiber20StateAt 61] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 61) []
    (chainClosureStep tmWord tmFiber20Prefix60 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 57) hparentBefore tmFiber20ReverseSingleStep61
theorem tmFiber20State61_in_pass1_full :
    tmFiber20StateAt 61 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix61 ++ [tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix61 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 61) tmFiber20State61_in_pass1_prefix61
theorem tmFiber20State62_in_pass1_prefix62 :
    tmFiber20StateAt 62 ∈ chainClosureStep tmWord tmFiber20Prefix62 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 30 ∈
      chainClosureStep tmWord tmFiber20Prefix61 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix61 = tmFiber20Prefix30 ++ [tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61]
      (chainClosureStep tmWord tmFiber20Prefix30 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 30) tmFiber20State30_in_pass1_prefix30
  rw [show tmFiber20Prefix62 = tmFiber20Prefix61 ++ [tmFiber20StateAt 62] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 62) []
    (chainClosureStep tmWord tmFiber20Prefix61 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 30) hparentBefore tmFiber20ReverseSingleStep62
theorem tmFiber20State62_in_pass1_full :
    tmFiber20StateAt 62 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix62 ++ [tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix62 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 62) tmFiber20State62_in_pass1_prefix62
theorem tmFiber20State63_in_pass1_prefix63 :
    tmFiber20StateAt 63 ∈ chainClosureStep tmWord tmFiber20Prefix63 ([tmFiber20StateAt 0]) := by
  have hparentBefore : tmFiber20StateAt 31 ∈
      chainClosureStep tmWord tmFiber20Prefix62 ([tmFiber20StateAt 0]) := by
    rw [show tmFiber20Prefix62 = tmFiber20Prefix31 ++ [tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62]
      (chainClosureStep tmWord tmFiber20Prefix31 ([tmFiber20StateAt 0]))
      (tmFiber20StateAt 31) tmFiber20State31_in_pass1_prefix31
  rw [show tmFiber20Prefix63 = tmFiber20Prefix62 ++ [tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 63) []
    (chainClosureStep tmWord tmFiber20Prefix62 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 31) hparentBefore tmFiber20ReverseSingleStep63
theorem tmFiber20State63_in_pass1_full :
    tmFiber20StateAt 63 ∈ chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0]) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix63 ++ [] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord []
    (chainClosureStep tmWord tmFiber20Prefix63 ([tmFiber20StateAt 0]))
    (tmFiber20StateAt 63) tmFiber20State63_in_pass1_prefix63
theorem tmFiber20State5_in_pass2_prefix5 :
    tmFiber20StateAt 5 ∈ chainClosureStep tmWord tmFiber20Prefix5 (chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0])) := by
  have hparentBefore : tmFiber20StateAt 7 ∈
      chainClosureStep tmWord tmFiber20Prefix4 (chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber20Prefix4
      (chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0])) (tmFiber20StateAt 7) tmFiber20State7_in_pass1_full
  rw [show tmFiber20Prefix5 = tmFiber20Prefix4 ++ [tmFiber20StateAt 5] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 5) []
    (chainClosureStep tmWord tmFiber20Prefix4 (chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0])))
    (tmFiber20StateAt 7) hparentBefore tmFiber20ReverseSingleStep5
theorem tmFiber20State5_in_pass2_full :
    tmFiber20StateAt 5 ∈ chainClosureStep tmWord tmFiber20DirectStates (chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0])) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix5 ++ [tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix5 (chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0])))
    (tmFiber20StateAt 5) tmFiber20State5_in_pass2_prefix5
theorem tmFiber20State13_in_pass2_prefix13 :
    tmFiber20StateAt 13 ∈ chainClosureStep tmWord tmFiber20Prefix13 (chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0])) := by
  have hparentBefore : tmFiber20StateAt 5 ∈
      chainClosureStep tmWord tmFiber20Prefix12 (chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0])) := by
    rw [show tmFiber20Prefix12 = tmFiber20Prefix5 ++ [tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12]
      (chainClosureStep tmWord tmFiber20Prefix5 (chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0])))
      (tmFiber20StateAt 5) tmFiber20State5_in_pass2_prefix5
  rw [show tmFiber20Prefix13 = tmFiber20Prefix12 ++ [tmFiber20StateAt 13] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 13) []
    (chainClosureStep tmWord tmFiber20Prefix12 (chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0])))
    (tmFiber20StateAt 5) hparentBefore tmFiber20ReverseSingleStep13
theorem tmFiber20State13_in_pass2_full :
    tmFiber20StateAt 13 ∈ chainClosureStep tmWord tmFiber20DirectStates (chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0])) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix13 ++ [tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix13 (chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0])))
    (tmFiber20StateAt 13) tmFiber20State13_in_pass2_prefix13
theorem tmFiber20State21_in_pass2_prefix21 :
    tmFiber20StateAt 21 ∈ chainClosureStep tmWord tmFiber20Prefix21 (chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0])) := by
  have hparentBefore : tmFiber20StateAt 13 ∈
      chainClosureStep tmWord tmFiber20Prefix20 (chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0])) := by
    rw [show tmFiber20Prefix20 = tmFiber20Prefix13 ++ [tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20]
      (chainClosureStep tmWord tmFiber20Prefix13 (chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0])))
      (tmFiber20StateAt 13) tmFiber20State13_in_pass2_prefix13
  rw [show tmFiber20Prefix21 = tmFiber20Prefix20 ++ [tmFiber20StateAt 21] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 21) []
    (chainClosureStep tmWord tmFiber20Prefix20 (chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0])))
    (tmFiber20StateAt 13) hparentBefore tmFiber20ReverseSingleStep21
theorem tmFiber20State21_in_pass2_full :
    tmFiber20StateAt 21 ∈ chainClosureStep tmWord tmFiber20DirectStates (chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0])) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix21 ++ [tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28, tmFiber20StateAt 29, tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix21 (chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0])))
    (tmFiber20StateAt 21) tmFiber20State21_in_pass2_prefix21
theorem tmFiber20State29_in_pass2_prefix29 :
    tmFiber20StateAt 29 ∈ chainClosureStep tmWord tmFiber20Prefix29 (chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0])) := by
  have hparentBefore : tmFiber20StateAt 5 ∈
      chainClosureStep tmWord tmFiber20Prefix28 (chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0])) := by
    rw [show tmFiber20Prefix28 = tmFiber20Prefix5 ++ [tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 6, tmFiber20StateAt 7, tmFiber20StateAt 8, tmFiber20StateAt 9, tmFiber20StateAt 10, tmFiber20StateAt 11, tmFiber20StateAt 12, tmFiber20StateAt 13, tmFiber20StateAt 14, tmFiber20StateAt 15, tmFiber20StateAt 16, tmFiber20StateAt 17, tmFiber20StateAt 18, tmFiber20StateAt 19, tmFiber20StateAt 20, tmFiber20StateAt 21, tmFiber20StateAt 22, tmFiber20StateAt 23, tmFiber20StateAt 24, tmFiber20StateAt 25, tmFiber20StateAt 26, tmFiber20StateAt 27, tmFiber20StateAt 28]
      (chainClosureStep tmWord tmFiber20Prefix5 (chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0])))
      (tmFiber20StateAt 5) tmFiber20State5_in_pass2_prefix5
  rw [show tmFiber20Prefix29 = tmFiber20Prefix28 ++ [tmFiber20StateAt 29] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber20StateAt 29) []
    (chainClosureStep tmWord tmFiber20Prefix28 (chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0])))
    (tmFiber20StateAt 5) hparentBefore tmFiber20ReverseSingleStep29
theorem tmFiber20State29_in_pass2_full :
    tmFiber20StateAt 29 ∈ chainClosureStep tmWord tmFiber20DirectStates (chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0])) := by
  rw [show tmFiber20DirectStates = tmFiber20Prefix29 ++ [tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber20StateAt 30, tmFiber20StateAt 31, tmFiber20StateAt 32, tmFiber20StateAt 33, tmFiber20StateAt 34, tmFiber20StateAt 35, tmFiber20StateAt 36, tmFiber20StateAt 37, tmFiber20StateAt 38, tmFiber20StateAt 39, tmFiber20StateAt 40, tmFiber20StateAt 41, tmFiber20StateAt 42, tmFiber20StateAt 43, tmFiber20StateAt 44, tmFiber20StateAt 45, tmFiber20StateAt 46, tmFiber20StateAt 47, tmFiber20StateAt 48, tmFiber20StateAt 49, tmFiber20StateAt 50, tmFiber20StateAt 51, tmFiber20StateAt 52, tmFiber20StateAt 53, tmFiber20StateAt 54, tmFiber20StateAt 55, tmFiber20StateAt 56, tmFiber20StateAt 57, tmFiber20StateAt 58, tmFiber20StateAt 59, tmFiber20StateAt 60, tmFiber20StateAt 61, tmFiber20StateAt 62, tmFiber20StateAt 63]
    (chainClosureStep tmWord tmFiber20Prefix29 (chainClosureStep tmWord tmFiber20DirectStates ([tmFiber20StateAt 0])))
    (tmFiber20StateAt 29) tmFiber20State29_in_pass2_prefix29
theorem tmFiber20FirstPassGrows :
    ((chainClosureStep tmWord tmFiber20DirectStates [tmFiber20StateAt 0]).length ==
      [tmFiber20StateAt 0].length) = false := by
  have hroot : tmFiber20StateAt 0 ∈
      chainClosureStep tmWord tmFiber20DirectStates [tmFiber20StateAt 0] :=
    chainClosureStep_mem_of_seen tmWord tmFiber20DirectStates
      [tmFiber20StateAt 0] (tmFiber20StateAt 0) (by simp)
  have hnew : tmFiber20StateAt 1 ∈
      chainClosureStep tmWord tmFiber20DirectStates [tmFiber20StateAt 0] :=
    tmFiber20State1_in_pass1_full
  simpa using list_length_beq_one_false_of_two_mem
    (chainClosureStep tmWord tmFiber20DirectStates [tmFiber20StateAt 0])
    (tmFiber20StateAt 0) (tmFiber20StateAt 1) hroot hnew (by decide)

theorem tmFiber20State0_in_close_short :
    tmFiber20StateAt 0 ∈ closeChainFiber tmWord tmFiber20DirectStates 0 [tmFiber20StateAt 0] := by
  simp [closeChainFiber]

theorem tmFiber20State1_in_close_short :
    tmFiber20StateAt 1 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 1) tmFiber20State1_in_pass1_full

theorem tmFiber20State2_in_close_short :
    tmFiber20StateAt 2 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 2) tmFiber20State2_in_pass1_full

theorem tmFiber20State3_in_close_short :
    tmFiber20StateAt 3 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 3) tmFiber20State3_in_pass1_full

theorem tmFiber20State4_in_close_short :
    tmFiber20StateAt 4 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 4) tmFiber20State4_in_pass1_full

theorem tmFiber20State6_in_close_short :
    tmFiber20StateAt 6 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 6) tmFiber20State6_in_pass1_full

theorem tmFiber20State7_in_close_short :
    tmFiber20StateAt 7 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 7) tmFiber20State7_in_pass1_full

theorem tmFiber20State8_in_close_short :
    tmFiber20StateAt 8 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 8) tmFiber20State8_in_pass1_full

theorem tmFiber20State9_in_close_short :
    tmFiber20StateAt 9 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 9) tmFiber20State9_in_pass1_full

theorem tmFiber20State10_in_close_short :
    tmFiber20StateAt 10 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 10) tmFiber20State10_in_pass1_full

theorem tmFiber20State11_in_close_short :
    tmFiber20StateAt 11 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 11) tmFiber20State11_in_pass1_full

theorem tmFiber20State12_in_close_short :
    tmFiber20StateAt 12 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 12) tmFiber20State12_in_pass1_full

theorem tmFiber20State14_in_close_short :
    tmFiber20StateAt 14 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 14) tmFiber20State14_in_pass1_full

theorem tmFiber20State15_in_close_short :
    tmFiber20StateAt 15 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 15) tmFiber20State15_in_pass1_full

theorem tmFiber20State16_in_close_short :
    tmFiber20StateAt 16 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 16) tmFiber20State16_in_pass1_full

theorem tmFiber20State17_in_close_short :
    tmFiber20StateAt 17 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 17) tmFiber20State17_in_pass1_full

theorem tmFiber20State18_in_close_short :
    tmFiber20StateAt 18 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 18) tmFiber20State18_in_pass1_full

theorem tmFiber20State19_in_close_short :
    tmFiber20StateAt 19 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 19) tmFiber20State19_in_pass1_full

theorem tmFiber20State20_in_close_short :
    tmFiber20StateAt 20 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 20) tmFiber20State20_in_pass1_full

theorem tmFiber20State22_in_close_short :
    tmFiber20StateAt 22 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 22) tmFiber20State22_in_pass1_full

theorem tmFiber20State23_in_close_short :
    tmFiber20StateAt 23 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 23) tmFiber20State23_in_pass1_full

theorem tmFiber20State24_in_close_short :
    tmFiber20StateAt 24 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 24) tmFiber20State24_in_pass1_full

theorem tmFiber20State25_in_close_short :
    tmFiber20StateAt 25 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 25) tmFiber20State25_in_pass1_full

theorem tmFiber20State26_in_close_short :
    tmFiber20StateAt 26 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 26) tmFiber20State26_in_pass1_full

theorem tmFiber20State27_in_close_short :
    tmFiber20StateAt 27 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 27) tmFiber20State27_in_pass1_full

theorem tmFiber20State28_in_close_short :
    tmFiber20StateAt 28 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 28) tmFiber20State28_in_pass1_full

theorem tmFiber20State30_in_close_short :
    tmFiber20StateAt 30 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 30) tmFiber20State30_in_pass1_full

theorem tmFiber20State31_in_close_short :
    tmFiber20StateAt 31 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 31) tmFiber20State31_in_pass1_full

theorem tmFiber20State32_in_close_short :
    tmFiber20StateAt 32 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 32) tmFiber20State32_in_pass1_full

theorem tmFiber20State33_in_close_short :
    tmFiber20StateAt 33 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 33) tmFiber20State33_in_pass1_full

theorem tmFiber20State34_in_close_short :
    tmFiber20StateAt 34 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 34) tmFiber20State34_in_pass1_full

theorem tmFiber20State35_in_close_short :
    tmFiber20StateAt 35 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 35) tmFiber20State35_in_pass1_full

theorem tmFiber20State36_in_close_short :
    tmFiber20StateAt 36 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 36) tmFiber20State36_in_pass1_full

theorem tmFiber20State37_in_close_short :
    tmFiber20StateAt 37 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 37) tmFiber20State37_in_pass1_full

theorem tmFiber20State38_in_close_short :
    tmFiber20StateAt 38 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 38) tmFiber20State38_in_pass1_full

theorem tmFiber20State39_in_close_short :
    tmFiber20StateAt 39 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 39) tmFiber20State39_in_pass1_full

theorem tmFiber20State40_in_close_short :
    tmFiber20StateAt 40 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 40) tmFiber20State40_in_pass1_full

theorem tmFiber20State41_in_close_short :
    tmFiber20StateAt 41 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 41) tmFiber20State41_in_pass1_full

theorem tmFiber20State42_in_close_short :
    tmFiber20StateAt 42 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 42) tmFiber20State42_in_pass1_full

theorem tmFiber20State43_in_close_short :
    tmFiber20StateAt 43 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 43) tmFiber20State43_in_pass1_full

theorem tmFiber20State44_in_close_short :
    tmFiber20StateAt 44 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 44) tmFiber20State44_in_pass1_full

theorem tmFiber20State45_in_close_short :
    tmFiber20StateAt 45 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 45) tmFiber20State45_in_pass1_full

theorem tmFiber20State46_in_close_short :
    tmFiber20StateAt 46 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 46) tmFiber20State46_in_pass1_full

theorem tmFiber20State47_in_close_short :
    tmFiber20StateAt 47 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 47) tmFiber20State47_in_pass1_full

theorem tmFiber20State48_in_close_short :
    tmFiber20StateAt 48 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 48) tmFiber20State48_in_pass1_full

theorem tmFiber20State49_in_close_short :
    tmFiber20StateAt 49 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 49) tmFiber20State49_in_pass1_full

theorem tmFiber20State50_in_close_short :
    tmFiber20StateAt 50 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 50) tmFiber20State50_in_pass1_full

theorem tmFiber20State51_in_close_short :
    tmFiber20StateAt 51 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 51) tmFiber20State51_in_pass1_full

theorem tmFiber20State52_in_close_short :
    tmFiber20StateAt 52 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 52) tmFiber20State52_in_pass1_full

theorem tmFiber20State53_in_close_short :
    tmFiber20StateAt 53 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 53) tmFiber20State53_in_pass1_full

theorem tmFiber20State54_in_close_short :
    tmFiber20StateAt 54 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 54) tmFiber20State54_in_pass1_full

theorem tmFiber20State55_in_close_short :
    tmFiber20StateAt 55 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 55) tmFiber20State55_in_pass1_full

theorem tmFiber20State56_in_close_short :
    tmFiber20StateAt 56 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 56) tmFiber20State56_in_pass1_full

theorem tmFiber20State57_in_close_short :
    tmFiber20StateAt 57 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 57) tmFiber20State57_in_pass1_full

theorem tmFiber20State58_in_close_short :
    tmFiber20StateAt 58 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 58) tmFiber20State58_in_pass1_full

theorem tmFiber20State59_in_close_short :
    tmFiber20StateAt 59 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 59) tmFiber20State59_in_pass1_full

theorem tmFiber20State60_in_close_short :
    tmFiber20StateAt 60 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 60) tmFiber20State60_in_pass1_full

theorem tmFiber20State61_in_close_short :
    tmFiber20StateAt 61 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 61) tmFiber20State61_in_pass1_full

theorem tmFiber20State62_in_close_short :
    tmFiber20StateAt 62 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 62) tmFiber20State62_in_pass1_full

theorem tmFiber20State63_in_close_short :
    tmFiber20StateAt 63 ∈ closeChainFiber tmWord tmFiber20DirectStates 1 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 63) tmFiber20State63_in_pass1_full

theorem tmFiber20State5_in_close_short :
    tmFiber20StateAt 5 ∈ closeChainFiber tmWord tmFiber20DirectStates 2 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 5) tmFiber20FirstPassGrows
    tmFiber20State5_in_pass2_full

theorem tmFiber20State13_in_close_short :
    tmFiber20StateAt 13 ∈ closeChainFiber tmWord tmFiber20DirectStates 2 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 13) tmFiber20FirstPassGrows
    tmFiber20State13_in_pass2_full

theorem tmFiber20State21_in_close_short :
    tmFiber20StateAt 21 ∈ closeChainFiber tmWord tmFiber20DirectStates 2 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 21) tmFiber20FirstPassGrows
    tmFiber20State21_in_pass2_full

theorem tmFiber20State29_in_close_short :
    tmFiber20StateAt 29 ∈ closeChainFiber tmWord tmFiber20DirectStates 2 [tmFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber20DirectStates 0
    [tmFiber20StateAt 0] (tmFiber20StateAt 29) tmFiber20FirstPassGrows
    tmFiber20State29_in_pass2_full

theorem tmFiber20State0_in_close :
    tmFiber20StateAt 0 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 0 ∈ closeChainFiber tmWord tmFiber20DirectStates (0 + 64) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 0 64
    [tmFiber20StateAt 0] (tmFiber20StateAt 0) tmFiber20State0_in_close_short

theorem tmFiber20State1_in_close :
    tmFiber20StateAt 1 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 1 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 1) tmFiber20State1_in_close_short

theorem tmFiber20State2_in_close :
    tmFiber20StateAt 2 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 2 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 2) tmFiber20State2_in_close_short

theorem tmFiber20State3_in_close :
    tmFiber20StateAt 3 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 3 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 3) tmFiber20State3_in_close_short

theorem tmFiber20State4_in_close :
    tmFiber20StateAt 4 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 4 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 4) tmFiber20State4_in_close_short

theorem tmFiber20State5_in_close :
    tmFiber20StateAt 5 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 5 ∈ closeChainFiber tmWord tmFiber20DirectStates (2 + 62) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 2 62
    [tmFiber20StateAt 0] (tmFiber20StateAt 5) tmFiber20State5_in_close_short

theorem tmFiber20State6_in_close :
    tmFiber20StateAt 6 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 6 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 6) tmFiber20State6_in_close_short

theorem tmFiber20State7_in_close :
    tmFiber20StateAt 7 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 7 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 7) tmFiber20State7_in_close_short

theorem tmFiber20State8_in_close :
    tmFiber20StateAt 8 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 8 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 8) tmFiber20State8_in_close_short

theorem tmFiber20State9_in_close :
    tmFiber20StateAt 9 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 9 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 9) tmFiber20State9_in_close_short

theorem tmFiber20State10_in_close :
    tmFiber20StateAt 10 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 10 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 10) tmFiber20State10_in_close_short

theorem tmFiber20State11_in_close :
    tmFiber20StateAt 11 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 11 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 11) tmFiber20State11_in_close_short

theorem tmFiber20State12_in_close :
    tmFiber20StateAt 12 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 12 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 12) tmFiber20State12_in_close_short

theorem tmFiber20State13_in_close :
    tmFiber20StateAt 13 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 13 ∈ closeChainFiber tmWord tmFiber20DirectStates (2 + 62) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 2 62
    [tmFiber20StateAt 0] (tmFiber20StateAt 13) tmFiber20State13_in_close_short

theorem tmFiber20State14_in_close :
    tmFiber20StateAt 14 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 14 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 14) tmFiber20State14_in_close_short

theorem tmFiber20State15_in_close :
    tmFiber20StateAt 15 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 15 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 15) tmFiber20State15_in_close_short

theorem tmFiber20State16_in_close :
    tmFiber20StateAt 16 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 16 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 16) tmFiber20State16_in_close_short

theorem tmFiber20State17_in_close :
    tmFiber20StateAt 17 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 17 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 17) tmFiber20State17_in_close_short

theorem tmFiber20State18_in_close :
    tmFiber20StateAt 18 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 18 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 18) tmFiber20State18_in_close_short

theorem tmFiber20State19_in_close :
    tmFiber20StateAt 19 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 19 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 19) tmFiber20State19_in_close_short

theorem tmFiber20State20_in_close :
    tmFiber20StateAt 20 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 20 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 20) tmFiber20State20_in_close_short

theorem tmFiber20State21_in_close :
    tmFiber20StateAt 21 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 21 ∈ closeChainFiber tmWord tmFiber20DirectStates (2 + 62) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 2 62
    [tmFiber20StateAt 0] (tmFiber20StateAt 21) tmFiber20State21_in_close_short

theorem tmFiber20State22_in_close :
    tmFiber20StateAt 22 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 22 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 22) tmFiber20State22_in_close_short

theorem tmFiber20State23_in_close :
    tmFiber20StateAt 23 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 23 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 23) tmFiber20State23_in_close_short

theorem tmFiber20State24_in_close :
    tmFiber20StateAt 24 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 24 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 24) tmFiber20State24_in_close_short

theorem tmFiber20State25_in_close :
    tmFiber20StateAt 25 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 25 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 25) tmFiber20State25_in_close_short

theorem tmFiber20State26_in_close :
    tmFiber20StateAt 26 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 26 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 26) tmFiber20State26_in_close_short

theorem tmFiber20State27_in_close :
    tmFiber20StateAt 27 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 27 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 27) tmFiber20State27_in_close_short

theorem tmFiber20State28_in_close :
    tmFiber20StateAt 28 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 28 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 28) tmFiber20State28_in_close_short

theorem tmFiber20State29_in_close :
    tmFiber20StateAt 29 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 29 ∈ closeChainFiber tmWord tmFiber20DirectStates (2 + 62) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 2 62
    [tmFiber20StateAt 0] (tmFiber20StateAt 29) tmFiber20State29_in_close_short

theorem tmFiber20State30_in_close :
    tmFiber20StateAt 30 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 30 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 30) tmFiber20State30_in_close_short

theorem tmFiber20State31_in_close :
    tmFiber20StateAt 31 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 31 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 31) tmFiber20State31_in_close_short

theorem tmFiber20State32_in_close :
    tmFiber20StateAt 32 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 32 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 32) tmFiber20State32_in_close_short

theorem tmFiber20State33_in_close :
    tmFiber20StateAt 33 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 33 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 33) tmFiber20State33_in_close_short

theorem tmFiber20State34_in_close :
    tmFiber20StateAt 34 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 34 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 34) tmFiber20State34_in_close_short

theorem tmFiber20State35_in_close :
    tmFiber20StateAt 35 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 35 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 35) tmFiber20State35_in_close_short

theorem tmFiber20State36_in_close :
    tmFiber20StateAt 36 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 36 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 36) tmFiber20State36_in_close_short

theorem tmFiber20State37_in_close :
    tmFiber20StateAt 37 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 37 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 37) tmFiber20State37_in_close_short

theorem tmFiber20State38_in_close :
    tmFiber20StateAt 38 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 38 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 38) tmFiber20State38_in_close_short

theorem tmFiber20State39_in_close :
    tmFiber20StateAt 39 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 39 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 39) tmFiber20State39_in_close_short

theorem tmFiber20State40_in_close :
    tmFiber20StateAt 40 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 40 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 40) tmFiber20State40_in_close_short

theorem tmFiber20State41_in_close :
    tmFiber20StateAt 41 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 41 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 41) tmFiber20State41_in_close_short

theorem tmFiber20State42_in_close :
    tmFiber20StateAt 42 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 42 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 42) tmFiber20State42_in_close_short

theorem tmFiber20State43_in_close :
    tmFiber20StateAt 43 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 43 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 43) tmFiber20State43_in_close_short

theorem tmFiber20State44_in_close :
    tmFiber20StateAt 44 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 44 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 44) tmFiber20State44_in_close_short

theorem tmFiber20State45_in_close :
    tmFiber20StateAt 45 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 45 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 45) tmFiber20State45_in_close_short

theorem tmFiber20State46_in_close :
    tmFiber20StateAt 46 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 46 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 46) tmFiber20State46_in_close_short

theorem tmFiber20State47_in_close :
    tmFiber20StateAt 47 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 47 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 47) tmFiber20State47_in_close_short

theorem tmFiber20State48_in_close :
    tmFiber20StateAt 48 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 48 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 48) tmFiber20State48_in_close_short

theorem tmFiber20State49_in_close :
    tmFiber20StateAt 49 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 49 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 49) tmFiber20State49_in_close_short

theorem tmFiber20State50_in_close :
    tmFiber20StateAt 50 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 50 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 50) tmFiber20State50_in_close_short

theorem tmFiber20State51_in_close :
    tmFiber20StateAt 51 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 51 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 51) tmFiber20State51_in_close_short

theorem tmFiber20State52_in_close :
    tmFiber20StateAt 52 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 52 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 52) tmFiber20State52_in_close_short

theorem tmFiber20State53_in_close :
    tmFiber20StateAt 53 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 53 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 53) tmFiber20State53_in_close_short

theorem tmFiber20State54_in_close :
    tmFiber20StateAt 54 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 54 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 54) tmFiber20State54_in_close_short

theorem tmFiber20State55_in_close :
    tmFiber20StateAt 55 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 55 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 55) tmFiber20State55_in_close_short

theorem tmFiber20State56_in_close :
    tmFiber20StateAt 56 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 56 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 56) tmFiber20State56_in_close_short

theorem tmFiber20State57_in_close :
    tmFiber20StateAt 57 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 57 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 57) tmFiber20State57_in_close_short

theorem tmFiber20State58_in_close :
    tmFiber20StateAt 58 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 58 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 58) tmFiber20State58_in_close_short

theorem tmFiber20State59_in_close :
    tmFiber20StateAt 59 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 59 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 59) tmFiber20State59_in_close_short

theorem tmFiber20State60_in_close :
    tmFiber20StateAt 60 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 60 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 60) tmFiber20State60_in_close_short

theorem tmFiber20State61_in_close :
    tmFiber20StateAt 61 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 61 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 61) tmFiber20State61_in_close_short

theorem tmFiber20State62_in_close :
    tmFiber20StateAt 62 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 62 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 62) tmFiber20State62_in_close_short

theorem tmFiber20State63_in_close :
    tmFiber20StateAt 63 ∈ closeChainFiber tmWord tmFiber20DirectStates tmFiber20DirectStates.length [tmFiber20StateAt 0] := by
  change tmFiber20StateAt 63 ∈ closeChainFiber tmWord tmFiber20DirectStates (1 + 63) [tmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber20DirectStates 1 63
    [tmFiber20StateAt 0] (tmFiber20StateAt 63) tmFiber20State63_in_close_short

theorem tmFiber20DirectConnected :
    chainFiberConnected tmWord tmFiber20DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [tmFiber20DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact tmFiber20State0_in_close
  · subst state
    exact tmFiber20State1_in_close
  · subst state
    exact tmFiber20State2_in_close
  · subst state
    exact tmFiber20State3_in_close
  · subst state
    exact tmFiber20State4_in_close
  · subst state
    exact tmFiber20State5_in_close
  · subst state
    exact tmFiber20State6_in_close
  · subst state
    exact tmFiber20State7_in_close
  · subst state
    exact tmFiber20State8_in_close
  · subst state
    exact tmFiber20State9_in_close
  · subst state
    exact tmFiber20State10_in_close
  · subst state
    exact tmFiber20State11_in_close
  · subst state
    exact tmFiber20State12_in_close
  · subst state
    exact tmFiber20State13_in_close
  · subst state
    exact tmFiber20State14_in_close
  · subst state
    exact tmFiber20State15_in_close
  · subst state
    exact tmFiber20State16_in_close
  · subst state
    exact tmFiber20State17_in_close
  · subst state
    exact tmFiber20State18_in_close
  · subst state
    exact tmFiber20State19_in_close
  · subst state
    exact tmFiber20State20_in_close
  · subst state
    exact tmFiber20State21_in_close
  · subst state
    exact tmFiber20State22_in_close
  · subst state
    exact tmFiber20State23_in_close
  · subst state
    exact tmFiber20State24_in_close
  · subst state
    exact tmFiber20State25_in_close
  · subst state
    exact tmFiber20State26_in_close
  · subst state
    exact tmFiber20State27_in_close
  · subst state
    exact tmFiber20State28_in_close
  · subst state
    exact tmFiber20State29_in_close
  · subst state
    exact tmFiber20State30_in_close
  · subst state
    exact tmFiber20State31_in_close
  · subst state
    exact tmFiber20State32_in_close
  · subst state
    exact tmFiber20State33_in_close
  · subst state
    exact tmFiber20State34_in_close
  · subst state
    exact tmFiber20State35_in_close
  · subst state
    exact tmFiber20State36_in_close
  · subst state
    exact tmFiber20State37_in_close
  · subst state
    exact tmFiber20State38_in_close
  · subst state
    exact tmFiber20State39_in_close
  · subst state
    exact tmFiber20State40_in_close
  · subst state
    exact tmFiber20State41_in_close
  · subst state
    exact tmFiber20State42_in_close
  · subst state
    exact tmFiber20State43_in_close
  · subst state
    exact tmFiber20State44_in_close
  · subst state
    exact tmFiber20State45_in_close
  · subst state
    exact tmFiber20State46_in_close
  · subst state
    exact tmFiber20State47_in_close
  · subst state
    exact tmFiber20State48_in_close
  · subst state
    exact tmFiber20State49_in_close
  · subst state
    exact tmFiber20State50_in_close
  · subst state
    exact tmFiber20State51_in_close
  · subst state
    exact tmFiber20State52_in_close
  · subst state
    exact tmFiber20State53_in_close
  · subst state
    exact tmFiber20State54_in_close
  · subst state
    exact tmFiber20State55_in_close
  · subst state
    exact tmFiber20State56_in_close
  · subst state
    exact tmFiber20State57_in_close
  · subst state
    exact tmFiber20State58_in_close
  · subst state
    exact tmFiber20State59_in_close
  · subst state
    exact tmFiber20State60_in_close
  · subst state
    exact tmFiber20State61_in_close
  · subst state
    exact tmFiber20State62_in_close
  · subst state
    exact tmFiber20State63_in_close
  · cases h

end GoertzelLemma818LengthTwoTMLargeFiberBridge

end Mettapedia.GraphTheory.FourColor
