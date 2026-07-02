import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMLargeFiberBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated multi-pass direct closure bridge for `normal,mirror` size-64 fiber 8

This module proves direct connectedness for a generated size-64 fiber
whose parent order needs two closure scans. It is generated from
row-local reverse certificate chunks and keeps Lean on default limits.
-/

namespace GoertzelLemma818LengthTwoTMLargeFiberBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818TauMirrorCertificate
open GoertzelLemma818TauMirrorReverseAudit

def tmFiber8StateAt (i : Nat) : List TauState :=
  directStates (tmFiber8RowAt i).sourceLeft (tmFiber8RowAt i).sourceRight

def tmFiber8DirectStates : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]

def tmFiber8Prefix0 : List (List TauState) :=
  [tmFiber8StateAt 0]

def tmFiber8Prefix1 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1]

def tmFiber8Prefix2 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2]

def tmFiber8Prefix3 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3]

def tmFiber8Prefix4 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4]

def tmFiber8Prefix5 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5]

def tmFiber8Prefix6 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6]

def tmFiber8Prefix7 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7]

def tmFiber8Prefix8 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8]

def tmFiber8Prefix9 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9]

def tmFiber8Prefix10 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10]

def tmFiber8Prefix11 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11]

def tmFiber8Prefix12 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12]

def tmFiber8Prefix13 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13]

def tmFiber8Prefix14 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14]

def tmFiber8Prefix15 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15]

def tmFiber8Prefix16 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16]

def tmFiber8Prefix17 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17]

def tmFiber8Prefix18 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18]

def tmFiber8Prefix19 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19]

def tmFiber8Prefix20 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20]

def tmFiber8Prefix21 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21]

def tmFiber8Prefix22 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22]

def tmFiber8Prefix23 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23]

def tmFiber8Prefix24 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24]

def tmFiber8Prefix25 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25]

def tmFiber8Prefix26 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26]

def tmFiber8Prefix27 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27]

def tmFiber8Prefix28 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28]

def tmFiber8Prefix29 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29]

def tmFiber8Prefix30 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30]

def tmFiber8Prefix31 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31]

def tmFiber8Prefix32 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32]

def tmFiber8Prefix33 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33]

def tmFiber8Prefix34 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34]

def tmFiber8Prefix35 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35]

def tmFiber8Prefix36 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36]

def tmFiber8Prefix37 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37]

def tmFiber8Prefix38 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38]

def tmFiber8Prefix39 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39]

def tmFiber8Prefix40 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40]

def tmFiber8Prefix41 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41]

def tmFiber8Prefix42 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42]

def tmFiber8Prefix43 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43]

def tmFiber8Prefix44 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44]

def tmFiber8Prefix45 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45]

def tmFiber8Prefix46 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46]

def tmFiber8Prefix47 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47]

def tmFiber8Prefix48 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48]

def tmFiber8Prefix49 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49]

def tmFiber8Prefix50 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50]

def tmFiber8Prefix51 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51]

def tmFiber8Prefix52 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52]

def tmFiber8Prefix53 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53]

def tmFiber8Prefix54 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54]

def tmFiber8Prefix55 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55]

def tmFiber8Prefix56 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56]

def tmFiber8Prefix57 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57]

def tmFiber8Prefix58 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58]

def tmFiber8Prefix59 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59]

def tmFiber8Prefix60 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60]

def tmFiber8Prefix61 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61]

def tmFiber8Prefix62 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62]

def tmFiber8Prefix63 : List (List TauState) :=
  [tmFiber8StateAt 0, tmFiber8StateAt 1, tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]

theorem tmFiber8ReverseRow_1_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 1) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk0_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 0) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber8ReverseSingleStep1 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 0) (tmFiber8StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 0) (tmFiber8StateAt 1)
    (tmFiber8RowAt 1).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 1) (by decide) tmFiber8ReverseRow_1_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_2_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 2) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk1_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 2) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber8ReverseSingleStep2 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 0) (tmFiber8StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 0) (tmFiber8StateAt 2)
    (tmFiber8RowAt 2).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 2) (by decide) tmFiber8ReverseRow_2_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_3_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 3) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk1_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 2) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber8ReverseSingleStep3 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 1) (tmFiber8StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 1) (tmFiber8StateAt 3)
    (tmFiber8RowAt 3).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 3) (by decide) tmFiber8ReverseRow_3_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_4_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 4) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk2_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 4) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber8ReverseSingleStep4 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 2) (tmFiber8StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 2) (tmFiber8StateAt 4)
    (tmFiber8RowAt 4).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 4) (by decide) tmFiber8ReverseRow_4_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_5_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 5) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk2_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 4) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber8ReverseSingleStep5 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 7) (tmFiber8StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 7) (tmFiber8StateAt 5)
    (tmFiber8RowAt 5).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 5) (by decide) tmFiber8ReverseRow_5_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_6_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 6) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk3_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 6) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber8ReverseSingleStep6 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 1) (tmFiber8StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 1) (tmFiber8StateAt 6)
    (tmFiber8RowAt 6).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 6) (by decide) tmFiber8ReverseRow_6_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_7_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 7) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk3_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 6) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber8ReverseSingleStep7 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 0) (tmFiber8StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 0) (tmFiber8StateAt 7)
    (tmFiber8RowAt 7).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 7) (by decide) tmFiber8ReverseRow_7_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_8_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 8) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk4_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 8) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber8ReverseSingleStep8 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 0) (tmFiber8StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 0) (tmFiber8StateAt 8)
    (tmFiber8RowAt 8).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 8) (by decide) tmFiber8ReverseRow_8_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_9_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 9) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk4_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 8) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber8ReverseSingleStep9 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 1) (tmFiber8StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 1) (tmFiber8StateAt 9)
    (tmFiber8RowAt 9).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 9) (by decide) tmFiber8ReverseRow_9_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_10_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 10) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk5_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 10) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber8ReverseSingleStep10 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 2) (tmFiber8StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 2) (tmFiber8StateAt 10)
    (tmFiber8RowAt 10).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 10) (by decide) tmFiber8ReverseRow_10_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_11_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 11) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk5_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 10) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber8ReverseSingleStep11 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 3) (tmFiber8StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 3) (tmFiber8StateAt 11)
    (tmFiber8RowAt 11).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 11) (by decide) tmFiber8ReverseRow_11_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_12_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 12) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk6_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 12) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber8ReverseSingleStep12 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 4) (tmFiber8StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 4) (tmFiber8StateAt 12)
    (tmFiber8RowAt 12).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 12) (by decide) tmFiber8ReverseRow_12_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_13_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 13) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk6_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 12) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber8ReverseSingleStep13 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 5) (tmFiber8StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 5) (tmFiber8StateAt 13)
    (tmFiber8RowAt 13).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 13) (by decide) tmFiber8ReverseRow_13_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_14_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 14) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk7_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 14) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber8ReverseSingleStep14 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 6) (tmFiber8StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 6) (tmFiber8StateAt 14)
    (tmFiber8RowAt 14).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 14) (by decide) tmFiber8ReverseRow_14_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_15_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 15) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk7_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 14) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber8ReverseSingleStep15 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 7) (tmFiber8StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 7) (tmFiber8StateAt 15)
    (tmFiber8RowAt 15).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 15) (by decide) tmFiber8ReverseRow_15_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_16_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 16) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk8_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 16) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber8ReverseSingleStep16 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 8) (tmFiber8StateAt 16) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 8) (tmFiber8StateAt 16)
    (tmFiber8RowAt 16).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 16) (by decide) tmFiber8ReverseRow_16_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_17_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 17) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk8_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 16) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber8ReverseSingleStep17 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 9) (tmFiber8StateAt 17) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 9) (tmFiber8StateAt 17)
    (tmFiber8RowAt 17).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 17) (by decide) tmFiber8ReverseRow_17_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_18_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 18) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk9_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 18) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber8ReverseSingleStep18 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 10) (tmFiber8StateAt 18) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 10) (tmFiber8StateAt 18)
    (tmFiber8RowAt 18).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 18) (by decide) tmFiber8ReverseRow_18_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_19_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 19) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk9_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 18) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber8ReverseSingleStep19 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 11) (tmFiber8StateAt 19) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 11) (tmFiber8StateAt 19)
    (tmFiber8RowAt 19).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 19) (by decide) tmFiber8ReverseRow_19_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_20_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 20) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk10_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 20) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber8ReverseSingleStep20 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 12) (tmFiber8StateAt 20) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 12) (tmFiber8StateAt 20)
    (tmFiber8RowAt 20).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 20) (by decide) tmFiber8ReverseRow_20_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_21_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 21) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk10_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 20) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber8ReverseSingleStep21 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 13) (tmFiber8StateAt 21) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 13) (tmFiber8StateAt 21)
    (tmFiber8RowAt 21).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 21) (by decide) tmFiber8ReverseRow_21_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_22_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 22) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk11_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 22) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber8ReverseSingleStep22 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 14) (tmFiber8StateAt 22) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 14) (tmFiber8StateAt 22)
    (tmFiber8RowAt 22).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 22) (by decide) tmFiber8ReverseRow_22_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_23_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 23) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk11_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 22) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber8ReverseSingleStep23 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 15) (tmFiber8StateAt 23) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 15) (tmFiber8StateAt 23)
    (tmFiber8RowAt 23).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 23) (by decide) tmFiber8ReverseRow_23_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_24_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 24) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk12_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 24) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber8ReverseSingleStep24 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 0) (tmFiber8StateAt 24) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 0) (tmFiber8StateAt 24)
    (tmFiber8RowAt 24).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 24) (by decide) tmFiber8ReverseRow_24_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_25_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 25) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk12_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 24) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber8ReverseSingleStep25 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 1) (tmFiber8StateAt 25) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 1) (tmFiber8StateAt 25)
    (tmFiber8RowAt 25).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 25) (by decide) tmFiber8ReverseRow_25_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_26_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 26) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk13_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 26) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber8ReverseSingleStep26 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 2) (tmFiber8StateAt 26) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 2) (tmFiber8StateAt 26)
    (tmFiber8RowAt 26).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 26) (by decide) tmFiber8ReverseRow_26_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_27_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 27) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk13_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 26) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber8ReverseSingleStep27 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 3) (tmFiber8StateAt 27) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 3) (tmFiber8StateAt 27)
    (tmFiber8RowAt 27).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 27) (by decide) tmFiber8ReverseRow_27_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_28_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 28) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk14_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 28) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber8ReverseSingleStep28 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 4) (tmFiber8StateAt 28) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 4) (tmFiber8StateAt 28)
    (tmFiber8RowAt 28).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 28) (by decide) tmFiber8ReverseRow_28_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_29_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 29) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk14_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 28) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber8ReverseSingleStep29 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 5) (tmFiber8StateAt 29) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 5) (tmFiber8StateAt 29)
    (tmFiber8RowAt 29).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 29) (by decide) tmFiber8ReverseRow_29_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_30_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 30) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk15_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 30) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber8ReverseSingleStep30 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 6) (tmFiber8StateAt 30) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 6) (tmFiber8StateAt 30)
    (tmFiber8RowAt 30).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 30) (by decide) tmFiber8ReverseRow_30_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_31_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 31) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk15_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 30) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber8ReverseSingleStep31 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 7) (tmFiber8StateAt 31) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 7) (tmFiber8StateAt 31)
    (tmFiber8RowAt 31).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 31) (by decide) tmFiber8ReverseRow_31_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_32_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 32) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk16_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 32) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber8ReverseSingleStep32 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 0) (tmFiber8StateAt 32) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 0) (tmFiber8StateAt 32)
    (tmFiber8RowAt 32).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 32) (by decide) tmFiber8ReverseRow_32_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_33_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 33) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk16_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 32) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber8ReverseSingleStep33 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 1) (tmFiber8StateAt 33) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 1) (tmFiber8StateAt 33)
    (tmFiber8RowAt 33).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 33) (by decide) tmFiber8ReverseRow_33_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_34_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 34) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk17_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 34) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber8ReverseSingleStep34 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 2) (tmFiber8StateAt 34) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 2) (tmFiber8StateAt 34)
    (tmFiber8RowAt 34).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 34) (by decide) tmFiber8ReverseRow_34_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_35_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 35) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk17_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 34) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber8ReverseSingleStep35 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 3) (tmFiber8StateAt 35) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 3) (tmFiber8StateAt 35)
    (tmFiber8RowAt 35).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 35) (by decide) tmFiber8ReverseRow_35_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_36_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 36) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk18_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 36) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber8ReverseSingleStep36 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 32) (tmFiber8StateAt 36) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 32) (tmFiber8StateAt 36)
    (tmFiber8RowAt 36).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 36) (by decide) tmFiber8ReverseRow_36_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_37_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 37) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk18_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 36) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber8ReverseSingleStep37 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 33) (tmFiber8StateAt 37) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 33) (tmFiber8StateAt 37)
    (tmFiber8RowAt 37).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 37) (by decide) tmFiber8ReverseRow_37_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_38_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 38) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk19_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 38) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber8ReverseSingleStep38 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 6) (tmFiber8StateAt 38) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 6) (tmFiber8StateAt 38)
    (tmFiber8RowAt 38).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 38) (by decide) tmFiber8ReverseRow_38_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_39_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 39) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk19_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 38) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber8ReverseSingleStep39 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 7) (tmFiber8StateAt 39) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 7) (tmFiber8StateAt 39)
    (tmFiber8RowAt 39).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 39) (by decide) tmFiber8ReverseRow_39_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_40_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 40) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk20_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 40) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber8ReverseSingleStep40 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 8) (tmFiber8StateAt 40) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 8) (tmFiber8StateAt 40)
    (tmFiber8RowAt 40).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 40) (by decide) tmFiber8ReverseRow_40_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_41_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 41) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk20_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 40) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber8ReverseSingleStep41 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 9) (tmFiber8StateAt 41) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 9) (tmFiber8StateAt 41)
    (tmFiber8RowAt 41).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 41) (by decide) tmFiber8ReverseRow_41_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_42_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 42) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk21_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 42) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber8ReverseSingleStep42 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 10) (tmFiber8StateAt 42) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 10) (tmFiber8StateAt 42)
    (tmFiber8RowAt 42).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 42) (by decide) tmFiber8ReverseRow_42_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_43_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 43) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk21_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 42) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber8ReverseSingleStep43 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 11) (tmFiber8StateAt 43) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 11) (tmFiber8StateAt 43)
    (tmFiber8RowAt 43).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 43) (by decide) tmFiber8ReverseRow_43_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_44_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 44) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk22_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 44) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber8ReverseSingleStep44 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 40) (tmFiber8StateAt 44) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 40) (tmFiber8StateAt 44)
    (tmFiber8RowAt 44).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 44) (by decide) tmFiber8ReverseRow_44_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_45_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 45) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk22_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 44) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber8ReverseSingleStep45 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 41) (tmFiber8StateAt 45) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 41) (tmFiber8StateAt 45)
    (tmFiber8RowAt 45).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 45) (by decide) tmFiber8ReverseRow_45_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_46_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 46) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk23_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 46) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber8ReverseSingleStep46 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 14) (tmFiber8StateAt 46) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 14) (tmFiber8StateAt 46)
    (tmFiber8RowAt 46).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 46) (by decide) tmFiber8ReverseRow_46_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_47_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 47) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk23_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 46) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber8ReverseSingleStep47 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 15) (tmFiber8StateAt 47) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 15) (tmFiber8StateAt 47)
    (tmFiber8RowAt 47).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 47) (by decide) tmFiber8ReverseRow_47_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_48_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 48) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk24_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 48) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber8ReverseSingleStep48 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 32) (tmFiber8StateAt 48) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 32) (tmFiber8StateAt 48)
    (tmFiber8RowAt 48).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 48) (by decide) tmFiber8ReverseRow_48_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_49_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 49) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk24_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 48) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber8ReverseSingleStep49 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 33) (tmFiber8StateAt 49) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 33) (tmFiber8StateAt 49)
    (tmFiber8RowAt 49).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 49) (by decide) tmFiber8ReverseRow_49_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_50_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 50) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk25_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 50) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber8ReverseSingleStep50 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 34) (tmFiber8StateAt 50) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 34) (tmFiber8StateAt 50)
    (tmFiber8RowAt 50).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 50) (by decide) tmFiber8ReverseRow_50_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_51_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 51) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk25_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 50) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber8ReverseSingleStep51 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 35) (tmFiber8StateAt 51) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 35) (tmFiber8StateAt 51)
    (tmFiber8RowAt 51).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 51) (by decide) tmFiber8ReverseRow_51_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_52_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 52) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk26_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 52) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber8ReverseSingleStep52 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 36) (tmFiber8StateAt 52) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 36) (tmFiber8StateAt 52)
    (tmFiber8RowAt 52).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 52) (by decide) tmFiber8ReverseRow_52_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_53_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 53) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk26_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 52) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber8ReverseSingleStep53 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 37) (tmFiber8StateAt 53) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 37) (tmFiber8StateAt 53)
    (tmFiber8RowAt 53).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 53) (by decide) tmFiber8ReverseRow_53_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_54_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 54) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk27_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 54) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber8ReverseSingleStep54 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 38) (tmFiber8StateAt 54) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 38) (tmFiber8StateAt 54)
    (tmFiber8RowAt 54).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 54) (by decide) tmFiber8ReverseRow_54_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_55_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 55) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk27_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 54) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber8ReverseSingleStep55 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 39) (tmFiber8StateAt 55) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 39) (tmFiber8StateAt 55)
    (tmFiber8RowAt 55).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 55) (by decide) tmFiber8ReverseRow_55_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_56_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 56) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk28_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 56) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber8ReverseSingleStep56 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 24) (tmFiber8StateAt 56) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 24) (tmFiber8StateAt 56)
    (tmFiber8RowAt 56).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 56) (by decide) tmFiber8ReverseRow_56_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_57_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 57) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk28_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 56) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber8ReverseSingleStep57 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 25) (tmFiber8StateAt 57) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 25) (tmFiber8StateAt 57)
    (tmFiber8RowAt 57).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 57) (by decide) tmFiber8ReverseRow_57_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_58_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 58) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk29_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 58) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber8ReverseSingleStep58 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 26) (tmFiber8StateAt 58) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 26) (tmFiber8StateAt 58)
    (tmFiber8RowAt 58).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 58) (by decide) tmFiber8ReverseRow_58_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_59_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 59) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk29_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 58) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber8ReverseSingleStep59 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 27) (tmFiber8StateAt 59) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 27) (tmFiber8StateAt 59)
    (tmFiber8RowAt 59).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 59) (by decide) tmFiber8ReverseRow_59_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_60_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 60) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk30_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 60) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber8ReverseSingleStep60 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 56) (tmFiber8StateAt 60) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 56) (tmFiber8StateAt 60)
    (tmFiber8RowAt 60).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 60) (by decide) tmFiber8ReverseRow_60_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_61_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 61) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk30_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 60) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber8ReverseSingleStep61 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 57) (tmFiber8StateAt 61) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 57) (tmFiber8StateAt 61)
    (tmFiber8RowAt 61).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 61) (by decide) tmFiber8ReverseRow_61_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_62_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 62) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk31_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 62) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber8ReverseSingleStep62 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 30) (tmFiber8StateAt 62) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 30) (tmFiber8StateAt 62)
    (tmFiber8RowAt 62).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 62) (by decide) tmFiber8ReverseRow_62_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8ReverseRow_63_ok :
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 63) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber8Chunk31_ok
  change (tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 62) &&
    tmRowReverseValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber8ReverseSingleStep63 :
    chainSingleKempeStep tmWord (tmFiber8StateAt 31) (tmFiber8StateAt 63) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber8StateAt 31) (tmFiber8StateAt 63)
    (tmFiber8RowAt 63).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber8Key tmFiber8Expected
        (tmFiber8RowAt 63) (by decide) tmFiber8ReverseRow_63_ok
      simpa [tmFiber8StateAt, tmFiber8RowAt, tmFiber8Rows, listGetD, directRow] using h)

theorem tmFiber8State1_in_pass1_prefix1 :
    tmFiber8StateAt 1 ∈ chainClosureStep tmWord tmFiber8Prefix1 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 0 ∈
      chainClosureStep tmWord tmFiber8Prefix0 ([tmFiber8StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber8Prefix0
      ([tmFiber8StateAt 0]) (tmFiber8StateAt 0) (by simp)
  rw [show tmFiber8Prefix1 = tmFiber8Prefix0 ++ [tmFiber8StateAt 1] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 1) []
    (chainClosureStep tmWord tmFiber8Prefix0 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 0) hparentBefore tmFiber8ReverseSingleStep1
theorem tmFiber8State1_in_pass1_full :
    tmFiber8StateAt 1 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix1 ++ [tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix1 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 1) tmFiber8State1_in_pass1_prefix1
theorem tmFiber8State2_in_pass1_prefix2 :
    tmFiber8StateAt 2 ∈ chainClosureStep tmWord tmFiber8Prefix2 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 0 ∈
      chainClosureStep tmWord tmFiber8Prefix1 ([tmFiber8StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber8Prefix1
      ([tmFiber8StateAt 0]) (tmFiber8StateAt 0) (by simp)
  rw [show tmFiber8Prefix2 = tmFiber8Prefix1 ++ [tmFiber8StateAt 2] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 2) []
    (chainClosureStep tmWord tmFiber8Prefix1 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 0) hparentBefore tmFiber8ReverseSingleStep2
theorem tmFiber8State2_in_pass1_full :
    tmFiber8StateAt 2 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix2 ++ [tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix2 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 2) tmFiber8State2_in_pass1_prefix2
theorem tmFiber8State3_in_pass1_prefix3 :
    tmFiber8StateAt 3 ∈ chainClosureStep tmWord tmFiber8Prefix3 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 1 ∈
      chainClosureStep tmWord tmFiber8Prefix2 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix2 = tmFiber8Prefix1 ++ [tmFiber8StateAt 2] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 2]
      (chainClosureStep tmWord tmFiber8Prefix1 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 1) tmFiber8State1_in_pass1_prefix1
  rw [show tmFiber8Prefix3 = tmFiber8Prefix2 ++ [tmFiber8StateAt 3] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 3) []
    (chainClosureStep tmWord tmFiber8Prefix2 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 1) hparentBefore tmFiber8ReverseSingleStep3
theorem tmFiber8State3_in_pass1_full :
    tmFiber8StateAt 3 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix3 ++ [tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix3 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 3) tmFiber8State3_in_pass1_prefix3
theorem tmFiber8State4_in_pass1_prefix4 :
    tmFiber8StateAt 4 ∈ chainClosureStep tmWord tmFiber8Prefix4 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 2 ∈
      chainClosureStep tmWord tmFiber8Prefix3 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix3 = tmFiber8Prefix2 ++ [tmFiber8StateAt 3] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 3]
      (chainClosureStep tmWord tmFiber8Prefix2 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 2) tmFiber8State2_in_pass1_prefix2
  rw [show tmFiber8Prefix4 = tmFiber8Prefix3 ++ [tmFiber8StateAt 4] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 4) []
    (chainClosureStep tmWord tmFiber8Prefix3 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 2) hparentBefore tmFiber8ReverseSingleStep4
theorem tmFiber8State4_in_pass1_full :
    tmFiber8StateAt 4 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix4 ++ [tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix4 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 4) tmFiber8State4_in_pass1_prefix4
theorem tmFiber8State6_in_pass1_prefix6 :
    tmFiber8StateAt 6 ∈ chainClosureStep tmWord tmFiber8Prefix6 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 1 ∈
      chainClosureStep tmWord tmFiber8Prefix5 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix5 = tmFiber8Prefix1 ++ [tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5]
      (chainClosureStep tmWord tmFiber8Prefix1 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 1) tmFiber8State1_in_pass1_prefix1
  rw [show tmFiber8Prefix6 = tmFiber8Prefix5 ++ [tmFiber8StateAt 6] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 6) []
    (chainClosureStep tmWord tmFiber8Prefix5 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 1) hparentBefore tmFiber8ReverseSingleStep6
theorem tmFiber8State6_in_pass1_full :
    tmFiber8StateAt 6 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix6 ++ [tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix6 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 6) tmFiber8State6_in_pass1_prefix6
theorem tmFiber8State7_in_pass1_prefix7 :
    tmFiber8StateAt 7 ∈ chainClosureStep tmWord tmFiber8Prefix7 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 0 ∈
      chainClosureStep tmWord tmFiber8Prefix6 ([tmFiber8StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber8Prefix6
      ([tmFiber8StateAt 0]) (tmFiber8StateAt 0) (by simp)
  rw [show tmFiber8Prefix7 = tmFiber8Prefix6 ++ [tmFiber8StateAt 7] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 7) []
    (chainClosureStep tmWord tmFiber8Prefix6 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 0) hparentBefore tmFiber8ReverseSingleStep7
theorem tmFiber8State7_in_pass1_full :
    tmFiber8StateAt 7 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix7 ++ [tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix7 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 7) tmFiber8State7_in_pass1_prefix7
theorem tmFiber8State8_in_pass1_prefix8 :
    tmFiber8StateAt 8 ∈ chainClosureStep tmWord tmFiber8Prefix8 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 0 ∈
      chainClosureStep tmWord tmFiber8Prefix7 ([tmFiber8StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber8Prefix7
      ([tmFiber8StateAt 0]) (tmFiber8StateAt 0) (by simp)
  rw [show tmFiber8Prefix8 = tmFiber8Prefix7 ++ [tmFiber8StateAt 8] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 8) []
    (chainClosureStep tmWord tmFiber8Prefix7 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 0) hparentBefore tmFiber8ReverseSingleStep8
theorem tmFiber8State8_in_pass1_full :
    tmFiber8StateAt 8 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix8 ++ [tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix8 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 8) tmFiber8State8_in_pass1_prefix8
theorem tmFiber8State9_in_pass1_prefix9 :
    tmFiber8StateAt 9 ∈ chainClosureStep tmWord tmFiber8Prefix9 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 1 ∈
      chainClosureStep tmWord tmFiber8Prefix8 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix8 = tmFiber8Prefix1 ++ [tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8]
      (chainClosureStep tmWord tmFiber8Prefix1 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 1) tmFiber8State1_in_pass1_prefix1
  rw [show tmFiber8Prefix9 = tmFiber8Prefix8 ++ [tmFiber8StateAt 9] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 9) []
    (chainClosureStep tmWord tmFiber8Prefix8 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 1) hparentBefore tmFiber8ReverseSingleStep9
theorem tmFiber8State9_in_pass1_full :
    tmFiber8StateAt 9 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix9 ++ [tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix9 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 9) tmFiber8State9_in_pass1_prefix9
theorem tmFiber8State10_in_pass1_prefix10 :
    tmFiber8StateAt 10 ∈ chainClosureStep tmWord tmFiber8Prefix10 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 2 ∈
      chainClosureStep tmWord tmFiber8Prefix9 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix9 = tmFiber8Prefix2 ++ [tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9]
      (chainClosureStep tmWord tmFiber8Prefix2 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 2) tmFiber8State2_in_pass1_prefix2
  rw [show tmFiber8Prefix10 = tmFiber8Prefix9 ++ [tmFiber8StateAt 10] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 10) []
    (chainClosureStep tmWord tmFiber8Prefix9 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 2) hparentBefore tmFiber8ReverseSingleStep10
theorem tmFiber8State10_in_pass1_full :
    tmFiber8StateAt 10 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix10 ++ [tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix10 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 10) tmFiber8State10_in_pass1_prefix10
theorem tmFiber8State11_in_pass1_prefix11 :
    tmFiber8StateAt 11 ∈ chainClosureStep tmWord tmFiber8Prefix11 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 3 ∈
      chainClosureStep tmWord tmFiber8Prefix10 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix10 = tmFiber8Prefix3 ++ [tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10]
      (chainClosureStep tmWord tmFiber8Prefix3 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 3) tmFiber8State3_in_pass1_prefix3
  rw [show tmFiber8Prefix11 = tmFiber8Prefix10 ++ [tmFiber8StateAt 11] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 11) []
    (chainClosureStep tmWord tmFiber8Prefix10 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 3) hparentBefore tmFiber8ReverseSingleStep11
theorem tmFiber8State11_in_pass1_full :
    tmFiber8StateAt 11 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix11 ++ [tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix11 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 11) tmFiber8State11_in_pass1_prefix11
theorem tmFiber8State12_in_pass1_prefix12 :
    tmFiber8StateAt 12 ∈ chainClosureStep tmWord tmFiber8Prefix12 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 4 ∈
      chainClosureStep tmWord tmFiber8Prefix11 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix11 = tmFiber8Prefix4 ++ [tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11]
      (chainClosureStep tmWord tmFiber8Prefix4 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 4) tmFiber8State4_in_pass1_prefix4
  rw [show tmFiber8Prefix12 = tmFiber8Prefix11 ++ [tmFiber8StateAt 12] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 12) []
    (chainClosureStep tmWord tmFiber8Prefix11 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 4) hparentBefore tmFiber8ReverseSingleStep12
theorem tmFiber8State12_in_pass1_full :
    tmFiber8StateAt 12 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix12 ++ [tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix12 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 12) tmFiber8State12_in_pass1_prefix12
theorem tmFiber8State14_in_pass1_prefix14 :
    tmFiber8StateAt 14 ∈ chainClosureStep tmWord tmFiber8Prefix14 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 6 ∈
      chainClosureStep tmWord tmFiber8Prefix13 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix13 = tmFiber8Prefix6 ++ [tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13]
      (chainClosureStep tmWord tmFiber8Prefix6 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 6) tmFiber8State6_in_pass1_prefix6
  rw [show tmFiber8Prefix14 = tmFiber8Prefix13 ++ [tmFiber8StateAt 14] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 14) []
    (chainClosureStep tmWord tmFiber8Prefix13 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 6) hparentBefore tmFiber8ReverseSingleStep14
theorem tmFiber8State14_in_pass1_full :
    tmFiber8StateAt 14 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix14 ++ [tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix14 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 14) tmFiber8State14_in_pass1_prefix14
theorem tmFiber8State15_in_pass1_prefix15 :
    tmFiber8StateAt 15 ∈ chainClosureStep tmWord tmFiber8Prefix15 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 7 ∈
      chainClosureStep tmWord tmFiber8Prefix14 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix14 = tmFiber8Prefix7 ++ [tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14]
      (chainClosureStep tmWord tmFiber8Prefix7 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 7) tmFiber8State7_in_pass1_prefix7
  rw [show tmFiber8Prefix15 = tmFiber8Prefix14 ++ [tmFiber8StateAt 15] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 15) []
    (chainClosureStep tmWord tmFiber8Prefix14 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 7) hparentBefore tmFiber8ReverseSingleStep15
theorem tmFiber8State15_in_pass1_full :
    tmFiber8StateAt 15 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix15 ++ [tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix15 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 15) tmFiber8State15_in_pass1_prefix15
theorem tmFiber8State16_in_pass1_prefix16 :
    tmFiber8StateAt 16 ∈ chainClosureStep tmWord tmFiber8Prefix16 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 8 ∈
      chainClosureStep tmWord tmFiber8Prefix15 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix15 = tmFiber8Prefix8 ++ [tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15]
      (chainClosureStep tmWord tmFiber8Prefix8 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 8) tmFiber8State8_in_pass1_prefix8
  rw [show tmFiber8Prefix16 = tmFiber8Prefix15 ++ [tmFiber8StateAt 16] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 16) []
    (chainClosureStep tmWord tmFiber8Prefix15 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 8) hparentBefore tmFiber8ReverseSingleStep16
theorem tmFiber8State16_in_pass1_full :
    tmFiber8StateAt 16 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix16 ++ [tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix16 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 16) tmFiber8State16_in_pass1_prefix16
theorem tmFiber8State17_in_pass1_prefix17 :
    tmFiber8StateAt 17 ∈ chainClosureStep tmWord tmFiber8Prefix17 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 9 ∈
      chainClosureStep tmWord tmFiber8Prefix16 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix16 = tmFiber8Prefix9 ++ [tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16]
      (chainClosureStep tmWord tmFiber8Prefix9 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 9) tmFiber8State9_in_pass1_prefix9
  rw [show tmFiber8Prefix17 = tmFiber8Prefix16 ++ [tmFiber8StateAt 17] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 17) []
    (chainClosureStep tmWord tmFiber8Prefix16 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 9) hparentBefore tmFiber8ReverseSingleStep17
theorem tmFiber8State17_in_pass1_full :
    tmFiber8StateAt 17 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix17 ++ [tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix17 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 17) tmFiber8State17_in_pass1_prefix17
theorem tmFiber8State18_in_pass1_prefix18 :
    tmFiber8StateAt 18 ∈ chainClosureStep tmWord tmFiber8Prefix18 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 10 ∈
      chainClosureStep tmWord tmFiber8Prefix17 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix17 = tmFiber8Prefix10 ++ [tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17]
      (chainClosureStep tmWord tmFiber8Prefix10 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 10) tmFiber8State10_in_pass1_prefix10
  rw [show tmFiber8Prefix18 = tmFiber8Prefix17 ++ [tmFiber8StateAt 18] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 18) []
    (chainClosureStep tmWord tmFiber8Prefix17 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 10) hparentBefore tmFiber8ReverseSingleStep18
theorem tmFiber8State18_in_pass1_full :
    tmFiber8StateAt 18 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix18 ++ [tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix18 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 18) tmFiber8State18_in_pass1_prefix18
theorem tmFiber8State19_in_pass1_prefix19 :
    tmFiber8StateAt 19 ∈ chainClosureStep tmWord tmFiber8Prefix19 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 11 ∈
      chainClosureStep tmWord tmFiber8Prefix18 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix18 = tmFiber8Prefix11 ++ [tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18]
      (chainClosureStep tmWord tmFiber8Prefix11 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 11) tmFiber8State11_in_pass1_prefix11
  rw [show tmFiber8Prefix19 = tmFiber8Prefix18 ++ [tmFiber8StateAt 19] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 19) []
    (chainClosureStep tmWord tmFiber8Prefix18 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 11) hparentBefore tmFiber8ReverseSingleStep19
theorem tmFiber8State19_in_pass1_full :
    tmFiber8StateAt 19 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix19 ++ [tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix19 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 19) tmFiber8State19_in_pass1_prefix19
theorem tmFiber8State20_in_pass1_prefix20 :
    tmFiber8StateAt 20 ∈ chainClosureStep tmWord tmFiber8Prefix20 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 12 ∈
      chainClosureStep tmWord tmFiber8Prefix19 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix19 = tmFiber8Prefix12 ++ [tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19]
      (chainClosureStep tmWord tmFiber8Prefix12 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 12) tmFiber8State12_in_pass1_prefix12
  rw [show tmFiber8Prefix20 = tmFiber8Prefix19 ++ [tmFiber8StateAt 20] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 20) []
    (chainClosureStep tmWord tmFiber8Prefix19 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 12) hparentBefore tmFiber8ReverseSingleStep20
theorem tmFiber8State20_in_pass1_full :
    tmFiber8StateAt 20 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix20 ++ [tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix20 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 20) tmFiber8State20_in_pass1_prefix20
theorem tmFiber8State22_in_pass1_prefix22 :
    tmFiber8StateAt 22 ∈ chainClosureStep tmWord tmFiber8Prefix22 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 14 ∈
      chainClosureStep tmWord tmFiber8Prefix21 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix21 = tmFiber8Prefix14 ++ [tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21]
      (chainClosureStep tmWord tmFiber8Prefix14 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 14) tmFiber8State14_in_pass1_prefix14
  rw [show tmFiber8Prefix22 = tmFiber8Prefix21 ++ [tmFiber8StateAt 22] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 22) []
    (chainClosureStep tmWord tmFiber8Prefix21 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 14) hparentBefore tmFiber8ReverseSingleStep22
theorem tmFiber8State22_in_pass1_full :
    tmFiber8StateAt 22 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix22 ++ [tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix22 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 22) tmFiber8State22_in_pass1_prefix22
theorem tmFiber8State23_in_pass1_prefix23 :
    tmFiber8StateAt 23 ∈ chainClosureStep tmWord tmFiber8Prefix23 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 15 ∈
      chainClosureStep tmWord tmFiber8Prefix22 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix22 = tmFiber8Prefix15 ++ [tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22]
      (chainClosureStep tmWord tmFiber8Prefix15 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 15) tmFiber8State15_in_pass1_prefix15
  rw [show tmFiber8Prefix23 = tmFiber8Prefix22 ++ [tmFiber8StateAt 23] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 23) []
    (chainClosureStep tmWord tmFiber8Prefix22 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 15) hparentBefore tmFiber8ReverseSingleStep23
theorem tmFiber8State23_in_pass1_full :
    tmFiber8StateAt 23 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix23 ++ [tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix23 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 23) tmFiber8State23_in_pass1_prefix23
theorem tmFiber8State24_in_pass1_prefix24 :
    tmFiber8StateAt 24 ∈ chainClosureStep tmWord tmFiber8Prefix24 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 0 ∈
      chainClosureStep tmWord tmFiber8Prefix23 ([tmFiber8StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber8Prefix23
      ([tmFiber8StateAt 0]) (tmFiber8StateAt 0) (by simp)
  rw [show tmFiber8Prefix24 = tmFiber8Prefix23 ++ [tmFiber8StateAt 24] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 24) []
    (chainClosureStep tmWord tmFiber8Prefix23 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 0) hparentBefore tmFiber8ReverseSingleStep24
theorem tmFiber8State24_in_pass1_full :
    tmFiber8StateAt 24 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix24 ++ [tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix24 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 24) tmFiber8State24_in_pass1_prefix24
theorem tmFiber8State25_in_pass1_prefix25 :
    tmFiber8StateAt 25 ∈ chainClosureStep tmWord tmFiber8Prefix25 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 1 ∈
      chainClosureStep tmWord tmFiber8Prefix24 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix24 = tmFiber8Prefix1 ++ [tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24]
      (chainClosureStep tmWord tmFiber8Prefix1 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 1) tmFiber8State1_in_pass1_prefix1
  rw [show tmFiber8Prefix25 = tmFiber8Prefix24 ++ [tmFiber8StateAt 25] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 25) []
    (chainClosureStep tmWord tmFiber8Prefix24 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 1) hparentBefore tmFiber8ReverseSingleStep25
theorem tmFiber8State25_in_pass1_full :
    tmFiber8StateAt 25 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix25 ++ [tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix25 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 25) tmFiber8State25_in_pass1_prefix25
theorem tmFiber8State26_in_pass1_prefix26 :
    tmFiber8StateAt 26 ∈ chainClosureStep tmWord tmFiber8Prefix26 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 2 ∈
      chainClosureStep tmWord tmFiber8Prefix25 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix25 = tmFiber8Prefix2 ++ [tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25]
      (chainClosureStep tmWord tmFiber8Prefix2 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 2) tmFiber8State2_in_pass1_prefix2
  rw [show tmFiber8Prefix26 = tmFiber8Prefix25 ++ [tmFiber8StateAt 26] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 26) []
    (chainClosureStep tmWord tmFiber8Prefix25 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 2) hparentBefore tmFiber8ReverseSingleStep26
theorem tmFiber8State26_in_pass1_full :
    tmFiber8StateAt 26 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix26 ++ [tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix26 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 26) tmFiber8State26_in_pass1_prefix26
theorem tmFiber8State27_in_pass1_prefix27 :
    tmFiber8StateAt 27 ∈ chainClosureStep tmWord tmFiber8Prefix27 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 3 ∈
      chainClosureStep tmWord tmFiber8Prefix26 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix26 = tmFiber8Prefix3 ++ [tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26]
      (chainClosureStep tmWord tmFiber8Prefix3 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 3) tmFiber8State3_in_pass1_prefix3
  rw [show tmFiber8Prefix27 = tmFiber8Prefix26 ++ [tmFiber8StateAt 27] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 27) []
    (chainClosureStep tmWord tmFiber8Prefix26 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 3) hparentBefore tmFiber8ReverseSingleStep27
theorem tmFiber8State27_in_pass1_full :
    tmFiber8StateAt 27 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix27 ++ [tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix27 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 27) tmFiber8State27_in_pass1_prefix27
theorem tmFiber8State28_in_pass1_prefix28 :
    tmFiber8StateAt 28 ∈ chainClosureStep tmWord tmFiber8Prefix28 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 4 ∈
      chainClosureStep tmWord tmFiber8Prefix27 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix27 = tmFiber8Prefix4 ++ [tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27]
      (chainClosureStep tmWord tmFiber8Prefix4 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 4) tmFiber8State4_in_pass1_prefix4
  rw [show tmFiber8Prefix28 = tmFiber8Prefix27 ++ [tmFiber8StateAt 28] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 28) []
    (chainClosureStep tmWord tmFiber8Prefix27 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 4) hparentBefore tmFiber8ReverseSingleStep28
theorem tmFiber8State28_in_pass1_full :
    tmFiber8StateAt 28 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix28 ++ [tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix28 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 28) tmFiber8State28_in_pass1_prefix28
theorem tmFiber8State30_in_pass1_prefix30 :
    tmFiber8StateAt 30 ∈ chainClosureStep tmWord tmFiber8Prefix30 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 6 ∈
      chainClosureStep tmWord tmFiber8Prefix29 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix29 = tmFiber8Prefix6 ++ [tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29]
      (chainClosureStep tmWord tmFiber8Prefix6 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 6) tmFiber8State6_in_pass1_prefix6
  rw [show tmFiber8Prefix30 = tmFiber8Prefix29 ++ [tmFiber8StateAt 30] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 30) []
    (chainClosureStep tmWord tmFiber8Prefix29 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 6) hparentBefore tmFiber8ReverseSingleStep30
theorem tmFiber8State30_in_pass1_full :
    tmFiber8StateAt 30 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix30 ++ [tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix30 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 30) tmFiber8State30_in_pass1_prefix30
theorem tmFiber8State31_in_pass1_prefix31 :
    tmFiber8StateAt 31 ∈ chainClosureStep tmWord tmFiber8Prefix31 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 7 ∈
      chainClosureStep tmWord tmFiber8Prefix30 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix30 = tmFiber8Prefix7 ++ [tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30]
      (chainClosureStep tmWord tmFiber8Prefix7 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 7) tmFiber8State7_in_pass1_prefix7
  rw [show tmFiber8Prefix31 = tmFiber8Prefix30 ++ [tmFiber8StateAt 31] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 31) []
    (chainClosureStep tmWord tmFiber8Prefix30 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 7) hparentBefore tmFiber8ReverseSingleStep31
theorem tmFiber8State31_in_pass1_full :
    tmFiber8StateAt 31 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix31 ++ [tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix31 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 31) tmFiber8State31_in_pass1_prefix31
theorem tmFiber8State32_in_pass1_prefix32 :
    tmFiber8StateAt 32 ∈ chainClosureStep tmWord tmFiber8Prefix32 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 0 ∈
      chainClosureStep tmWord tmFiber8Prefix31 ([tmFiber8StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber8Prefix31
      ([tmFiber8StateAt 0]) (tmFiber8StateAt 0) (by simp)
  rw [show tmFiber8Prefix32 = tmFiber8Prefix31 ++ [tmFiber8StateAt 32] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 32) []
    (chainClosureStep tmWord tmFiber8Prefix31 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 0) hparentBefore tmFiber8ReverseSingleStep32
theorem tmFiber8State32_in_pass1_full :
    tmFiber8StateAt 32 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix32 ++ [tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix32 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 32) tmFiber8State32_in_pass1_prefix32
theorem tmFiber8State33_in_pass1_prefix33 :
    tmFiber8StateAt 33 ∈ chainClosureStep tmWord tmFiber8Prefix33 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 1 ∈
      chainClosureStep tmWord tmFiber8Prefix32 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix32 = tmFiber8Prefix1 ++ [tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 2, tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32]
      (chainClosureStep tmWord tmFiber8Prefix1 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 1) tmFiber8State1_in_pass1_prefix1
  rw [show tmFiber8Prefix33 = tmFiber8Prefix32 ++ [tmFiber8StateAt 33] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 33) []
    (chainClosureStep tmWord tmFiber8Prefix32 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 1) hparentBefore tmFiber8ReverseSingleStep33
theorem tmFiber8State33_in_pass1_full :
    tmFiber8StateAt 33 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix33 ++ [tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix33 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 33) tmFiber8State33_in_pass1_prefix33
theorem tmFiber8State34_in_pass1_prefix34 :
    tmFiber8StateAt 34 ∈ chainClosureStep tmWord tmFiber8Prefix34 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 2 ∈
      chainClosureStep tmWord tmFiber8Prefix33 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix33 = tmFiber8Prefix2 ++ [tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 3, tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33]
      (chainClosureStep tmWord tmFiber8Prefix2 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 2) tmFiber8State2_in_pass1_prefix2
  rw [show tmFiber8Prefix34 = tmFiber8Prefix33 ++ [tmFiber8StateAt 34] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 34) []
    (chainClosureStep tmWord tmFiber8Prefix33 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 2) hparentBefore tmFiber8ReverseSingleStep34
theorem tmFiber8State34_in_pass1_full :
    tmFiber8StateAt 34 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix34 ++ [tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix34 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 34) tmFiber8State34_in_pass1_prefix34
theorem tmFiber8State35_in_pass1_prefix35 :
    tmFiber8StateAt 35 ∈ chainClosureStep tmWord tmFiber8Prefix35 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 3 ∈
      chainClosureStep tmWord tmFiber8Prefix34 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix34 = tmFiber8Prefix3 ++ [tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 4, tmFiber8StateAt 5, tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34]
      (chainClosureStep tmWord tmFiber8Prefix3 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 3) tmFiber8State3_in_pass1_prefix3
  rw [show tmFiber8Prefix35 = tmFiber8Prefix34 ++ [tmFiber8StateAt 35] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 35) []
    (chainClosureStep tmWord tmFiber8Prefix34 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 3) hparentBefore tmFiber8ReverseSingleStep35
theorem tmFiber8State35_in_pass1_full :
    tmFiber8StateAt 35 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix35 ++ [tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix35 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 35) tmFiber8State35_in_pass1_prefix35
theorem tmFiber8State36_in_pass1_prefix36 :
    tmFiber8StateAt 36 ∈ chainClosureStep tmWord tmFiber8Prefix36 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 32 ∈
      chainClosureStep tmWord tmFiber8Prefix35 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix35 = tmFiber8Prefix32 ++ [tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35]
      (chainClosureStep tmWord tmFiber8Prefix32 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 32) tmFiber8State32_in_pass1_prefix32
  rw [show tmFiber8Prefix36 = tmFiber8Prefix35 ++ [tmFiber8StateAt 36] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 36) []
    (chainClosureStep tmWord tmFiber8Prefix35 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 32) hparentBefore tmFiber8ReverseSingleStep36
theorem tmFiber8State36_in_pass1_full :
    tmFiber8StateAt 36 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix36 ++ [tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix36 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 36) tmFiber8State36_in_pass1_prefix36
theorem tmFiber8State37_in_pass1_prefix37 :
    tmFiber8StateAt 37 ∈ chainClosureStep tmWord tmFiber8Prefix37 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 33 ∈
      chainClosureStep tmWord tmFiber8Prefix36 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix36 = tmFiber8Prefix33 ++ [tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36]
      (chainClosureStep tmWord tmFiber8Prefix33 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 33) tmFiber8State33_in_pass1_prefix33
  rw [show tmFiber8Prefix37 = tmFiber8Prefix36 ++ [tmFiber8StateAt 37] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 37) []
    (chainClosureStep tmWord tmFiber8Prefix36 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 33) hparentBefore tmFiber8ReverseSingleStep37
theorem tmFiber8State37_in_pass1_full :
    tmFiber8StateAt 37 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix37 ++ [tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix37 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 37) tmFiber8State37_in_pass1_prefix37
theorem tmFiber8State38_in_pass1_prefix38 :
    tmFiber8StateAt 38 ∈ chainClosureStep tmWord tmFiber8Prefix38 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 6 ∈
      chainClosureStep tmWord tmFiber8Prefix37 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix37 = tmFiber8Prefix6 ++ [tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37]
      (chainClosureStep tmWord tmFiber8Prefix6 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 6) tmFiber8State6_in_pass1_prefix6
  rw [show tmFiber8Prefix38 = tmFiber8Prefix37 ++ [tmFiber8StateAt 38] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 38) []
    (chainClosureStep tmWord tmFiber8Prefix37 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 6) hparentBefore tmFiber8ReverseSingleStep38
theorem tmFiber8State38_in_pass1_full :
    tmFiber8StateAt 38 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix38 ++ [tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix38 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 38) tmFiber8State38_in_pass1_prefix38
theorem tmFiber8State39_in_pass1_prefix39 :
    tmFiber8StateAt 39 ∈ chainClosureStep tmWord tmFiber8Prefix39 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 7 ∈
      chainClosureStep tmWord tmFiber8Prefix38 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix38 = tmFiber8Prefix7 ++ [tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38]
      (chainClosureStep tmWord tmFiber8Prefix7 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 7) tmFiber8State7_in_pass1_prefix7
  rw [show tmFiber8Prefix39 = tmFiber8Prefix38 ++ [tmFiber8StateAt 39] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 39) []
    (chainClosureStep tmWord tmFiber8Prefix38 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 7) hparentBefore tmFiber8ReverseSingleStep39
theorem tmFiber8State39_in_pass1_full :
    tmFiber8StateAt 39 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix39 ++ [tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix39 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 39) tmFiber8State39_in_pass1_prefix39
theorem tmFiber8State40_in_pass1_prefix40 :
    tmFiber8StateAt 40 ∈ chainClosureStep tmWord tmFiber8Prefix40 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 8 ∈
      chainClosureStep tmWord tmFiber8Prefix39 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix39 = tmFiber8Prefix8 ++ [tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39]
      (chainClosureStep tmWord tmFiber8Prefix8 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 8) tmFiber8State8_in_pass1_prefix8
  rw [show tmFiber8Prefix40 = tmFiber8Prefix39 ++ [tmFiber8StateAt 40] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 40) []
    (chainClosureStep tmWord tmFiber8Prefix39 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 8) hparentBefore tmFiber8ReverseSingleStep40
theorem tmFiber8State40_in_pass1_full :
    tmFiber8StateAt 40 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix40 ++ [tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix40 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 40) tmFiber8State40_in_pass1_prefix40
theorem tmFiber8State41_in_pass1_prefix41 :
    tmFiber8StateAt 41 ∈ chainClosureStep tmWord tmFiber8Prefix41 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 9 ∈
      chainClosureStep tmWord tmFiber8Prefix40 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix40 = tmFiber8Prefix9 ++ [tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40]
      (chainClosureStep tmWord tmFiber8Prefix9 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 9) tmFiber8State9_in_pass1_prefix9
  rw [show tmFiber8Prefix41 = tmFiber8Prefix40 ++ [tmFiber8StateAt 41] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 41) []
    (chainClosureStep tmWord tmFiber8Prefix40 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 9) hparentBefore tmFiber8ReverseSingleStep41
theorem tmFiber8State41_in_pass1_full :
    tmFiber8StateAt 41 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix41 ++ [tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix41 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 41) tmFiber8State41_in_pass1_prefix41
theorem tmFiber8State42_in_pass1_prefix42 :
    tmFiber8StateAt 42 ∈ chainClosureStep tmWord tmFiber8Prefix42 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 10 ∈
      chainClosureStep tmWord tmFiber8Prefix41 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix41 = tmFiber8Prefix10 ++ [tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41]
      (chainClosureStep tmWord tmFiber8Prefix10 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 10) tmFiber8State10_in_pass1_prefix10
  rw [show tmFiber8Prefix42 = tmFiber8Prefix41 ++ [tmFiber8StateAt 42] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 42) []
    (chainClosureStep tmWord tmFiber8Prefix41 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 10) hparentBefore tmFiber8ReverseSingleStep42
theorem tmFiber8State42_in_pass1_full :
    tmFiber8StateAt 42 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix42 ++ [tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix42 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 42) tmFiber8State42_in_pass1_prefix42
theorem tmFiber8State43_in_pass1_prefix43 :
    tmFiber8StateAt 43 ∈ chainClosureStep tmWord tmFiber8Prefix43 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 11 ∈
      chainClosureStep tmWord tmFiber8Prefix42 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix42 = tmFiber8Prefix11 ++ [tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42]
      (chainClosureStep tmWord tmFiber8Prefix11 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 11) tmFiber8State11_in_pass1_prefix11
  rw [show tmFiber8Prefix43 = tmFiber8Prefix42 ++ [tmFiber8StateAt 43] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 43) []
    (chainClosureStep tmWord tmFiber8Prefix42 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 11) hparentBefore tmFiber8ReverseSingleStep43
theorem tmFiber8State43_in_pass1_full :
    tmFiber8StateAt 43 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix43 ++ [tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix43 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 43) tmFiber8State43_in_pass1_prefix43
theorem tmFiber8State44_in_pass1_prefix44 :
    tmFiber8StateAt 44 ∈ chainClosureStep tmWord tmFiber8Prefix44 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 40 ∈
      chainClosureStep tmWord tmFiber8Prefix43 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix43 = tmFiber8Prefix40 ++ [tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43]
      (chainClosureStep tmWord tmFiber8Prefix40 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 40) tmFiber8State40_in_pass1_prefix40
  rw [show tmFiber8Prefix44 = tmFiber8Prefix43 ++ [tmFiber8StateAt 44] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 44) []
    (chainClosureStep tmWord tmFiber8Prefix43 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 40) hparentBefore tmFiber8ReverseSingleStep44
theorem tmFiber8State44_in_pass1_full :
    tmFiber8StateAt 44 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix44 ++ [tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix44 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 44) tmFiber8State44_in_pass1_prefix44
theorem tmFiber8State45_in_pass1_prefix45 :
    tmFiber8StateAt 45 ∈ chainClosureStep tmWord tmFiber8Prefix45 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 41 ∈
      chainClosureStep tmWord tmFiber8Prefix44 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix44 = tmFiber8Prefix41 ++ [tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44]
      (chainClosureStep tmWord tmFiber8Prefix41 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 41) tmFiber8State41_in_pass1_prefix41
  rw [show tmFiber8Prefix45 = tmFiber8Prefix44 ++ [tmFiber8StateAt 45] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 45) []
    (chainClosureStep tmWord tmFiber8Prefix44 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 41) hparentBefore tmFiber8ReverseSingleStep45
theorem tmFiber8State45_in_pass1_full :
    tmFiber8StateAt 45 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix45 ++ [tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix45 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 45) tmFiber8State45_in_pass1_prefix45
theorem tmFiber8State46_in_pass1_prefix46 :
    tmFiber8StateAt 46 ∈ chainClosureStep tmWord tmFiber8Prefix46 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 14 ∈
      chainClosureStep tmWord tmFiber8Prefix45 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix45 = tmFiber8Prefix14 ++ [tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45]
      (chainClosureStep tmWord tmFiber8Prefix14 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 14) tmFiber8State14_in_pass1_prefix14
  rw [show tmFiber8Prefix46 = tmFiber8Prefix45 ++ [tmFiber8StateAt 46] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 46) []
    (chainClosureStep tmWord tmFiber8Prefix45 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 14) hparentBefore tmFiber8ReverseSingleStep46
theorem tmFiber8State46_in_pass1_full :
    tmFiber8StateAt 46 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix46 ++ [tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix46 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 46) tmFiber8State46_in_pass1_prefix46
theorem tmFiber8State47_in_pass1_prefix47 :
    tmFiber8StateAt 47 ∈ chainClosureStep tmWord tmFiber8Prefix47 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 15 ∈
      chainClosureStep tmWord tmFiber8Prefix46 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix46 = tmFiber8Prefix15 ++ [tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46]
      (chainClosureStep tmWord tmFiber8Prefix15 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 15) tmFiber8State15_in_pass1_prefix15
  rw [show tmFiber8Prefix47 = tmFiber8Prefix46 ++ [tmFiber8StateAt 47] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 47) []
    (chainClosureStep tmWord tmFiber8Prefix46 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 15) hparentBefore tmFiber8ReverseSingleStep47
theorem tmFiber8State47_in_pass1_full :
    tmFiber8StateAt 47 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix47 ++ [tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix47 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 47) tmFiber8State47_in_pass1_prefix47
theorem tmFiber8State48_in_pass1_prefix48 :
    tmFiber8StateAt 48 ∈ chainClosureStep tmWord tmFiber8Prefix48 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 32 ∈
      chainClosureStep tmWord tmFiber8Prefix47 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix47 = tmFiber8Prefix32 ++ [tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47]
      (chainClosureStep tmWord tmFiber8Prefix32 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 32) tmFiber8State32_in_pass1_prefix32
  rw [show tmFiber8Prefix48 = tmFiber8Prefix47 ++ [tmFiber8StateAt 48] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 48) []
    (chainClosureStep tmWord tmFiber8Prefix47 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 32) hparentBefore tmFiber8ReverseSingleStep48
theorem tmFiber8State48_in_pass1_full :
    tmFiber8StateAt 48 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix48 ++ [tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix48 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 48) tmFiber8State48_in_pass1_prefix48
theorem tmFiber8State49_in_pass1_prefix49 :
    tmFiber8StateAt 49 ∈ chainClosureStep tmWord tmFiber8Prefix49 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 33 ∈
      chainClosureStep tmWord tmFiber8Prefix48 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix48 = tmFiber8Prefix33 ++ [tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48]
      (chainClosureStep tmWord tmFiber8Prefix33 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 33) tmFiber8State33_in_pass1_prefix33
  rw [show tmFiber8Prefix49 = tmFiber8Prefix48 ++ [tmFiber8StateAt 49] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 49) []
    (chainClosureStep tmWord tmFiber8Prefix48 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 33) hparentBefore tmFiber8ReverseSingleStep49
theorem tmFiber8State49_in_pass1_full :
    tmFiber8StateAt 49 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix49 ++ [tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix49 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 49) tmFiber8State49_in_pass1_prefix49
theorem tmFiber8State50_in_pass1_prefix50 :
    tmFiber8StateAt 50 ∈ chainClosureStep tmWord tmFiber8Prefix50 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 34 ∈
      chainClosureStep tmWord tmFiber8Prefix49 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix49 = tmFiber8Prefix34 ++ [tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49]
      (chainClosureStep tmWord tmFiber8Prefix34 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 34) tmFiber8State34_in_pass1_prefix34
  rw [show tmFiber8Prefix50 = tmFiber8Prefix49 ++ [tmFiber8StateAt 50] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 50) []
    (chainClosureStep tmWord tmFiber8Prefix49 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 34) hparentBefore tmFiber8ReverseSingleStep50
theorem tmFiber8State50_in_pass1_full :
    tmFiber8StateAt 50 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix50 ++ [tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix50 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 50) tmFiber8State50_in_pass1_prefix50
theorem tmFiber8State51_in_pass1_prefix51 :
    tmFiber8StateAt 51 ∈ chainClosureStep tmWord tmFiber8Prefix51 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 35 ∈
      chainClosureStep tmWord tmFiber8Prefix50 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix50 = tmFiber8Prefix35 ++ [tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50]
      (chainClosureStep tmWord tmFiber8Prefix35 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 35) tmFiber8State35_in_pass1_prefix35
  rw [show tmFiber8Prefix51 = tmFiber8Prefix50 ++ [tmFiber8StateAt 51] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 51) []
    (chainClosureStep tmWord tmFiber8Prefix50 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 35) hparentBefore tmFiber8ReverseSingleStep51
theorem tmFiber8State51_in_pass1_full :
    tmFiber8StateAt 51 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix51 ++ [tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix51 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 51) tmFiber8State51_in_pass1_prefix51
theorem tmFiber8State52_in_pass1_prefix52 :
    tmFiber8StateAt 52 ∈ chainClosureStep tmWord tmFiber8Prefix52 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 36 ∈
      chainClosureStep tmWord tmFiber8Prefix51 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix51 = tmFiber8Prefix36 ++ [tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51]
      (chainClosureStep tmWord tmFiber8Prefix36 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 36) tmFiber8State36_in_pass1_prefix36
  rw [show tmFiber8Prefix52 = tmFiber8Prefix51 ++ [tmFiber8StateAt 52] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 52) []
    (chainClosureStep tmWord tmFiber8Prefix51 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 36) hparentBefore tmFiber8ReverseSingleStep52
theorem tmFiber8State52_in_pass1_full :
    tmFiber8StateAt 52 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix52 ++ [tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix52 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 52) tmFiber8State52_in_pass1_prefix52
theorem tmFiber8State53_in_pass1_prefix53 :
    tmFiber8StateAt 53 ∈ chainClosureStep tmWord tmFiber8Prefix53 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 37 ∈
      chainClosureStep tmWord tmFiber8Prefix52 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix52 = tmFiber8Prefix37 ++ [tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52]
      (chainClosureStep tmWord tmFiber8Prefix37 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 37) tmFiber8State37_in_pass1_prefix37
  rw [show tmFiber8Prefix53 = tmFiber8Prefix52 ++ [tmFiber8StateAt 53] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 53) []
    (chainClosureStep tmWord tmFiber8Prefix52 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 37) hparentBefore tmFiber8ReverseSingleStep53
theorem tmFiber8State53_in_pass1_full :
    tmFiber8StateAt 53 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix53 ++ [tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix53 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 53) tmFiber8State53_in_pass1_prefix53
theorem tmFiber8State54_in_pass1_prefix54 :
    tmFiber8StateAt 54 ∈ chainClosureStep tmWord tmFiber8Prefix54 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 38 ∈
      chainClosureStep tmWord tmFiber8Prefix53 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix53 = tmFiber8Prefix38 ++ [tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53]
      (chainClosureStep tmWord tmFiber8Prefix38 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 38) tmFiber8State38_in_pass1_prefix38
  rw [show tmFiber8Prefix54 = tmFiber8Prefix53 ++ [tmFiber8StateAt 54] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 54) []
    (chainClosureStep tmWord tmFiber8Prefix53 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 38) hparentBefore tmFiber8ReverseSingleStep54
theorem tmFiber8State54_in_pass1_full :
    tmFiber8StateAt 54 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix54 ++ [tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix54 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 54) tmFiber8State54_in_pass1_prefix54
theorem tmFiber8State55_in_pass1_prefix55 :
    tmFiber8StateAt 55 ∈ chainClosureStep tmWord tmFiber8Prefix55 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 39 ∈
      chainClosureStep tmWord tmFiber8Prefix54 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix54 = tmFiber8Prefix39 ++ [tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54]
      (chainClosureStep tmWord tmFiber8Prefix39 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 39) tmFiber8State39_in_pass1_prefix39
  rw [show tmFiber8Prefix55 = tmFiber8Prefix54 ++ [tmFiber8StateAt 55] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 55) []
    (chainClosureStep tmWord tmFiber8Prefix54 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 39) hparentBefore tmFiber8ReverseSingleStep55
theorem tmFiber8State55_in_pass1_full :
    tmFiber8StateAt 55 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix55 ++ [tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix55 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 55) tmFiber8State55_in_pass1_prefix55
theorem tmFiber8State56_in_pass1_prefix56 :
    tmFiber8StateAt 56 ∈ chainClosureStep tmWord tmFiber8Prefix56 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 24 ∈
      chainClosureStep tmWord tmFiber8Prefix55 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix55 = tmFiber8Prefix24 ++ [tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55]
      (chainClosureStep tmWord tmFiber8Prefix24 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 24) tmFiber8State24_in_pass1_prefix24
  rw [show tmFiber8Prefix56 = tmFiber8Prefix55 ++ [tmFiber8StateAt 56] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 56) []
    (chainClosureStep tmWord tmFiber8Prefix55 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 24) hparentBefore tmFiber8ReverseSingleStep56
theorem tmFiber8State56_in_pass1_full :
    tmFiber8StateAt 56 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix56 ++ [tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix56 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 56) tmFiber8State56_in_pass1_prefix56
theorem tmFiber8State57_in_pass1_prefix57 :
    tmFiber8StateAt 57 ∈ chainClosureStep tmWord tmFiber8Prefix57 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 25 ∈
      chainClosureStep tmWord tmFiber8Prefix56 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix56 = tmFiber8Prefix25 ++ [tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56]
      (chainClosureStep tmWord tmFiber8Prefix25 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 25) tmFiber8State25_in_pass1_prefix25
  rw [show tmFiber8Prefix57 = tmFiber8Prefix56 ++ [tmFiber8StateAt 57] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 57) []
    (chainClosureStep tmWord tmFiber8Prefix56 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 25) hparentBefore tmFiber8ReverseSingleStep57
theorem tmFiber8State57_in_pass1_full :
    tmFiber8StateAt 57 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix57 ++ [tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix57 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 57) tmFiber8State57_in_pass1_prefix57
theorem tmFiber8State58_in_pass1_prefix58 :
    tmFiber8StateAt 58 ∈ chainClosureStep tmWord tmFiber8Prefix58 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 26 ∈
      chainClosureStep tmWord tmFiber8Prefix57 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix57 = tmFiber8Prefix26 ++ [tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57]
      (chainClosureStep tmWord tmFiber8Prefix26 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 26) tmFiber8State26_in_pass1_prefix26
  rw [show tmFiber8Prefix58 = tmFiber8Prefix57 ++ [tmFiber8StateAt 58] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 58) []
    (chainClosureStep tmWord tmFiber8Prefix57 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 26) hparentBefore tmFiber8ReverseSingleStep58
theorem tmFiber8State58_in_pass1_full :
    tmFiber8StateAt 58 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix58 ++ [tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix58 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 58) tmFiber8State58_in_pass1_prefix58
theorem tmFiber8State59_in_pass1_prefix59 :
    tmFiber8StateAt 59 ∈ chainClosureStep tmWord tmFiber8Prefix59 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 27 ∈
      chainClosureStep tmWord tmFiber8Prefix58 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix58 = tmFiber8Prefix27 ++ [tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58]
      (chainClosureStep tmWord tmFiber8Prefix27 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 27) tmFiber8State27_in_pass1_prefix27
  rw [show tmFiber8Prefix59 = tmFiber8Prefix58 ++ [tmFiber8StateAt 59] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 59) []
    (chainClosureStep tmWord tmFiber8Prefix58 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 27) hparentBefore tmFiber8ReverseSingleStep59
theorem tmFiber8State59_in_pass1_full :
    tmFiber8StateAt 59 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix59 ++ [tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix59 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 59) tmFiber8State59_in_pass1_prefix59
theorem tmFiber8State60_in_pass1_prefix60 :
    tmFiber8StateAt 60 ∈ chainClosureStep tmWord tmFiber8Prefix60 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 56 ∈
      chainClosureStep tmWord tmFiber8Prefix59 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix59 = tmFiber8Prefix56 ++ [tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59]
      (chainClosureStep tmWord tmFiber8Prefix56 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 56) tmFiber8State56_in_pass1_prefix56
  rw [show tmFiber8Prefix60 = tmFiber8Prefix59 ++ [tmFiber8StateAt 60] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 60) []
    (chainClosureStep tmWord tmFiber8Prefix59 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 56) hparentBefore tmFiber8ReverseSingleStep60
theorem tmFiber8State60_in_pass1_full :
    tmFiber8StateAt 60 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix60 ++ [tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix60 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 60) tmFiber8State60_in_pass1_prefix60
theorem tmFiber8State61_in_pass1_prefix61 :
    tmFiber8StateAt 61 ∈ chainClosureStep tmWord tmFiber8Prefix61 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 57 ∈
      chainClosureStep tmWord tmFiber8Prefix60 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix60 = tmFiber8Prefix57 ++ [tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60]
      (chainClosureStep tmWord tmFiber8Prefix57 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 57) tmFiber8State57_in_pass1_prefix57
  rw [show tmFiber8Prefix61 = tmFiber8Prefix60 ++ [tmFiber8StateAt 61] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 61) []
    (chainClosureStep tmWord tmFiber8Prefix60 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 57) hparentBefore tmFiber8ReverseSingleStep61
theorem tmFiber8State61_in_pass1_full :
    tmFiber8StateAt 61 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix61 ++ [tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix61 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 61) tmFiber8State61_in_pass1_prefix61
theorem tmFiber8State62_in_pass1_prefix62 :
    tmFiber8StateAt 62 ∈ chainClosureStep tmWord tmFiber8Prefix62 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 30 ∈
      chainClosureStep tmWord tmFiber8Prefix61 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix61 = tmFiber8Prefix30 ++ [tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61]
      (chainClosureStep tmWord tmFiber8Prefix30 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 30) tmFiber8State30_in_pass1_prefix30
  rw [show tmFiber8Prefix62 = tmFiber8Prefix61 ++ [tmFiber8StateAt 62] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 62) []
    (chainClosureStep tmWord tmFiber8Prefix61 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 30) hparentBefore tmFiber8ReverseSingleStep62
theorem tmFiber8State62_in_pass1_full :
    tmFiber8StateAt 62 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix62 ++ [tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix62 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 62) tmFiber8State62_in_pass1_prefix62
theorem tmFiber8State63_in_pass1_prefix63 :
    tmFiber8StateAt 63 ∈ chainClosureStep tmWord tmFiber8Prefix63 ([tmFiber8StateAt 0]) := by
  have hparentBefore : tmFiber8StateAt 31 ∈
      chainClosureStep tmWord tmFiber8Prefix62 ([tmFiber8StateAt 0]) := by
    rw [show tmFiber8Prefix62 = tmFiber8Prefix31 ++ [tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62]
      (chainClosureStep tmWord tmFiber8Prefix31 ([tmFiber8StateAt 0]))
      (tmFiber8StateAt 31) tmFiber8State31_in_pass1_prefix31
  rw [show tmFiber8Prefix63 = tmFiber8Prefix62 ++ [tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 63) []
    (chainClosureStep tmWord tmFiber8Prefix62 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 31) hparentBefore tmFiber8ReverseSingleStep63
theorem tmFiber8State63_in_pass1_full :
    tmFiber8StateAt 63 ∈ chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0]) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix63 ++ [] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord []
    (chainClosureStep tmWord tmFiber8Prefix63 ([tmFiber8StateAt 0]))
    (tmFiber8StateAt 63) tmFiber8State63_in_pass1_prefix63
theorem tmFiber8State5_in_pass2_prefix5 :
    tmFiber8StateAt 5 ∈ chainClosureStep tmWord tmFiber8Prefix5 (chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0])) := by
  have hparentBefore : tmFiber8StateAt 7 ∈
      chainClosureStep tmWord tmFiber8Prefix4 (chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber8Prefix4
      (chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0])) (tmFiber8StateAt 7) tmFiber8State7_in_pass1_full
  rw [show tmFiber8Prefix5 = tmFiber8Prefix4 ++ [tmFiber8StateAt 5] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 5) []
    (chainClosureStep tmWord tmFiber8Prefix4 (chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0])))
    (tmFiber8StateAt 7) hparentBefore tmFiber8ReverseSingleStep5
theorem tmFiber8State5_in_pass2_full :
    tmFiber8StateAt 5 ∈ chainClosureStep tmWord tmFiber8DirectStates (chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0])) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix5 ++ [tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix5 (chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0])))
    (tmFiber8StateAt 5) tmFiber8State5_in_pass2_prefix5
theorem tmFiber8State13_in_pass2_prefix13 :
    tmFiber8StateAt 13 ∈ chainClosureStep tmWord tmFiber8Prefix13 (chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0])) := by
  have hparentBefore : tmFiber8StateAt 5 ∈
      chainClosureStep tmWord tmFiber8Prefix12 (chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0])) := by
    rw [show tmFiber8Prefix12 = tmFiber8Prefix5 ++ [tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12]
      (chainClosureStep tmWord tmFiber8Prefix5 (chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0])))
      (tmFiber8StateAt 5) tmFiber8State5_in_pass2_prefix5
  rw [show tmFiber8Prefix13 = tmFiber8Prefix12 ++ [tmFiber8StateAt 13] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 13) []
    (chainClosureStep tmWord tmFiber8Prefix12 (chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0])))
    (tmFiber8StateAt 5) hparentBefore tmFiber8ReverseSingleStep13
theorem tmFiber8State13_in_pass2_full :
    tmFiber8StateAt 13 ∈ chainClosureStep tmWord tmFiber8DirectStates (chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0])) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix13 ++ [tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix13 (chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0])))
    (tmFiber8StateAt 13) tmFiber8State13_in_pass2_prefix13
theorem tmFiber8State21_in_pass2_prefix21 :
    tmFiber8StateAt 21 ∈ chainClosureStep tmWord tmFiber8Prefix21 (chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0])) := by
  have hparentBefore : tmFiber8StateAt 13 ∈
      chainClosureStep tmWord tmFiber8Prefix20 (chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0])) := by
    rw [show tmFiber8Prefix20 = tmFiber8Prefix13 ++ [tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20]
      (chainClosureStep tmWord tmFiber8Prefix13 (chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0])))
      (tmFiber8StateAt 13) tmFiber8State13_in_pass2_prefix13
  rw [show tmFiber8Prefix21 = tmFiber8Prefix20 ++ [tmFiber8StateAt 21] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 21) []
    (chainClosureStep tmWord tmFiber8Prefix20 (chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0])))
    (tmFiber8StateAt 13) hparentBefore tmFiber8ReverseSingleStep21
theorem tmFiber8State21_in_pass2_full :
    tmFiber8StateAt 21 ∈ chainClosureStep tmWord tmFiber8DirectStates (chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0])) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix21 ++ [tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28, tmFiber8StateAt 29, tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix21 (chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0])))
    (tmFiber8StateAt 21) tmFiber8State21_in_pass2_prefix21
theorem tmFiber8State29_in_pass2_prefix29 :
    tmFiber8StateAt 29 ∈ chainClosureStep tmWord tmFiber8Prefix29 (chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0])) := by
  have hparentBefore : tmFiber8StateAt 5 ∈
      chainClosureStep tmWord tmFiber8Prefix28 (chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0])) := by
    rw [show tmFiber8Prefix28 = tmFiber8Prefix5 ++ [tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 6, tmFiber8StateAt 7, tmFiber8StateAt 8, tmFiber8StateAt 9, tmFiber8StateAt 10, tmFiber8StateAt 11, tmFiber8StateAt 12, tmFiber8StateAt 13, tmFiber8StateAt 14, tmFiber8StateAt 15, tmFiber8StateAt 16, tmFiber8StateAt 17, tmFiber8StateAt 18, tmFiber8StateAt 19, tmFiber8StateAt 20, tmFiber8StateAt 21, tmFiber8StateAt 22, tmFiber8StateAt 23, tmFiber8StateAt 24, tmFiber8StateAt 25, tmFiber8StateAt 26, tmFiber8StateAt 27, tmFiber8StateAt 28]
      (chainClosureStep tmWord tmFiber8Prefix5 (chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0])))
      (tmFiber8StateAt 5) tmFiber8State5_in_pass2_prefix5
  rw [show tmFiber8Prefix29 = tmFiber8Prefix28 ++ [tmFiber8StateAt 29] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber8StateAt 29) []
    (chainClosureStep tmWord tmFiber8Prefix28 (chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0])))
    (tmFiber8StateAt 5) hparentBefore tmFiber8ReverseSingleStep29
theorem tmFiber8State29_in_pass2_full :
    tmFiber8StateAt 29 ∈ chainClosureStep tmWord tmFiber8DirectStates (chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0])) := by
  rw [show tmFiber8DirectStates = tmFiber8Prefix29 ++ [tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber8StateAt 30, tmFiber8StateAt 31, tmFiber8StateAt 32, tmFiber8StateAt 33, tmFiber8StateAt 34, tmFiber8StateAt 35, tmFiber8StateAt 36, tmFiber8StateAt 37, tmFiber8StateAt 38, tmFiber8StateAt 39, tmFiber8StateAt 40, tmFiber8StateAt 41, tmFiber8StateAt 42, tmFiber8StateAt 43, tmFiber8StateAt 44, tmFiber8StateAt 45, tmFiber8StateAt 46, tmFiber8StateAt 47, tmFiber8StateAt 48, tmFiber8StateAt 49, tmFiber8StateAt 50, tmFiber8StateAt 51, tmFiber8StateAt 52, tmFiber8StateAt 53, tmFiber8StateAt 54, tmFiber8StateAt 55, tmFiber8StateAt 56, tmFiber8StateAt 57, tmFiber8StateAt 58, tmFiber8StateAt 59, tmFiber8StateAt 60, tmFiber8StateAt 61, tmFiber8StateAt 62, tmFiber8StateAt 63]
    (chainClosureStep tmWord tmFiber8Prefix29 (chainClosureStep tmWord tmFiber8DirectStates ([tmFiber8StateAt 0])))
    (tmFiber8StateAt 29) tmFiber8State29_in_pass2_prefix29
theorem tmFiber8FirstPassGrows :
    ((chainClosureStep tmWord tmFiber8DirectStates [tmFiber8StateAt 0]).length ==
      [tmFiber8StateAt 0].length) = false := by
  have hroot : tmFiber8StateAt 0 ∈
      chainClosureStep tmWord tmFiber8DirectStates [tmFiber8StateAt 0] :=
    chainClosureStep_mem_of_seen tmWord tmFiber8DirectStates
      [tmFiber8StateAt 0] (tmFiber8StateAt 0) (by simp)
  have hnew : tmFiber8StateAt 1 ∈
      chainClosureStep tmWord tmFiber8DirectStates [tmFiber8StateAt 0] :=
    tmFiber8State1_in_pass1_full
  simpa using list_length_beq_one_false_of_two_mem
    (chainClosureStep tmWord tmFiber8DirectStates [tmFiber8StateAt 0])
    (tmFiber8StateAt 0) (tmFiber8StateAt 1) hroot hnew (by decide)

theorem tmFiber8State0_in_close_short :
    tmFiber8StateAt 0 ∈ closeChainFiber tmWord tmFiber8DirectStates 0 [tmFiber8StateAt 0] := by
  simp [closeChainFiber]

theorem tmFiber8State1_in_close_short :
    tmFiber8StateAt 1 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 1) tmFiber8State1_in_pass1_full

theorem tmFiber8State2_in_close_short :
    tmFiber8StateAt 2 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 2) tmFiber8State2_in_pass1_full

theorem tmFiber8State3_in_close_short :
    tmFiber8StateAt 3 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 3) tmFiber8State3_in_pass1_full

theorem tmFiber8State4_in_close_short :
    tmFiber8StateAt 4 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 4) tmFiber8State4_in_pass1_full

theorem tmFiber8State6_in_close_short :
    tmFiber8StateAt 6 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 6) tmFiber8State6_in_pass1_full

theorem tmFiber8State7_in_close_short :
    tmFiber8StateAt 7 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 7) tmFiber8State7_in_pass1_full

theorem tmFiber8State8_in_close_short :
    tmFiber8StateAt 8 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 8) tmFiber8State8_in_pass1_full

theorem tmFiber8State9_in_close_short :
    tmFiber8StateAt 9 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 9) tmFiber8State9_in_pass1_full

theorem tmFiber8State10_in_close_short :
    tmFiber8StateAt 10 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 10) tmFiber8State10_in_pass1_full

theorem tmFiber8State11_in_close_short :
    tmFiber8StateAt 11 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 11) tmFiber8State11_in_pass1_full

theorem tmFiber8State12_in_close_short :
    tmFiber8StateAt 12 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 12) tmFiber8State12_in_pass1_full

theorem tmFiber8State14_in_close_short :
    tmFiber8StateAt 14 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 14) tmFiber8State14_in_pass1_full

theorem tmFiber8State15_in_close_short :
    tmFiber8StateAt 15 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 15) tmFiber8State15_in_pass1_full

theorem tmFiber8State16_in_close_short :
    tmFiber8StateAt 16 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 16) tmFiber8State16_in_pass1_full

theorem tmFiber8State17_in_close_short :
    tmFiber8StateAt 17 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 17) tmFiber8State17_in_pass1_full

theorem tmFiber8State18_in_close_short :
    tmFiber8StateAt 18 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 18) tmFiber8State18_in_pass1_full

theorem tmFiber8State19_in_close_short :
    tmFiber8StateAt 19 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 19) tmFiber8State19_in_pass1_full

theorem tmFiber8State20_in_close_short :
    tmFiber8StateAt 20 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 20) tmFiber8State20_in_pass1_full

theorem tmFiber8State22_in_close_short :
    tmFiber8StateAt 22 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 22) tmFiber8State22_in_pass1_full

theorem tmFiber8State23_in_close_short :
    tmFiber8StateAt 23 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 23) tmFiber8State23_in_pass1_full

theorem tmFiber8State24_in_close_short :
    tmFiber8StateAt 24 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 24) tmFiber8State24_in_pass1_full

theorem tmFiber8State25_in_close_short :
    tmFiber8StateAt 25 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 25) tmFiber8State25_in_pass1_full

theorem tmFiber8State26_in_close_short :
    tmFiber8StateAt 26 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 26) tmFiber8State26_in_pass1_full

theorem tmFiber8State27_in_close_short :
    tmFiber8StateAt 27 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 27) tmFiber8State27_in_pass1_full

theorem tmFiber8State28_in_close_short :
    tmFiber8StateAt 28 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 28) tmFiber8State28_in_pass1_full

theorem tmFiber8State30_in_close_short :
    tmFiber8StateAt 30 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 30) tmFiber8State30_in_pass1_full

theorem tmFiber8State31_in_close_short :
    tmFiber8StateAt 31 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 31) tmFiber8State31_in_pass1_full

theorem tmFiber8State32_in_close_short :
    tmFiber8StateAt 32 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 32) tmFiber8State32_in_pass1_full

theorem tmFiber8State33_in_close_short :
    tmFiber8StateAt 33 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 33) tmFiber8State33_in_pass1_full

theorem tmFiber8State34_in_close_short :
    tmFiber8StateAt 34 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 34) tmFiber8State34_in_pass1_full

theorem tmFiber8State35_in_close_short :
    tmFiber8StateAt 35 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 35) tmFiber8State35_in_pass1_full

theorem tmFiber8State36_in_close_short :
    tmFiber8StateAt 36 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 36) tmFiber8State36_in_pass1_full

theorem tmFiber8State37_in_close_short :
    tmFiber8StateAt 37 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 37) tmFiber8State37_in_pass1_full

theorem tmFiber8State38_in_close_short :
    tmFiber8StateAt 38 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 38) tmFiber8State38_in_pass1_full

theorem tmFiber8State39_in_close_short :
    tmFiber8StateAt 39 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 39) tmFiber8State39_in_pass1_full

theorem tmFiber8State40_in_close_short :
    tmFiber8StateAt 40 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 40) tmFiber8State40_in_pass1_full

theorem tmFiber8State41_in_close_short :
    tmFiber8StateAt 41 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 41) tmFiber8State41_in_pass1_full

theorem tmFiber8State42_in_close_short :
    tmFiber8StateAt 42 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 42) tmFiber8State42_in_pass1_full

theorem tmFiber8State43_in_close_short :
    tmFiber8StateAt 43 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 43) tmFiber8State43_in_pass1_full

theorem tmFiber8State44_in_close_short :
    tmFiber8StateAt 44 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 44) tmFiber8State44_in_pass1_full

theorem tmFiber8State45_in_close_short :
    tmFiber8StateAt 45 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 45) tmFiber8State45_in_pass1_full

theorem tmFiber8State46_in_close_short :
    tmFiber8StateAt 46 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 46) tmFiber8State46_in_pass1_full

theorem tmFiber8State47_in_close_short :
    tmFiber8StateAt 47 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 47) tmFiber8State47_in_pass1_full

theorem tmFiber8State48_in_close_short :
    tmFiber8StateAt 48 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 48) tmFiber8State48_in_pass1_full

theorem tmFiber8State49_in_close_short :
    tmFiber8StateAt 49 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 49) tmFiber8State49_in_pass1_full

theorem tmFiber8State50_in_close_short :
    tmFiber8StateAt 50 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 50) tmFiber8State50_in_pass1_full

theorem tmFiber8State51_in_close_short :
    tmFiber8StateAt 51 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 51) tmFiber8State51_in_pass1_full

theorem tmFiber8State52_in_close_short :
    tmFiber8StateAt 52 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 52) tmFiber8State52_in_pass1_full

theorem tmFiber8State53_in_close_short :
    tmFiber8StateAt 53 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 53) tmFiber8State53_in_pass1_full

theorem tmFiber8State54_in_close_short :
    tmFiber8StateAt 54 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 54) tmFiber8State54_in_pass1_full

theorem tmFiber8State55_in_close_short :
    tmFiber8StateAt 55 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 55) tmFiber8State55_in_pass1_full

theorem tmFiber8State56_in_close_short :
    tmFiber8StateAt 56 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 56) tmFiber8State56_in_pass1_full

theorem tmFiber8State57_in_close_short :
    tmFiber8StateAt 57 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 57) tmFiber8State57_in_pass1_full

theorem tmFiber8State58_in_close_short :
    tmFiber8StateAt 58 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 58) tmFiber8State58_in_pass1_full

theorem tmFiber8State59_in_close_short :
    tmFiber8StateAt 59 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 59) tmFiber8State59_in_pass1_full

theorem tmFiber8State60_in_close_short :
    tmFiber8StateAt 60 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 60) tmFiber8State60_in_pass1_full

theorem tmFiber8State61_in_close_short :
    tmFiber8StateAt 61 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 61) tmFiber8State61_in_pass1_full

theorem tmFiber8State62_in_close_short :
    tmFiber8StateAt 62 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 62) tmFiber8State62_in_pass1_full

theorem tmFiber8State63_in_close_short :
    tmFiber8StateAt 63 ∈ closeChainFiber tmWord tmFiber8DirectStates 1 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 63) tmFiber8State63_in_pass1_full

theorem tmFiber8State5_in_close_short :
    tmFiber8StateAt 5 ∈ closeChainFiber tmWord tmFiber8DirectStates 2 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 5) tmFiber8FirstPassGrows
    tmFiber8State5_in_pass2_full

theorem tmFiber8State13_in_close_short :
    tmFiber8StateAt 13 ∈ closeChainFiber tmWord tmFiber8DirectStates 2 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 13) tmFiber8FirstPassGrows
    tmFiber8State13_in_pass2_full

theorem tmFiber8State21_in_close_short :
    tmFiber8StateAt 21 ∈ closeChainFiber tmWord tmFiber8DirectStates 2 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 21) tmFiber8FirstPassGrows
    tmFiber8State21_in_pass2_full

theorem tmFiber8State29_in_close_short :
    tmFiber8StateAt 29 ∈ closeChainFiber tmWord tmFiber8DirectStates 2 [tmFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber8DirectStates 0
    [tmFiber8StateAt 0] (tmFiber8StateAt 29) tmFiber8FirstPassGrows
    tmFiber8State29_in_pass2_full

theorem tmFiber8State0_in_close :
    tmFiber8StateAt 0 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 0 ∈ closeChainFiber tmWord tmFiber8DirectStates (0 + 64) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 0 64
    [tmFiber8StateAt 0] (tmFiber8StateAt 0) tmFiber8State0_in_close_short

theorem tmFiber8State1_in_close :
    tmFiber8StateAt 1 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 1 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 1) tmFiber8State1_in_close_short

theorem tmFiber8State2_in_close :
    tmFiber8StateAt 2 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 2 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 2) tmFiber8State2_in_close_short

theorem tmFiber8State3_in_close :
    tmFiber8StateAt 3 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 3 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 3) tmFiber8State3_in_close_short

theorem tmFiber8State4_in_close :
    tmFiber8StateAt 4 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 4 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 4) tmFiber8State4_in_close_short

theorem tmFiber8State5_in_close :
    tmFiber8StateAt 5 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 5 ∈ closeChainFiber tmWord tmFiber8DirectStates (2 + 62) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 2 62
    [tmFiber8StateAt 0] (tmFiber8StateAt 5) tmFiber8State5_in_close_short

theorem tmFiber8State6_in_close :
    tmFiber8StateAt 6 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 6 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 6) tmFiber8State6_in_close_short

theorem tmFiber8State7_in_close :
    tmFiber8StateAt 7 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 7 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 7) tmFiber8State7_in_close_short

theorem tmFiber8State8_in_close :
    tmFiber8StateAt 8 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 8 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 8) tmFiber8State8_in_close_short

theorem tmFiber8State9_in_close :
    tmFiber8StateAt 9 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 9 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 9) tmFiber8State9_in_close_short

theorem tmFiber8State10_in_close :
    tmFiber8StateAt 10 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 10 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 10) tmFiber8State10_in_close_short

theorem tmFiber8State11_in_close :
    tmFiber8StateAt 11 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 11 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 11) tmFiber8State11_in_close_short

theorem tmFiber8State12_in_close :
    tmFiber8StateAt 12 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 12 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 12) tmFiber8State12_in_close_short

theorem tmFiber8State13_in_close :
    tmFiber8StateAt 13 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 13 ∈ closeChainFiber tmWord tmFiber8DirectStates (2 + 62) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 2 62
    [tmFiber8StateAt 0] (tmFiber8StateAt 13) tmFiber8State13_in_close_short

theorem tmFiber8State14_in_close :
    tmFiber8StateAt 14 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 14 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 14) tmFiber8State14_in_close_short

theorem tmFiber8State15_in_close :
    tmFiber8StateAt 15 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 15 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 15) tmFiber8State15_in_close_short

theorem tmFiber8State16_in_close :
    tmFiber8StateAt 16 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 16 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 16) tmFiber8State16_in_close_short

theorem tmFiber8State17_in_close :
    tmFiber8StateAt 17 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 17 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 17) tmFiber8State17_in_close_short

theorem tmFiber8State18_in_close :
    tmFiber8StateAt 18 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 18 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 18) tmFiber8State18_in_close_short

theorem tmFiber8State19_in_close :
    tmFiber8StateAt 19 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 19 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 19) tmFiber8State19_in_close_short

theorem tmFiber8State20_in_close :
    tmFiber8StateAt 20 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 20 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 20) tmFiber8State20_in_close_short

theorem tmFiber8State21_in_close :
    tmFiber8StateAt 21 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 21 ∈ closeChainFiber tmWord tmFiber8DirectStates (2 + 62) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 2 62
    [tmFiber8StateAt 0] (tmFiber8StateAt 21) tmFiber8State21_in_close_short

theorem tmFiber8State22_in_close :
    tmFiber8StateAt 22 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 22 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 22) tmFiber8State22_in_close_short

theorem tmFiber8State23_in_close :
    tmFiber8StateAt 23 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 23 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 23) tmFiber8State23_in_close_short

theorem tmFiber8State24_in_close :
    tmFiber8StateAt 24 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 24 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 24) tmFiber8State24_in_close_short

theorem tmFiber8State25_in_close :
    tmFiber8StateAt 25 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 25 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 25) tmFiber8State25_in_close_short

theorem tmFiber8State26_in_close :
    tmFiber8StateAt 26 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 26 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 26) tmFiber8State26_in_close_short

theorem tmFiber8State27_in_close :
    tmFiber8StateAt 27 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 27 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 27) tmFiber8State27_in_close_short

theorem tmFiber8State28_in_close :
    tmFiber8StateAt 28 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 28 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 28) tmFiber8State28_in_close_short

theorem tmFiber8State29_in_close :
    tmFiber8StateAt 29 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 29 ∈ closeChainFiber tmWord tmFiber8DirectStates (2 + 62) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 2 62
    [tmFiber8StateAt 0] (tmFiber8StateAt 29) tmFiber8State29_in_close_short

theorem tmFiber8State30_in_close :
    tmFiber8StateAt 30 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 30 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 30) tmFiber8State30_in_close_short

theorem tmFiber8State31_in_close :
    tmFiber8StateAt 31 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 31 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 31) tmFiber8State31_in_close_short

theorem tmFiber8State32_in_close :
    tmFiber8StateAt 32 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 32 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 32) tmFiber8State32_in_close_short

theorem tmFiber8State33_in_close :
    tmFiber8StateAt 33 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 33 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 33) tmFiber8State33_in_close_short

theorem tmFiber8State34_in_close :
    tmFiber8StateAt 34 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 34 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 34) tmFiber8State34_in_close_short

theorem tmFiber8State35_in_close :
    tmFiber8StateAt 35 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 35 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 35) tmFiber8State35_in_close_short

theorem tmFiber8State36_in_close :
    tmFiber8StateAt 36 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 36 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 36) tmFiber8State36_in_close_short

theorem tmFiber8State37_in_close :
    tmFiber8StateAt 37 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 37 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 37) tmFiber8State37_in_close_short

theorem tmFiber8State38_in_close :
    tmFiber8StateAt 38 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 38 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 38) tmFiber8State38_in_close_short

theorem tmFiber8State39_in_close :
    tmFiber8StateAt 39 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 39 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 39) tmFiber8State39_in_close_short

theorem tmFiber8State40_in_close :
    tmFiber8StateAt 40 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 40 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 40) tmFiber8State40_in_close_short

theorem tmFiber8State41_in_close :
    tmFiber8StateAt 41 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 41 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 41) tmFiber8State41_in_close_short

theorem tmFiber8State42_in_close :
    tmFiber8StateAt 42 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 42 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 42) tmFiber8State42_in_close_short

theorem tmFiber8State43_in_close :
    tmFiber8StateAt 43 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 43 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 43) tmFiber8State43_in_close_short

theorem tmFiber8State44_in_close :
    tmFiber8StateAt 44 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 44 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 44) tmFiber8State44_in_close_short

theorem tmFiber8State45_in_close :
    tmFiber8StateAt 45 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 45 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 45) tmFiber8State45_in_close_short

theorem tmFiber8State46_in_close :
    tmFiber8StateAt 46 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 46 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 46) tmFiber8State46_in_close_short

theorem tmFiber8State47_in_close :
    tmFiber8StateAt 47 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 47 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 47) tmFiber8State47_in_close_short

theorem tmFiber8State48_in_close :
    tmFiber8StateAt 48 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 48 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 48) tmFiber8State48_in_close_short

theorem tmFiber8State49_in_close :
    tmFiber8StateAt 49 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 49 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 49) tmFiber8State49_in_close_short

theorem tmFiber8State50_in_close :
    tmFiber8StateAt 50 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 50 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 50) tmFiber8State50_in_close_short

theorem tmFiber8State51_in_close :
    tmFiber8StateAt 51 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 51 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 51) tmFiber8State51_in_close_short

theorem tmFiber8State52_in_close :
    tmFiber8StateAt 52 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 52 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 52) tmFiber8State52_in_close_short

theorem tmFiber8State53_in_close :
    tmFiber8StateAt 53 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 53 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 53) tmFiber8State53_in_close_short

theorem tmFiber8State54_in_close :
    tmFiber8StateAt 54 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 54 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 54) tmFiber8State54_in_close_short

theorem tmFiber8State55_in_close :
    tmFiber8StateAt 55 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 55 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 55) tmFiber8State55_in_close_short

theorem tmFiber8State56_in_close :
    tmFiber8StateAt 56 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 56 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 56) tmFiber8State56_in_close_short

theorem tmFiber8State57_in_close :
    tmFiber8StateAt 57 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 57 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 57) tmFiber8State57_in_close_short

theorem tmFiber8State58_in_close :
    tmFiber8StateAt 58 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 58 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 58) tmFiber8State58_in_close_short

theorem tmFiber8State59_in_close :
    tmFiber8StateAt 59 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 59 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 59) tmFiber8State59_in_close_short

theorem tmFiber8State60_in_close :
    tmFiber8StateAt 60 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 60 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 60) tmFiber8State60_in_close_short

theorem tmFiber8State61_in_close :
    tmFiber8StateAt 61 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 61 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 61) tmFiber8State61_in_close_short

theorem tmFiber8State62_in_close :
    tmFiber8StateAt 62 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 62 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 62) tmFiber8State62_in_close_short

theorem tmFiber8State63_in_close :
    tmFiber8StateAt 63 ∈ closeChainFiber tmWord tmFiber8DirectStates tmFiber8DirectStates.length [tmFiber8StateAt 0] := by
  change tmFiber8StateAt 63 ∈ closeChainFiber tmWord tmFiber8DirectStates (1 + 63) [tmFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber8DirectStates 1 63
    [tmFiber8StateAt 0] (tmFiber8StateAt 63) tmFiber8State63_in_close_short

theorem tmFiber8DirectConnected :
    chainFiberConnected tmWord tmFiber8DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [tmFiber8DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact tmFiber8State0_in_close
  · subst state
    exact tmFiber8State1_in_close
  · subst state
    exact tmFiber8State2_in_close
  · subst state
    exact tmFiber8State3_in_close
  · subst state
    exact tmFiber8State4_in_close
  · subst state
    exact tmFiber8State5_in_close
  · subst state
    exact tmFiber8State6_in_close
  · subst state
    exact tmFiber8State7_in_close
  · subst state
    exact tmFiber8State8_in_close
  · subst state
    exact tmFiber8State9_in_close
  · subst state
    exact tmFiber8State10_in_close
  · subst state
    exact tmFiber8State11_in_close
  · subst state
    exact tmFiber8State12_in_close
  · subst state
    exact tmFiber8State13_in_close
  · subst state
    exact tmFiber8State14_in_close
  · subst state
    exact tmFiber8State15_in_close
  · subst state
    exact tmFiber8State16_in_close
  · subst state
    exact tmFiber8State17_in_close
  · subst state
    exact tmFiber8State18_in_close
  · subst state
    exact tmFiber8State19_in_close
  · subst state
    exact tmFiber8State20_in_close
  · subst state
    exact tmFiber8State21_in_close
  · subst state
    exact tmFiber8State22_in_close
  · subst state
    exact tmFiber8State23_in_close
  · subst state
    exact tmFiber8State24_in_close
  · subst state
    exact tmFiber8State25_in_close
  · subst state
    exact tmFiber8State26_in_close
  · subst state
    exact tmFiber8State27_in_close
  · subst state
    exact tmFiber8State28_in_close
  · subst state
    exact tmFiber8State29_in_close
  · subst state
    exact tmFiber8State30_in_close
  · subst state
    exact tmFiber8State31_in_close
  · subst state
    exact tmFiber8State32_in_close
  · subst state
    exact tmFiber8State33_in_close
  · subst state
    exact tmFiber8State34_in_close
  · subst state
    exact tmFiber8State35_in_close
  · subst state
    exact tmFiber8State36_in_close
  · subst state
    exact tmFiber8State37_in_close
  · subst state
    exact tmFiber8State38_in_close
  · subst state
    exact tmFiber8State39_in_close
  · subst state
    exact tmFiber8State40_in_close
  · subst state
    exact tmFiber8State41_in_close
  · subst state
    exact tmFiber8State42_in_close
  · subst state
    exact tmFiber8State43_in_close
  · subst state
    exact tmFiber8State44_in_close
  · subst state
    exact tmFiber8State45_in_close
  · subst state
    exact tmFiber8State46_in_close
  · subst state
    exact tmFiber8State47_in_close
  · subst state
    exact tmFiber8State48_in_close
  · subst state
    exact tmFiber8State49_in_close
  · subst state
    exact tmFiber8State50_in_close
  · subst state
    exact tmFiber8State51_in_close
  · subst state
    exact tmFiber8State52_in_close
  · subst state
    exact tmFiber8State53_in_close
  · subst state
    exact tmFiber8State54_in_close
  · subst state
    exact tmFiber8State55_in_close
  · subst state
    exact tmFiber8State56_in_close
  · subst state
    exact tmFiber8State57_in_close
  · subst state
    exact tmFiber8State58_in_close
  · subst state
    exact tmFiber8State59_in_close
  · subst state
    exact tmFiber8State60_in_close
  · subst state
    exact tmFiber8State61_in_close
  · subst state
    exact tmFiber8State62_in_close
  · subst state
    exact tmFiber8State63_in_close
  · cases h

end GoertzelLemma818LengthTwoTMLargeFiberBridge

end Mettapedia.GraphTheory.FourColor
