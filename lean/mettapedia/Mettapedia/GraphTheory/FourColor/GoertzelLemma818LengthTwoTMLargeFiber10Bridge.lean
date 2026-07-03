import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMLargeFiberBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated multi-pass direct closure bridge for `normal,mirror` size-64 fiber 10

This module proves direct connectedness for one generated size-64 fiber
whose parent order needs multiple closure scans. It is generated from
row-local reverse certificate chunks and keeps Lean on default limits.
-/

namespace GoertzelLemma818LengthTwoTMLargeFiberBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818TauMirrorCertificate
open GoertzelLemma818TauMirrorReverseAudit

def tmFiber10StateAt (i : Nat) : List TauState :=
  directStates (tmFiber10RowAt i).sourceLeft (tmFiber10RowAt i).sourceRight

def tmFiber10DirectStates : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]

def tmFiber10Prefix0 : List (List TauState) :=
  [tmFiber10StateAt 0]

def tmFiber10Prefix1 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1]

def tmFiber10Prefix2 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2]

def tmFiber10Prefix3 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3]

def tmFiber10Prefix4 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4]

def tmFiber10Prefix5 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5]

def tmFiber10Prefix6 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6]

def tmFiber10Prefix7 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7]

def tmFiber10Prefix8 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8]

def tmFiber10Prefix9 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9]

def tmFiber10Prefix10 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10]

def tmFiber10Prefix11 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11]

def tmFiber10Prefix12 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12]

def tmFiber10Prefix13 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13]

def tmFiber10Prefix14 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14]

def tmFiber10Prefix15 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15]

def tmFiber10Prefix16 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16]

def tmFiber10Prefix17 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17]

def tmFiber10Prefix18 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18]

def tmFiber10Prefix19 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19]

def tmFiber10Prefix20 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20]

def tmFiber10Prefix21 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21]

def tmFiber10Prefix22 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22]

def tmFiber10Prefix23 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23]

def tmFiber10Prefix24 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24]

def tmFiber10Prefix25 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25]

def tmFiber10Prefix26 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26]

def tmFiber10Prefix27 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27]

def tmFiber10Prefix28 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28]

def tmFiber10Prefix29 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29]

def tmFiber10Prefix30 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30]

def tmFiber10Prefix31 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31]

def tmFiber10Prefix32 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32]

def tmFiber10Prefix33 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33]

def tmFiber10Prefix34 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34]

def tmFiber10Prefix35 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35]

def tmFiber10Prefix36 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36]

def tmFiber10Prefix37 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37]

def tmFiber10Prefix38 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38]

def tmFiber10Prefix39 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39]

def tmFiber10Prefix40 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40]

def tmFiber10Prefix41 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41]

def tmFiber10Prefix42 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42]

def tmFiber10Prefix43 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43]

def tmFiber10Prefix44 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44]

def tmFiber10Prefix45 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45]

def tmFiber10Prefix46 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46]

def tmFiber10Prefix47 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47]

def tmFiber10Prefix48 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48]

def tmFiber10Prefix49 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49]

def tmFiber10Prefix50 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50]

def tmFiber10Prefix51 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51]

def tmFiber10Prefix52 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52]

def tmFiber10Prefix53 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53]

def tmFiber10Prefix54 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54]

def tmFiber10Prefix55 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55]

def tmFiber10Prefix56 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56]

def tmFiber10Prefix57 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57]

def tmFiber10Prefix58 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58]

def tmFiber10Prefix59 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59]

def tmFiber10Prefix60 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60]

def tmFiber10Prefix61 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61]

def tmFiber10Prefix62 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62]

def tmFiber10Prefix63 : List (List TauState) :=
  [tmFiber10StateAt 0, tmFiber10StateAt 1, tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]

theorem tmFiber10ReverseRow_1_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 1) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk0_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 0) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber10ReverseSingleStep1 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 0) (tmFiber10StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 0) (tmFiber10StateAt 1)
    (tmFiber10RowAt 1).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 1) (by decide) tmFiber10ReverseRow_1_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_2_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 2) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk1_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 2) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber10ReverseSingleStep2 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 1) (tmFiber10StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 1) (tmFiber10StateAt 2)
    (tmFiber10RowAt 2).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 2) (by decide) tmFiber10ReverseRow_2_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_3_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 3) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk1_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 2) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber10ReverseSingleStep3 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 0) (tmFiber10StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 0) (tmFiber10StateAt 3)
    (tmFiber10RowAt 3).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 3) (by decide) tmFiber10ReverseRow_3_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_4_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 4) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk2_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 4) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber10ReverseSingleStep4 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 0) (tmFiber10StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 0) (tmFiber10StateAt 4)
    (tmFiber10RowAt 4).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 4) (by decide) tmFiber10ReverseRow_4_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_5_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 5) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk2_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 4) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber10ReverseSingleStep5 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 1) (tmFiber10StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 1) (tmFiber10StateAt 5)
    (tmFiber10RowAt 5).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 5) (by decide) tmFiber10ReverseRow_5_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_6_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 6) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk3_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 6) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber10ReverseSingleStep6 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 4) (tmFiber10StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 4) (tmFiber10StateAt 6)
    (tmFiber10RowAt 6).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 6) (by decide) tmFiber10ReverseRow_6_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_7_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 7) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk3_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 6) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber10ReverseSingleStep7 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 3) (tmFiber10StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 3) (tmFiber10StateAt 7)
    (tmFiber10RowAt 7).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 7) (by decide) tmFiber10ReverseRow_7_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_8_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 8) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk4_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 8) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber10ReverseSingleStep8 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 0) (tmFiber10StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 0) (tmFiber10StateAt 8)
    (tmFiber10RowAt 8).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 8) (by decide) tmFiber10ReverseRow_8_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_9_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 9) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk4_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 8) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber10ReverseSingleStep9 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 1) (tmFiber10StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 1) (tmFiber10StateAt 9)
    (tmFiber10RowAt 9).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 9) (by decide) tmFiber10ReverseRow_9_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_10_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 10) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk5_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 10) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber10ReverseSingleStep10 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 2) (tmFiber10StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 2) (tmFiber10StateAt 10)
    (tmFiber10RowAt 10).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 10) (by decide) tmFiber10ReverseRow_10_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_11_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 11) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk5_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 10) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber10ReverseSingleStep11 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 3) (tmFiber10StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 3) (tmFiber10StateAt 11)
    (tmFiber10RowAt 11).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 11) (by decide) tmFiber10ReverseRow_11_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_12_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 12) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk6_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 12) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber10ReverseSingleStep12 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 4) (tmFiber10StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 4) (tmFiber10StateAt 12)
    (tmFiber10RowAt 12).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 12) (by decide) tmFiber10ReverseRow_12_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_13_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 13) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk6_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 12) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber10ReverseSingleStep13 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 5) (tmFiber10StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 5) (tmFiber10StateAt 13)
    (tmFiber10RowAt 13).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 13) (by decide) tmFiber10ReverseRow_13_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_14_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 14) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk7_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 14) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber10ReverseSingleStep14 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 6) (tmFiber10StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 6) (tmFiber10StateAt 14)
    (tmFiber10RowAt 14).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 14) (by decide) tmFiber10ReverseRow_14_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_15_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 15) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk7_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 14) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber10ReverseSingleStep15 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 7) (tmFiber10StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 7) (tmFiber10StateAt 15)
    (tmFiber10RowAt 15).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 15) (by decide) tmFiber10ReverseRow_15_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_16_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 16) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk8_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 16) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber10ReverseSingleStep16 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 0) (tmFiber10StateAt 16) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 0) (tmFiber10StateAt 16)
    (tmFiber10RowAt 16).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 16) (by decide) tmFiber10ReverseRow_16_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_17_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 17) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk8_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 16) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber10ReverseSingleStep17 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 1) (tmFiber10StateAt 17) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 1) (tmFiber10StateAt 17)
    (tmFiber10RowAt 17).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 17) (by decide) tmFiber10ReverseRow_17_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_18_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 18) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk9_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 18) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber10ReverseSingleStep18 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 2) (tmFiber10StateAt 18) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 2) (tmFiber10StateAt 18)
    (tmFiber10RowAt 18).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 18) (by decide) tmFiber10ReverseRow_18_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_19_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 19) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk9_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 18) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber10ReverseSingleStep19 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 3) (tmFiber10StateAt 19) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 3) (tmFiber10StateAt 19)
    (tmFiber10RowAt 19).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 19) (by decide) tmFiber10ReverseRow_19_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_20_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 20) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk10_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 20) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber10ReverseSingleStep20 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 4) (tmFiber10StateAt 20) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 4) (tmFiber10StateAt 20)
    (tmFiber10RowAt 20).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 20) (by decide) tmFiber10ReverseRow_20_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_21_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 21) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk10_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 20) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber10ReverseSingleStep21 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 5) (tmFiber10StateAt 21) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 5) (tmFiber10StateAt 21)
    (tmFiber10RowAt 21).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 21) (by decide) tmFiber10ReverseRow_21_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_22_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 22) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk11_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 22) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber10ReverseSingleStep22 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 6) (tmFiber10StateAt 22) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 6) (tmFiber10StateAt 22)
    (tmFiber10RowAt 22).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 22) (by decide) tmFiber10ReverseRow_22_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_23_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 23) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk11_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 22) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber10ReverseSingleStep23 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 7) (tmFiber10StateAt 23) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 7) (tmFiber10StateAt 23)
    (tmFiber10RowAt 23).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 23) (by decide) tmFiber10ReverseRow_23_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_24_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 24) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk12_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 24) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber10ReverseSingleStep24 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 8) (tmFiber10StateAt 24) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 8) (tmFiber10StateAt 24)
    (tmFiber10RowAt 24).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 24) (by decide) tmFiber10ReverseRow_24_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_25_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 25) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk12_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 24) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber10ReverseSingleStep25 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 9) (tmFiber10StateAt 25) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 9) (tmFiber10StateAt 25)
    (tmFiber10RowAt 25).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 25) (by decide) tmFiber10ReverseRow_25_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_26_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 26) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk13_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 26) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber10ReverseSingleStep26 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 10) (tmFiber10StateAt 26) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 10) (tmFiber10StateAt 26)
    (tmFiber10RowAt 26).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 26) (by decide) tmFiber10ReverseRow_26_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_27_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 27) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk13_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 26) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber10ReverseSingleStep27 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 11) (tmFiber10StateAt 27) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 11) (tmFiber10StateAt 27)
    (tmFiber10RowAt 27).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 27) (by decide) tmFiber10ReverseRow_27_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_28_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 28) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk14_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 28) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber10ReverseSingleStep28 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 12) (tmFiber10StateAt 28) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 12) (tmFiber10StateAt 28)
    (tmFiber10RowAt 28).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 28) (by decide) tmFiber10ReverseRow_28_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_29_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 29) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk14_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 28) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber10ReverseSingleStep29 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 13) (tmFiber10StateAt 29) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 13) (tmFiber10StateAt 29)
    (tmFiber10RowAt 29).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 29) (by decide) tmFiber10ReverseRow_29_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_30_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 30) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk15_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 30) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber10ReverseSingleStep30 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 14) (tmFiber10StateAt 30) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 14) (tmFiber10StateAt 30)
    (tmFiber10RowAt 30).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 30) (by decide) tmFiber10ReverseRow_30_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_31_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 31) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk15_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 30) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber10ReverseSingleStep31 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 15) (tmFiber10StateAt 31) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 15) (tmFiber10StateAt 31)
    (tmFiber10RowAt 31).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 31) (by decide) tmFiber10ReverseRow_31_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_32_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 32) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk16_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 32) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber10ReverseSingleStep32 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 36) (tmFiber10StateAt 32) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 36) (tmFiber10StateAt 32)
    (tmFiber10RowAt 32).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 32) (by decide) tmFiber10ReverseRow_32_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_33_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 33) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk16_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 32) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber10ReverseSingleStep33 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 37) (tmFiber10StateAt 33) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 37) (tmFiber10StateAt 33)
    (tmFiber10RowAt 33).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 33) (by decide) tmFiber10ReverseRow_33_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_34_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 34) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk17_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 34) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber10ReverseSingleStep34 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 20) (tmFiber10StateAt 34) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 20) (tmFiber10StateAt 34)
    (tmFiber10RowAt 34).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 34) (by decide) tmFiber10ReverseRow_34_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_35_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 35) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk17_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 34) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber10ReverseSingleStep35 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 21) (tmFiber10StateAt 35) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 21) (tmFiber10StateAt 35)
    (tmFiber10RowAt 35).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 35) (by decide) tmFiber10ReverseRow_35_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_36_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 36) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk18_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 36) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber10ReverseSingleStep36 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 16) (tmFiber10StateAt 36) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 16) (tmFiber10StateAt 36)
    (tmFiber10RowAt 36).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 36) (by decide) tmFiber10ReverseRow_36_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_37_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 37) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk18_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 36) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber10ReverseSingleStep37 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 17) (tmFiber10StateAt 37) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 17) (tmFiber10StateAt 37)
    (tmFiber10RowAt 37).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 37) (by decide) tmFiber10ReverseRow_37_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_38_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 38) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk19_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 38) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber10ReverseSingleStep38 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 18) (tmFiber10StateAt 38) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 18) (tmFiber10StateAt 38)
    (tmFiber10RowAt 38).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 38) (by decide) tmFiber10ReverseRow_38_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_39_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 39) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk19_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 38) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber10ReverseSingleStep39 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 19) (tmFiber10StateAt 39) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 19) (tmFiber10StateAt 39)
    (tmFiber10RowAt 39).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 39) (by decide) tmFiber10ReverseRow_39_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_40_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 40) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk20_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 40) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber10ReverseSingleStep40 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 44) (tmFiber10StateAt 40) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 44) (tmFiber10StateAt 40)
    (tmFiber10RowAt 40).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 40) (by decide) tmFiber10ReverseRow_40_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_41_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 41) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk20_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 40) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber10ReverseSingleStep41 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 45) (tmFiber10StateAt 41) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 45) (tmFiber10StateAt 41)
    (tmFiber10RowAt 41).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 41) (by decide) tmFiber10ReverseRow_41_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_42_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 42) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk21_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 42) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber10ReverseSingleStep42 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 58) (tmFiber10StateAt 42) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 58) (tmFiber10StateAt 42)
    (tmFiber10RowAt 42).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 42) (by decide) tmFiber10ReverseRow_42_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_43_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 43) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk21_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 42) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber10ReverseSingleStep43 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 59) (tmFiber10StateAt 43) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 59) (tmFiber10StateAt 43)
    (tmFiber10RowAt 43).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 43) (by decide) tmFiber10ReverseRow_43_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_44_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 44) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk22_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 44) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber10ReverseSingleStep44 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 60) (tmFiber10StateAt 44) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 60) (tmFiber10StateAt 44)
    (tmFiber10RowAt 44).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 44) (by decide) tmFiber10ReverseRow_44_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_45_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 45) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk22_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 44) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber10ReverseSingleStep45 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 61) (tmFiber10StateAt 45) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 61) (tmFiber10StateAt 45)
    (tmFiber10RowAt 45).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 45) (by decide) tmFiber10ReverseRow_45_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_46_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 46) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk23_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 46) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber10ReverseSingleStep46 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 62) (tmFiber10StateAt 46) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 62) (tmFiber10StateAt 46)
    (tmFiber10RowAt 46).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 46) (by decide) tmFiber10ReverseRow_46_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_47_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 47) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk23_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 46) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber10ReverseSingleStep47 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 63) (tmFiber10StateAt 47) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 63) (tmFiber10StateAt 47)
    (tmFiber10RowAt 47).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 47) (by decide) tmFiber10ReverseRow_47_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_48_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 48) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk24_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 48) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber10ReverseSingleStep48 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 52) (tmFiber10StateAt 48) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 52) (tmFiber10StateAt 48)
    (tmFiber10RowAt 48).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 48) (by decide) tmFiber10ReverseRow_48_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_49_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 49) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk24_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 48) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber10ReverseSingleStep49 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 53) (tmFiber10StateAt 49) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 53) (tmFiber10StateAt 49)
    (tmFiber10RowAt 49).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 49) (by decide) tmFiber10ReverseRow_49_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_50_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 50) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk25_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 50) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber10ReverseSingleStep50 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 12) (tmFiber10StateAt 50) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 12) (tmFiber10StateAt 50)
    (tmFiber10RowAt 50).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 50) (by decide) tmFiber10ReverseRow_50_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_51_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 51) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk25_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 50) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber10ReverseSingleStep51 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 13) (tmFiber10StateAt 51) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 13) (tmFiber10StateAt 51)
    (tmFiber10RowAt 51).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 51) (by decide) tmFiber10ReverseRow_51_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_52_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 52) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk26_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 52) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber10ReverseSingleStep52 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 8) (tmFiber10StateAt 52) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 8) (tmFiber10StateAt 52)
    (tmFiber10RowAt 52).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 52) (by decide) tmFiber10ReverseRow_52_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_53_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 53) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk26_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 52) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber10ReverseSingleStep53 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 9) (tmFiber10StateAt 53) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 9) (tmFiber10StateAt 53)
    (tmFiber10RowAt 53).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 53) (by decide) tmFiber10ReverseRow_53_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_54_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 54) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk27_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 54) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber10ReverseSingleStep54 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 10) (tmFiber10StateAt 54) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 10) (tmFiber10StateAt 54)
    (tmFiber10RowAt 54).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 54) (by decide) tmFiber10ReverseRow_54_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_55_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 55) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk27_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 54) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber10ReverseSingleStep55 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 11) (tmFiber10StateAt 55) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 11) (tmFiber10StateAt 55)
    (tmFiber10RowAt 55).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 55) (by decide) tmFiber10ReverseRow_55_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_56_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 56) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk28_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 56) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber10ReverseSingleStep56 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 60) (tmFiber10StateAt 56) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 60) (tmFiber10StateAt 56)
    (tmFiber10RowAt 56).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 56) (by decide) tmFiber10ReverseRow_56_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_57_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 57) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk28_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 56) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber10ReverseSingleStep57 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 61) (tmFiber10StateAt 57) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 61) (tmFiber10StateAt 57)
    (tmFiber10RowAt 57).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 57) (by decide) tmFiber10ReverseRow_57_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_58_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 58) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk29_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 58) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber10ReverseSingleStep58 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 4) (tmFiber10StateAt 58) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 4) (tmFiber10StateAt 58)
    (tmFiber10RowAt 58).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 58) (by decide) tmFiber10ReverseRow_58_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_59_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 59) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk29_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 58) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber10ReverseSingleStep59 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 5) (tmFiber10StateAt 59) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 5) (tmFiber10StateAt 59)
    (tmFiber10RowAt 59).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 59) (by decide) tmFiber10ReverseRow_59_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_60_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 60) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk30_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 60) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber10ReverseSingleStep60 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 0) (tmFiber10StateAt 60) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 0) (tmFiber10StateAt 60)
    (tmFiber10RowAt 60).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 60) (by decide) tmFiber10ReverseRow_60_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_61_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 61) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk30_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 60) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber10ReverseSingleStep61 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 1) (tmFiber10StateAt 61) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 1) (tmFiber10StateAt 61)
    (tmFiber10RowAt 61).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 61) (by decide) tmFiber10ReverseRow_61_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_62_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 62) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk31_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 62) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber10ReverseSingleStep62 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 2) (tmFiber10StateAt 62) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 2) (tmFiber10StateAt 62)
    (tmFiber10RowAt 62).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 62) (by decide) tmFiber10ReverseRow_62_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10ReverseRow_63_ok :
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 63) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber10Chunk31_ok
  change (tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 62) &&
    tmRowReverseValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber10ReverseSingleStep63 :
    chainSingleKempeStep tmWord (tmFiber10StateAt 3) (tmFiber10StateAt 63) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber10StateAt 3) (tmFiber10StateAt 63)
    (tmFiber10RowAt 63).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber10Key tmFiber10Expected
        (tmFiber10RowAt 63) (by decide) tmFiber10ReverseRow_63_ok
      simpa [tmFiber10StateAt, tmFiber10RowAt, tmFiber10Rows, listGetD, directRow] using h)

theorem tmFiber10State1_in_pass1_prefix1 :
    tmFiber10StateAt 1 ∈ chainClosureStep tmWord tmFiber10Prefix1 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 0 ∈
      chainClosureStep tmWord tmFiber10Prefix0 ([tmFiber10StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber10Prefix0
      ([tmFiber10StateAt 0]) (tmFiber10StateAt 0) (by simp)
  rw [show tmFiber10Prefix1 = tmFiber10Prefix0 ++ [tmFiber10StateAt 1] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 1) []
    (chainClosureStep tmWord tmFiber10Prefix0 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 0) hparentBefore tmFiber10ReverseSingleStep1

theorem tmFiber10State1_in_pass1_full :
    tmFiber10StateAt 1 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix1 ++ [tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix1 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 1) tmFiber10State1_in_pass1_prefix1

theorem tmFiber10State2_in_pass1_prefix2 :
    tmFiber10StateAt 2 ∈ chainClosureStep tmWord tmFiber10Prefix2 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 1 ∈
      chainClosureStep tmWord tmFiber10Prefix1 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix1 = tmFiber10Prefix1 ++ [] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord []
      (chainClosureStep tmWord tmFiber10Prefix1 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 1) tmFiber10State1_in_pass1_prefix1
  rw [show tmFiber10Prefix2 = tmFiber10Prefix1 ++ [tmFiber10StateAt 2] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 2) []
    (chainClosureStep tmWord tmFiber10Prefix1 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 1) hparentBefore tmFiber10ReverseSingleStep2

theorem tmFiber10State2_in_pass1_full :
    tmFiber10StateAt 2 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix2 ++ [tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix2 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 2) tmFiber10State2_in_pass1_prefix2

theorem tmFiber10State3_in_pass1_prefix3 :
    tmFiber10StateAt 3 ∈ chainClosureStep tmWord tmFiber10Prefix3 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 0 ∈
      chainClosureStep tmWord tmFiber10Prefix2 ([tmFiber10StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber10Prefix2
      ([tmFiber10StateAt 0]) (tmFiber10StateAt 0) (by simp)
  rw [show tmFiber10Prefix3 = tmFiber10Prefix2 ++ [tmFiber10StateAt 3] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 3) []
    (chainClosureStep tmWord tmFiber10Prefix2 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 0) hparentBefore tmFiber10ReverseSingleStep3

theorem tmFiber10State3_in_pass1_full :
    tmFiber10StateAt 3 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix3 ++ [tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix3 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 3) tmFiber10State3_in_pass1_prefix3

theorem tmFiber10State4_in_pass1_prefix4 :
    tmFiber10StateAt 4 ∈ chainClosureStep tmWord tmFiber10Prefix4 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 0 ∈
      chainClosureStep tmWord tmFiber10Prefix3 ([tmFiber10StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber10Prefix3
      ([tmFiber10StateAt 0]) (tmFiber10StateAt 0) (by simp)
  rw [show tmFiber10Prefix4 = tmFiber10Prefix3 ++ [tmFiber10StateAt 4] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 4) []
    (chainClosureStep tmWord tmFiber10Prefix3 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 0) hparentBefore tmFiber10ReverseSingleStep4

theorem tmFiber10State4_in_pass1_full :
    tmFiber10StateAt 4 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix4 ++ [tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix4 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 4) tmFiber10State4_in_pass1_prefix4

theorem tmFiber10State5_in_pass1_prefix5 :
    tmFiber10StateAt 5 ∈ chainClosureStep tmWord tmFiber10Prefix5 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 1 ∈
      chainClosureStep tmWord tmFiber10Prefix4 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix4 = tmFiber10Prefix1 ++ [tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4]
      (chainClosureStep tmWord tmFiber10Prefix1 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 1) tmFiber10State1_in_pass1_prefix1
  rw [show tmFiber10Prefix5 = tmFiber10Prefix4 ++ [tmFiber10StateAt 5] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 5) []
    (chainClosureStep tmWord tmFiber10Prefix4 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 1) hparentBefore tmFiber10ReverseSingleStep5

theorem tmFiber10State5_in_pass1_full :
    tmFiber10StateAt 5 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix5 ++ [tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix5 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 5) tmFiber10State5_in_pass1_prefix5

theorem tmFiber10State6_in_pass1_prefix6 :
    tmFiber10StateAt 6 ∈ chainClosureStep tmWord tmFiber10Prefix6 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 4 ∈
      chainClosureStep tmWord tmFiber10Prefix5 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix5 = tmFiber10Prefix4 ++ [tmFiber10StateAt 5] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 5]
      (chainClosureStep tmWord tmFiber10Prefix4 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 4) tmFiber10State4_in_pass1_prefix4
  rw [show tmFiber10Prefix6 = tmFiber10Prefix5 ++ [tmFiber10StateAt 6] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 6) []
    (chainClosureStep tmWord tmFiber10Prefix5 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 4) hparentBefore tmFiber10ReverseSingleStep6

theorem tmFiber10State6_in_pass1_full :
    tmFiber10StateAt 6 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix6 ++ [tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix6 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 6) tmFiber10State6_in_pass1_prefix6

theorem tmFiber10State7_in_pass1_prefix7 :
    tmFiber10StateAt 7 ∈ chainClosureStep tmWord tmFiber10Prefix7 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 3 ∈
      chainClosureStep tmWord tmFiber10Prefix6 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix6 = tmFiber10Prefix3 ++ [tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6]
      (chainClosureStep tmWord tmFiber10Prefix3 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 3) tmFiber10State3_in_pass1_prefix3
  rw [show tmFiber10Prefix7 = tmFiber10Prefix6 ++ [tmFiber10StateAt 7] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 7) []
    (chainClosureStep tmWord tmFiber10Prefix6 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 3) hparentBefore tmFiber10ReverseSingleStep7

theorem tmFiber10State7_in_pass1_full :
    tmFiber10StateAt 7 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix7 ++ [tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix7 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 7) tmFiber10State7_in_pass1_prefix7

theorem tmFiber10State8_in_pass1_prefix8 :
    tmFiber10StateAt 8 ∈ chainClosureStep tmWord tmFiber10Prefix8 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 0 ∈
      chainClosureStep tmWord tmFiber10Prefix7 ([tmFiber10StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber10Prefix7
      ([tmFiber10StateAt 0]) (tmFiber10StateAt 0) (by simp)
  rw [show tmFiber10Prefix8 = tmFiber10Prefix7 ++ [tmFiber10StateAt 8] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 8) []
    (chainClosureStep tmWord tmFiber10Prefix7 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 0) hparentBefore tmFiber10ReverseSingleStep8

theorem tmFiber10State8_in_pass1_full :
    tmFiber10StateAt 8 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix8 ++ [tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix8 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 8) tmFiber10State8_in_pass1_prefix8

theorem tmFiber10State9_in_pass1_prefix9 :
    tmFiber10StateAt 9 ∈ chainClosureStep tmWord tmFiber10Prefix9 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 1 ∈
      chainClosureStep tmWord tmFiber10Prefix8 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix8 = tmFiber10Prefix1 ++ [tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8]
      (chainClosureStep tmWord tmFiber10Prefix1 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 1) tmFiber10State1_in_pass1_prefix1
  rw [show tmFiber10Prefix9 = tmFiber10Prefix8 ++ [tmFiber10StateAt 9] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 9) []
    (chainClosureStep tmWord tmFiber10Prefix8 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 1) hparentBefore tmFiber10ReverseSingleStep9

theorem tmFiber10State9_in_pass1_full :
    tmFiber10StateAt 9 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix9 ++ [tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix9 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 9) tmFiber10State9_in_pass1_prefix9

theorem tmFiber10State10_in_pass1_prefix10 :
    tmFiber10StateAt 10 ∈ chainClosureStep tmWord tmFiber10Prefix10 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 2 ∈
      chainClosureStep tmWord tmFiber10Prefix9 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix9 = tmFiber10Prefix2 ++ [tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9]
      (chainClosureStep tmWord tmFiber10Prefix2 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 2) tmFiber10State2_in_pass1_prefix2
  rw [show tmFiber10Prefix10 = tmFiber10Prefix9 ++ [tmFiber10StateAt 10] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 10) []
    (chainClosureStep tmWord tmFiber10Prefix9 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 2) hparentBefore tmFiber10ReverseSingleStep10

theorem tmFiber10State10_in_pass1_full :
    tmFiber10StateAt 10 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix10 ++ [tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix10 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 10) tmFiber10State10_in_pass1_prefix10

theorem tmFiber10State11_in_pass1_prefix11 :
    tmFiber10StateAt 11 ∈ chainClosureStep tmWord tmFiber10Prefix11 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 3 ∈
      chainClosureStep tmWord tmFiber10Prefix10 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix10 = tmFiber10Prefix3 ++ [tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10]
      (chainClosureStep tmWord tmFiber10Prefix3 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 3) tmFiber10State3_in_pass1_prefix3
  rw [show tmFiber10Prefix11 = tmFiber10Prefix10 ++ [tmFiber10StateAt 11] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 11) []
    (chainClosureStep tmWord tmFiber10Prefix10 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 3) hparentBefore tmFiber10ReverseSingleStep11

theorem tmFiber10State11_in_pass1_full :
    tmFiber10StateAt 11 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix11 ++ [tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix11 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 11) tmFiber10State11_in_pass1_prefix11

theorem tmFiber10State12_in_pass1_prefix12 :
    tmFiber10StateAt 12 ∈ chainClosureStep tmWord tmFiber10Prefix12 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 4 ∈
      chainClosureStep tmWord tmFiber10Prefix11 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix11 = tmFiber10Prefix4 ++ [tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11]
      (chainClosureStep tmWord tmFiber10Prefix4 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 4) tmFiber10State4_in_pass1_prefix4
  rw [show tmFiber10Prefix12 = tmFiber10Prefix11 ++ [tmFiber10StateAt 12] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 12) []
    (chainClosureStep tmWord tmFiber10Prefix11 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 4) hparentBefore tmFiber10ReverseSingleStep12

theorem tmFiber10State12_in_pass1_full :
    tmFiber10StateAt 12 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix12 ++ [tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix12 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 12) tmFiber10State12_in_pass1_prefix12

theorem tmFiber10State13_in_pass1_prefix13 :
    tmFiber10StateAt 13 ∈ chainClosureStep tmWord tmFiber10Prefix13 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 5 ∈
      chainClosureStep tmWord tmFiber10Prefix12 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix12 = tmFiber10Prefix5 ++ [tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12]
      (chainClosureStep tmWord tmFiber10Prefix5 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 5) tmFiber10State5_in_pass1_prefix5
  rw [show tmFiber10Prefix13 = tmFiber10Prefix12 ++ [tmFiber10StateAt 13] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 13) []
    (chainClosureStep tmWord tmFiber10Prefix12 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 5) hparentBefore tmFiber10ReverseSingleStep13

theorem tmFiber10State13_in_pass1_full :
    tmFiber10StateAt 13 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix13 ++ [tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix13 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 13) tmFiber10State13_in_pass1_prefix13

theorem tmFiber10State14_in_pass1_prefix14 :
    tmFiber10StateAt 14 ∈ chainClosureStep tmWord tmFiber10Prefix14 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 6 ∈
      chainClosureStep tmWord tmFiber10Prefix13 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix13 = tmFiber10Prefix6 ++ [tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13]
      (chainClosureStep tmWord tmFiber10Prefix6 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 6) tmFiber10State6_in_pass1_prefix6
  rw [show tmFiber10Prefix14 = tmFiber10Prefix13 ++ [tmFiber10StateAt 14] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 14) []
    (chainClosureStep tmWord tmFiber10Prefix13 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 6) hparentBefore tmFiber10ReverseSingleStep14

theorem tmFiber10State14_in_pass1_full :
    tmFiber10StateAt 14 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix14 ++ [tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix14 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 14) tmFiber10State14_in_pass1_prefix14

theorem tmFiber10State15_in_pass1_prefix15 :
    tmFiber10StateAt 15 ∈ chainClosureStep tmWord tmFiber10Prefix15 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 7 ∈
      chainClosureStep tmWord tmFiber10Prefix14 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix14 = tmFiber10Prefix7 ++ [tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14]
      (chainClosureStep tmWord tmFiber10Prefix7 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 7) tmFiber10State7_in_pass1_prefix7
  rw [show tmFiber10Prefix15 = tmFiber10Prefix14 ++ [tmFiber10StateAt 15] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 15) []
    (chainClosureStep tmWord tmFiber10Prefix14 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 7) hparentBefore tmFiber10ReverseSingleStep15

theorem tmFiber10State15_in_pass1_full :
    tmFiber10StateAt 15 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix15 ++ [tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix15 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 15) tmFiber10State15_in_pass1_prefix15

theorem tmFiber10State16_in_pass1_prefix16 :
    tmFiber10StateAt 16 ∈ chainClosureStep tmWord tmFiber10Prefix16 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 0 ∈
      chainClosureStep tmWord tmFiber10Prefix15 ([tmFiber10StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber10Prefix15
      ([tmFiber10StateAt 0]) (tmFiber10StateAt 0) (by simp)
  rw [show tmFiber10Prefix16 = tmFiber10Prefix15 ++ [tmFiber10StateAt 16] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 16) []
    (chainClosureStep tmWord tmFiber10Prefix15 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 0) hparentBefore tmFiber10ReverseSingleStep16

theorem tmFiber10State16_in_pass1_full :
    tmFiber10StateAt 16 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix16 ++ [tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix16 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 16) tmFiber10State16_in_pass1_prefix16

theorem tmFiber10State17_in_pass1_prefix17 :
    tmFiber10StateAt 17 ∈ chainClosureStep tmWord tmFiber10Prefix17 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 1 ∈
      chainClosureStep tmWord tmFiber10Prefix16 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix16 = tmFiber10Prefix1 ++ [tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16]
      (chainClosureStep tmWord tmFiber10Prefix1 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 1) tmFiber10State1_in_pass1_prefix1
  rw [show tmFiber10Prefix17 = tmFiber10Prefix16 ++ [tmFiber10StateAt 17] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 17) []
    (chainClosureStep tmWord tmFiber10Prefix16 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 1) hparentBefore tmFiber10ReverseSingleStep17

theorem tmFiber10State17_in_pass1_full :
    tmFiber10StateAt 17 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix17 ++ [tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix17 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 17) tmFiber10State17_in_pass1_prefix17

theorem tmFiber10State18_in_pass1_prefix18 :
    tmFiber10StateAt 18 ∈ chainClosureStep tmWord tmFiber10Prefix18 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 2 ∈
      chainClosureStep tmWord tmFiber10Prefix17 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix17 = tmFiber10Prefix2 ++ [tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17]
      (chainClosureStep tmWord tmFiber10Prefix2 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 2) tmFiber10State2_in_pass1_prefix2
  rw [show tmFiber10Prefix18 = tmFiber10Prefix17 ++ [tmFiber10StateAt 18] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 18) []
    (chainClosureStep tmWord tmFiber10Prefix17 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 2) hparentBefore tmFiber10ReverseSingleStep18

theorem tmFiber10State18_in_pass1_full :
    tmFiber10StateAt 18 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix18 ++ [tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix18 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 18) tmFiber10State18_in_pass1_prefix18

theorem tmFiber10State19_in_pass1_prefix19 :
    tmFiber10StateAt 19 ∈ chainClosureStep tmWord tmFiber10Prefix19 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 3 ∈
      chainClosureStep tmWord tmFiber10Prefix18 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix18 = tmFiber10Prefix3 ++ [tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18]
      (chainClosureStep tmWord tmFiber10Prefix3 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 3) tmFiber10State3_in_pass1_prefix3
  rw [show tmFiber10Prefix19 = tmFiber10Prefix18 ++ [tmFiber10StateAt 19] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 19) []
    (chainClosureStep tmWord tmFiber10Prefix18 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 3) hparentBefore tmFiber10ReverseSingleStep19

theorem tmFiber10State19_in_pass1_full :
    tmFiber10StateAt 19 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix19 ++ [tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix19 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 19) tmFiber10State19_in_pass1_prefix19

theorem tmFiber10State20_in_pass1_prefix20 :
    tmFiber10StateAt 20 ∈ chainClosureStep tmWord tmFiber10Prefix20 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 4 ∈
      chainClosureStep tmWord tmFiber10Prefix19 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix19 = tmFiber10Prefix4 ++ [tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19]
      (chainClosureStep tmWord tmFiber10Prefix4 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 4) tmFiber10State4_in_pass1_prefix4
  rw [show tmFiber10Prefix20 = tmFiber10Prefix19 ++ [tmFiber10StateAt 20] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 20) []
    (chainClosureStep tmWord tmFiber10Prefix19 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 4) hparentBefore tmFiber10ReverseSingleStep20

theorem tmFiber10State20_in_pass1_full :
    tmFiber10StateAt 20 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix20 ++ [tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix20 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 20) tmFiber10State20_in_pass1_prefix20

theorem tmFiber10State21_in_pass1_prefix21 :
    tmFiber10StateAt 21 ∈ chainClosureStep tmWord tmFiber10Prefix21 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 5 ∈
      chainClosureStep tmWord tmFiber10Prefix20 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix20 = tmFiber10Prefix5 ++ [tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20]
      (chainClosureStep tmWord tmFiber10Prefix5 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 5) tmFiber10State5_in_pass1_prefix5
  rw [show tmFiber10Prefix21 = tmFiber10Prefix20 ++ [tmFiber10StateAt 21] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 21) []
    (chainClosureStep tmWord tmFiber10Prefix20 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 5) hparentBefore tmFiber10ReverseSingleStep21

theorem tmFiber10State21_in_pass1_full :
    tmFiber10StateAt 21 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix21 ++ [tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix21 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 21) tmFiber10State21_in_pass1_prefix21

theorem tmFiber10State22_in_pass1_prefix22 :
    tmFiber10StateAt 22 ∈ chainClosureStep tmWord tmFiber10Prefix22 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 6 ∈
      chainClosureStep tmWord tmFiber10Prefix21 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix21 = tmFiber10Prefix6 ++ [tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21]
      (chainClosureStep tmWord tmFiber10Prefix6 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 6) tmFiber10State6_in_pass1_prefix6
  rw [show tmFiber10Prefix22 = tmFiber10Prefix21 ++ [tmFiber10StateAt 22] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 22) []
    (chainClosureStep tmWord tmFiber10Prefix21 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 6) hparentBefore tmFiber10ReverseSingleStep22

theorem tmFiber10State22_in_pass1_full :
    tmFiber10StateAt 22 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix22 ++ [tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix22 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 22) tmFiber10State22_in_pass1_prefix22

theorem tmFiber10State23_in_pass1_prefix23 :
    tmFiber10StateAt 23 ∈ chainClosureStep tmWord tmFiber10Prefix23 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 7 ∈
      chainClosureStep tmWord tmFiber10Prefix22 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix22 = tmFiber10Prefix7 ++ [tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22]
      (chainClosureStep tmWord tmFiber10Prefix7 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 7) tmFiber10State7_in_pass1_prefix7
  rw [show tmFiber10Prefix23 = tmFiber10Prefix22 ++ [tmFiber10StateAt 23] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 23) []
    (chainClosureStep tmWord tmFiber10Prefix22 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 7) hparentBefore tmFiber10ReverseSingleStep23

theorem tmFiber10State23_in_pass1_full :
    tmFiber10StateAt 23 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix23 ++ [tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix23 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 23) tmFiber10State23_in_pass1_prefix23

theorem tmFiber10State24_in_pass1_prefix24 :
    tmFiber10StateAt 24 ∈ chainClosureStep tmWord tmFiber10Prefix24 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 8 ∈
      chainClosureStep tmWord tmFiber10Prefix23 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix23 = tmFiber10Prefix8 ++ [tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23]
      (chainClosureStep tmWord tmFiber10Prefix8 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 8) tmFiber10State8_in_pass1_prefix8
  rw [show tmFiber10Prefix24 = tmFiber10Prefix23 ++ [tmFiber10StateAt 24] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 24) []
    (chainClosureStep tmWord tmFiber10Prefix23 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 8) hparentBefore tmFiber10ReverseSingleStep24

theorem tmFiber10State24_in_pass1_full :
    tmFiber10StateAt 24 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix24 ++ [tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix24 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 24) tmFiber10State24_in_pass1_prefix24

theorem tmFiber10State25_in_pass1_prefix25 :
    tmFiber10StateAt 25 ∈ chainClosureStep tmWord tmFiber10Prefix25 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 9 ∈
      chainClosureStep tmWord tmFiber10Prefix24 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix24 = tmFiber10Prefix9 ++ [tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24]
      (chainClosureStep tmWord tmFiber10Prefix9 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 9) tmFiber10State9_in_pass1_prefix9
  rw [show tmFiber10Prefix25 = tmFiber10Prefix24 ++ [tmFiber10StateAt 25] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 25) []
    (chainClosureStep tmWord tmFiber10Prefix24 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 9) hparentBefore tmFiber10ReverseSingleStep25

theorem tmFiber10State25_in_pass1_full :
    tmFiber10StateAt 25 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix25 ++ [tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix25 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 25) tmFiber10State25_in_pass1_prefix25

theorem tmFiber10State26_in_pass1_prefix26 :
    tmFiber10StateAt 26 ∈ chainClosureStep tmWord tmFiber10Prefix26 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 10 ∈
      chainClosureStep tmWord tmFiber10Prefix25 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix25 = tmFiber10Prefix10 ++ [tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25]
      (chainClosureStep tmWord tmFiber10Prefix10 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 10) tmFiber10State10_in_pass1_prefix10
  rw [show tmFiber10Prefix26 = tmFiber10Prefix25 ++ [tmFiber10StateAt 26] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 26) []
    (chainClosureStep tmWord tmFiber10Prefix25 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 10) hparentBefore tmFiber10ReverseSingleStep26

theorem tmFiber10State26_in_pass1_full :
    tmFiber10StateAt 26 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix26 ++ [tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix26 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 26) tmFiber10State26_in_pass1_prefix26

theorem tmFiber10State27_in_pass1_prefix27 :
    tmFiber10StateAt 27 ∈ chainClosureStep tmWord tmFiber10Prefix27 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 11 ∈
      chainClosureStep tmWord tmFiber10Prefix26 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix26 = tmFiber10Prefix11 ++ [tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26]
      (chainClosureStep tmWord tmFiber10Prefix11 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 11) tmFiber10State11_in_pass1_prefix11
  rw [show tmFiber10Prefix27 = tmFiber10Prefix26 ++ [tmFiber10StateAt 27] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 27) []
    (chainClosureStep tmWord tmFiber10Prefix26 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 11) hparentBefore tmFiber10ReverseSingleStep27

theorem tmFiber10State27_in_pass1_full :
    tmFiber10StateAt 27 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix27 ++ [tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix27 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 27) tmFiber10State27_in_pass1_prefix27

theorem tmFiber10State28_in_pass1_prefix28 :
    tmFiber10StateAt 28 ∈ chainClosureStep tmWord tmFiber10Prefix28 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 12 ∈
      chainClosureStep tmWord tmFiber10Prefix27 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix27 = tmFiber10Prefix12 ++ [tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27]
      (chainClosureStep tmWord tmFiber10Prefix12 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 12) tmFiber10State12_in_pass1_prefix12
  rw [show tmFiber10Prefix28 = tmFiber10Prefix27 ++ [tmFiber10StateAt 28] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 28) []
    (chainClosureStep tmWord tmFiber10Prefix27 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 12) hparentBefore tmFiber10ReverseSingleStep28

theorem tmFiber10State28_in_pass1_full :
    tmFiber10StateAt 28 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix28 ++ [tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix28 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 28) tmFiber10State28_in_pass1_prefix28

theorem tmFiber10State29_in_pass1_prefix29 :
    tmFiber10StateAt 29 ∈ chainClosureStep tmWord tmFiber10Prefix29 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 13 ∈
      chainClosureStep tmWord tmFiber10Prefix28 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix28 = tmFiber10Prefix13 ++ [tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28]
      (chainClosureStep tmWord tmFiber10Prefix13 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 13) tmFiber10State13_in_pass1_prefix13
  rw [show tmFiber10Prefix29 = tmFiber10Prefix28 ++ [tmFiber10StateAt 29] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 29) []
    (chainClosureStep tmWord tmFiber10Prefix28 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 13) hparentBefore tmFiber10ReverseSingleStep29

theorem tmFiber10State29_in_pass1_full :
    tmFiber10StateAt 29 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix29 ++ [tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix29 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 29) tmFiber10State29_in_pass1_prefix29

theorem tmFiber10State30_in_pass1_prefix30 :
    tmFiber10StateAt 30 ∈ chainClosureStep tmWord tmFiber10Prefix30 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 14 ∈
      chainClosureStep tmWord tmFiber10Prefix29 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix29 = tmFiber10Prefix14 ++ [tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29]
      (chainClosureStep tmWord tmFiber10Prefix14 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 14) tmFiber10State14_in_pass1_prefix14
  rw [show tmFiber10Prefix30 = tmFiber10Prefix29 ++ [tmFiber10StateAt 30] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 30) []
    (chainClosureStep tmWord tmFiber10Prefix29 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 14) hparentBefore tmFiber10ReverseSingleStep30

theorem tmFiber10State30_in_pass1_full :
    tmFiber10StateAt 30 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix30 ++ [tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix30 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 30) tmFiber10State30_in_pass1_prefix30

theorem tmFiber10State31_in_pass1_prefix31 :
    tmFiber10StateAt 31 ∈ chainClosureStep tmWord tmFiber10Prefix31 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 15 ∈
      chainClosureStep tmWord tmFiber10Prefix30 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix30 = tmFiber10Prefix15 ++ [tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30]
      (chainClosureStep tmWord tmFiber10Prefix15 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 15) tmFiber10State15_in_pass1_prefix15
  rw [show tmFiber10Prefix31 = tmFiber10Prefix30 ++ [tmFiber10StateAt 31] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 31) []
    (chainClosureStep tmWord tmFiber10Prefix30 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 15) hparentBefore tmFiber10ReverseSingleStep31

theorem tmFiber10State31_in_pass1_full :
    tmFiber10StateAt 31 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix31 ++ [tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix31 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 31) tmFiber10State31_in_pass1_prefix31

theorem tmFiber10State34_in_pass1_prefix34 :
    tmFiber10StateAt 34 ∈ chainClosureStep tmWord tmFiber10Prefix34 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 20 ∈
      chainClosureStep tmWord tmFiber10Prefix33 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix33 = tmFiber10Prefix20 ++ [tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33]
      (chainClosureStep tmWord tmFiber10Prefix20 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 20) tmFiber10State20_in_pass1_prefix20
  rw [show tmFiber10Prefix34 = tmFiber10Prefix33 ++ [tmFiber10StateAt 34] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 34) []
    (chainClosureStep tmWord tmFiber10Prefix33 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 20) hparentBefore tmFiber10ReverseSingleStep34

theorem tmFiber10State34_in_pass1_full :
    tmFiber10StateAt 34 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix34 ++ [tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix34 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 34) tmFiber10State34_in_pass1_prefix34

theorem tmFiber10State35_in_pass1_prefix35 :
    tmFiber10StateAt 35 ∈ chainClosureStep tmWord tmFiber10Prefix35 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 21 ∈
      chainClosureStep tmWord tmFiber10Prefix34 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix34 = tmFiber10Prefix21 ++ [tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34]
      (chainClosureStep tmWord tmFiber10Prefix21 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 21) tmFiber10State21_in_pass1_prefix21
  rw [show tmFiber10Prefix35 = tmFiber10Prefix34 ++ [tmFiber10StateAt 35] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 35) []
    (chainClosureStep tmWord tmFiber10Prefix34 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 21) hparentBefore tmFiber10ReverseSingleStep35

theorem tmFiber10State35_in_pass1_full :
    tmFiber10StateAt 35 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix35 ++ [tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix35 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 35) tmFiber10State35_in_pass1_prefix35

theorem tmFiber10State36_in_pass1_prefix36 :
    tmFiber10StateAt 36 ∈ chainClosureStep tmWord tmFiber10Prefix36 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 16 ∈
      chainClosureStep tmWord tmFiber10Prefix35 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix35 = tmFiber10Prefix16 ++ [tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35]
      (chainClosureStep tmWord tmFiber10Prefix16 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 16) tmFiber10State16_in_pass1_prefix16
  rw [show tmFiber10Prefix36 = tmFiber10Prefix35 ++ [tmFiber10StateAt 36] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 36) []
    (chainClosureStep tmWord tmFiber10Prefix35 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 16) hparentBefore tmFiber10ReverseSingleStep36

theorem tmFiber10State36_in_pass1_full :
    tmFiber10StateAt 36 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix36 ++ [tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix36 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 36) tmFiber10State36_in_pass1_prefix36

theorem tmFiber10State37_in_pass1_prefix37 :
    tmFiber10StateAt 37 ∈ chainClosureStep tmWord tmFiber10Prefix37 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 17 ∈
      chainClosureStep tmWord tmFiber10Prefix36 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix36 = tmFiber10Prefix17 ++ [tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36]
      (chainClosureStep tmWord tmFiber10Prefix17 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 17) tmFiber10State17_in_pass1_prefix17
  rw [show tmFiber10Prefix37 = tmFiber10Prefix36 ++ [tmFiber10StateAt 37] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 37) []
    (chainClosureStep tmWord tmFiber10Prefix36 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 17) hparentBefore tmFiber10ReverseSingleStep37

theorem tmFiber10State37_in_pass1_full :
    tmFiber10StateAt 37 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix37 ++ [tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix37 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 37) tmFiber10State37_in_pass1_prefix37

theorem tmFiber10State38_in_pass1_prefix38 :
    tmFiber10StateAt 38 ∈ chainClosureStep tmWord tmFiber10Prefix38 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 18 ∈
      chainClosureStep tmWord tmFiber10Prefix37 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix37 = tmFiber10Prefix18 ++ [tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37]
      (chainClosureStep tmWord tmFiber10Prefix18 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 18) tmFiber10State18_in_pass1_prefix18
  rw [show tmFiber10Prefix38 = tmFiber10Prefix37 ++ [tmFiber10StateAt 38] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 38) []
    (chainClosureStep tmWord tmFiber10Prefix37 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 18) hparentBefore tmFiber10ReverseSingleStep38

theorem tmFiber10State38_in_pass1_full :
    tmFiber10StateAt 38 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix38 ++ [tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix38 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 38) tmFiber10State38_in_pass1_prefix38

theorem tmFiber10State39_in_pass1_prefix39 :
    tmFiber10StateAt 39 ∈ chainClosureStep tmWord tmFiber10Prefix39 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 19 ∈
      chainClosureStep tmWord tmFiber10Prefix38 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix38 = tmFiber10Prefix19 ++ [tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38]
      (chainClosureStep tmWord tmFiber10Prefix19 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 19) tmFiber10State19_in_pass1_prefix19
  rw [show tmFiber10Prefix39 = tmFiber10Prefix38 ++ [tmFiber10StateAt 39] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 39) []
    (chainClosureStep tmWord tmFiber10Prefix38 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 19) hparentBefore tmFiber10ReverseSingleStep39

theorem tmFiber10State39_in_pass1_full :
    tmFiber10StateAt 39 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix39 ++ [tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix39 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 39) tmFiber10State39_in_pass1_prefix39

theorem tmFiber10State50_in_pass1_prefix50 :
    tmFiber10StateAt 50 ∈ chainClosureStep tmWord tmFiber10Prefix50 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 12 ∈
      chainClosureStep tmWord tmFiber10Prefix49 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix49 = tmFiber10Prefix12 ++ [tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49]
      (chainClosureStep tmWord tmFiber10Prefix12 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 12) tmFiber10State12_in_pass1_prefix12
  rw [show tmFiber10Prefix50 = tmFiber10Prefix49 ++ [tmFiber10StateAt 50] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 50) []
    (chainClosureStep tmWord tmFiber10Prefix49 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 12) hparentBefore tmFiber10ReverseSingleStep50

theorem tmFiber10State50_in_pass1_full :
    tmFiber10StateAt 50 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix50 ++ [tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix50 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 50) tmFiber10State50_in_pass1_prefix50

theorem tmFiber10State51_in_pass1_prefix51 :
    tmFiber10StateAt 51 ∈ chainClosureStep tmWord tmFiber10Prefix51 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 13 ∈
      chainClosureStep tmWord tmFiber10Prefix50 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix50 = tmFiber10Prefix13 ++ [tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50]
      (chainClosureStep tmWord tmFiber10Prefix13 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 13) tmFiber10State13_in_pass1_prefix13
  rw [show tmFiber10Prefix51 = tmFiber10Prefix50 ++ [tmFiber10StateAt 51] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 51) []
    (chainClosureStep tmWord tmFiber10Prefix50 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 13) hparentBefore tmFiber10ReverseSingleStep51

theorem tmFiber10State51_in_pass1_full :
    tmFiber10StateAt 51 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix51 ++ [tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix51 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 51) tmFiber10State51_in_pass1_prefix51

theorem tmFiber10State52_in_pass1_prefix52 :
    tmFiber10StateAt 52 ∈ chainClosureStep tmWord tmFiber10Prefix52 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 8 ∈
      chainClosureStep tmWord tmFiber10Prefix51 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix51 = tmFiber10Prefix8 ++ [tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51]
      (chainClosureStep tmWord tmFiber10Prefix8 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 8) tmFiber10State8_in_pass1_prefix8
  rw [show tmFiber10Prefix52 = tmFiber10Prefix51 ++ [tmFiber10StateAt 52] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 52) []
    (chainClosureStep tmWord tmFiber10Prefix51 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 8) hparentBefore tmFiber10ReverseSingleStep52

theorem tmFiber10State52_in_pass1_full :
    tmFiber10StateAt 52 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix52 ++ [tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix52 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 52) tmFiber10State52_in_pass1_prefix52

theorem tmFiber10State53_in_pass1_prefix53 :
    tmFiber10StateAt 53 ∈ chainClosureStep tmWord tmFiber10Prefix53 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 9 ∈
      chainClosureStep tmWord tmFiber10Prefix52 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix52 = tmFiber10Prefix9 ++ [tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52]
      (chainClosureStep tmWord tmFiber10Prefix9 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 9) tmFiber10State9_in_pass1_prefix9
  rw [show tmFiber10Prefix53 = tmFiber10Prefix52 ++ [tmFiber10StateAt 53] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 53) []
    (chainClosureStep tmWord tmFiber10Prefix52 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 9) hparentBefore tmFiber10ReverseSingleStep53

theorem tmFiber10State53_in_pass1_full :
    tmFiber10StateAt 53 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix53 ++ [tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix53 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 53) tmFiber10State53_in_pass1_prefix53

theorem tmFiber10State54_in_pass1_prefix54 :
    tmFiber10StateAt 54 ∈ chainClosureStep tmWord tmFiber10Prefix54 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 10 ∈
      chainClosureStep tmWord tmFiber10Prefix53 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix53 = tmFiber10Prefix10 ++ [tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53]
      (chainClosureStep tmWord tmFiber10Prefix10 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 10) tmFiber10State10_in_pass1_prefix10
  rw [show tmFiber10Prefix54 = tmFiber10Prefix53 ++ [tmFiber10StateAt 54] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 54) []
    (chainClosureStep tmWord tmFiber10Prefix53 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 10) hparentBefore tmFiber10ReverseSingleStep54

theorem tmFiber10State54_in_pass1_full :
    tmFiber10StateAt 54 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix54 ++ [tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix54 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 54) tmFiber10State54_in_pass1_prefix54

theorem tmFiber10State55_in_pass1_prefix55 :
    tmFiber10StateAt 55 ∈ chainClosureStep tmWord tmFiber10Prefix55 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 11 ∈
      chainClosureStep tmWord tmFiber10Prefix54 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix54 = tmFiber10Prefix11 ++ [tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54]
      (chainClosureStep tmWord tmFiber10Prefix11 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 11) tmFiber10State11_in_pass1_prefix11
  rw [show tmFiber10Prefix55 = tmFiber10Prefix54 ++ [tmFiber10StateAt 55] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 55) []
    (chainClosureStep tmWord tmFiber10Prefix54 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 11) hparentBefore tmFiber10ReverseSingleStep55

theorem tmFiber10State55_in_pass1_full :
    tmFiber10StateAt 55 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix55 ++ [tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix55 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 55) tmFiber10State55_in_pass1_prefix55

theorem tmFiber10State58_in_pass1_prefix58 :
    tmFiber10StateAt 58 ∈ chainClosureStep tmWord tmFiber10Prefix58 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 4 ∈
      chainClosureStep tmWord tmFiber10Prefix57 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix57 = tmFiber10Prefix4 ++ [tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57]
      (chainClosureStep tmWord tmFiber10Prefix4 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 4) tmFiber10State4_in_pass1_prefix4
  rw [show tmFiber10Prefix58 = tmFiber10Prefix57 ++ [tmFiber10StateAt 58] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 58) []
    (chainClosureStep tmWord tmFiber10Prefix57 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 4) hparentBefore tmFiber10ReverseSingleStep58

theorem tmFiber10State58_in_pass1_full :
    tmFiber10StateAt 58 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix58 ++ [tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix58 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 58) tmFiber10State58_in_pass1_prefix58

theorem tmFiber10State59_in_pass1_prefix59 :
    tmFiber10StateAt 59 ∈ chainClosureStep tmWord tmFiber10Prefix59 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 5 ∈
      chainClosureStep tmWord tmFiber10Prefix58 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix58 = tmFiber10Prefix5 ++ [tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58]
      (chainClosureStep tmWord tmFiber10Prefix5 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 5) tmFiber10State5_in_pass1_prefix5
  rw [show tmFiber10Prefix59 = tmFiber10Prefix58 ++ [tmFiber10StateAt 59] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 59) []
    (chainClosureStep tmWord tmFiber10Prefix58 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 5) hparentBefore tmFiber10ReverseSingleStep59

theorem tmFiber10State59_in_pass1_full :
    tmFiber10StateAt 59 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix59 ++ [tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix59 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 59) tmFiber10State59_in_pass1_prefix59

theorem tmFiber10State60_in_pass1_prefix60 :
    tmFiber10StateAt 60 ∈ chainClosureStep tmWord tmFiber10Prefix60 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 0 ∈
      chainClosureStep tmWord tmFiber10Prefix59 ([tmFiber10StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber10Prefix59
      ([tmFiber10StateAt 0]) (tmFiber10StateAt 0) (by simp)
  rw [show tmFiber10Prefix60 = tmFiber10Prefix59 ++ [tmFiber10StateAt 60] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 60) []
    (chainClosureStep tmWord tmFiber10Prefix59 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 0) hparentBefore tmFiber10ReverseSingleStep60

theorem tmFiber10State60_in_pass1_full :
    tmFiber10StateAt 60 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix60 ++ [tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix60 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 60) tmFiber10State60_in_pass1_prefix60

theorem tmFiber10State61_in_pass1_prefix61 :
    tmFiber10StateAt 61 ∈ chainClosureStep tmWord tmFiber10Prefix61 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 1 ∈
      chainClosureStep tmWord tmFiber10Prefix60 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix60 = tmFiber10Prefix1 ++ [tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 2, tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60]
      (chainClosureStep tmWord tmFiber10Prefix1 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 1) tmFiber10State1_in_pass1_prefix1
  rw [show tmFiber10Prefix61 = tmFiber10Prefix60 ++ [tmFiber10StateAt 61] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 61) []
    (chainClosureStep tmWord tmFiber10Prefix60 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 1) hparentBefore tmFiber10ReverseSingleStep61

theorem tmFiber10State61_in_pass1_full :
    tmFiber10StateAt 61 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix61 ++ [tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix61 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 61) tmFiber10State61_in_pass1_prefix61

theorem tmFiber10State62_in_pass1_prefix62 :
    tmFiber10StateAt 62 ∈ chainClosureStep tmWord tmFiber10Prefix62 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 2 ∈
      chainClosureStep tmWord tmFiber10Prefix61 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix61 = tmFiber10Prefix2 ++ [tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 3, tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61]
      (chainClosureStep tmWord tmFiber10Prefix2 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 2) tmFiber10State2_in_pass1_prefix2
  rw [show tmFiber10Prefix62 = tmFiber10Prefix61 ++ [tmFiber10StateAt 62] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 62) []
    (chainClosureStep tmWord tmFiber10Prefix61 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 2) hparentBefore tmFiber10ReverseSingleStep62

theorem tmFiber10State62_in_pass1_full :
    tmFiber10StateAt 62 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix62 ++ [tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix62 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 62) tmFiber10State62_in_pass1_prefix62

theorem tmFiber10State63_in_pass1_prefix63 :
    tmFiber10StateAt 63 ∈ chainClosureStep tmWord tmFiber10Prefix63 ([tmFiber10StateAt 0]) := by
  have hparentBefore : tmFiber10StateAt 3 ∈
      chainClosureStep tmWord tmFiber10Prefix62 ([tmFiber10StateAt 0]) := by
    rw [show tmFiber10Prefix62 = tmFiber10Prefix3 ++ [tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 4, tmFiber10StateAt 5, tmFiber10StateAt 6, tmFiber10StateAt 7, tmFiber10StateAt 8, tmFiber10StateAt 9, tmFiber10StateAt 10, tmFiber10StateAt 11, tmFiber10StateAt 12, tmFiber10StateAt 13, tmFiber10StateAt 14, tmFiber10StateAt 15, tmFiber10StateAt 16, tmFiber10StateAt 17, tmFiber10StateAt 18, tmFiber10StateAt 19, tmFiber10StateAt 20, tmFiber10StateAt 21, tmFiber10StateAt 22, tmFiber10StateAt 23, tmFiber10StateAt 24, tmFiber10StateAt 25, tmFiber10StateAt 26, tmFiber10StateAt 27, tmFiber10StateAt 28, tmFiber10StateAt 29, tmFiber10StateAt 30, tmFiber10StateAt 31, tmFiber10StateAt 32, tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62]
      (chainClosureStep tmWord tmFiber10Prefix3 ([tmFiber10StateAt 0]))
      (tmFiber10StateAt 3) tmFiber10State3_in_pass1_prefix3
  rw [show tmFiber10Prefix63 = tmFiber10Prefix62 ++ [tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 63) []
    (chainClosureStep tmWord tmFiber10Prefix62 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 3) hparentBefore tmFiber10ReverseSingleStep63

theorem tmFiber10State63_in_pass1_full :
    tmFiber10StateAt 63 ∈ chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix63 ++ [] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord []
    (chainClosureStep tmWord tmFiber10Prefix63 ([tmFiber10StateAt 0]))
    (tmFiber10StateAt 63) tmFiber10State63_in_pass1_prefix63

theorem tmFiber10State32_in_pass2_prefix32 :
    tmFiber10StateAt 32 ∈ chainClosureStep tmWord tmFiber10Prefix32 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) := by
  have hparentBefore : tmFiber10StateAt 36 ∈
      chainClosureStep tmWord tmFiber10Prefix31 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber10Prefix31
      (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) (tmFiber10StateAt 36) tmFiber10State36_in_pass1_full
  rw [show tmFiber10Prefix32 = tmFiber10Prefix31 ++ [tmFiber10StateAt 32] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 32) []
    (chainClosureStep tmWord tmFiber10Prefix31 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])))
    (tmFiber10StateAt 36) hparentBefore tmFiber10ReverseSingleStep32

theorem tmFiber10State32_in_pass2_full :
    tmFiber10StateAt 32 ∈ chainClosureStep tmWord tmFiber10DirectStates (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix32 ++ [tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 33, tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix32 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])))
    (tmFiber10StateAt 32) tmFiber10State32_in_pass2_prefix32

theorem tmFiber10State33_in_pass2_prefix33 :
    tmFiber10StateAt 33 ∈ chainClosureStep tmWord tmFiber10Prefix33 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) := by
  have hparentBefore : tmFiber10StateAt 37 ∈
      chainClosureStep tmWord tmFiber10Prefix32 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber10Prefix32
      (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) (tmFiber10StateAt 37) tmFiber10State37_in_pass1_full
  rw [show tmFiber10Prefix33 = tmFiber10Prefix32 ++ [tmFiber10StateAt 33] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 33) []
    (chainClosureStep tmWord tmFiber10Prefix32 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])))
    (tmFiber10StateAt 37) hparentBefore tmFiber10ReverseSingleStep33

theorem tmFiber10State33_in_pass2_full :
    tmFiber10StateAt 33 ∈ chainClosureStep tmWord tmFiber10DirectStates (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix33 ++ [tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 34, tmFiber10StateAt 35, tmFiber10StateAt 36, tmFiber10StateAt 37, tmFiber10StateAt 38, tmFiber10StateAt 39, tmFiber10StateAt 40, tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix33 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])))
    (tmFiber10StateAt 33) tmFiber10State33_in_pass2_prefix33

theorem tmFiber10State42_in_pass2_prefix42 :
    tmFiber10StateAt 42 ∈ chainClosureStep tmWord tmFiber10Prefix42 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) := by
  have hparentBefore : tmFiber10StateAt 58 ∈
      chainClosureStep tmWord tmFiber10Prefix41 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber10Prefix41
      (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) (tmFiber10StateAt 58) tmFiber10State58_in_pass1_full
  rw [show tmFiber10Prefix42 = tmFiber10Prefix41 ++ [tmFiber10StateAt 42] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 42) []
    (chainClosureStep tmWord tmFiber10Prefix41 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])))
    (tmFiber10StateAt 58) hparentBefore tmFiber10ReverseSingleStep42

theorem tmFiber10State42_in_pass2_full :
    tmFiber10StateAt 42 ∈ chainClosureStep tmWord tmFiber10DirectStates (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix42 ++ [tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix42 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])))
    (tmFiber10StateAt 42) tmFiber10State42_in_pass2_prefix42

theorem tmFiber10State43_in_pass2_prefix43 :
    tmFiber10StateAt 43 ∈ chainClosureStep tmWord tmFiber10Prefix43 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) := by
  have hparentBefore : tmFiber10StateAt 59 ∈
      chainClosureStep tmWord tmFiber10Prefix42 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber10Prefix42
      (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) (tmFiber10StateAt 59) tmFiber10State59_in_pass1_full
  rw [show tmFiber10Prefix43 = tmFiber10Prefix42 ++ [tmFiber10StateAt 43] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 43) []
    (chainClosureStep tmWord tmFiber10Prefix42 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])))
    (tmFiber10StateAt 59) hparentBefore tmFiber10ReverseSingleStep43

theorem tmFiber10State43_in_pass2_full :
    tmFiber10StateAt 43 ∈ chainClosureStep tmWord tmFiber10DirectStates (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix43 ++ [tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix43 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])))
    (tmFiber10StateAt 43) tmFiber10State43_in_pass2_prefix43

theorem tmFiber10State44_in_pass2_prefix44 :
    tmFiber10StateAt 44 ∈ chainClosureStep tmWord tmFiber10Prefix44 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) := by
  have hparentBefore : tmFiber10StateAt 60 ∈
      chainClosureStep tmWord tmFiber10Prefix43 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber10Prefix43
      (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) (tmFiber10StateAt 60) tmFiber10State60_in_pass1_full
  rw [show tmFiber10Prefix44 = tmFiber10Prefix43 ++ [tmFiber10StateAt 44] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 44) []
    (chainClosureStep tmWord tmFiber10Prefix43 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])))
    (tmFiber10StateAt 60) hparentBefore tmFiber10ReverseSingleStep44

theorem tmFiber10State44_in_pass2_full :
    tmFiber10StateAt 44 ∈ chainClosureStep tmWord tmFiber10DirectStates (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix44 ++ [tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix44 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])))
    (tmFiber10StateAt 44) tmFiber10State44_in_pass2_prefix44

theorem tmFiber10State45_in_pass2_prefix45 :
    tmFiber10StateAt 45 ∈ chainClosureStep tmWord tmFiber10Prefix45 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) := by
  have hparentBefore : tmFiber10StateAt 61 ∈
      chainClosureStep tmWord tmFiber10Prefix44 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber10Prefix44
      (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) (tmFiber10StateAt 61) tmFiber10State61_in_pass1_full
  rw [show tmFiber10Prefix45 = tmFiber10Prefix44 ++ [tmFiber10StateAt 45] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 45) []
    (chainClosureStep tmWord tmFiber10Prefix44 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])))
    (tmFiber10StateAt 61) hparentBefore tmFiber10ReverseSingleStep45

theorem tmFiber10State45_in_pass2_full :
    tmFiber10StateAt 45 ∈ chainClosureStep tmWord tmFiber10DirectStates (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix45 ++ [tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix45 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])))
    (tmFiber10StateAt 45) tmFiber10State45_in_pass2_prefix45

theorem tmFiber10State46_in_pass2_prefix46 :
    tmFiber10StateAt 46 ∈ chainClosureStep tmWord tmFiber10Prefix46 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) := by
  have hparentBefore : tmFiber10StateAt 62 ∈
      chainClosureStep tmWord tmFiber10Prefix45 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber10Prefix45
      (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) (tmFiber10StateAt 62) tmFiber10State62_in_pass1_full
  rw [show tmFiber10Prefix46 = tmFiber10Prefix45 ++ [tmFiber10StateAt 46] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 46) []
    (chainClosureStep tmWord tmFiber10Prefix45 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])))
    (tmFiber10StateAt 62) hparentBefore tmFiber10ReverseSingleStep46

theorem tmFiber10State46_in_pass2_full :
    tmFiber10StateAt 46 ∈ chainClosureStep tmWord tmFiber10DirectStates (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix46 ++ [tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix46 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])))
    (tmFiber10StateAt 46) tmFiber10State46_in_pass2_prefix46

theorem tmFiber10State47_in_pass2_prefix47 :
    tmFiber10StateAt 47 ∈ chainClosureStep tmWord tmFiber10Prefix47 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) := by
  have hparentBefore : tmFiber10StateAt 63 ∈
      chainClosureStep tmWord tmFiber10Prefix46 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber10Prefix46
      (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) (tmFiber10StateAt 63) tmFiber10State63_in_pass1_full
  rw [show tmFiber10Prefix47 = tmFiber10Prefix46 ++ [tmFiber10StateAt 47] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 47) []
    (chainClosureStep tmWord tmFiber10Prefix46 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])))
    (tmFiber10StateAt 63) hparentBefore tmFiber10ReverseSingleStep47

theorem tmFiber10State47_in_pass2_full :
    tmFiber10StateAt 47 ∈ chainClosureStep tmWord tmFiber10DirectStates (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix47 ++ [tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix47 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])))
    (tmFiber10StateAt 47) tmFiber10State47_in_pass2_prefix47

theorem tmFiber10State48_in_pass2_prefix48 :
    tmFiber10StateAt 48 ∈ chainClosureStep tmWord tmFiber10Prefix48 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) := by
  have hparentBefore : tmFiber10StateAt 52 ∈
      chainClosureStep tmWord tmFiber10Prefix47 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber10Prefix47
      (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) (tmFiber10StateAt 52) tmFiber10State52_in_pass1_full
  rw [show tmFiber10Prefix48 = tmFiber10Prefix47 ++ [tmFiber10StateAt 48] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 48) []
    (chainClosureStep tmWord tmFiber10Prefix47 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])))
    (tmFiber10StateAt 52) hparentBefore tmFiber10ReverseSingleStep48

theorem tmFiber10State48_in_pass2_full :
    tmFiber10StateAt 48 ∈ chainClosureStep tmWord tmFiber10DirectStates (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix48 ++ [tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix48 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])))
    (tmFiber10StateAt 48) tmFiber10State48_in_pass2_prefix48

theorem tmFiber10State49_in_pass2_prefix49 :
    tmFiber10StateAt 49 ∈ chainClosureStep tmWord tmFiber10Prefix49 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) := by
  have hparentBefore : tmFiber10StateAt 53 ∈
      chainClosureStep tmWord tmFiber10Prefix48 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber10Prefix48
      (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) (tmFiber10StateAt 53) tmFiber10State53_in_pass1_full
  rw [show tmFiber10Prefix49 = tmFiber10Prefix48 ++ [tmFiber10StateAt 49] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 49) []
    (chainClosureStep tmWord tmFiber10Prefix48 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])))
    (tmFiber10StateAt 53) hparentBefore tmFiber10ReverseSingleStep49

theorem tmFiber10State49_in_pass2_full :
    tmFiber10StateAt 49 ∈ chainClosureStep tmWord tmFiber10DirectStates (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix49 ++ [tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix49 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])))
    (tmFiber10StateAt 49) tmFiber10State49_in_pass2_prefix49

theorem tmFiber10State56_in_pass2_prefix56 :
    tmFiber10StateAt 56 ∈ chainClosureStep tmWord tmFiber10Prefix56 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) := by
  have hparentBefore : tmFiber10StateAt 60 ∈
      chainClosureStep tmWord tmFiber10Prefix55 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber10Prefix55
      (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) (tmFiber10StateAt 60) tmFiber10State60_in_pass1_full
  rw [show tmFiber10Prefix56 = tmFiber10Prefix55 ++ [tmFiber10StateAt 56] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 56) []
    (chainClosureStep tmWord tmFiber10Prefix55 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])))
    (tmFiber10StateAt 60) hparentBefore tmFiber10ReverseSingleStep56

theorem tmFiber10State56_in_pass2_full :
    tmFiber10StateAt 56 ∈ chainClosureStep tmWord tmFiber10DirectStates (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix56 ++ [tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix56 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])))
    (tmFiber10StateAt 56) tmFiber10State56_in_pass2_prefix56

theorem tmFiber10State57_in_pass2_prefix57 :
    tmFiber10StateAt 57 ∈ chainClosureStep tmWord tmFiber10Prefix57 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) := by
  have hparentBefore : tmFiber10StateAt 61 ∈
      chainClosureStep tmWord tmFiber10Prefix56 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber10Prefix56
      (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) (tmFiber10StateAt 61) tmFiber10State61_in_pass1_full
  rw [show tmFiber10Prefix57 = tmFiber10Prefix56 ++ [tmFiber10StateAt 57] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 57) []
    (chainClosureStep tmWord tmFiber10Prefix56 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])))
    (tmFiber10StateAt 61) hparentBefore tmFiber10ReverseSingleStep57

theorem tmFiber10State57_in_pass2_full :
    tmFiber10StateAt 57 ∈ chainClosureStep tmWord tmFiber10DirectStates (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix57 ++ [tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix57 (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0])))
    (tmFiber10StateAt 57) tmFiber10State57_in_pass2_prefix57

theorem tmFiber10State40_in_pass3_prefix40 :
    tmFiber10StateAt 40 ∈ chainClosureStep tmWord tmFiber10Prefix40 (chainClosureStep tmWord tmFiber10DirectStates (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]))) := by
  have hparentBefore : tmFiber10StateAt 44 ∈
      chainClosureStep tmWord tmFiber10Prefix39 (chainClosureStep tmWord tmFiber10DirectStates (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]))) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber10Prefix39
      (chainClosureStep tmWord tmFiber10DirectStates (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]))) (tmFiber10StateAt 44) tmFiber10State44_in_pass2_full
  rw [show tmFiber10Prefix40 = tmFiber10Prefix39 ++ [tmFiber10StateAt 40] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 40) []
    (chainClosureStep tmWord tmFiber10Prefix39 (chainClosureStep tmWord tmFiber10DirectStates (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]))))
    (tmFiber10StateAt 44) hparentBefore tmFiber10ReverseSingleStep40

theorem tmFiber10State40_in_pass3_full :
    tmFiber10StateAt 40 ∈ chainClosureStep tmWord tmFiber10DirectStates (chainClosureStep tmWord tmFiber10DirectStates (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]))) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix40 ++ [tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 41, tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix40 (chainClosureStep tmWord tmFiber10DirectStates (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]))))
    (tmFiber10StateAt 40) tmFiber10State40_in_pass3_prefix40

theorem tmFiber10State41_in_pass3_prefix41 :
    tmFiber10StateAt 41 ∈ chainClosureStep tmWord tmFiber10Prefix41 (chainClosureStep tmWord tmFiber10DirectStates (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]))) := by
  have hparentBefore : tmFiber10StateAt 45 ∈
      chainClosureStep tmWord tmFiber10Prefix40 (chainClosureStep tmWord tmFiber10DirectStates (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]))) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber10Prefix40
      (chainClosureStep tmWord tmFiber10DirectStates (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]))) (tmFiber10StateAt 45) tmFiber10State45_in_pass2_full
  rw [show tmFiber10Prefix41 = tmFiber10Prefix40 ++ [tmFiber10StateAt 41] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber10StateAt 41) []
    (chainClosureStep tmWord tmFiber10Prefix40 (chainClosureStep tmWord tmFiber10DirectStates (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]))))
    (tmFiber10StateAt 45) hparentBefore tmFiber10ReverseSingleStep41

theorem tmFiber10State41_in_pass3_full :
    tmFiber10StateAt 41 ∈ chainClosureStep tmWord tmFiber10DirectStates (chainClosureStep tmWord tmFiber10DirectStates (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]))) := by
  rw [show tmFiber10DirectStates = tmFiber10Prefix41 ++ [tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber10StateAt 42, tmFiber10StateAt 43, tmFiber10StateAt 44, tmFiber10StateAt 45, tmFiber10StateAt 46, tmFiber10StateAt 47, tmFiber10StateAt 48, tmFiber10StateAt 49, tmFiber10StateAt 50, tmFiber10StateAt 51, tmFiber10StateAt 52, tmFiber10StateAt 53, tmFiber10StateAt 54, tmFiber10StateAt 55, tmFiber10StateAt 56, tmFiber10StateAt 57, tmFiber10StateAt 58, tmFiber10StateAt 59, tmFiber10StateAt 60, tmFiber10StateAt 61, tmFiber10StateAt 62, tmFiber10StateAt 63]
    (chainClosureStep tmWord tmFiber10Prefix41 (chainClosureStep tmWord tmFiber10DirectStates (chainClosureStep tmWord tmFiber10DirectStates ([tmFiber10StateAt 0]))))
    (tmFiber10StateAt 41) tmFiber10State41_in_pass3_prefix41

theorem tmFiber10FirstPassGrows :
    ((chainClosureStep tmWord tmFiber10DirectStates [tmFiber10StateAt 0]).length ==
      [tmFiber10StateAt 0].length) = false := by
  have hroot : tmFiber10StateAt 0 ∈
      chainClosureStep tmWord tmFiber10DirectStates [tmFiber10StateAt 0] :=
    chainClosureStep_mem_of_seen tmWord tmFiber10DirectStates
      [tmFiber10StateAt 0] (tmFiber10StateAt 0) (by simp)
  have hnew : tmFiber10StateAt 1 ∈
      chainClosureStep tmWord tmFiber10DirectStates [tmFiber10StateAt 0] :=
    tmFiber10State1_in_pass1_full
  simpa using list_length_beq_one_false_of_two_mem
    (chainClosureStep tmWord tmFiber10DirectStates [tmFiber10StateAt 0])
    (tmFiber10StateAt 0) (tmFiber10StateAt 1) hroot hnew (by decide)

theorem tmFiber10State0_in_close_short :
    tmFiber10StateAt 0 ∈ closeChainFiber tmWord tmFiber10DirectStates 0 [tmFiber10StateAt 0] := by
  simp [closeChainFiber]

theorem tmFiber10State1_in_close_short :
    tmFiber10StateAt 1 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 1) tmFiber10State1_in_pass1_full

theorem tmFiber10State2_in_close_short :
    tmFiber10StateAt 2 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 2) tmFiber10State2_in_pass1_full

theorem tmFiber10State3_in_close_short :
    tmFiber10StateAt 3 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 3) tmFiber10State3_in_pass1_full

theorem tmFiber10State4_in_close_short :
    tmFiber10StateAt 4 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 4) tmFiber10State4_in_pass1_full

theorem tmFiber10State5_in_close_short :
    tmFiber10StateAt 5 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 5) tmFiber10State5_in_pass1_full

theorem tmFiber10State6_in_close_short :
    tmFiber10StateAt 6 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 6) tmFiber10State6_in_pass1_full

theorem tmFiber10State7_in_close_short :
    tmFiber10StateAt 7 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 7) tmFiber10State7_in_pass1_full

theorem tmFiber10State8_in_close_short :
    tmFiber10StateAt 8 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 8) tmFiber10State8_in_pass1_full

theorem tmFiber10State9_in_close_short :
    tmFiber10StateAt 9 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 9) tmFiber10State9_in_pass1_full

theorem tmFiber10State10_in_close_short :
    tmFiber10StateAt 10 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 10) tmFiber10State10_in_pass1_full

theorem tmFiber10State11_in_close_short :
    tmFiber10StateAt 11 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 11) tmFiber10State11_in_pass1_full

theorem tmFiber10State12_in_close_short :
    tmFiber10StateAt 12 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 12) tmFiber10State12_in_pass1_full

theorem tmFiber10State13_in_close_short :
    tmFiber10StateAt 13 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 13) tmFiber10State13_in_pass1_full

theorem tmFiber10State14_in_close_short :
    tmFiber10StateAt 14 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 14) tmFiber10State14_in_pass1_full

theorem tmFiber10State15_in_close_short :
    tmFiber10StateAt 15 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 15) tmFiber10State15_in_pass1_full

theorem tmFiber10State16_in_close_short :
    tmFiber10StateAt 16 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 16) tmFiber10State16_in_pass1_full

theorem tmFiber10State17_in_close_short :
    tmFiber10StateAt 17 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 17) tmFiber10State17_in_pass1_full

theorem tmFiber10State18_in_close_short :
    tmFiber10StateAt 18 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 18) tmFiber10State18_in_pass1_full

theorem tmFiber10State19_in_close_short :
    tmFiber10StateAt 19 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 19) tmFiber10State19_in_pass1_full

theorem tmFiber10State20_in_close_short :
    tmFiber10StateAt 20 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 20) tmFiber10State20_in_pass1_full

theorem tmFiber10State21_in_close_short :
    tmFiber10StateAt 21 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 21) tmFiber10State21_in_pass1_full

theorem tmFiber10State22_in_close_short :
    tmFiber10StateAt 22 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 22) tmFiber10State22_in_pass1_full

theorem tmFiber10State23_in_close_short :
    tmFiber10StateAt 23 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 23) tmFiber10State23_in_pass1_full

theorem tmFiber10State24_in_close_short :
    tmFiber10StateAt 24 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 24) tmFiber10State24_in_pass1_full

theorem tmFiber10State25_in_close_short :
    tmFiber10StateAt 25 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 25) tmFiber10State25_in_pass1_full

theorem tmFiber10State26_in_close_short :
    tmFiber10StateAt 26 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 26) tmFiber10State26_in_pass1_full

theorem tmFiber10State27_in_close_short :
    tmFiber10StateAt 27 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 27) tmFiber10State27_in_pass1_full

theorem tmFiber10State28_in_close_short :
    tmFiber10StateAt 28 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 28) tmFiber10State28_in_pass1_full

theorem tmFiber10State29_in_close_short :
    tmFiber10StateAt 29 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 29) tmFiber10State29_in_pass1_full

theorem tmFiber10State30_in_close_short :
    tmFiber10StateAt 30 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 30) tmFiber10State30_in_pass1_full

theorem tmFiber10State31_in_close_short :
    tmFiber10StateAt 31 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 31) tmFiber10State31_in_pass1_full

theorem tmFiber10State34_in_close_short :
    tmFiber10StateAt 34 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 34) tmFiber10State34_in_pass1_full

theorem tmFiber10State35_in_close_short :
    tmFiber10StateAt 35 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 35) tmFiber10State35_in_pass1_full

theorem tmFiber10State36_in_close_short :
    tmFiber10StateAt 36 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 36) tmFiber10State36_in_pass1_full

theorem tmFiber10State37_in_close_short :
    tmFiber10StateAt 37 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 37) tmFiber10State37_in_pass1_full

theorem tmFiber10State38_in_close_short :
    tmFiber10StateAt 38 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 38) tmFiber10State38_in_pass1_full

theorem tmFiber10State39_in_close_short :
    tmFiber10StateAt 39 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 39) tmFiber10State39_in_pass1_full

theorem tmFiber10State50_in_close_short :
    tmFiber10StateAt 50 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 50) tmFiber10State50_in_pass1_full

theorem tmFiber10State51_in_close_short :
    tmFiber10StateAt 51 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 51) tmFiber10State51_in_pass1_full

theorem tmFiber10State52_in_close_short :
    tmFiber10StateAt 52 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 52) tmFiber10State52_in_pass1_full

theorem tmFiber10State53_in_close_short :
    tmFiber10StateAt 53 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 53) tmFiber10State53_in_pass1_full

theorem tmFiber10State54_in_close_short :
    tmFiber10StateAt 54 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 54) tmFiber10State54_in_pass1_full

theorem tmFiber10State55_in_close_short :
    tmFiber10StateAt 55 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 55) tmFiber10State55_in_pass1_full

theorem tmFiber10State58_in_close_short :
    tmFiber10StateAt 58 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 58) tmFiber10State58_in_pass1_full

theorem tmFiber10State59_in_close_short :
    tmFiber10StateAt 59 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 59) tmFiber10State59_in_pass1_full

theorem tmFiber10State60_in_close_short :
    tmFiber10StateAt 60 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 60) tmFiber10State60_in_pass1_full

theorem tmFiber10State61_in_close_short :
    tmFiber10StateAt 61 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 61) tmFiber10State61_in_pass1_full

theorem tmFiber10State62_in_close_short :
    tmFiber10StateAt 62 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 62) tmFiber10State62_in_pass1_full

theorem tmFiber10State63_in_close_short :
    tmFiber10StateAt 63 ∈ closeChainFiber tmWord tmFiber10DirectStates 1 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 63) tmFiber10State63_in_pass1_full

theorem tmFiber10State32_in_close_short :
    tmFiber10StateAt 32 ∈ closeChainFiber tmWord tmFiber10DirectStates 2 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 32) tmFiber10FirstPassGrows
    tmFiber10State32_in_pass2_full

theorem tmFiber10State33_in_close_short :
    tmFiber10StateAt 33 ∈ closeChainFiber tmWord tmFiber10DirectStates 2 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 33) tmFiber10FirstPassGrows
    tmFiber10State33_in_pass2_full

theorem tmFiber10State42_in_close_short :
    tmFiber10StateAt 42 ∈ closeChainFiber tmWord tmFiber10DirectStates 2 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 42) tmFiber10FirstPassGrows
    tmFiber10State42_in_pass2_full

theorem tmFiber10State43_in_close_short :
    tmFiber10StateAt 43 ∈ closeChainFiber tmWord tmFiber10DirectStates 2 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 43) tmFiber10FirstPassGrows
    tmFiber10State43_in_pass2_full

theorem tmFiber10State44_in_close_short :
    tmFiber10StateAt 44 ∈ closeChainFiber tmWord tmFiber10DirectStates 2 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 44) tmFiber10FirstPassGrows
    tmFiber10State44_in_pass2_full

theorem tmFiber10State45_in_close_short :
    tmFiber10StateAt 45 ∈ closeChainFiber tmWord tmFiber10DirectStates 2 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 45) tmFiber10FirstPassGrows
    tmFiber10State45_in_pass2_full

theorem tmFiber10State46_in_close_short :
    tmFiber10StateAt 46 ∈ closeChainFiber tmWord tmFiber10DirectStates 2 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 46) tmFiber10FirstPassGrows
    tmFiber10State46_in_pass2_full

theorem tmFiber10State47_in_close_short :
    tmFiber10StateAt 47 ∈ closeChainFiber tmWord tmFiber10DirectStates 2 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 47) tmFiber10FirstPassGrows
    tmFiber10State47_in_pass2_full

theorem tmFiber10State48_in_close_short :
    tmFiber10StateAt 48 ∈ closeChainFiber tmWord tmFiber10DirectStates 2 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 48) tmFiber10FirstPassGrows
    tmFiber10State48_in_pass2_full

theorem tmFiber10State49_in_close_short :
    tmFiber10StateAt 49 ∈ closeChainFiber tmWord tmFiber10DirectStates 2 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 49) tmFiber10FirstPassGrows
    tmFiber10State49_in_pass2_full

theorem tmFiber10State56_in_close_short :
    tmFiber10StateAt 56 ∈ closeChainFiber tmWord tmFiber10DirectStates 2 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 56) tmFiber10FirstPassGrows
    tmFiber10State56_in_pass2_full

theorem tmFiber10State57_in_close_short :
    tmFiber10StateAt 57 ∈ closeChainFiber tmWord tmFiber10DirectStates 2 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber10DirectStates 0
    [tmFiber10StateAt 0] (tmFiber10StateAt 57) tmFiber10FirstPassGrows
    tmFiber10State57_in_pass2_full

theorem tmFiber10State40_in_close_short :
    tmFiber10StateAt 40 ∈ closeChainFiber tmWord tmFiber10DirectStates 3 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_step_of_close tmWord tmFiber10DirectStates 2
    [tmFiber10StateAt 0] (tmFiber10StateAt 44) (tmFiber10StateAt 40)
    (by simp) tmFiber10State44_in_close_short (by decide) tmFiber10ReverseSingleStep40

theorem tmFiber10State41_in_close_short :
    tmFiber10StateAt 41 ∈ closeChainFiber tmWord tmFiber10DirectStates 3 [tmFiber10StateAt 0] := by
  exact closeChainFiber_mem_step_of_close tmWord tmFiber10DirectStates 2
    [tmFiber10StateAt 0] (tmFiber10StateAt 45) (tmFiber10StateAt 41)
    (by simp) tmFiber10State45_in_close_short (by decide) tmFiber10ReverseSingleStep41

theorem tmFiber10State0_in_close :
    tmFiber10StateAt 0 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 0 ∈ closeChainFiber tmWord tmFiber10DirectStates (0 + 64) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 0 64
    [tmFiber10StateAt 0] (tmFiber10StateAt 0) tmFiber10State0_in_close_short

theorem tmFiber10State1_in_close :
    tmFiber10StateAt 1 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 1 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 1) tmFiber10State1_in_close_short

theorem tmFiber10State2_in_close :
    tmFiber10StateAt 2 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 2 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 2) tmFiber10State2_in_close_short

theorem tmFiber10State3_in_close :
    tmFiber10StateAt 3 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 3 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 3) tmFiber10State3_in_close_short

theorem tmFiber10State4_in_close :
    tmFiber10StateAt 4 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 4 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 4) tmFiber10State4_in_close_short

theorem tmFiber10State5_in_close :
    tmFiber10StateAt 5 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 5 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 5) tmFiber10State5_in_close_short

theorem tmFiber10State6_in_close :
    tmFiber10StateAt 6 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 6 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 6) tmFiber10State6_in_close_short

theorem tmFiber10State7_in_close :
    tmFiber10StateAt 7 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 7 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 7) tmFiber10State7_in_close_short

theorem tmFiber10State8_in_close :
    tmFiber10StateAt 8 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 8 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 8) tmFiber10State8_in_close_short

theorem tmFiber10State9_in_close :
    tmFiber10StateAt 9 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 9 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 9) tmFiber10State9_in_close_short

theorem tmFiber10State10_in_close :
    tmFiber10StateAt 10 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 10 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 10) tmFiber10State10_in_close_short

theorem tmFiber10State11_in_close :
    tmFiber10StateAt 11 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 11 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 11) tmFiber10State11_in_close_short

theorem tmFiber10State12_in_close :
    tmFiber10StateAt 12 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 12 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 12) tmFiber10State12_in_close_short

theorem tmFiber10State13_in_close :
    tmFiber10StateAt 13 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 13 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 13) tmFiber10State13_in_close_short

theorem tmFiber10State14_in_close :
    tmFiber10StateAt 14 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 14 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 14) tmFiber10State14_in_close_short

theorem tmFiber10State15_in_close :
    tmFiber10StateAt 15 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 15 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 15) tmFiber10State15_in_close_short

theorem tmFiber10State16_in_close :
    tmFiber10StateAt 16 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 16 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 16) tmFiber10State16_in_close_short

theorem tmFiber10State17_in_close :
    tmFiber10StateAt 17 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 17 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 17) tmFiber10State17_in_close_short

theorem tmFiber10State18_in_close :
    tmFiber10StateAt 18 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 18 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 18) tmFiber10State18_in_close_short

theorem tmFiber10State19_in_close :
    tmFiber10StateAt 19 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 19 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 19) tmFiber10State19_in_close_short

theorem tmFiber10State20_in_close :
    tmFiber10StateAt 20 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 20 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 20) tmFiber10State20_in_close_short

theorem tmFiber10State21_in_close :
    tmFiber10StateAt 21 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 21 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 21) tmFiber10State21_in_close_short

theorem tmFiber10State22_in_close :
    tmFiber10StateAt 22 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 22 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 22) tmFiber10State22_in_close_short

theorem tmFiber10State23_in_close :
    tmFiber10StateAt 23 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 23 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 23) tmFiber10State23_in_close_short

theorem tmFiber10State24_in_close :
    tmFiber10StateAt 24 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 24 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 24) tmFiber10State24_in_close_short

theorem tmFiber10State25_in_close :
    tmFiber10StateAt 25 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 25 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 25) tmFiber10State25_in_close_short

theorem tmFiber10State26_in_close :
    tmFiber10StateAt 26 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 26 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 26) tmFiber10State26_in_close_short

theorem tmFiber10State27_in_close :
    tmFiber10StateAt 27 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 27 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 27) tmFiber10State27_in_close_short

theorem tmFiber10State28_in_close :
    tmFiber10StateAt 28 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 28 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 28) tmFiber10State28_in_close_short

theorem tmFiber10State29_in_close :
    tmFiber10StateAt 29 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 29 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 29) tmFiber10State29_in_close_short

theorem tmFiber10State30_in_close :
    tmFiber10StateAt 30 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 30 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 30) tmFiber10State30_in_close_short

theorem tmFiber10State31_in_close :
    tmFiber10StateAt 31 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 31 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 31) tmFiber10State31_in_close_short

theorem tmFiber10State32_in_close :
    tmFiber10StateAt 32 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 32 ∈ closeChainFiber tmWord tmFiber10DirectStates (2 + 62) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 2 62
    [tmFiber10StateAt 0] (tmFiber10StateAt 32) tmFiber10State32_in_close_short

theorem tmFiber10State33_in_close :
    tmFiber10StateAt 33 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 33 ∈ closeChainFiber tmWord tmFiber10DirectStates (2 + 62) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 2 62
    [tmFiber10StateAt 0] (tmFiber10StateAt 33) tmFiber10State33_in_close_short

theorem tmFiber10State34_in_close :
    tmFiber10StateAt 34 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 34 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 34) tmFiber10State34_in_close_short

theorem tmFiber10State35_in_close :
    tmFiber10StateAt 35 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 35 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 35) tmFiber10State35_in_close_short

theorem tmFiber10State36_in_close :
    tmFiber10StateAt 36 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 36 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 36) tmFiber10State36_in_close_short

theorem tmFiber10State37_in_close :
    tmFiber10StateAt 37 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 37 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 37) tmFiber10State37_in_close_short

theorem tmFiber10State38_in_close :
    tmFiber10StateAt 38 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 38 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 38) tmFiber10State38_in_close_short

theorem tmFiber10State39_in_close :
    tmFiber10StateAt 39 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 39 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 39) tmFiber10State39_in_close_short

theorem tmFiber10State40_in_close :
    tmFiber10StateAt 40 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 40 ∈ closeChainFiber tmWord tmFiber10DirectStates (3 + 61) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 3 61
    [tmFiber10StateAt 0] (tmFiber10StateAt 40) tmFiber10State40_in_close_short

theorem tmFiber10State41_in_close :
    tmFiber10StateAt 41 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 41 ∈ closeChainFiber tmWord tmFiber10DirectStates (3 + 61) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 3 61
    [tmFiber10StateAt 0] (tmFiber10StateAt 41) tmFiber10State41_in_close_short

theorem tmFiber10State42_in_close :
    tmFiber10StateAt 42 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 42 ∈ closeChainFiber tmWord tmFiber10DirectStates (2 + 62) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 2 62
    [tmFiber10StateAt 0] (tmFiber10StateAt 42) tmFiber10State42_in_close_short

theorem tmFiber10State43_in_close :
    tmFiber10StateAt 43 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 43 ∈ closeChainFiber tmWord tmFiber10DirectStates (2 + 62) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 2 62
    [tmFiber10StateAt 0] (tmFiber10StateAt 43) tmFiber10State43_in_close_short

theorem tmFiber10State44_in_close :
    tmFiber10StateAt 44 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 44 ∈ closeChainFiber tmWord tmFiber10DirectStates (2 + 62) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 2 62
    [tmFiber10StateAt 0] (tmFiber10StateAt 44) tmFiber10State44_in_close_short

theorem tmFiber10State45_in_close :
    tmFiber10StateAt 45 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 45 ∈ closeChainFiber tmWord tmFiber10DirectStates (2 + 62) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 2 62
    [tmFiber10StateAt 0] (tmFiber10StateAt 45) tmFiber10State45_in_close_short

theorem tmFiber10State46_in_close :
    tmFiber10StateAt 46 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 46 ∈ closeChainFiber tmWord tmFiber10DirectStates (2 + 62) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 2 62
    [tmFiber10StateAt 0] (tmFiber10StateAt 46) tmFiber10State46_in_close_short

theorem tmFiber10State47_in_close :
    tmFiber10StateAt 47 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 47 ∈ closeChainFiber tmWord tmFiber10DirectStates (2 + 62) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 2 62
    [tmFiber10StateAt 0] (tmFiber10StateAt 47) tmFiber10State47_in_close_short

theorem tmFiber10State48_in_close :
    tmFiber10StateAt 48 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 48 ∈ closeChainFiber tmWord tmFiber10DirectStates (2 + 62) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 2 62
    [tmFiber10StateAt 0] (tmFiber10StateAt 48) tmFiber10State48_in_close_short

theorem tmFiber10State49_in_close :
    tmFiber10StateAt 49 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 49 ∈ closeChainFiber tmWord tmFiber10DirectStates (2 + 62) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 2 62
    [tmFiber10StateAt 0] (tmFiber10StateAt 49) tmFiber10State49_in_close_short

theorem tmFiber10State50_in_close :
    tmFiber10StateAt 50 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 50 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 50) tmFiber10State50_in_close_short

theorem tmFiber10State51_in_close :
    tmFiber10StateAt 51 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 51 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 51) tmFiber10State51_in_close_short

theorem tmFiber10State52_in_close :
    tmFiber10StateAt 52 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 52 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 52) tmFiber10State52_in_close_short

theorem tmFiber10State53_in_close :
    tmFiber10StateAt 53 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 53 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 53) tmFiber10State53_in_close_short

theorem tmFiber10State54_in_close :
    tmFiber10StateAt 54 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 54 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 54) tmFiber10State54_in_close_short

theorem tmFiber10State55_in_close :
    tmFiber10StateAt 55 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 55 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 55) tmFiber10State55_in_close_short

theorem tmFiber10State56_in_close :
    tmFiber10StateAt 56 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 56 ∈ closeChainFiber tmWord tmFiber10DirectStates (2 + 62) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 2 62
    [tmFiber10StateAt 0] (tmFiber10StateAt 56) tmFiber10State56_in_close_short

theorem tmFiber10State57_in_close :
    tmFiber10StateAt 57 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 57 ∈ closeChainFiber tmWord tmFiber10DirectStates (2 + 62) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 2 62
    [tmFiber10StateAt 0] (tmFiber10StateAt 57) tmFiber10State57_in_close_short

theorem tmFiber10State58_in_close :
    tmFiber10StateAt 58 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 58 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 58) tmFiber10State58_in_close_short

theorem tmFiber10State59_in_close :
    tmFiber10StateAt 59 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 59 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 59) tmFiber10State59_in_close_short

theorem tmFiber10State60_in_close :
    tmFiber10StateAt 60 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 60 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 60) tmFiber10State60_in_close_short

theorem tmFiber10State61_in_close :
    tmFiber10StateAt 61 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 61 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 61) tmFiber10State61_in_close_short

theorem tmFiber10State62_in_close :
    tmFiber10StateAt 62 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 62 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 62) tmFiber10State62_in_close_short

theorem tmFiber10State63_in_close :
    tmFiber10StateAt 63 ∈ closeChainFiber tmWord tmFiber10DirectStates tmFiber10DirectStates.length [tmFiber10StateAt 0] := by
  change tmFiber10StateAt 63 ∈ closeChainFiber tmWord tmFiber10DirectStates (1 + 63) [tmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber10DirectStates 1 63
    [tmFiber10StateAt 0] (tmFiber10StateAt 63) tmFiber10State63_in_close_short

theorem tmFiber10DirectConnected :
    chainFiberConnected tmWord tmFiber10DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [tmFiber10DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact tmFiber10State0_in_close
  · subst state
    exact tmFiber10State1_in_close
  · subst state
    exact tmFiber10State2_in_close
  · subst state
    exact tmFiber10State3_in_close
  · subst state
    exact tmFiber10State4_in_close
  · subst state
    exact tmFiber10State5_in_close
  · subst state
    exact tmFiber10State6_in_close
  · subst state
    exact tmFiber10State7_in_close
  · subst state
    exact tmFiber10State8_in_close
  · subst state
    exact tmFiber10State9_in_close
  · subst state
    exact tmFiber10State10_in_close
  · subst state
    exact tmFiber10State11_in_close
  · subst state
    exact tmFiber10State12_in_close
  · subst state
    exact tmFiber10State13_in_close
  · subst state
    exact tmFiber10State14_in_close
  · subst state
    exact tmFiber10State15_in_close
  · subst state
    exact tmFiber10State16_in_close
  · subst state
    exact tmFiber10State17_in_close
  · subst state
    exact tmFiber10State18_in_close
  · subst state
    exact tmFiber10State19_in_close
  · subst state
    exact tmFiber10State20_in_close
  · subst state
    exact tmFiber10State21_in_close
  · subst state
    exact tmFiber10State22_in_close
  · subst state
    exact tmFiber10State23_in_close
  · subst state
    exact tmFiber10State24_in_close
  · subst state
    exact tmFiber10State25_in_close
  · subst state
    exact tmFiber10State26_in_close
  · subst state
    exact tmFiber10State27_in_close
  · subst state
    exact tmFiber10State28_in_close
  · subst state
    exact tmFiber10State29_in_close
  · subst state
    exact tmFiber10State30_in_close
  · subst state
    exact tmFiber10State31_in_close
  · subst state
    exact tmFiber10State32_in_close
  · subst state
    exact tmFiber10State33_in_close
  · subst state
    exact tmFiber10State34_in_close
  · subst state
    exact tmFiber10State35_in_close
  · subst state
    exact tmFiber10State36_in_close
  · subst state
    exact tmFiber10State37_in_close
  · subst state
    exact tmFiber10State38_in_close
  · subst state
    exact tmFiber10State39_in_close
  · subst state
    exact tmFiber10State40_in_close
  · subst state
    exact tmFiber10State41_in_close
  · subst state
    exact tmFiber10State42_in_close
  · subst state
    exact tmFiber10State43_in_close
  · subst state
    exact tmFiber10State44_in_close
  · subst state
    exact tmFiber10State45_in_close
  · subst state
    exact tmFiber10State46_in_close
  · subst state
    exact tmFiber10State47_in_close
  · subst state
    exact tmFiber10State48_in_close
  · subst state
    exact tmFiber10State49_in_close
  · subst state
    exact tmFiber10State50_in_close
  · subst state
    exact tmFiber10State51_in_close
  · subst state
    exact tmFiber10State52_in_close
  · subst state
    exact tmFiber10State53_in_close
  · subst state
    exact tmFiber10State54_in_close
  · subst state
    exact tmFiber10State55_in_close
  · subst state
    exact tmFiber10State56_in_close
  · subst state
    exact tmFiber10State57_in_close
  · subst state
    exact tmFiber10State58_in_close
  · subst state
    exact tmFiber10State59_in_close
  · subst state
    exact tmFiber10State60_in_close
  · subst state
    exact tmFiber10State61_in_close
  · subst state
    exact tmFiber10State62_in_close
  · subst state
    exact tmFiber10State63_in_close
  · cases h

end GoertzelLemma818LengthTwoTMLargeFiberBridge

end Mettapedia.GraphTheory.FourColor
