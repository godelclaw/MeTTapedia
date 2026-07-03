import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMLargeFiberBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated multi-pass direct closure bridge for `normal,mirror` size-64 fiber 4

This module proves direct connectedness for one generated size-64 fiber
whose parent order needs multiple closure scans. It is generated from
row-local reverse certificate chunks and keeps Lean on default limits.
-/

namespace GoertzelLemma818LengthTwoTMLargeFiberBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818TauMirrorCertificate
open GoertzelLemma818TauMirrorReverseAudit

def tmFiber4StateAt (i : Nat) : List TauState :=
  directStates (tmFiber4RowAt i).sourceLeft (tmFiber4RowAt i).sourceRight

def tmFiber4DirectStates : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]

def tmFiber4Prefix0 : List (List TauState) :=
  [tmFiber4StateAt 0]

def tmFiber4Prefix1 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1]

def tmFiber4Prefix2 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2]

def tmFiber4Prefix3 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3]

def tmFiber4Prefix4 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4]

def tmFiber4Prefix5 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5]

def tmFiber4Prefix6 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6]

def tmFiber4Prefix7 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7]

def tmFiber4Prefix8 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8]

def tmFiber4Prefix9 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9]

def tmFiber4Prefix10 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10]

def tmFiber4Prefix11 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11]

def tmFiber4Prefix12 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12]

def tmFiber4Prefix13 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13]

def tmFiber4Prefix14 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14]

def tmFiber4Prefix15 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15]

def tmFiber4Prefix16 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16]

def tmFiber4Prefix17 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17]

def tmFiber4Prefix18 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18]

def tmFiber4Prefix19 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19]

def tmFiber4Prefix20 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20]

def tmFiber4Prefix21 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21]

def tmFiber4Prefix22 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22]

def tmFiber4Prefix23 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23]

def tmFiber4Prefix24 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24]

def tmFiber4Prefix25 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25]

def tmFiber4Prefix26 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26]

def tmFiber4Prefix27 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27]

def tmFiber4Prefix28 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28]

def tmFiber4Prefix29 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29]

def tmFiber4Prefix30 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30]

def tmFiber4Prefix31 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31]

def tmFiber4Prefix32 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32]

def tmFiber4Prefix33 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33]

def tmFiber4Prefix34 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34]

def tmFiber4Prefix35 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35]

def tmFiber4Prefix36 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36]

def tmFiber4Prefix37 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37]

def tmFiber4Prefix38 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38]

def tmFiber4Prefix39 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39]

def tmFiber4Prefix40 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40]

def tmFiber4Prefix41 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41]

def tmFiber4Prefix42 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42]

def tmFiber4Prefix43 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43]

def tmFiber4Prefix44 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44]

def tmFiber4Prefix45 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45]

def tmFiber4Prefix46 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46]

def tmFiber4Prefix47 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47]

def tmFiber4Prefix48 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48]

def tmFiber4Prefix49 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49]

def tmFiber4Prefix50 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50]

def tmFiber4Prefix51 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51]

def tmFiber4Prefix52 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52]

def tmFiber4Prefix53 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53]

def tmFiber4Prefix54 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54]

def tmFiber4Prefix55 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55]

def tmFiber4Prefix56 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56]

def tmFiber4Prefix57 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57]

def tmFiber4Prefix58 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58]

def tmFiber4Prefix59 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59]

def tmFiber4Prefix60 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60]

def tmFiber4Prefix61 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61]

def tmFiber4Prefix62 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62]

def tmFiber4Prefix63 : List (List TauState) :=
  [tmFiber4StateAt 0, tmFiber4StateAt 1, tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]

theorem tmFiber4ReverseRow_1_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 1) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk0_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 0) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber4ReverseSingleStep1 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 0) (tmFiber4StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 0) (tmFiber4StateAt 1)
    (tmFiber4RowAt 1).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 1) (by decide) tmFiber4ReverseRow_1_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_2_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 2) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk1_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 2) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber4ReverseSingleStep2 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 1) (tmFiber4StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 1) (tmFiber4StateAt 2)
    (tmFiber4RowAt 2).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 2) (by decide) tmFiber4ReverseRow_2_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_3_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 3) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk1_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 2) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber4ReverseSingleStep3 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 0) (tmFiber4StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 0) (tmFiber4StateAt 3)
    (tmFiber4RowAt 3).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 3) (by decide) tmFiber4ReverseRow_3_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_4_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 4) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk2_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 4) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber4ReverseSingleStep4 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 0) (tmFiber4StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 0) (tmFiber4StateAt 4)
    (tmFiber4RowAt 4).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 4) (by decide) tmFiber4ReverseRow_4_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_5_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 5) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk2_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 4) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber4ReverseSingleStep5 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 1) (tmFiber4StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 1) (tmFiber4StateAt 5)
    (tmFiber4RowAt 5).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 5) (by decide) tmFiber4ReverseRow_5_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_6_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 6) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk3_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 6) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber4ReverseSingleStep6 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 4) (tmFiber4StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 4) (tmFiber4StateAt 6)
    (tmFiber4RowAt 6).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 6) (by decide) tmFiber4ReverseRow_6_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_7_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 7) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk3_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 6) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber4ReverseSingleStep7 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 3) (tmFiber4StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 3) (tmFiber4StateAt 7)
    (tmFiber4RowAt 7).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 7) (by decide) tmFiber4ReverseRow_7_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_8_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 8) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk4_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 8) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber4ReverseSingleStep8 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 0) (tmFiber4StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 0) (tmFiber4StateAt 8)
    (tmFiber4RowAt 8).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 8) (by decide) tmFiber4ReverseRow_8_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_9_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 9) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk4_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 8) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber4ReverseSingleStep9 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 1) (tmFiber4StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 1) (tmFiber4StateAt 9)
    (tmFiber4RowAt 9).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 9) (by decide) tmFiber4ReverseRow_9_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_10_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 10) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk5_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 10) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber4ReverseSingleStep10 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 2) (tmFiber4StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 2) (tmFiber4StateAt 10)
    (tmFiber4RowAt 10).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 10) (by decide) tmFiber4ReverseRow_10_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_11_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 11) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk5_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 10) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber4ReverseSingleStep11 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 3) (tmFiber4StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 3) (tmFiber4StateAt 11)
    (tmFiber4RowAt 11).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 11) (by decide) tmFiber4ReverseRow_11_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_12_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 12) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk6_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 12) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber4ReverseSingleStep12 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 4) (tmFiber4StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 4) (tmFiber4StateAt 12)
    (tmFiber4RowAt 12).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 12) (by decide) tmFiber4ReverseRow_12_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_13_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 13) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk6_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 12) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber4ReverseSingleStep13 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 5) (tmFiber4StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 5) (tmFiber4StateAt 13)
    (tmFiber4RowAt 13).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 13) (by decide) tmFiber4ReverseRow_13_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_14_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 14) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk7_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 14) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber4ReverseSingleStep14 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 6) (tmFiber4StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 6) (tmFiber4StateAt 14)
    (tmFiber4RowAt 14).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 14) (by decide) tmFiber4ReverseRow_14_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_15_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 15) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk7_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 14) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber4ReverseSingleStep15 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 7) (tmFiber4StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 7) (tmFiber4StateAt 15)
    (tmFiber4RowAt 15).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 15) (by decide) tmFiber4ReverseRow_15_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_16_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 16) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk8_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 16) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber4ReverseSingleStep16 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 0) (tmFiber4StateAt 16) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 0) (tmFiber4StateAt 16)
    (tmFiber4RowAt 16).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 16) (by decide) tmFiber4ReverseRow_16_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_17_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 17) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk8_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 16) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber4ReverseSingleStep17 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 1) (tmFiber4StateAt 17) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 1) (tmFiber4StateAt 17)
    (tmFiber4RowAt 17).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 17) (by decide) tmFiber4ReverseRow_17_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_18_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 18) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk9_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 18) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber4ReverseSingleStep18 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 2) (tmFiber4StateAt 18) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 2) (tmFiber4StateAt 18)
    (tmFiber4RowAt 18).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 18) (by decide) tmFiber4ReverseRow_18_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_19_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 19) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk9_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 18) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber4ReverseSingleStep19 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 3) (tmFiber4StateAt 19) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 3) (tmFiber4StateAt 19)
    (tmFiber4RowAt 19).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 19) (by decide) tmFiber4ReverseRow_19_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_20_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 20) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk10_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 20) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber4ReverseSingleStep20 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 4) (tmFiber4StateAt 20) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 4) (tmFiber4StateAt 20)
    (tmFiber4RowAt 20).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 20) (by decide) tmFiber4ReverseRow_20_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_21_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 21) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk10_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 20) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber4ReverseSingleStep21 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 5) (tmFiber4StateAt 21) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 5) (tmFiber4StateAt 21)
    (tmFiber4RowAt 21).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 21) (by decide) tmFiber4ReverseRow_21_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_22_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 22) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk11_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 22) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber4ReverseSingleStep22 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 6) (tmFiber4StateAt 22) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 6) (tmFiber4StateAt 22)
    (tmFiber4RowAt 22).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 22) (by decide) tmFiber4ReverseRow_22_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_23_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 23) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk11_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 22) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber4ReverseSingleStep23 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 7) (tmFiber4StateAt 23) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 7) (tmFiber4StateAt 23)
    (tmFiber4RowAt 23).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 23) (by decide) tmFiber4ReverseRow_23_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_24_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 24) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk12_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 24) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber4ReverseSingleStep24 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 8) (tmFiber4StateAt 24) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 8) (tmFiber4StateAt 24)
    (tmFiber4RowAt 24).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 24) (by decide) tmFiber4ReverseRow_24_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_25_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 25) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk12_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 24) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber4ReverseSingleStep25 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 9) (tmFiber4StateAt 25) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 9) (tmFiber4StateAt 25)
    (tmFiber4RowAt 25).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 25) (by decide) tmFiber4ReverseRow_25_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_26_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 26) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk13_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 26) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber4ReverseSingleStep26 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 10) (tmFiber4StateAt 26) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 10) (tmFiber4StateAt 26)
    (tmFiber4RowAt 26).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 26) (by decide) tmFiber4ReverseRow_26_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_27_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 27) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk13_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 26) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber4ReverseSingleStep27 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 11) (tmFiber4StateAt 27) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 11) (tmFiber4StateAt 27)
    (tmFiber4RowAt 27).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 27) (by decide) tmFiber4ReverseRow_27_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_28_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 28) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk14_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 28) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber4ReverseSingleStep28 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 12) (tmFiber4StateAt 28) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 12) (tmFiber4StateAt 28)
    (tmFiber4RowAt 28).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 28) (by decide) tmFiber4ReverseRow_28_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_29_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 29) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk14_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 28) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber4ReverseSingleStep29 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 13) (tmFiber4StateAt 29) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 13) (tmFiber4StateAt 29)
    (tmFiber4RowAt 29).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 29) (by decide) tmFiber4ReverseRow_29_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_30_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 30) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk15_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 30) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber4ReverseSingleStep30 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 14) (tmFiber4StateAt 30) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 14) (tmFiber4StateAt 30)
    (tmFiber4RowAt 30).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 30) (by decide) tmFiber4ReverseRow_30_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_31_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 31) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk15_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 30) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber4ReverseSingleStep31 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 15) (tmFiber4StateAt 31) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 15) (tmFiber4StateAt 31)
    (tmFiber4RowAt 31).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 31) (by decide) tmFiber4ReverseRow_31_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_32_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 32) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk16_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 32) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber4ReverseSingleStep32 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 36) (tmFiber4StateAt 32) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 36) (tmFiber4StateAt 32)
    (tmFiber4RowAt 32).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 32) (by decide) tmFiber4ReverseRow_32_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_33_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 33) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk16_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 32) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber4ReverseSingleStep33 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 37) (tmFiber4StateAt 33) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 37) (tmFiber4StateAt 33)
    (tmFiber4RowAt 33).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 33) (by decide) tmFiber4ReverseRow_33_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_34_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 34) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk17_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 34) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber4ReverseSingleStep34 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 20) (tmFiber4StateAt 34) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 20) (tmFiber4StateAt 34)
    (tmFiber4RowAt 34).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 34) (by decide) tmFiber4ReverseRow_34_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_35_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 35) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk17_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 34) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber4ReverseSingleStep35 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 21) (tmFiber4StateAt 35) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 21) (tmFiber4StateAt 35)
    (tmFiber4RowAt 35).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 35) (by decide) tmFiber4ReverseRow_35_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_36_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 36) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk18_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 36) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber4ReverseSingleStep36 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 16) (tmFiber4StateAt 36) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 16) (tmFiber4StateAt 36)
    (tmFiber4RowAt 36).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 36) (by decide) tmFiber4ReverseRow_36_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_37_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 37) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk18_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 36) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber4ReverseSingleStep37 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 17) (tmFiber4StateAt 37) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 17) (tmFiber4StateAt 37)
    (tmFiber4RowAt 37).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 37) (by decide) tmFiber4ReverseRow_37_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_38_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 38) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk19_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 38) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber4ReverseSingleStep38 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 18) (tmFiber4StateAt 38) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 18) (tmFiber4StateAt 38)
    (tmFiber4RowAt 38).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 38) (by decide) tmFiber4ReverseRow_38_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_39_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 39) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk19_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 38) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber4ReverseSingleStep39 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 19) (tmFiber4StateAt 39) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 19) (tmFiber4StateAt 39)
    (tmFiber4RowAt 39).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 39) (by decide) tmFiber4ReverseRow_39_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_40_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 40) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk20_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 40) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber4ReverseSingleStep40 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 44) (tmFiber4StateAt 40) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 44) (tmFiber4StateAt 40)
    (tmFiber4RowAt 40).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 40) (by decide) tmFiber4ReverseRow_40_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_41_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 41) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk20_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 40) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber4ReverseSingleStep41 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 45) (tmFiber4StateAt 41) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 45) (tmFiber4StateAt 41)
    (tmFiber4RowAt 41).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 41) (by decide) tmFiber4ReverseRow_41_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_42_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 42) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk21_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 42) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber4ReverseSingleStep42 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 58) (tmFiber4StateAt 42) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 58) (tmFiber4StateAt 42)
    (tmFiber4RowAt 42).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 42) (by decide) tmFiber4ReverseRow_42_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_43_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 43) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk21_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 42) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber4ReverseSingleStep43 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 59) (tmFiber4StateAt 43) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 59) (tmFiber4StateAt 43)
    (tmFiber4RowAt 43).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 43) (by decide) tmFiber4ReverseRow_43_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_44_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 44) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk22_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 44) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber4ReverseSingleStep44 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 60) (tmFiber4StateAt 44) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 60) (tmFiber4StateAt 44)
    (tmFiber4RowAt 44).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 44) (by decide) tmFiber4ReverseRow_44_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_45_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 45) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk22_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 44) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber4ReverseSingleStep45 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 61) (tmFiber4StateAt 45) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 61) (tmFiber4StateAt 45)
    (tmFiber4RowAt 45).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 45) (by decide) tmFiber4ReverseRow_45_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_46_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 46) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk23_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 46) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber4ReverseSingleStep46 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 62) (tmFiber4StateAt 46) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 62) (tmFiber4StateAt 46)
    (tmFiber4RowAt 46).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 46) (by decide) tmFiber4ReverseRow_46_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_47_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 47) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk23_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 46) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber4ReverseSingleStep47 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 63) (tmFiber4StateAt 47) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 63) (tmFiber4StateAt 47)
    (tmFiber4RowAt 47).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 47) (by decide) tmFiber4ReverseRow_47_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_48_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 48) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk24_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 48) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber4ReverseSingleStep48 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 52) (tmFiber4StateAt 48) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 52) (tmFiber4StateAt 48)
    (tmFiber4RowAt 48).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 48) (by decide) tmFiber4ReverseRow_48_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_49_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 49) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk24_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 48) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber4ReverseSingleStep49 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 53) (tmFiber4StateAt 49) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 53) (tmFiber4StateAt 49)
    (tmFiber4RowAt 49).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 49) (by decide) tmFiber4ReverseRow_49_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_50_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 50) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk25_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 50) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber4ReverseSingleStep50 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 12) (tmFiber4StateAt 50) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 12) (tmFiber4StateAt 50)
    (tmFiber4RowAt 50).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 50) (by decide) tmFiber4ReverseRow_50_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_51_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 51) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk25_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 50) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber4ReverseSingleStep51 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 13) (tmFiber4StateAt 51) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 13) (tmFiber4StateAt 51)
    (tmFiber4RowAt 51).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 51) (by decide) tmFiber4ReverseRow_51_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_52_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 52) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk26_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 52) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber4ReverseSingleStep52 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 8) (tmFiber4StateAt 52) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 8) (tmFiber4StateAt 52)
    (tmFiber4RowAt 52).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 52) (by decide) tmFiber4ReverseRow_52_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_53_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 53) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk26_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 52) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber4ReverseSingleStep53 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 9) (tmFiber4StateAt 53) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 9) (tmFiber4StateAt 53)
    (tmFiber4RowAt 53).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 53) (by decide) tmFiber4ReverseRow_53_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_54_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 54) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk27_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 54) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber4ReverseSingleStep54 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 10) (tmFiber4StateAt 54) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 10) (tmFiber4StateAt 54)
    (tmFiber4RowAt 54).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 54) (by decide) tmFiber4ReverseRow_54_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_55_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 55) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk27_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 54) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber4ReverseSingleStep55 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 11) (tmFiber4StateAt 55) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 11) (tmFiber4StateAt 55)
    (tmFiber4RowAt 55).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 55) (by decide) tmFiber4ReverseRow_55_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_56_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 56) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk28_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 56) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber4ReverseSingleStep56 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 60) (tmFiber4StateAt 56) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 60) (tmFiber4StateAt 56)
    (tmFiber4RowAt 56).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 56) (by decide) tmFiber4ReverseRow_56_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_57_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 57) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk28_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 56) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber4ReverseSingleStep57 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 61) (tmFiber4StateAt 57) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 61) (tmFiber4StateAt 57)
    (tmFiber4RowAt 57).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 57) (by decide) tmFiber4ReverseRow_57_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_58_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 58) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk29_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 58) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber4ReverseSingleStep58 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 4) (tmFiber4StateAt 58) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 4) (tmFiber4StateAt 58)
    (tmFiber4RowAt 58).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 58) (by decide) tmFiber4ReverseRow_58_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_59_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 59) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk29_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 58) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber4ReverseSingleStep59 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 5) (tmFiber4StateAt 59) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 5) (tmFiber4StateAt 59)
    (tmFiber4RowAt 59).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 59) (by decide) tmFiber4ReverseRow_59_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_60_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 60) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk30_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 60) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber4ReverseSingleStep60 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 0) (tmFiber4StateAt 60) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 0) (tmFiber4StateAt 60)
    (tmFiber4RowAt 60).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 60) (by decide) tmFiber4ReverseRow_60_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_61_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 61) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk30_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 60) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber4ReverseSingleStep61 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 1) (tmFiber4StateAt 61) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 1) (tmFiber4StateAt 61)
    (tmFiber4RowAt 61).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 61) (by decide) tmFiber4ReverseRow_61_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_62_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 62) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk31_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 62) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber4ReverseSingleStep62 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 2) (tmFiber4StateAt 62) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 2) (tmFiber4StateAt 62)
    (tmFiber4RowAt 62).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 62) (by decide) tmFiber4ReverseRow_62_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4ReverseRow_63_ok :
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 63) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber4Chunk31_ok
  change (tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 62) &&
    tmRowReverseValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber4ReverseSingleStep63 :
    chainSingleKempeStep tmWord (tmFiber4StateAt 3) (tmFiber4StateAt 63) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber4StateAt 3) (tmFiber4StateAt 63)
    (tmFiber4RowAt 63).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber4Key tmFiber4Expected
        (tmFiber4RowAt 63) (by decide) tmFiber4ReverseRow_63_ok
      simpa [tmFiber4StateAt, tmFiber4RowAt, tmFiber4Rows, listGetD, directRow] using h)

theorem tmFiber4State1_in_pass1_prefix1 :
    tmFiber4StateAt 1 ∈ chainClosureStep tmWord tmFiber4Prefix1 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 0 ∈
      chainClosureStep tmWord tmFiber4Prefix0 ([tmFiber4StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber4Prefix0
      ([tmFiber4StateAt 0]) (tmFiber4StateAt 0) (by simp)
  rw [show tmFiber4Prefix1 = tmFiber4Prefix0 ++ [tmFiber4StateAt 1] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 1) []
    (chainClosureStep tmWord tmFiber4Prefix0 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 0) hparentBefore tmFiber4ReverseSingleStep1

theorem tmFiber4State1_in_pass1_full :
    tmFiber4StateAt 1 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix1 ++ [tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix1 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 1) tmFiber4State1_in_pass1_prefix1

theorem tmFiber4State2_in_pass1_prefix2 :
    tmFiber4StateAt 2 ∈ chainClosureStep tmWord tmFiber4Prefix2 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 1 ∈
      chainClosureStep tmWord tmFiber4Prefix1 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix1 = tmFiber4Prefix1 ++ [] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord []
      (chainClosureStep tmWord tmFiber4Prefix1 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 1) tmFiber4State1_in_pass1_prefix1
  rw [show tmFiber4Prefix2 = tmFiber4Prefix1 ++ [tmFiber4StateAt 2] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 2) []
    (chainClosureStep tmWord tmFiber4Prefix1 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 1) hparentBefore tmFiber4ReverseSingleStep2

theorem tmFiber4State2_in_pass1_full :
    tmFiber4StateAt 2 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix2 ++ [tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix2 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 2) tmFiber4State2_in_pass1_prefix2

theorem tmFiber4State3_in_pass1_prefix3 :
    tmFiber4StateAt 3 ∈ chainClosureStep tmWord tmFiber4Prefix3 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 0 ∈
      chainClosureStep tmWord tmFiber4Prefix2 ([tmFiber4StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber4Prefix2
      ([tmFiber4StateAt 0]) (tmFiber4StateAt 0) (by simp)
  rw [show tmFiber4Prefix3 = tmFiber4Prefix2 ++ [tmFiber4StateAt 3] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 3) []
    (chainClosureStep tmWord tmFiber4Prefix2 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 0) hparentBefore tmFiber4ReverseSingleStep3

theorem tmFiber4State3_in_pass1_full :
    tmFiber4StateAt 3 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix3 ++ [tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix3 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 3) tmFiber4State3_in_pass1_prefix3

theorem tmFiber4State4_in_pass1_prefix4 :
    tmFiber4StateAt 4 ∈ chainClosureStep tmWord tmFiber4Prefix4 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 0 ∈
      chainClosureStep tmWord tmFiber4Prefix3 ([tmFiber4StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber4Prefix3
      ([tmFiber4StateAt 0]) (tmFiber4StateAt 0) (by simp)
  rw [show tmFiber4Prefix4 = tmFiber4Prefix3 ++ [tmFiber4StateAt 4] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 4) []
    (chainClosureStep tmWord tmFiber4Prefix3 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 0) hparentBefore tmFiber4ReverseSingleStep4

theorem tmFiber4State4_in_pass1_full :
    tmFiber4StateAt 4 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix4 ++ [tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix4 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 4) tmFiber4State4_in_pass1_prefix4

theorem tmFiber4State5_in_pass1_prefix5 :
    tmFiber4StateAt 5 ∈ chainClosureStep tmWord tmFiber4Prefix5 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 1 ∈
      chainClosureStep tmWord tmFiber4Prefix4 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix4 = tmFiber4Prefix1 ++ [tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4]
      (chainClosureStep tmWord tmFiber4Prefix1 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 1) tmFiber4State1_in_pass1_prefix1
  rw [show tmFiber4Prefix5 = tmFiber4Prefix4 ++ [tmFiber4StateAt 5] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 5) []
    (chainClosureStep tmWord tmFiber4Prefix4 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 1) hparentBefore tmFiber4ReverseSingleStep5

theorem tmFiber4State5_in_pass1_full :
    tmFiber4StateAt 5 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix5 ++ [tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix5 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 5) tmFiber4State5_in_pass1_prefix5

theorem tmFiber4State6_in_pass1_prefix6 :
    tmFiber4StateAt 6 ∈ chainClosureStep tmWord tmFiber4Prefix6 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 4 ∈
      chainClosureStep tmWord tmFiber4Prefix5 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix5 = tmFiber4Prefix4 ++ [tmFiber4StateAt 5] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 5]
      (chainClosureStep tmWord tmFiber4Prefix4 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 4) tmFiber4State4_in_pass1_prefix4
  rw [show tmFiber4Prefix6 = tmFiber4Prefix5 ++ [tmFiber4StateAt 6] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 6) []
    (chainClosureStep tmWord tmFiber4Prefix5 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 4) hparentBefore tmFiber4ReverseSingleStep6

theorem tmFiber4State6_in_pass1_full :
    tmFiber4StateAt 6 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix6 ++ [tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix6 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 6) tmFiber4State6_in_pass1_prefix6

theorem tmFiber4State7_in_pass1_prefix7 :
    tmFiber4StateAt 7 ∈ chainClosureStep tmWord tmFiber4Prefix7 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 3 ∈
      chainClosureStep tmWord tmFiber4Prefix6 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix6 = tmFiber4Prefix3 ++ [tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6]
      (chainClosureStep tmWord tmFiber4Prefix3 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 3) tmFiber4State3_in_pass1_prefix3
  rw [show tmFiber4Prefix7 = tmFiber4Prefix6 ++ [tmFiber4StateAt 7] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 7) []
    (chainClosureStep tmWord tmFiber4Prefix6 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 3) hparentBefore tmFiber4ReverseSingleStep7

theorem tmFiber4State7_in_pass1_full :
    tmFiber4StateAt 7 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix7 ++ [tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix7 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 7) tmFiber4State7_in_pass1_prefix7

theorem tmFiber4State8_in_pass1_prefix8 :
    tmFiber4StateAt 8 ∈ chainClosureStep tmWord tmFiber4Prefix8 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 0 ∈
      chainClosureStep tmWord tmFiber4Prefix7 ([tmFiber4StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber4Prefix7
      ([tmFiber4StateAt 0]) (tmFiber4StateAt 0) (by simp)
  rw [show tmFiber4Prefix8 = tmFiber4Prefix7 ++ [tmFiber4StateAt 8] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 8) []
    (chainClosureStep tmWord tmFiber4Prefix7 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 0) hparentBefore tmFiber4ReverseSingleStep8

theorem tmFiber4State8_in_pass1_full :
    tmFiber4StateAt 8 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix8 ++ [tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix8 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 8) tmFiber4State8_in_pass1_prefix8

theorem tmFiber4State9_in_pass1_prefix9 :
    tmFiber4StateAt 9 ∈ chainClosureStep tmWord tmFiber4Prefix9 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 1 ∈
      chainClosureStep tmWord tmFiber4Prefix8 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix8 = tmFiber4Prefix1 ++ [tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8]
      (chainClosureStep tmWord tmFiber4Prefix1 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 1) tmFiber4State1_in_pass1_prefix1
  rw [show tmFiber4Prefix9 = tmFiber4Prefix8 ++ [tmFiber4StateAt 9] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 9) []
    (chainClosureStep tmWord tmFiber4Prefix8 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 1) hparentBefore tmFiber4ReverseSingleStep9

theorem tmFiber4State9_in_pass1_full :
    tmFiber4StateAt 9 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix9 ++ [tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix9 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 9) tmFiber4State9_in_pass1_prefix9

theorem tmFiber4State10_in_pass1_prefix10 :
    tmFiber4StateAt 10 ∈ chainClosureStep tmWord tmFiber4Prefix10 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 2 ∈
      chainClosureStep tmWord tmFiber4Prefix9 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix9 = tmFiber4Prefix2 ++ [tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9]
      (chainClosureStep tmWord tmFiber4Prefix2 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 2) tmFiber4State2_in_pass1_prefix2
  rw [show tmFiber4Prefix10 = tmFiber4Prefix9 ++ [tmFiber4StateAt 10] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 10) []
    (chainClosureStep tmWord tmFiber4Prefix9 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 2) hparentBefore tmFiber4ReverseSingleStep10

theorem tmFiber4State10_in_pass1_full :
    tmFiber4StateAt 10 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix10 ++ [tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix10 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 10) tmFiber4State10_in_pass1_prefix10

theorem tmFiber4State11_in_pass1_prefix11 :
    tmFiber4StateAt 11 ∈ chainClosureStep tmWord tmFiber4Prefix11 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 3 ∈
      chainClosureStep tmWord tmFiber4Prefix10 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix10 = tmFiber4Prefix3 ++ [tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10]
      (chainClosureStep tmWord tmFiber4Prefix3 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 3) tmFiber4State3_in_pass1_prefix3
  rw [show tmFiber4Prefix11 = tmFiber4Prefix10 ++ [tmFiber4StateAt 11] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 11) []
    (chainClosureStep tmWord tmFiber4Prefix10 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 3) hparentBefore tmFiber4ReverseSingleStep11

theorem tmFiber4State11_in_pass1_full :
    tmFiber4StateAt 11 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix11 ++ [tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix11 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 11) tmFiber4State11_in_pass1_prefix11

theorem tmFiber4State12_in_pass1_prefix12 :
    tmFiber4StateAt 12 ∈ chainClosureStep tmWord tmFiber4Prefix12 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 4 ∈
      chainClosureStep tmWord tmFiber4Prefix11 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix11 = tmFiber4Prefix4 ++ [tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11]
      (chainClosureStep tmWord tmFiber4Prefix4 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 4) tmFiber4State4_in_pass1_prefix4
  rw [show tmFiber4Prefix12 = tmFiber4Prefix11 ++ [tmFiber4StateAt 12] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 12) []
    (chainClosureStep tmWord tmFiber4Prefix11 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 4) hparentBefore tmFiber4ReverseSingleStep12

theorem tmFiber4State12_in_pass1_full :
    tmFiber4StateAt 12 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix12 ++ [tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix12 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 12) tmFiber4State12_in_pass1_prefix12

theorem tmFiber4State13_in_pass1_prefix13 :
    tmFiber4StateAt 13 ∈ chainClosureStep tmWord tmFiber4Prefix13 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 5 ∈
      chainClosureStep tmWord tmFiber4Prefix12 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix12 = tmFiber4Prefix5 ++ [tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12]
      (chainClosureStep tmWord tmFiber4Prefix5 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 5) tmFiber4State5_in_pass1_prefix5
  rw [show tmFiber4Prefix13 = tmFiber4Prefix12 ++ [tmFiber4StateAt 13] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 13) []
    (chainClosureStep tmWord tmFiber4Prefix12 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 5) hparentBefore tmFiber4ReverseSingleStep13

theorem tmFiber4State13_in_pass1_full :
    tmFiber4StateAt 13 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix13 ++ [tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix13 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 13) tmFiber4State13_in_pass1_prefix13

theorem tmFiber4State14_in_pass1_prefix14 :
    tmFiber4StateAt 14 ∈ chainClosureStep tmWord tmFiber4Prefix14 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 6 ∈
      chainClosureStep tmWord tmFiber4Prefix13 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix13 = tmFiber4Prefix6 ++ [tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13]
      (chainClosureStep tmWord tmFiber4Prefix6 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 6) tmFiber4State6_in_pass1_prefix6
  rw [show tmFiber4Prefix14 = tmFiber4Prefix13 ++ [tmFiber4StateAt 14] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 14) []
    (chainClosureStep tmWord tmFiber4Prefix13 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 6) hparentBefore tmFiber4ReverseSingleStep14

theorem tmFiber4State14_in_pass1_full :
    tmFiber4StateAt 14 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix14 ++ [tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix14 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 14) tmFiber4State14_in_pass1_prefix14

theorem tmFiber4State15_in_pass1_prefix15 :
    tmFiber4StateAt 15 ∈ chainClosureStep tmWord tmFiber4Prefix15 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 7 ∈
      chainClosureStep tmWord tmFiber4Prefix14 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix14 = tmFiber4Prefix7 ++ [tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14]
      (chainClosureStep tmWord tmFiber4Prefix7 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 7) tmFiber4State7_in_pass1_prefix7
  rw [show tmFiber4Prefix15 = tmFiber4Prefix14 ++ [tmFiber4StateAt 15] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 15) []
    (chainClosureStep tmWord tmFiber4Prefix14 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 7) hparentBefore tmFiber4ReverseSingleStep15

theorem tmFiber4State15_in_pass1_full :
    tmFiber4StateAt 15 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix15 ++ [tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix15 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 15) tmFiber4State15_in_pass1_prefix15

theorem tmFiber4State16_in_pass1_prefix16 :
    tmFiber4StateAt 16 ∈ chainClosureStep tmWord tmFiber4Prefix16 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 0 ∈
      chainClosureStep tmWord tmFiber4Prefix15 ([tmFiber4StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber4Prefix15
      ([tmFiber4StateAt 0]) (tmFiber4StateAt 0) (by simp)
  rw [show tmFiber4Prefix16 = tmFiber4Prefix15 ++ [tmFiber4StateAt 16] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 16) []
    (chainClosureStep tmWord tmFiber4Prefix15 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 0) hparentBefore tmFiber4ReverseSingleStep16

theorem tmFiber4State16_in_pass1_full :
    tmFiber4StateAt 16 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix16 ++ [tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix16 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 16) tmFiber4State16_in_pass1_prefix16

theorem tmFiber4State17_in_pass1_prefix17 :
    tmFiber4StateAt 17 ∈ chainClosureStep tmWord tmFiber4Prefix17 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 1 ∈
      chainClosureStep tmWord tmFiber4Prefix16 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix16 = tmFiber4Prefix1 ++ [tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16]
      (chainClosureStep tmWord tmFiber4Prefix1 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 1) tmFiber4State1_in_pass1_prefix1
  rw [show tmFiber4Prefix17 = tmFiber4Prefix16 ++ [tmFiber4StateAt 17] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 17) []
    (chainClosureStep tmWord tmFiber4Prefix16 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 1) hparentBefore tmFiber4ReverseSingleStep17

theorem tmFiber4State17_in_pass1_full :
    tmFiber4StateAt 17 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix17 ++ [tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix17 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 17) tmFiber4State17_in_pass1_prefix17

theorem tmFiber4State18_in_pass1_prefix18 :
    tmFiber4StateAt 18 ∈ chainClosureStep tmWord tmFiber4Prefix18 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 2 ∈
      chainClosureStep tmWord tmFiber4Prefix17 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix17 = tmFiber4Prefix2 ++ [tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17]
      (chainClosureStep tmWord tmFiber4Prefix2 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 2) tmFiber4State2_in_pass1_prefix2
  rw [show tmFiber4Prefix18 = tmFiber4Prefix17 ++ [tmFiber4StateAt 18] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 18) []
    (chainClosureStep tmWord tmFiber4Prefix17 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 2) hparentBefore tmFiber4ReverseSingleStep18

theorem tmFiber4State18_in_pass1_full :
    tmFiber4StateAt 18 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix18 ++ [tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix18 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 18) tmFiber4State18_in_pass1_prefix18

theorem tmFiber4State19_in_pass1_prefix19 :
    tmFiber4StateAt 19 ∈ chainClosureStep tmWord tmFiber4Prefix19 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 3 ∈
      chainClosureStep tmWord tmFiber4Prefix18 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix18 = tmFiber4Prefix3 ++ [tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18]
      (chainClosureStep tmWord tmFiber4Prefix3 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 3) tmFiber4State3_in_pass1_prefix3
  rw [show tmFiber4Prefix19 = tmFiber4Prefix18 ++ [tmFiber4StateAt 19] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 19) []
    (chainClosureStep tmWord tmFiber4Prefix18 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 3) hparentBefore tmFiber4ReverseSingleStep19

theorem tmFiber4State19_in_pass1_full :
    tmFiber4StateAt 19 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix19 ++ [tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix19 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 19) tmFiber4State19_in_pass1_prefix19

theorem tmFiber4State20_in_pass1_prefix20 :
    tmFiber4StateAt 20 ∈ chainClosureStep tmWord tmFiber4Prefix20 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 4 ∈
      chainClosureStep tmWord tmFiber4Prefix19 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix19 = tmFiber4Prefix4 ++ [tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19]
      (chainClosureStep tmWord tmFiber4Prefix4 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 4) tmFiber4State4_in_pass1_prefix4
  rw [show tmFiber4Prefix20 = tmFiber4Prefix19 ++ [tmFiber4StateAt 20] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 20) []
    (chainClosureStep tmWord tmFiber4Prefix19 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 4) hparentBefore tmFiber4ReverseSingleStep20

theorem tmFiber4State20_in_pass1_full :
    tmFiber4StateAt 20 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix20 ++ [tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix20 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 20) tmFiber4State20_in_pass1_prefix20

theorem tmFiber4State21_in_pass1_prefix21 :
    tmFiber4StateAt 21 ∈ chainClosureStep tmWord tmFiber4Prefix21 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 5 ∈
      chainClosureStep tmWord tmFiber4Prefix20 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix20 = tmFiber4Prefix5 ++ [tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20]
      (chainClosureStep tmWord tmFiber4Prefix5 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 5) tmFiber4State5_in_pass1_prefix5
  rw [show tmFiber4Prefix21 = tmFiber4Prefix20 ++ [tmFiber4StateAt 21] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 21) []
    (chainClosureStep tmWord tmFiber4Prefix20 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 5) hparentBefore tmFiber4ReverseSingleStep21

theorem tmFiber4State21_in_pass1_full :
    tmFiber4StateAt 21 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix21 ++ [tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix21 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 21) tmFiber4State21_in_pass1_prefix21

theorem tmFiber4State22_in_pass1_prefix22 :
    tmFiber4StateAt 22 ∈ chainClosureStep tmWord tmFiber4Prefix22 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 6 ∈
      chainClosureStep tmWord tmFiber4Prefix21 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix21 = tmFiber4Prefix6 ++ [tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21]
      (chainClosureStep tmWord tmFiber4Prefix6 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 6) tmFiber4State6_in_pass1_prefix6
  rw [show tmFiber4Prefix22 = tmFiber4Prefix21 ++ [tmFiber4StateAt 22] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 22) []
    (chainClosureStep tmWord tmFiber4Prefix21 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 6) hparentBefore tmFiber4ReverseSingleStep22

theorem tmFiber4State22_in_pass1_full :
    tmFiber4StateAt 22 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix22 ++ [tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix22 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 22) tmFiber4State22_in_pass1_prefix22

theorem tmFiber4State23_in_pass1_prefix23 :
    tmFiber4StateAt 23 ∈ chainClosureStep tmWord tmFiber4Prefix23 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 7 ∈
      chainClosureStep tmWord tmFiber4Prefix22 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix22 = tmFiber4Prefix7 ++ [tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22]
      (chainClosureStep tmWord tmFiber4Prefix7 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 7) tmFiber4State7_in_pass1_prefix7
  rw [show tmFiber4Prefix23 = tmFiber4Prefix22 ++ [tmFiber4StateAt 23] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 23) []
    (chainClosureStep tmWord tmFiber4Prefix22 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 7) hparentBefore tmFiber4ReverseSingleStep23

theorem tmFiber4State23_in_pass1_full :
    tmFiber4StateAt 23 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix23 ++ [tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix23 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 23) tmFiber4State23_in_pass1_prefix23

theorem tmFiber4State24_in_pass1_prefix24 :
    tmFiber4StateAt 24 ∈ chainClosureStep tmWord tmFiber4Prefix24 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 8 ∈
      chainClosureStep tmWord tmFiber4Prefix23 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix23 = tmFiber4Prefix8 ++ [tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23]
      (chainClosureStep tmWord tmFiber4Prefix8 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 8) tmFiber4State8_in_pass1_prefix8
  rw [show tmFiber4Prefix24 = tmFiber4Prefix23 ++ [tmFiber4StateAt 24] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 24) []
    (chainClosureStep tmWord tmFiber4Prefix23 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 8) hparentBefore tmFiber4ReverseSingleStep24

theorem tmFiber4State24_in_pass1_full :
    tmFiber4StateAt 24 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix24 ++ [tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix24 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 24) tmFiber4State24_in_pass1_prefix24

theorem tmFiber4State25_in_pass1_prefix25 :
    tmFiber4StateAt 25 ∈ chainClosureStep tmWord tmFiber4Prefix25 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 9 ∈
      chainClosureStep tmWord tmFiber4Prefix24 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix24 = tmFiber4Prefix9 ++ [tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24]
      (chainClosureStep tmWord tmFiber4Prefix9 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 9) tmFiber4State9_in_pass1_prefix9
  rw [show tmFiber4Prefix25 = tmFiber4Prefix24 ++ [tmFiber4StateAt 25] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 25) []
    (chainClosureStep tmWord tmFiber4Prefix24 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 9) hparentBefore tmFiber4ReverseSingleStep25

theorem tmFiber4State25_in_pass1_full :
    tmFiber4StateAt 25 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix25 ++ [tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix25 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 25) tmFiber4State25_in_pass1_prefix25

theorem tmFiber4State26_in_pass1_prefix26 :
    tmFiber4StateAt 26 ∈ chainClosureStep tmWord tmFiber4Prefix26 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 10 ∈
      chainClosureStep tmWord tmFiber4Prefix25 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix25 = tmFiber4Prefix10 ++ [tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25]
      (chainClosureStep tmWord tmFiber4Prefix10 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 10) tmFiber4State10_in_pass1_prefix10
  rw [show tmFiber4Prefix26 = tmFiber4Prefix25 ++ [tmFiber4StateAt 26] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 26) []
    (chainClosureStep tmWord tmFiber4Prefix25 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 10) hparentBefore tmFiber4ReverseSingleStep26

theorem tmFiber4State26_in_pass1_full :
    tmFiber4StateAt 26 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix26 ++ [tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix26 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 26) tmFiber4State26_in_pass1_prefix26

theorem tmFiber4State27_in_pass1_prefix27 :
    tmFiber4StateAt 27 ∈ chainClosureStep tmWord tmFiber4Prefix27 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 11 ∈
      chainClosureStep tmWord tmFiber4Prefix26 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix26 = tmFiber4Prefix11 ++ [tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26]
      (chainClosureStep tmWord tmFiber4Prefix11 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 11) tmFiber4State11_in_pass1_prefix11
  rw [show tmFiber4Prefix27 = tmFiber4Prefix26 ++ [tmFiber4StateAt 27] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 27) []
    (chainClosureStep tmWord tmFiber4Prefix26 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 11) hparentBefore tmFiber4ReverseSingleStep27

theorem tmFiber4State27_in_pass1_full :
    tmFiber4StateAt 27 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix27 ++ [tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix27 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 27) tmFiber4State27_in_pass1_prefix27

theorem tmFiber4State28_in_pass1_prefix28 :
    tmFiber4StateAt 28 ∈ chainClosureStep tmWord tmFiber4Prefix28 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 12 ∈
      chainClosureStep tmWord tmFiber4Prefix27 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix27 = tmFiber4Prefix12 ++ [tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27]
      (chainClosureStep tmWord tmFiber4Prefix12 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 12) tmFiber4State12_in_pass1_prefix12
  rw [show tmFiber4Prefix28 = tmFiber4Prefix27 ++ [tmFiber4StateAt 28] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 28) []
    (chainClosureStep tmWord tmFiber4Prefix27 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 12) hparentBefore tmFiber4ReverseSingleStep28

theorem tmFiber4State28_in_pass1_full :
    tmFiber4StateAt 28 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix28 ++ [tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix28 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 28) tmFiber4State28_in_pass1_prefix28

theorem tmFiber4State29_in_pass1_prefix29 :
    tmFiber4StateAt 29 ∈ chainClosureStep tmWord tmFiber4Prefix29 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 13 ∈
      chainClosureStep tmWord tmFiber4Prefix28 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix28 = tmFiber4Prefix13 ++ [tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28]
      (chainClosureStep tmWord tmFiber4Prefix13 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 13) tmFiber4State13_in_pass1_prefix13
  rw [show tmFiber4Prefix29 = tmFiber4Prefix28 ++ [tmFiber4StateAt 29] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 29) []
    (chainClosureStep tmWord tmFiber4Prefix28 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 13) hparentBefore tmFiber4ReverseSingleStep29

theorem tmFiber4State29_in_pass1_full :
    tmFiber4StateAt 29 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix29 ++ [tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix29 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 29) tmFiber4State29_in_pass1_prefix29

theorem tmFiber4State30_in_pass1_prefix30 :
    tmFiber4StateAt 30 ∈ chainClosureStep tmWord tmFiber4Prefix30 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 14 ∈
      chainClosureStep tmWord tmFiber4Prefix29 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix29 = tmFiber4Prefix14 ++ [tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29]
      (chainClosureStep tmWord tmFiber4Prefix14 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 14) tmFiber4State14_in_pass1_prefix14
  rw [show tmFiber4Prefix30 = tmFiber4Prefix29 ++ [tmFiber4StateAt 30] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 30) []
    (chainClosureStep tmWord tmFiber4Prefix29 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 14) hparentBefore tmFiber4ReverseSingleStep30

theorem tmFiber4State30_in_pass1_full :
    tmFiber4StateAt 30 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix30 ++ [tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix30 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 30) tmFiber4State30_in_pass1_prefix30

theorem tmFiber4State31_in_pass1_prefix31 :
    tmFiber4StateAt 31 ∈ chainClosureStep tmWord tmFiber4Prefix31 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 15 ∈
      chainClosureStep tmWord tmFiber4Prefix30 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix30 = tmFiber4Prefix15 ++ [tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30]
      (chainClosureStep tmWord tmFiber4Prefix15 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 15) tmFiber4State15_in_pass1_prefix15
  rw [show tmFiber4Prefix31 = tmFiber4Prefix30 ++ [tmFiber4StateAt 31] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 31) []
    (chainClosureStep tmWord tmFiber4Prefix30 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 15) hparentBefore tmFiber4ReverseSingleStep31

theorem tmFiber4State31_in_pass1_full :
    tmFiber4StateAt 31 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix31 ++ [tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix31 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 31) tmFiber4State31_in_pass1_prefix31

theorem tmFiber4State34_in_pass1_prefix34 :
    tmFiber4StateAt 34 ∈ chainClosureStep tmWord tmFiber4Prefix34 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 20 ∈
      chainClosureStep tmWord tmFiber4Prefix33 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix33 = tmFiber4Prefix20 ++ [tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33]
      (chainClosureStep tmWord tmFiber4Prefix20 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 20) tmFiber4State20_in_pass1_prefix20
  rw [show tmFiber4Prefix34 = tmFiber4Prefix33 ++ [tmFiber4StateAt 34] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 34) []
    (chainClosureStep tmWord tmFiber4Prefix33 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 20) hparentBefore tmFiber4ReverseSingleStep34

theorem tmFiber4State34_in_pass1_full :
    tmFiber4StateAt 34 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix34 ++ [tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix34 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 34) tmFiber4State34_in_pass1_prefix34

theorem tmFiber4State35_in_pass1_prefix35 :
    tmFiber4StateAt 35 ∈ chainClosureStep tmWord tmFiber4Prefix35 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 21 ∈
      chainClosureStep tmWord tmFiber4Prefix34 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix34 = tmFiber4Prefix21 ++ [tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34]
      (chainClosureStep tmWord tmFiber4Prefix21 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 21) tmFiber4State21_in_pass1_prefix21
  rw [show tmFiber4Prefix35 = tmFiber4Prefix34 ++ [tmFiber4StateAt 35] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 35) []
    (chainClosureStep tmWord tmFiber4Prefix34 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 21) hparentBefore tmFiber4ReverseSingleStep35

theorem tmFiber4State35_in_pass1_full :
    tmFiber4StateAt 35 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix35 ++ [tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix35 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 35) tmFiber4State35_in_pass1_prefix35

theorem tmFiber4State36_in_pass1_prefix36 :
    tmFiber4StateAt 36 ∈ chainClosureStep tmWord tmFiber4Prefix36 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 16 ∈
      chainClosureStep tmWord tmFiber4Prefix35 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix35 = tmFiber4Prefix16 ++ [tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35]
      (chainClosureStep tmWord tmFiber4Prefix16 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 16) tmFiber4State16_in_pass1_prefix16
  rw [show tmFiber4Prefix36 = tmFiber4Prefix35 ++ [tmFiber4StateAt 36] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 36) []
    (chainClosureStep tmWord tmFiber4Prefix35 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 16) hparentBefore tmFiber4ReverseSingleStep36

theorem tmFiber4State36_in_pass1_full :
    tmFiber4StateAt 36 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix36 ++ [tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix36 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 36) tmFiber4State36_in_pass1_prefix36

theorem tmFiber4State37_in_pass1_prefix37 :
    tmFiber4StateAt 37 ∈ chainClosureStep tmWord tmFiber4Prefix37 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 17 ∈
      chainClosureStep tmWord tmFiber4Prefix36 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix36 = tmFiber4Prefix17 ++ [tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36]
      (chainClosureStep tmWord tmFiber4Prefix17 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 17) tmFiber4State17_in_pass1_prefix17
  rw [show tmFiber4Prefix37 = tmFiber4Prefix36 ++ [tmFiber4StateAt 37] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 37) []
    (chainClosureStep tmWord tmFiber4Prefix36 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 17) hparentBefore tmFiber4ReverseSingleStep37

theorem tmFiber4State37_in_pass1_full :
    tmFiber4StateAt 37 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix37 ++ [tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix37 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 37) tmFiber4State37_in_pass1_prefix37

theorem tmFiber4State38_in_pass1_prefix38 :
    tmFiber4StateAt 38 ∈ chainClosureStep tmWord tmFiber4Prefix38 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 18 ∈
      chainClosureStep tmWord tmFiber4Prefix37 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix37 = tmFiber4Prefix18 ++ [tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37]
      (chainClosureStep tmWord tmFiber4Prefix18 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 18) tmFiber4State18_in_pass1_prefix18
  rw [show tmFiber4Prefix38 = tmFiber4Prefix37 ++ [tmFiber4StateAt 38] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 38) []
    (chainClosureStep tmWord tmFiber4Prefix37 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 18) hparentBefore tmFiber4ReverseSingleStep38

theorem tmFiber4State38_in_pass1_full :
    tmFiber4StateAt 38 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix38 ++ [tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix38 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 38) tmFiber4State38_in_pass1_prefix38

theorem tmFiber4State39_in_pass1_prefix39 :
    tmFiber4StateAt 39 ∈ chainClosureStep tmWord tmFiber4Prefix39 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 19 ∈
      chainClosureStep tmWord tmFiber4Prefix38 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix38 = tmFiber4Prefix19 ++ [tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38]
      (chainClosureStep tmWord tmFiber4Prefix19 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 19) tmFiber4State19_in_pass1_prefix19
  rw [show tmFiber4Prefix39 = tmFiber4Prefix38 ++ [tmFiber4StateAt 39] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 39) []
    (chainClosureStep tmWord tmFiber4Prefix38 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 19) hparentBefore tmFiber4ReverseSingleStep39

theorem tmFiber4State39_in_pass1_full :
    tmFiber4StateAt 39 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix39 ++ [tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix39 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 39) tmFiber4State39_in_pass1_prefix39

theorem tmFiber4State50_in_pass1_prefix50 :
    tmFiber4StateAt 50 ∈ chainClosureStep tmWord tmFiber4Prefix50 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 12 ∈
      chainClosureStep tmWord tmFiber4Prefix49 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix49 = tmFiber4Prefix12 ++ [tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49]
      (chainClosureStep tmWord tmFiber4Prefix12 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 12) tmFiber4State12_in_pass1_prefix12
  rw [show tmFiber4Prefix50 = tmFiber4Prefix49 ++ [tmFiber4StateAt 50] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 50) []
    (chainClosureStep tmWord tmFiber4Prefix49 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 12) hparentBefore tmFiber4ReverseSingleStep50

theorem tmFiber4State50_in_pass1_full :
    tmFiber4StateAt 50 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix50 ++ [tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix50 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 50) tmFiber4State50_in_pass1_prefix50

theorem tmFiber4State51_in_pass1_prefix51 :
    tmFiber4StateAt 51 ∈ chainClosureStep tmWord tmFiber4Prefix51 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 13 ∈
      chainClosureStep tmWord tmFiber4Prefix50 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix50 = tmFiber4Prefix13 ++ [tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50]
      (chainClosureStep tmWord tmFiber4Prefix13 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 13) tmFiber4State13_in_pass1_prefix13
  rw [show tmFiber4Prefix51 = tmFiber4Prefix50 ++ [tmFiber4StateAt 51] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 51) []
    (chainClosureStep tmWord tmFiber4Prefix50 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 13) hparentBefore tmFiber4ReverseSingleStep51

theorem tmFiber4State51_in_pass1_full :
    tmFiber4StateAt 51 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix51 ++ [tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix51 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 51) tmFiber4State51_in_pass1_prefix51

theorem tmFiber4State52_in_pass1_prefix52 :
    tmFiber4StateAt 52 ∈ chainClosureStep tmWord tmFiber4Prefix52 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 8 ∈
      chainClosureStep tmWord tmFiber4Prefix51 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix51 = tmFiber4Prefix8 ++ [tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51]
      (chainClosureStep tmWord tmFiber4Prefix8 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 8) tmFiber4State8_in_pass1_prefix8
  rw [show tmFiber4Prefix52 = tmFiber4Prefix51 ++ [tmFiber4StateAt 52] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 52) []
    (chainClosureStep tmWord tmFiber4Prefix51 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 8) hparentBefore tmFiber4ReverseSingleStep52

theorem tmFiber4State52_in_pass1_full :
    tmFiber4StateAt 52 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix52 ++ [tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix52 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 52) tmFiber4State52_in_pass1_prefix52

theorem tmFiber4State53_in_pass1_prefix53 :
    tmFiber4StateAt 53 ∈ chainClosureStep tmWord tmFiber4Prefix53 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 9 ∈
      chainClosureStep tmWord tmFiber4Prefix52 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix52 = tmFiber4Prefix9 ++ [tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52]
      (chainClosureStep tmWord tmFiber4Prefix9 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 9) tmFiber4State9_in_pass1_prefix9
  rw [show tmFiber4Prefix53 = tmFiber4Prefix52 ++ [tmFiber4StateAt 53] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 53) []
    (chainClosureStep tmWord tmFiber4Prefix52 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 9) hparentBefore tmFiber4ReverseSingleStep53

theorem tmFiber4State53_in_pass1_full :
    tmFiber4StateAt 53 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix53 ++ [tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix53 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 53) tmFiber4State53_in_pass1_prefix53

theorem tmFiber4State54_in_pass1_prefix54 :
    tmFiber4StateAt 54 ∈ chainClosureStep tmWord tmFiber4Prefix54 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 10 ∈
      chainClosureStep tmWord tmFiber4Prefix53 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix53 = tmFiber4Prefix10 ++ [tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53]
      (chainClosureStep tmWord tmFiber4Prefix10 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 10) tmFiber4State10_in_pass1_prefix10
  rw [show tmFiber4Prefix54 = tmFiber4Prefix53 ++ [tmFiber4StateAt 54] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 54) []
    (chainClosureStep tmWord tmFiber4Prefix53 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 10) hparentBefore tmFiber4ReverseSingleStep54

theorem tmFiber4State54_in_pass1_full :
    tmFiber4StateAt 54 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix54 ++ [tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix54 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 54) tmFiber4State54_in_pass1_prefix54

theorem tmFiber4State55_in_pass1_prefix55 :
    tmFiber4StateAt 55 ∈ chainClosureStep tmWord tmFiber4Prefix55 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 11 ∈
      chainClosureStep tmWord tmFiber4Prefix54 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix54 = tmFiber4Prefix11 ++ [tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54]
      (chainClosureStep tmWord tmFiber4Prefix11 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 11) tmFiber4State11_in_pass1_prefix11
  rw [show tmFiber4Prefix55 = tmFiber4Prefix54 ++ [tmFiber4StateAt 55] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 55) []
    (chainClosureStep tmWord tmFiber4Prefix54 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 11) hparentBefore tmFiber4ReverseSingleStep55

theorem tmFiber4State55_in_pass1_full :
    tmFiber4StateAt 55 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix55 ++ [tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix55 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 55) tmFiber4State55_in_pass1_prefix55

theorem tmFiber4State58_in_pass1_prefix58 :
    tmFiber4StateAt 58 ∈ chainClosureStep tmWord tmFiber4Prefix58 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 4 ∈
      chainClosureStep tmWord tmFiber4Prefix57 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix57 = tmFiber4Prefix4 ++ [tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57]
      (chainClosureStep tmWord tmFiber4Prefix4 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 4) tmFiber4State4_in_pass1_prefix4
  rw [show tmFiber4Prefix58 = tmFiber4Prefix57 ++ [tmFiber4StateAt 58] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 58) []
    (chainClosureStep tmWord tmFiber4Prefix57 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 4) hparentBefore tmFiber4ReverseSingleStep58

theorem tmFiber4State58_in_pass1_full :
    tmFiber4StateAt 58 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix58 ++ [tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix58 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 58) tmFiber4State58_in_pass1_prefix58

theorem tmFiber4State59_in_pass1_prefix59 :
    tmFiber4StateAt 59 ∈ chainClosureStep tmWord tmFiber4Prefix59 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 5 ∈
      chainClosureStep tmWord tmFiber4Prefix58 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix58 = tmFiber4Prefix5 ++ [tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58]
      (chainClosureStep tmWord tmFiber4Prefix5 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 5) tmFiber4State5_in_pass1_prefix5
  rw [show tmFiber4Prefix59 = tmFiber4Prefix58 ++ [tmFiber4StateAt 59] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 59) []
    (chainClosureStep tmWord tmFiber4Prefix58 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 5) hparentBefore tmFiber4ReverseSingleStep59

theorem tmFiber4State59_in_pass1_full :
    tmFiber4StateAt 59 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix59 ++ [tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix59 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 59) tmFiber4State59_in_pass1_prefix59

theorem tmFiber4State60_in_pass1_prefix60 :
    tmFiber4StateAt 60 ∈ chainClosureStep tmWord tmFiber4Prefix60 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 0 ∈
      chainClosureStep tmWord tmFiber4Prefix59 ([tmFiber4StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber4Prefix59
      ([tmFiber4StateAt 0]) (tmFiber4StateAt 0) (by simp)
  rw [show tmFiber4Prefix60 = tmFiber4Prefix59 ++ [tmFiber4StateAt 60] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 60) []
    (chainClosureStep tmWord tmFiber4Prefix59 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 0) hparentBefore tmFiber4ReverseSingleStep60

theorem tmFiber4State60_in_pass1_full :
    tmFiber4StateAt 60 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix60 ++ [tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix60 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 60) tmFiber4State60_in_pass1_prefix60

theorem tmFiber4State61_in_pass1_prefix61 :
    tmFiber4StateAt 61 ∈ chainClosureStep tmWord tmFiber4Prefix61 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 1 ∈
      chainClosureStep tmWord tmFiber4Prefix60 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix60 = tmFiber4Prefix1 ++ [tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 2, tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60]
      (chainClosureStep tmWord tmFiber4Prefix1 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 1) tmFiber4State1_in_pass1_prefix1
  rw [show tmFiber4Prefix61 = tmFiber4Prefix60 ++ [tmFiber4StateAt 61] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 61) []
    (chainClosureStep tmWord tmFiber4Prefix60 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 1) hparentBefore tmFiber4ReverseSingleStep61

theorem tmFiber4State61_in_pass1_full :
    tmFiber4StateAt 61 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix61 ++ [tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix61 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 61) tmFiber4State61_in_pass1_prefix61

theorem tmFiber4State62_in_pass1_prefix62 :
    tmFiber4StateAt 62 ∈ chainClosureStep tmWord tmFiber4Prefix62 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 2 ∈
      chainClosureStep tmWord tmFiber4Prefix61 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix61 = tmFiber4Prefix2 ++ [tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 3, tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61]
      (chainClosureStep tmWord tmFiber4Prefix2 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 2) tmFiber4State2_in_pass1_prefix2
  rw [show tmFiber4Prefix62 = tmFiber4Prefix61 ++ [tmFiber4StateAt 62] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 62) []
    (chainClosureStep tmWord tmFiber4Prefix61 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 2) hparentBefore tmFiber4ReverseSingleStep62

theorem tmFiber4State62_in_pass1_full :
    tmFiber4StateAt 62 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix62 ++ [tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix62 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 62) tmFiber4State62_in_pass1_prefix62

theorem tmFiber4State63_in_pass1_prefix63 :
    tmFiber4StateAt 63 ∈ chainClosureStep tmWord tmFiber4Prefix63 ([tmFiber4StateAt 0]) := by
  have hparentBefore : tmFiber4StateAt 3 ∈
      chainClosureStep tmWord tmFiber4Prefix62 ([tmFiber4StateAt 0]) := by
    rw [show tmFiber4Prefix62 = tmFiber4Prefix3 ++ [tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 4, tmFiber4StateAt 5, tmFiber4StateAt 6, tmFiber4StateAt 7, tmFiber4StateAt 8, tmFiber4StateAt 9, tmFiber4StateAt 10, tmFiber4StateAt 11, tmFiber4StateAt 12, tmFiber4StateAt 13, tmFiber4StateAt 14, tmFiber4StateAt 15, tmFiber4StateAt 16, tmFiber4StateAt 17, tmFiber4StateAt 18, tmFiber4StateAt 19, tmFiber4StateAt 20, tmFiber4StateAt 21, tmFiber4StateAt 22, tmFiber4StateAt 23, tmFiber4StateAt 24, tmFiber4StateAt 25, tmFiber4StateAt 26, tmFiber4StateAt 27, tmFiber4StateAt 28, tmFiber4StateAt 29, tmFiber4StateAt 30, tmFiber4StateAt 31, tmFiber4StateAt 32, tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62]
      (chainClosureStep tmWord tmFiber4Prefix3 ([tmFiber4StateAt 0]))
      (tmFiber4StateAt 3) tmFiber4State3_in_pass1_prefix3
  rw [show tmFiber4Prefix63 = tmFiber4Prefix62 ++ [tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 63) []
    (chainClosureStep tmWord tmFiber4Prefix62 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 3) hparentBefore tmFiber4ReverseSingleStep63

theorem tmFiber4State63_in_pass1_full :
    tmFiber4StateAt 63 ∈ chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix63 ++ [] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord []
    (chainClosureStep tmWord tmFiber4Prefix63 ([tmFiber4StateAt 0]))
    (tmFiber4StateAt 63) tmFiber4State63_in_pass1_prefix63

theorem tmFiber4State32_in_pass2_prefix32 :
    tmFiber4StateAt 32 ∈ chainClosureStep tmWord tmFiber4Prefix32 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) := by
  have hparentBefore : tmFiber4StateAt 36 ∈
      chainClosureStep tmWord tmFiber4Prefix31 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber4Prefix31
      (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) (tmFiber4StateAt 36) tmFiber4State36_in_pass1_full
  rw [show tmFiber4Prefix32 = tmFiber4Prefix31 ++ [tmFiber4StateAt 32] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 32) []
    (chainClosureStep tmWord tmFiber4Prefix31 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])))
    (tmFiber4StateAt 36) hparentBefore tmFiber4ReverseSingleStep32

theorem tmFiber4State32_in_pass2_full :
    tmFiber4StateAt 32 ∈ chainClosureStep tmWord tmFiber4DirectStates (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix32 ++ [tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 33, tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix32 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])))
    (tmFiber4StateAt 32) tmFiber4State32_in_pass2_prefix32

theorem tmFiber4State33_in_pass2_prefix33 :
    tmFiber4StateAt 33 ∈ chainClosureStep tmWord tmFiber4Prefix33 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) := by
  have hparentBefore : tmFiber4StateAt 37 ∈
      chainClosureStep tmWord tmFiber4Prefix32 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber4Prefix32
      (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) (tmFiber4StateAt 37) tmFiber4State37_in_pass1_full
  rw [show tmFiber4Prefix33 = tmFiber4Prefix32 ++ [tmFiber4StateAt 33] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 33) []
    (chainClosureStep tmWord tmFiber4Prefix32 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])))
    (tmFiber4StateAt 37) hparentBefore tmFiber4ReverseSingleStep33

theorem tmFiber4State33_in_pass2_full :
    tmFiber4StateAt 33 ∈ chainClosureStep tmWord tmFiber4DirectStates (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix33 ++ [tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 34, tmFiber4StateAt 35, tmFiber4StateAt 36, tmFiber4StateAt 37, tmFiber4StateAt 38, tmFiber4StateAt 39, tmFiber4StateAt 40, tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix33 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])))
    (tmFiber4StateAt 33) tmFiber4State33_in_pass2_prefix33

theorem tmFiber4State42_in_pass2_prefix42 :
    tmFiber4StateAt 42 ∈ chainClosureStep tmWord tmFiber4Prefix42 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) := by
  have hparentBefore : tmFiber4StateAt 58 ∈
      chainClosureStep tmWord tmFiber4Prefix41 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber4Prefix41
      (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) (tmFiber4StateAt 58) tmFiber4State58_in_pass1_full
  rw [show tmFiber4Prefix42 = tmFiber4Prefix41 ++ [tmFiber4StateAt 42] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 42) []
    (chainClosureStep tmWord tmFiber4Prefix41 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])))
    (tmFiber4StateAt 58) hparentBefore tmFiber4ReverseSingleStep42

theorem tmFiber4State42_in_pass2_full :
    tmFiber4StateAt 42 ∈ chainClosureStep tmWord tmFiber4DirectStates (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix42 ++ [tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix42 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])))
    (tmFiber4StateAt 42) tmFiber4State42_in_pass2_prefix42

theorem tmFiber4State43_in_pass2_prefix43 :
    tmFiber4StateAt 43 ∈ chainClosureStep tmWord tmFiber4Prefix43 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) := by
  have hparentBefore : tmFiber4StateAt 59 ∈
      chainClosureStep tmWord tmFiber4Prefix42 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber4Prefix42
      (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) (tmFiber4StateAt 59) tmFiber4State59_in_pass1_full
  rw [show tmFiber4Prefix43 = tmFiber4Prefix42 ++ [tmFiber4StateAt 43] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 43) []
    (chainClosureStep tmWord tmFiber4Prefix42 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])))
    (tmFiber4StateAt 59) hparentBefore tmFiber4ReverseSingleStep43

theorem tmFiber4State43_in_pass2_full :
    tmFiber4StateAt 43 ∈ chainClosureStep tmWord tmFiber4DirectStates (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix43 ++ [tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix43 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])))
    (tmFiber4StateAt 43) tmFiber4State43_in_pass2_prefix43

theorem tmFiber4State44_in_pass2_prefix44 :
    tmFiber4StateAt 44 ∈ chainClosureStep tmWord tmFiber4Prefix44 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) := by
  have hparentBefore : tmFiber4StateAt 60 ∈
      chainClosureStep tmWord tmFiber4Prefix43 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber4Prefix43
      (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) (tmFiber4StateAt 60) tmFiber4State60_in_pass1_full
  rw [show tmFiber4Prefix44 = tmFiber4Prefix43 ++ [tmFiber4StateAt 44] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 44) []
    (chainClosureStep tmWord tmFiber4Prefix43 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])))
    (tmFiber4StateAt 60) hparentBefore tmFiber4ReverseSingleStep44

theorem tmFiber4State44_in_pass2_full :
    tmFiber4StateAt 44 ∈ chainClosureStep tmWord tmFiber4DirectStates (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix44 ++ [tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix44 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])))
    (tmFiber4StateAt 44) tmFiber4State44_in_pass2_prefix44

theorem tmFiber4State45_in_pass2_prefix45 :
    tmFiber4StateAt 45 ∈ chainClosureStep tmWord tmFiber4Prefix45 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) := by
  have hparentBefore : tmFiber4StateAt 61 ∈
      chainClosureStep tmWord tmFiber4Prefix44 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber4Prefix44
      (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) (tmFiber4StateAt 61) tmFiber4State61_in_pass1_full
  rw [show tmFiber4Prefix45 = tmFiber4Prefix44 ++ [tmFiber4StateAt 45] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 45) []
    (chainClosureStep tmWord tmFiber4Prefix44 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])))
    (tmFiber4StateAt 61) hparentBefore tmFiber4ReverseSingleStep45

theorem tmFiber4State45_in_pass2_full :
    tmFiber4StateAt 45 ∈ chainClosureStep tmWord tmFiber4DirectStates (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix45 ++ [tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix45 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])))
    (tmFiber4StateAt 45) tmFiber4State45_in_pass2_prefix45

theorem tmFiber4State46_in_pass2_prefix46 :
    tmFiber4StateAt 46 ∈ chainClosureStep tmWord tmFiber4Prefix46 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) := by
  have hparentBefore : tmFiber4StateAt 62 ∈
      chainClosureStep tmWord tmFiber4Prefix45 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber4Prefix45
      (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) (tmFiber4StateAt 62) tmFiber4State62_in_pass1_full
  rw [show tmFiber4Prefix46 = tmFiber4Prefix45 ++ [tmFiber4StateAt 46] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 46) []
    (chainClosureStep tmWord tmFiber4Prefix45 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])))
    (tmFiber4StateAt 62) hparentBefore tmFiber4ReverseSingleStep46

theorem tmFiber4State46_in_pass2_full :
    tmFiber4StateAt 46 ∈ chainClosureStep tmWord tmFiber4DirectStates (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix46 ++ [tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix46 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])))
    (tmFiber4StateAt 46) tmFiber4State46_in_pass2_prefix46

theorem tmFiber4State47_in_pass2_prefix47 :
    tmFiber4StateAt 47 ∈ chainClosureStep tmWord tmFiber4Prefix47 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) := by
  have hparentBefore : tmFiber4StateAt 63 ∈
      chainClosureStep tmWord tmFiber4Prefix46 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber4Prefix46
      (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) (tmFiber4StateAt 63) tmFiber4State63_in_pass1_full
  rw [show tmFiber4Prefix47 = tmFiber4Prefix46 ++ [tmFiber4StateAt 47] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 47) []
    (chainClosureStep tmWord tmFiber4Prefix46 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])))
    (tmFiber4StateAt 63) hparentBefore tmFiber4ReverseSingleStep47

theorem tmFiber4State47_in_pass2_full :
    tmFiber4StateAt 47 ∈ chainClosureStep tmWord tmFiber4DirectStates (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix47 ++ [tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix47 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])))
    (tmFiber4StateAt 47) tmFiber4State47_in_pass2_prefix47

theorem tmFiber4State48_in_pass2_prefix48 :
    tmFiber4StateAt 48 ∈ chainClosureStep tmWord tmFiber4Prefix48 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) := by
  have hparentBefore : tmFiber4StateAt 52 ∈
      chainClosureStep tmWord tmFiber4Prefix47 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber4Prefix47
      (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) (tmFiber4StateAt 52) tmFiber4State52_in_pass1_full
  rw [show tmFiber4Prefix48 = tmFiber4Prefix47 ++ [tmFiber4StateAt 48] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 48) []
    (chainClosureStep tmWord tmFiber4Prefix47 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])))
    (tmFiber4StateAt 52) hparentBefore tmFiber4ReverseSingleStep48

theorem tmFiber4State48_in_pass2_full :
    tmFiber4StateAt 48 ∈ chainClosureStep tmWord tmFiber4DirectStates (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix48 ++ [tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix48 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])))
    (tmFiber4StateAt 48) tmFiber4State48_in_pass2_prefix48

theorem tmFiber4State49_in_pass2_prefix49 :
    tmFiber4StateAt 49 ∈ chainClosureStep tmWord tmFiber4Prefix49 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) := by
  have hparentBefore : tmFiber4StateAt 53 ∈
      chainClosureStep tmWord tmFiber4Prefix48 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber4Prefix48
      (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) (tmFiber4StateAt 53) tmFiber4State53_in_pass1_full
  rw [show tmFiber4Prefix49 = tmFiber4Prefix48 ++ [tmFiber4StateAt 49] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 49) []
    (chainClosureStep tmWord tmFiber4Prefix48 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])))
    (tmFiber4StateAt 53) hparentBefore tmFiber4ReverseSingleStep49

theorem tmFiber4State49_in_pass2_full :
    tmFiber4StateAt 49 ∈ chainClosureStep tmWord tmFiber4DirectStates (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix49 ++ [tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix49 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])))
    (tmFiber4StateAt 49) tmFiber4State49_in_pass2_prefix49

theorem tmFiber4State56_in_pass2_prefix56 :
    tmFiber4StateAt 56 ∈ chainClosureStep tmWord tmFiber4Prefix56 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) := by
  have hparentBefore : tmFiber4StateAt 60 ∈
      chainClosureStep tmWord tmFiber4Prefix55 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber4Prefix55
      (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) (tmFiber4StateAt 60) tmFiber4State60_in_pass1_full
  rw [show tmFiber4Prefix56 = tmFiber4Prefix55 ++ [tmFiber4StateAt 56] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 56) []
    (chainClosureStep tmWord tmFiber4Prefix55 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])))
    (tmFiber4StateAt 60) hparentBefore tmFiber4ReverseSingleStep56

theorem tmFiber4State56_in_pass2_full :
    tmFiber4StateAt 56 ∈ chainClosureStep tmWord tmFiber4DirectStates (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix56 ++ [tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix56 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])))
    (tmFiber4StateAt 56) tmFiber4State56_in_pass2_prefix56

theorem tmFiber4State57_in_pass2_prefix57 :
    tmFiber4StateAt 57 ∈ chainClosureStep tmWord tmFiber4Prefix57 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) := by
  have hparentBefore : tmFiber4StateAt 61 ∈
      chainClosureStep tmWord tmFiber4Prefix56 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber4Prefix56
      (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) (tmFiber4StateAt 61) tmFiber4State61_in_pass1_full
  rw [show tmFiber4Prefix57 = tmFiber4Prefix56 ++ [tmFiber4StateAt 57] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 57) []
    (chainClosureStep tmWord tmFiber4Prefix56 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])))
    (tmFiber4StateAt 61) hparentBefore tmFiber4ReverseSingleStep57

theorem tmFiber4State57_in_pass2_full :
    tmFiber4StateAt 57 ∈ chainClosureStep tmWord tmFiber4DirectStates (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix57 ++ [tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix57 (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0])))
    (tmFiber4StateAt 57) tmFiber4State57_in_pass2_prefix57

theorem tmFiber4State40_in_pass3_prefix40 :
    tmFiber4StateAt 40 ∈ chainClosureStep tmWord tmFiber4Prefix40 (chainClosureStep tmWord tmFiber4DirectStates (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]))) := by
  have hparentBefore : tmFiber4StateAt 44 ∈
      chainClosureStep tmWord tmFiber4Prefix39 (chainClosureStep tmWord tmFiber4DirectStates (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]))) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber4Prefix39
      (chainClosureStep tmWord tmFiber4DirectStates (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]))) (tmFiber4StateAt 44) tmFiber4State44_in_pass2_full
  rw [show tmFiber4Prefix40 = tmFiber4Prefix39 ++ [tmFiber4StateAt 40] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 40) []
    (chainClosureStep tmWord tmFiber4Prefix39 (chainClosureStep tmWord tmFiber4DirectStates (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]))))
    (tmFiber4StateAt 44) hparentBefore tmFiber4ReverseSingleStep40

theorem tmFiber4State40_in_pass3_full :
    tmFiber4StateAt 40 ∈ chainClosureStep tmWord tmFiber4DirectStates (chainClosureStep tmWord tmFiber4DirectStates (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]))) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix40 ++ [tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 41, tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix40 (chainClosureStep tmWord tmFiber4DirectStates (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]))))
    (tmFiber4StateAt 40) tmFiber4State40_in_pass3_prefix40

theorem tmFiber4State41_in_pass3_prefix41 :
    tmFiber4StateAt 41 ∈ chainClosureStep tmWord tmFiber4Prefix41 (chainClosureStep tmWord tmFiber4DirectStates (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]))) := by
  have hparentBefore : tmFiber4StateAt 45 ∈
      chainClosureStep tmWord tmFiber4Prefix40 (chainClosureStep tmWord tmFiber4DirectStates (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]))) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber4Prefix40
      (chainClosureStep tmWord tmFiber4DirectStates (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]))) (tmFiber4StateAt 45) tmFiber4State45_in_pass2_full
  rw [show tmFiber4Prefix41 = tmFiber4Prefix40 ++ [tmFiber4StateAt 41] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber4StateAt 41) []
    (chainClosureStep tmWord tmFiber4Prefix40 (chainClosureStep tmWord tmFiber4DirectStates (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]))))
    (tmFiber4StateAt 45) hparentBefore tmFiber4ReverseSingleStep41

theorem tmFiber4State41_in_pass3_full :
    tmFiber4StateAt 41 ∈ chainClosureStep tmWord tmFiber4DirectStates (chainClosureStep tmWord tmFiber4DirectStates (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]))) := by
  rw [show tmFiber4DirectStates = tmFiber4Prefix41 ++ [tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber4StateAt 42, tmFiber4StateAt 43, tmFiber4StateAt 44, tmFiber4StateAt 45, tmFiber4StateAt 46, tmFiber4StateAt 47, tmFiber4StateAt 48, tmFiber4StateAt 49, tmFiber4StateAt 50, tmFiber4StateAt 51, tmFiber4StateAt 52, tmFiber4StateAt 53, tmFiber4StateAt 54, tmFiber4StateAt 55, tmFiber4StateAt 56, tmFiber4StateAt 57, tmFiber4StateAt 58, tmFiber4StateAt 59, tmFiber4StateAt 60, tmFiber4StateAt 61, tmFiber4StateAt 62, tmFiber4StateAt 63]
    (chainClosureStep tmWord tmFiber4Prefix41 (chainClosureStep tmWord tmFiber4DirectStates (chainClosureStep tmWord tmFiber4DirectStates ([tmFiber4StateAt 0]))))
    (tmFiber4StateAt 41) tmFiber4State41_in_pass3_prefix41

theorem tmFiber4FirstPassGrows :
    ((chainClosureStep tmWord tmFiber4DirectStates [tmFiber4StateAt 0]).length ==
      [tmFiber4StateAt 0].length) = false := by
  have hroot : tmFiber4StateAt 0 ∈
      chainClosureStep tmWord tmFiber4DirectStates [tmFiber4StateAt 0] :=
    chainClosureStep_mem_of_seen tmWord tmFiber4DirectStates
      [tmFiber4StateAt 0] (tmFiber4StateAt 0) (by simp)
  have hnew : tmFiber4StateAt 1 ∈
      chainClosureStep tmWord tmFiber4DirectStates [tmFiber4StateAt 0] :=
    tmFiber4State1_in_pass1_full
  simpa using list_length_beq_one_false_of_two_mem
    (chainClosureStep tmWord tmFiber4DirectStates [tmFiber4StateAt 0])
    (tmFiber4StateAt 0) (tmFiber4StateAt 1) hroot hnew (by decide)

theorem tmFiber4State0_in_close_short :
    tmFiber4StateAt 0 ∈ closeChainFiber tmWord tmFiber4DirectStates 0 [tmFiber4StateAt 0] := by
  simp [closeChainFiber]

theorem tmFiber4State1_in_close_short :
    tmFiber4StateAt 1 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 1) tmFiber4State1_in_pass1_full

theorem tmFiber4State2_in_close_short :
    tmFiber4StateAt 2 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 2) tmFiber4State2_in_pass1_full

theorem tmFiber4State3_in_close_short :
    tmFiber4StateAt 3 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 3) tmFiber4State3_in_pass1_full

theorem tmFiber4State4_in_close_short :
    tmFiber4StateAt 4 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 4) tmFiber4State4_in_pass1_full

theorem tmFiber4State5_in_close_short :
    tmFiber4StateAt 5 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 5) tmFiber4State5_in_pass1_full

theorem tmFiber4State6_in_close_short :
    tmFiber4StateAt 6 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 6) tmFiber4State6_in_pass1_full

theorem tmFiber4State7_in_close_short :
    tmFiber4StateAt 7 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 7) tmFiber4State7_in_pass1_full

theorem tmFiber4State8_in_close_short :
    tmFiber4StateAt 8 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 8) tmFiber4State8_in_pass1_full

theorem tmFiber4State9_in_close_short :
    tmFiber4StateAt 9 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 9) tmFiber4State9_in_pass1_full

theorem tmFiber4State10_in_close_short :
    tmFiber4StateAt 10 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 10) tmFiber4State10_in_pass1_full

theorem tmFiber4State11_in_close_short :
    tmFiber4StateAt 11 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 11) tmFiber4State11_in_pass1_full

theorem tmFiber4State12_in_close_short :
    tmFiber4StateAt 12 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 12) tmFiber4State12_in_pass1_full

theorem tmFiber4State13_in_close_short :
    tmFiber4StateAt 13 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 13) tmFiber4State13_in_pass1_full

theorem tmFiber4State14_in_close_short :
    tmFiber4StateAt 14 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 14) tmFiber4State14_in_pass1_full

theorem tmFiber4State15_in_close_short :
    tmFiber4StateAt 15 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 15) tmFiber4State15_in_pass1_full

theorem tmFiber4State16_in_close_short :
    tmFiber4StateAt 16 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 16) tmFiber4State16_in_pass1_full

theorem tmFiber4State17_in_close_short :
    tmFiber4StateAt 17 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 17) tmFiber4State17_in_pass1_full

theorem tmFiber4State18_in_close_short :
    tmFiber4StateAt 18 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 18) tmFiber4State18_in_pass1_full

theorem tmFiber4State19_in_close_short :
    tmFiber4StateAt 19 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 19) tmFiber4State19_in_pass1_full

theorem tmFiber4State20_in_close_short :
    tmFiber4StateAt 20 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 20) tmFiber4State20_in_pass1_full

theorem tmFiber4State21_in_close_short :
    tmFiber4StateAt 21 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 21) tmFiber4State21_in_pass1_full

theorem tmFiber4State22_in_close_short :
    tmFiber4StateAt 22 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 22) tmFiber4State22_in_pass1_full

theorem tmFiber4State23_in_close_short :
    tmFiber4StateAt 23 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 23) tmFiber4State23_in_pass1_full

theorem tmFiber4State24_in_close_short :
    tmFiber4StateAt 24 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 24) tmFiber4State24_in_pass1_full

theorem tmFiber4State25_in_close_short :
    tmFiber4StateAt 25 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 25) tmFiber4State25_in_pass1_full

theorem tmFiber4State26_in_close_short :
    tmFiber4StateAt 26 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 26) tmFiber4State26_in_pass1_full

theorem tmFiber4State27_in_close_short :
    tmFiber4StateAt 27 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 27) tmFiber4State27_in_pass1_full

theorem tmFiber4State28_in_close_short :
    tmFiber4StateAt 28 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 28) tmFiber4State28_in_pass1_full

theorem tmFiber4State29_in_close_short :
    tmFiber4StateAt 29 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 29) tmFiber4State29_in_pass1_full

theorem tmFiber4State30_in_close_short :
    tmFiber4StateAt 30 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 30) tmFiber4State30_in_pass1_full

theorem tmFiber4State31_in_close_short :
    tmFiber4StateAt 31 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 31) tmFiber4State31_in_pass1_full

theorem tmFiber4State34_in_close_short :
    tmFiber4StateAt 34 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 34) tmFiber4State34_in_pass1_full

theorem tmFiber4State35_in_close_short :
    tmFiber4StateAt 35 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 35) tmFiber4State35_in_pass1_full

theorem tmFiber4State36_in_close_short :
    tmFiber4StateAt 36 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 36) tmFiber4State36_in_pass1_full

theorem tmFiber4State37_in_close_short :
    tmFiber4StateAt 37 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 37) tmFiber4State37_in_pass1_full

theorem tmFiber4State38_in_close_short :
    tmFiber4StateAt 38 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 38) tmFiber4State38_in_pass1_full

theorem tmFiber4State39_in_close_short :
    tmFiber4StateAt 39 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 39) tmFiber4State39_in_pass1_full

theorem tmFiber4State50_in_close_short :
    tmFiber4StateAt 50 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 50) tmFiber4State50_in_pass1_full

theorem tmFiber4State51_in_close_short :
    tmFiber4StateAt 51 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 51) tmFiber4State51_in_pass1_full

theorem tmFiber4State52_in_close_short :
    tmFiber4StateAt 52 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 52) tmFiber4State52_in_pass1_full

theorem tmFiber4State53_in_close_short :
    tmFiber4StateAt 53 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 53) tmFiber4State53_in_pass1_full

theorem tmFiber4State54_in_close_short :
    tmFiber4StateAt 54 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 54) tmFiber4State54_in_pass1_full

theorem tmFiber4State55_in_close_short :
    tmFiber4StateAt 55 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 55) tmFiber4State55_in_pass1_full

theorem tmFiber4State58_in_close_short :
    tmFiber4StateAt 58 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 58) tmFiber4State58_in_pass1_full

theorem tmFiber4State59_in_close_short :
    tmFiber4StateAt 59 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 59) tmFiber4State59_in_pass1_full

theorem tmFiber4State60_in_close_short :
    tmFiber4StateAt 60 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 60) tmFiber4State60_in_pass1_full

theorem tmFiber4State61_in_close_short :
    tmFiber4StateAt 61 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 61) tmFiber4State61_in_pass1_full

theorem tmFiber4State62_in_close_short :
    tmFiber4StateAt 62 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 62) tmFiber4State62_in_pass1_full

theorem tmFiber4State63_in_close_short :
    tmFiber4StateAt 63 ∈ closeChainFiber tmWord tmFiber4DirectStates 1 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 63) tmFiber4State63_in_pass1_full

theorem tmFiber4State32_in_close_short :
    tmFiber4StateAt 32 ∈ closeChainFiber tmWord tmFiber4DirectStates 2 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 32) tmFiber4FirstPassGrows
    tmFiber4State32_in_pass2_full

theorem tmFiber4State33_in_close_short :
    tmFiber4StateAt 33 ∈ closeChainFiber tmWord tmFiber4DirectStates 2 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 33) tmFiber4FirstPassGrows
    tmFiber4State33_in_pass2_full

theorem tmFiber4State42_in_close_short :
    tmFiber4StateAt 42 ∈ closeChainFiber tmWord tmFiber4DirectStates 2 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 42) tmFiber4FirstPassGrows
    tmFiber4State42_in_pass2_full

theorem tmFiber4State43_in_close_short :
    tmFiber4StateAt 43 ∈ closeChainFiber tmWord tmFiber4DirectStates 2 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 43) tmFiber4FirstPassGrows
    tmFiber4State43_in_pass2_full

theorem tmFiber4State44_in_close_short :
    tmFiber4StateAt 44 ∈ closeChainFiber tmWord tmFiber4DirectStates 2 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 44) tmFiber4FirstPassGrows
    tmFiber4State44_in_pass2_full

theorem tmFiber4State45_in_close_short :
    tmFiber4StateAt 45 ∈ closeChainFiber tmWord tmFiber4DirectStates 2 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 45) tmFiber4FirstPassGrows
    tmFiber4State45_in_pass2_full

theorem tmFiber4State46_in_close_short :
    tmFiber4StateAt 46 ∈ closeChainFiber tmWord tmFiber4DirectStates 2 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 46) tmFiber4FirstPassGrows
    tmFiber4State46_in_pass2_full

theorem tmFiber4State47_in_close_short :
    tmFiber4StateAt 47 ∈ closeChainFiber tmWord tmFiber4DirectStates 2 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 47) tmFiber4FirstPassGrows
    tmFiber4State47_in_pass2_full

theorem tmFiber4State48_in_close_short :
    tmFiber4StateAt 48 ∈ closeChainFiber tmWord tmFiber4DirectStates 2 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 48) tmFiber4FirstPassGrows
    tmFiber4State48_in_pass2_full

theorem tmFiber4State49_in_close_short :
    tmFiber4StateAt 49 ∈ closeChainFiber tmWord tmFiber4DirectStates 2 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 49) tmFiber4FirstPassGrows
    tmFiber4State49_in_pass2_full

theorem tmFiber4State56_in_close_short :
    tmFiber4StateAt 56 ∈ closeChainFiber tmWord tmFiber4DirectStates 2 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 56) tmFiber4FirstPassGrows
    tmFiber4State56_in_pass2_full

theorem tmFiber4State57_in_close_short :
    tmFiber4StateAt 57 ∈ closeChainFiber tmWord tmFiber4DirectStates 2 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber4DirectStates 0
    [tmFiber4StateAt 0] (tmFiber4StateAt 57) tmFiber4FirstPassGrows
    tmFiber4State57_in_pass2_full

theorem tmFiber4State40_in_close_short :
    tmFiber4StateAt 40 ∈ closeChainFiber tmWord tmFiber4DirectStates 3 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_step_of_close tmWord tmFiber4DirectStates 2
    [tmFiber4StateAt 0] (tmFiber4StateAt 44) (tmFiber4StateAt 40)
    (by simp) tmFiber4State44_in_close_short (by decide) tmFiber4ReverseSingleStep40

theorem tmFiber4State41_in_close_short :
    tmFiber4StateAt 41 ∈ closeChainFiber tmWord tmFiber4DirectStates 3 [tmFiber4StateAt 0] := by
  exact closeChainFiber_mem_step_of_close tmWord tmFiber4DirectStates 2
    [tmFiber4StateAt 0] (tmFiber4StateAt 45) (tmFiber4StateAt 41)
    (by simp) tmFiber4State45_in_close_short (by decide) tmFiber4ReverseSingleStep41

theorem tmFiber4State0_in_close :
    tmFiber4StateAt 0 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 0 ∈ closeChainFiber tmWord tmFiber4DirectStates (0 + 64) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 0 64
    [tmFiber4StateAt 0] (tmFiber4StateAt 0) tmFiber4State0_in_close_short

theorem tmFiber4State1_in_close :
    tmFiber4StateAt 1 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 1 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 1) tmFiber4State1_in_close_short

theorem tmFiber4State2_in_close :
    tmFiber4StateAt 2 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 2 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 2) tmFiber4State2_in_close_short

theorem tmFiber4State3_in_close :
    tmFiber4StateAt 3 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 3 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 3) tmFiber4State3_in_close_short

theorem tmFiber4State4_in_close :
    tmFiber4StateAt 4 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 4 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 4) tmFiber4State4_in_close_short

theorem tmFiber4State5_in_close :
    tmFiber4StateAt 5 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 5 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 5) tmFiber4State5_in_close_short

theorem tmFiber4State6_in_close :
    tmFiber4StateAt 6 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 6 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 6) tmFiber4State6_in_close_short

theorem tmFiber4State7_in_close :
    tmFiber4StateAt 7 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 7 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 7) tmFiber4State7_in_close_short

theorem tmFiber4State8_in_close :
    tmFiber4StateAt 8 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 8 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 8) tmFiber4State8_in_close_short

theorem tmFiber4State9_in_close :
    tmFiber4StateAt 9 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 9 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 9) tmFiber4State9_in_close_short

theorem tmFiber4State10_in_close :
    tmFiber4StateAt 10 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 10 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 10) tmFiber4State10_in_close_short

theorem tmFiber4State11_in_close :
    tmFiber4StateAt 11 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 11 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 11) tmFiber4State11_in_close_short

theorem tmFiber4State12_in_close :
    tmFiber4StateAt 12 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 12 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 12) tmFiber4State12_in_close_short

theorem tmFiber4State13_in_close :
    tmFiber4StateAt 13 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 13 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 13) tmFiber4State13_in_close_short

theorem tmFiber4State14_in_close :
    tmFiber4StateAt 14 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 14 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 14) tmFiber4State14_in_close_short

theorem tmFiber4State15_in_close :
    tmFiber4StateAt 15 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 15 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 15) tmFiber4State15_in_close_short

theorem tmFiber4State16_in_close :
    tmFiber4StateAt 16 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 16 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 16) tmFiber4State16_in_close_short

theorem tmFiber4State17_in_close :
    tmFiber4StateAt 17 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 17 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 17) tmFiber4State17_in_close_short

theorem tmFiber4State18_in_close :
    tmFiber4StateAt 18 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 18 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 18) tmFiber4State18_in_close_short

theorem tmFiber4State19_in_close :
    tmFiber4StateAt 19 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 19 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 19) tmFiber4State19_in_close_short

theorem tmFiber4State20_in_close :
    tmFiber4StateAt 20 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 20 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 20) tmFiber4State20_in_close_short

theorem tmFiber4State21_in_close :
    tmFiber4StateAt 21 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 21 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 21) tmFiber4State21_in_close_short

theorem tmFiber4State22_in_close :
    tmFiber4StateAt 22 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 22 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 22) tmFiber4State22_in_close_short

theorem tmFiber4State23_in_close :
    tmFiber4StateAt 23 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 23 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 23) tmFiber4State23_in_close_short

theorem tmFiber4State24_in_close :
    tmFiber4StateAt 24 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 24 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 24) tmFiber4State24_in_close_short

theorem tmFiber4State25_in_close :
    tmFiber4StateAt 25 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 25 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 25) tmFiber4State25_in_close_short

theorem tmFiber4State26_in_close :
    tmFiber4StateAt 26 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 26 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 26) tmFiber4State26_in_close_short

theorem tmFiber4State27_in_close :
    tmFiber4StateAt 27 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 27 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 27) tmFiber4State27_in_close_short

theorem tmFiber4State28_in_close :
    tmFiber4StateAt 28 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 28 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 28) tmFiber4State28_in_close_short

theorem tmFiber4State29_in_close :
    tmFiber4StateAt 29 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 29 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 29) tmFiber4State29_in_close_short

theorem tmFiber4State30_in_close :
    tmFiber4StateAt 30 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 30 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 30) tmFiber4State30_in_close_short

theorem tmFiber4State31_in_close :
    tmFiber4StateAt 31 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 31 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 31) tmFiber4State31_in_close_short

theorem tmFiber4State32_in_close :
    tmFiber4StateAt 32 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 32 ∈ closeChainFiber tmWord tmFiber4DirectStates (2 + 62) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 2 62
    [tmFiber4StateAt 0] (tmFiber4StateAt 32) tmFiber4State32_in_close_short

theorem tmFiber4State33_in_close :
    tmFiber4StateAt 33 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 33 ∈ closeChainFiber tmWord tmFiber4DirectStates (2 + 62) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 2 62
    [tmFiber4StateAt 0] (tmFiber4StateAt 33) tmFiber4State33_in_close_short

theorem tmFiber4State34_in_close :
    tmFiber4StateAt 34 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 34 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 34) tmFiber4State34_in_close_short

theorem tmFiber4State35_in_close :
    tmFiber4StateAt 35 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 35 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 35) tmFiber4State35_in_close_short

theorem tmFiber4State36_in_close :
    tmFiber4StateAt 36 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 36 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 36) tmFiber4State36_in_close_short

theorem tmFiber4State37_in_close :
    tmFiber4StateAt 37 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 37 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 37) tmFiber4State37_in_close_short

theorem tmFiber4State38_in_close :
    tmFiber4StateAt 38 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 38 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 38) tmFiber4State38_in_close_short

theorem tmFiber4State39_in_close :
    tmFiber4StateAt 39 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 39 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 39) tmFiber4State39_in_close_short

theorem tmFiber4State40_in_close :
    tmFiber4StateAt 40 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 40 ∈ closeChainFiber tmWord tmFiber4DirectStates (3 + 61) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 3 61
    [tmFiber4StateAt 0] (tmFiber4StateAt 40) tmFiber4State40_in_close_short

theorem tmFiber4State41_in_close :
    tmFiber4StateAt 41 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 41 ∈ closeChainFiber tmWord tmFiber4DirectStates (3 + 61) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 3 61
    [tmFiber4StateAt 0] (tmFiber4StateAt 41) tmFiber4State41_in_close_short

theorem tmFiber4State42_in_close :
    tmFiber4StateAt 42 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 42 ∈ closeChainFiber tmWord tmFiber4DirectStates (2 + 62) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 2 62
    [tmFiber4StateAt 0] (tmFiber4StateAt 42) tmFiber4State42_in_close_short

theorem tmFiber4State43_in_close :
    tmFiber4StateAt 43 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 43 ∈ closeChainFiber tmWord tmFiber4DirectStates (2 + 62) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 2 62
    [tmFiber4StateAt 0] (tmFiber4StateAt 43) tmFiber4State43_in_close_short

theorem tmFiber4State44_in_close :
    tmFiber4StateAt 44 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 44 ∈ closeChainFiber tmWord tmFiber4DirectStates (2 + 62) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 2 62
    [tmFiber4StateAt 0] (tmFiber4StateAt 44) tmFiber4State44_in_close_short

theorem tmFiber4State45_in_close :
    tmFiber4StateAt 45 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 45 ∈ closeChainFiber tmWord tmFiber4DirectStates (2 + 62) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 2 62
    [tmFiber4StateAt 0] (tmFiber4StateAt 45) tmFiber4State45_in_close_short

theorem tmFiber4State46_in_close :
    tmFiber4StateAt 46 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 46 ∈ closeChainFiber tmWord tmFiber4DirectStates (2 + 62) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 2 62
    [tmFiber4StateAt 0] (tmFiber4StateAt 46) tmFiber4State46_in_close_short

theorem tmFiber4State47_in_close :
    tmFiber4StateAt 47 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 47 ∈ closeChainFiber tmWord tmFiber4DirectStates (2 + 62) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 2 62
    [tmFiber4StateAt 0] (tmFiber4StateAt 47) tmFiber4State47_in_close_short

theorem tmFiber4State48_in_close :
    tmFiber4StateAt 48 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 48 ∈ closeChainFiber tmWord tmFiber4DirectStates (2 + 62) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 2 62
    [tmFiber4StateAt 0] (tmFiber4StateAt 48) tmFiber4State48_in_close_short

theorem tmFiber4State49_in_close :
    tmFiber4StateAt 49 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 49 ∈ closeChainFiber tmWord tmFiber4DirectStates (2 + 62) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 2 62
    [tmFiber4StateAt 0] (tmFiber4StateAt 49) tmFiber4State49_in_close_short

theorem tmFiber4State50_in_close :
    tmFiber4StateAt 50 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 50 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 50) tmFiber4State50_in_close_short

theorem tmFiber4State51_in_close :
    tmFiber4StateAt 51 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 51 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 51) tmFiber4State51_in_close_short

theorem tmFiber4State52_in_close :
    tmFiber4StateAt 52 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 52 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 52) tmFiber4State52_in_close_short

theorem tmFiber4State53_in_close :
    tmFiber4StateAt 53 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 53 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 53) tmFiber4State53_in_close_short

theorem tmFiber4State54_in_close :
    tmFiber4StateAt 54 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 54 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 54) tmFiber4State54_in_close_short

theorem tmFiber4State55_in_close :
    tmFiber4StateAt 55 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 55 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 55) tmFiber4State55_in_close_short

theorem tmFiber4State56_in_close :
    tmFiber4StateAt 56 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 56 ∈ closeChainFiber tmWord tmFiber4DirectStates (2 + 62) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 2 62
    [tmFiber4StateAt 0] (tmFiber4StateAt 56) tmFiber4State56_in_close_short

theorem tmFiber4State57_in_close :
    tmFiber4StateAt 57 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 57 ∈ closeChainFiber tmWord tmFiber4DirectStates (2 + 62) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 2 62
    [tmFiber4StateAt 0] (tmFiber4StateAt 57) tmFiber4State57_in_close_short

theorem tmFiber4State58_in_close :
    tmFiber4StateAt 58 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 58 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 58) tmFiber4State58_in_close_short

theorem tmFiber4State59_in_close :
    tmFiber4StateAt 59 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 59 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 59) tmFiber4State59_in_close_short

theorem tmFiber4State60_in_close :
    tmFiber4StateAt 60 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 60 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 60) tmFiber4State60_in_close_short

theorem tmFiber4State61_in_close :
    tmFiber4StateAt 61 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 61 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 61) tmFiber4State61_in_close_short

theorem tmFiber4State62_in_close :
    tmFiber4StateAt 62 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 62 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 62) tmFiber4State62_in_close_short

theorem tmFiber4State63_in_close :
    tmFiber4StateAt 63 ∈ closeChainFiber tmWord tmFiber4DirectStates tmFiber4DirectStates.length [tmFiber4StateAt 0] := by
  change tmFiber4StateAt 63 ∈ closeChainFiber tmWord tmFiber4DirectStates (1 + 63) [tmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber4DirectStates 1 63
    [tmFiber4StateAt 0] (tmFiber4StateAt 63) tmFiber4State63_in_close_short

theorem tmFiber4DirectConnected :
    chainFiberConnected tmWord tmFiber4DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [tmFiber4DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact tmFiber4State0_in_close
  · subst state
    exact tmFiber4State1_in_close
  · subst state
    exact tmFiber4State2_in_close
  · subst state
    exact tmFiber4State3_in_close
  · subst state
    exact tmFiber4State4_in_close
  · subst state
    exact tmFiber4State5_in_close
  · subst state
    exact tmFiber4State6_in_close
  · subst state
    exact tmFiber4State7_in_close
  · subst state
    exact tmFiber4State8_in_close
  · subst state
    exact tmFiber4State9_in_close
  · subst state
    exact tmFiber4State10_in_close
  · subst state
    exact tmFiber4State11_in_close
  · subst state
    exact tmFiber4State12_in_close
  · subst state
    exact tmFiber4State13_in_close
  · subst state
    exact tmFiber4State14_in_close
  · subst state
    exact tmFiber4State15_in_close
  · subst state
    exact tmFiber4State16_in_close
  · subst state
    exact tmFiber4State17_in_close
  · subst state
    exact tmFiber4State18_in_close
  · subst state
    exact tmFiber4State19_in_close
  · subst state
    exact tmFiber4State20_in_close
  · subst state
    exact tmFiber4State21_in_close
  · subst state
    exact tmFiber4State22_in_close
  · subst state
    exact tmFiber4State23_in_close
  · subst state
    exact tmFiber4State24_in_close
  · subst state
    exact tmFiber4State25_in_close
  · subst state
    exact tmFiber4State26_in_close
  · subst state
    exact tmFiber4State27_in_close
  · subst state
    exact tmFiber4State28_in_close
  · subst state
    exact tmFiber4State29_in_close
  · subst state
    exact tmFiber4State30_in_close
  · subst state
    exact tmFiber4State31_in_close
  · subst state
    exact tmFiber4State32_in_close
  · subst state
    exact tmFiber4State33_in_close
  · subst state
    exact tmFiber4State34_in_close
  · subst state
    exact tmFiber4State35_in_close
  · subst state
    exact tmFiber4State36_in_close
  · subst state
    exact tmFiber4State37_in_close
  · subst state
    exact tmFiber4State38_in_close
  · subst state
    exact tmFiber4State39_in_close
  · subst state
    exact tmFiber4State40_in_close
  · subst state
    exact tmFiber4State41_in_close
  · subst state
    exact tmFiber4State42_in_close
  · subst state
    exact tmFiber4State43_in_close
  · subst state
    exact tmFiber4State44_in_close
  · subst state
    exact tmFiber4State45_in_close
  · subst state
    exact tmFiber4State46_in_close
  · subst state
    exact tmFiber4State47_in_close
  · subst state
    exact tmFiber4State48_in_close
  · subst state
    exact tmFiber4State49_in_close
  · subst state
    exact tmFiber4State50_in_close
  · subst state
    exact tmFiber4State51_in_close
  · subst state
    exact tmFiber4State52_in_close
  · subst state
    exact tmFiber4State53_in_close
  · subst state
    exact tmFiber4State54_in_close
  · subst state
    exact tmFiber4State55_in_close
  · subst state
    exact tmFiber4State56_in_close
  · subst state
    exact tmFiber4State57_in_close
  · subst state
    exact tmFiber4State58_in_close
  · subst state
    exact tmFiber4State59_in_close
  · subst state
    exact tmFiber4State60_in_close
  · subst state
    exact tmFiber4State61_in_close
  · subst state
    exact tmFiber4State62_in_close
  · subst state
    exact tmFiber4State63_in_close
  · cases h

end GoertzelLemma818LengthTwoTMLargeFiberBridge

end Mettapedia.GraphTheory.FourColor
